From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

(* notice that is_list itself is of the form A -> val -> iProp for some A! *)
Fixpoint is_list `{!heapG Σ} {A} (res : A -> val -> iProp Σ) (xs : list A) (vs : val) : iProp Σ :=
  match xs with
  | [] => ⌜vs = InjLV #()⌝
  | x :: xs' => ∃(lh : loc) (v vs' : val), ⌜vs = InjRV #lh⌝ ∗ lh ↦ (v, vs') ∗ res x v ∗ is_list res xs' vs'
end%I.

Section MutatingMap.
  Context `{heapG Σ}.

  Definition prog_for_each : val :=
    rec: "for_each" "f" "xs" :=
      match: "xs" with
        InjL <> => Skip
      | InjR "cons" => "f" (Fst !"cons");; "for_each" "f" (Snd !"cons")
      end.

  Lemma prog_for_each_loop_wp {A}
        (past : list A)
        (res : A -> val -> iProp Σ)
        (I : list A -> iProp Σ)
        (f_coq : A -> A)
        (xs : list A)
        (f : val)
        (vs : val):
    {{{ is_list res xs vs
      ∗ I past
      (* the invariant needs to be stated in terms of the old list,
      and not the new one, because f_coq might not have an inverse. Of
      course we could also give both the old and the new values, but
      that would be redundant since x' = f_coq x. *)
      ∗ (∀ y ys vy, {{{ res y vy ∗ I ys }}} f vy {{{ RET #(); res (f_coq y) vy ∗ I (ys ++ [y]) }}})
    }}}
      prog_for_each f vs
    {{{ RET #(); is_list res (f_coq <$> xs) vs ∗ I (past ++ xs) }}}.
  Proof.
    iIntros (Φ) "(Hxs & HI & #Hf) HΦ".
    iInduction xs as [|x xs'] "IH" forall (past vs Φ); simpl; wp_rec; wp_let.
    - iDestruct "Hxs" as "%"; subst. wp_pures.
      iApply "HΦ".
      rewrite app_nil_r.
      by iFrame.
    - iDestruct "Hxs" as (lh v vs' ->) "(Hlh & Hres & Hxs')".
      wp_pures. wp_load. wp_proj.
      wp_apply ("Hf" $! x past v with "[$HI $Hres]").
      iIntros "[Hres HI]".
      wp_seq. wp_load. wp_proj.
      wp_apply ("IH" with "Hxs' HI").
      iIntros "[Hfxs HI]".
      iApply "HΦ".
      rewrite <- app_assoc.
      simpl.
      iFrame.
      iExists lh, v, vs'.
      by iFrame.
  Qed.

  Definition prog_for_each_wp {A} := @prog_for_each_loop_wp A [].

End MutatingMap.

Section SumExample.
  Context `{!heapG Σ}.

  Definition prog_mapper : val := λ: "s" "x", "s" <- !"s" + !"x";; "x" <- !"x" + #1.

  Definition prog_sum_loop : val := λ: "s" "xs",
    let: "f" := prog_mapper "s" in
    prog_for_each "f" "xs".

  Definition prog_sum : val := λ: "xs",
    let: "s" := ref #0 in
    prog_sum_loop "s" "xs";; !"s".

  Definition num_to_ref (x : Z) (v : val) : iProp Σ :=
    (∃(l : loc), ⌜v = #l⌝ ∗ l ↦ #x)%I.

  Definition add_one (x : Z) : Z := x + 1.

  Definition sum (xs : list Z) : Z := fold_right Z.add 0 xs.

  Definition sum_invariant (ls : loc) (n : Z) (xs : list Z) : iProp Σ :=
    (ls ↦ #(sum xs + n))%I.

  Lemma foldr_sum x xs:
    foldr Z.add x xs = x + foldr Z.add 0 xs.
  Proof.
    induction xs as [|x' xs'].
    - simpl. omega.
    - simpl. rewrite IHxs'. omega.
  Qed.

  Lemma prog_sum_loop_wp (ls : loc) (n : Z) (v : val) (xs : list Z):
    {{{ is_list num_to_ref xs v ∗ ls ↦ #n }}}
      prog_sum_loop #ls v
    {{{ RET #(); is_list num_to_ref (add_one <$> xs) v ∗ ls ↦ #(sum xs + n) }}}.
  Proof.
    iIntros (Φ) "[Hv Hls] HΦ".
    wp_rec; wp_pures. wp_lam. wp_pures.
    iAssert (sum_invariant ls n []) with "[Hls]" as "Hls".
    { rewrite /sum_invariant. simpl. by replace (0 + n)%Z with n%Z by omega. }
    wp_apply (prog_for_each_wp
                num_to_ref
                (sum_invariant ls n)
                add_one
                xs
                with "[$Hv $Hls]").
    - (* prove Hoare triple about f *)
      iIntros (y ys vy Φ'). iModIntro.
      iIntros "[Hy Hinv] HΦ'".
      wp_pures.
      rewrite /sum_invariant /num_to_ref.
      iDestruct "Hy" as (ly ->) "Hly".
      wp_load. wp_load. wp_op. wp_store.
      wp_load. wp_op. wp_store. iApply "HΦ'".
      iSplitL "Hly".
      + iExists ly. rewrite /add_one. by iFrame.
      + rewrite /sum. rewrite foldr_app. simpl.
        replace (y + 0)%Z with y%Z by omega.
        rewrite (foldr_sum y ys).
        by replace (foldr Z.add 0 ys + n + y) with (y + foldr Z.add 0 ys + n) by omega.
    - iFrame.
  Qed.

  Lemma prog_sum_wp (v : val) (xs : list Z):
    {{{ is_list num_to_ref xs v }}}
      prog_sum v
    {{{ s, RET s; is_list num_to_ref (add_one <$> xs) v ∗ ⌜s = #(sum xs)⌝}}}.
  Proof.
    iIntros (Φ) "Hxs HΦ".
    wp_lam. wp_alloc s as "Hs". wp_let.
    wp_apply (prog_sum_loop_wp with "[$Hxs $Hs]").
    iIntros "[Hxs Hs]".
    wp_seq. wp_load.
    iApply "HΦ".
    iFrame.
    iPureIntro. by replace (sum xs + 0) with (sum xs) by omega.
  Qed.

End SumExample.
