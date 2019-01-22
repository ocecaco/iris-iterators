From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

(* different from the other is_list from foldr.v *)
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
        (f : val)
        (xs : list A)
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

  Definition nums_to_refs (xs : list Z) : list (val -> iProp Σ) :=
    map num_to_ref xs.

  Definition before_after (xs : list Z) : list ((val -> iProp Σ) * (val -> iProp Σ)) :=
    map (fun x => (num_to_ref x, num_to_ref (x + 1))) xs.

  Definition sum_invariant (ls : loc) (n : Z) (Ps : list (val -> iProp Σ)) : iProp Σ :=
    (∃(values : list ((val -> iProp Σ) * (loc * Z))),
        ⌜map fst values = Ps⌝
      ∗ ls ↦ #(fold_right Z.add 0 (map (snd ∘ snd) values) + n)
      ∗ [∗ list] cell ∈ values, cell.2.1 ↦ #(cell.2.2 + 1 : Z) ∗ cell.1 #(cell.2.1 : loc)
      )%I.

  Lemma prog_sum_loop_wp (ls : loc) (n : Z) (v : val) (xs : list Z):
    {{{ is_list v (map fst (before_after xs)) ∗ ls ↦ #n }}}
      prog_sum_loop #ls v
    {{{ RET #(); is_list v (map snd (before_after xs)) ∗ ls ↦ #(fold_right Z.add 0 xs + n) }}}.
  Proof.
    iIntros (Φ) "[Hv Hls] HΦ".
    wp_rec; wp_pures. wp_lam. wp_pures.
    wp_apply (prog_for_each_wp
                v
                (before_after xs)
                (sum_invariant ls n)
                _
                with "[$Hv Hls]").
    - admit.
    - iIntros "[Hv Hinv]".
      iApply "HΦ". iFrame.
      rewrite /sum_invariant.
      iDestruct "Hinv" as (values) "(HPs & Hls & Hlink)".
      iInduction xs as [|k xs'] "IH" forall (values); simpl.
      + iDestruct "HPs" as "%". apply map_eq_nil in H; subst; simpl. done.
      + destruct values.
        (* empty list is impossible at this point *)
        { simpl. iDestruct "HPs" as "%". discriminate. }
        destruct p as [Ψ [lx x]].
        simpl.
        iDestruct "HPs" as %H. inversion H; subst.
        rewrite /num_to_ref.
        iDestruct "Hlink" as "[[Hlx Hk] Hrest]".
        iDestruct "Hk" as (ly) "[Heq Hly]".
        iDestruct "Heq" as %Heq. inversion Heq; subst.
        iDestruct "Hlx" as "[Hlx1 Hlx2]".
        iDestruct "Hly" as "[Hly1 Hly2]".
        iAssert (⌜x = k⌝)%I with "[Hlx1 Hly1]" as "Hxk".
        admit.
  Admitted.

  (* Idea: you should not be able to assume that the list will be
  processed in any particular order in the mapping function that is
  supplied as the argument. *)
  Lemma prog_sum_wp (v : val) (xs : list Z):
    {{{ is_list v (map fst (before_after xs)) }}}
      prog_sum v
    {{{ r, RET r; is_list v (map snd (before_after xs)) ∗ ⌜r = #(fold_right Z.add 0 xs)⌝ }}}.
  Proof.
    iIntros (Φ) "Hv HΦ".
    wp_rec. wp_alloc ls as "Hs". wp_pures.
    wp_apply (prog_sum_loop_wp ls 0 v xs with "[$Hv $Hs]").
    iIntros "[Hv Hls]".
    wp_seq.
    wp_load.
    iApply "HΦ".
    iFrame.
    rewrite Z.add_0_r.
    done.
  Qed.

End SumExample.
