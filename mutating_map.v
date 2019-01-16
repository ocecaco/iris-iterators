From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

(* different from the other is_list from foldr.v *)
Fixpoint is_list `{!heapG Σ} (v : val) (Ψs : list (val -> iProp Σ)) : iProp Σ :=
  match Ψs with
  | [] => ⌜v = InjLV #()⌝
  | Ψ :: Ψs' => ∃(lh : loc) (x vt : val), ⌜v = InjRV #lh⌝ ∗ lh ↦ (x, vt) ∗ Ψ x ∗ is_list vt Ψs'
end%I.

Section MyTests.
  Context `{heapG Σ}.

  Definition prog_mktestlist : val := λ: "unit",
                                      let: "x" := ref #3 in
                                      let: "cons" := ref ("x", InjL #()) in
                                      InjR "cons".

  Definition points_to_three (v : val) : iProp Σ :=
    (∃(l : loc), ⌜v = #l⌝ ∗ l ↦ #3)%I.

  Lemma prog_mktestlist_wp:
    WP prog_mktestlist #() {{ v, is_list v [points_to_three] }}%I.
  Proof.
    wp_rec. wp_pures.
    wp_alloc lc1 as "H1". wp_pures.
    wp_alloc lc2 as "H2". wp_pures.
    rewrite /is_list /points_to_three.
    iExists lc2, #lc1, (InjLV #()).
    iFrame.
    iSplitR. done.
    iSplitL. iExists lc1. iFrame. done.
    done.
  Qed.

  Definition closure_test : expr :=
    let: "s" := ref #0 in
    let: "f" := λ: "x", "s" <- !"s" + "x" in
    "f" #1;; !"s".

  Lemma closure_test_wp:
    WP closure_test {{ v, ⌜v = #1⌝ }}%I.
  Proof.
    iIntros "".
    rewrite /closure_test.
    wp_alloc ls as "Hs".
    by repeat (wp_load || wp_store || wp_pure _).
  Qed.

  Definition test_preds (ls : loc) : list ((val -> iProp Σ) * (val -> iProp Σ)) :=
    [(fun v => (⌜v = #ls⌝ ∗ ls ↦ #2)%I, fun v => (⌜v = #ls⌝ ∗ ls ↦ #3)%I)].

End MyTests.

Section MutatingMap.
  Context `{heapG Σ}.

  Definition prog_for_each : val :=
    rec: "for_each" "f" "xs" :=
      match: "xs" with
        InjL "unit" => Skip
      | InjR "cons" => "f" (Fst !"cons");; "for_each" "f" (Snd !"cons")
      end.

  Lemma prog_for_each_wp_loop
        (v : val)
        (Ψs : list ((val -> iProp Σ) * (val -> iProp Σ)))
        (I : list (val -> iProp Σ) -> iProp Σ)
        (past : list (val -> iProp Σ))
        (f : val):
    {{{ is_list v (map fst Ψs)
      ∗ I past
      ∗ [∗ list] P ∈ Ψs, (∀ x xs, {{{ P.1 x ∗ I xs }}} f x {{{ RET #(); P.2 x ∗ I (P.2 :: xs) }}})
    }}}
      prog_for_each f v
    {{{ RET #(); is_list v (map snd Ψs) ∗ I (reverse (map snd Ψs) ++ past) }}}.
  Proof.
    iIntros (Φ) "(Hv & HI & Hf) HΦ".
    iInduction Ψs as [|P Ψs'] "IH" forall (v Φ past); simpl.
    - iDestruct "Hv" as "%"; subst.
      wp_rec. wp_pures.
      iApply "HΦ".
      (* rewrite app_nil_r. *)
      by iFrame.
    - iDestruct "Hv" as (lh x vt ->) "(Hlh & HP1 & Hvt)".
      iDestruct "Hf" as "[Hf0 Hfr]".
      wp_rec. wp_pures. wp_load. wp_pures.
      iSpecialize ("Hf0" $! x past).
      wp_apply ("Hf0" with "[$HP1 $HI]").
      iIntros "[HP2 HI]".
      wp_seq. wp_load. wp_proj.
      iSpecialize ("IH" $! vt Φ (P.2 :: past) with "Hvt HI Hfr").
      wp_apply "IH".
      iIntros "[Hvt HI]".
      iApply "HΦ".
      replace (reverse (P.2 :: map snd Ψs') ++ past) with (reverse (map snd Ψs') ++ P.2 :: past).
      + iFrame.
        iExists lh, x, vt. by iFrame.
      + rewrite reverse_cons.
        rewrite app_assoc_reverse.
        simpl. done.
  Qed.

  Definition prog_for_each_loop
    (v : val)
    (Ψs : list ((val -> iProp Σ) * (val -> iProp Σ)))
    (I : list (val -> iProp Σ) -> iProp Σ)
    (past : list (val -> iProp Σ))
    (f : val) := prog_for_each_wp_loop v Ψs I [] f.

  Check prog_for_each_loop.

End MutatingMap.

Section SumExample.
  Context `{!heapG Σ}.

   Definition prog_increment_closure (ls : loc) : val :=
    λ: "x", #ls <- !#ls + !"x";; "x" <- !"x" + #1.

  Definition prog_sum_loop : val := λ: "s" "xs",
    let: "f" := (λ: "x", "s" <- !"s" + !"x";; "x" <- !"x" + #1) in
    prog_for_each "f" "xs".

  Definition prog_sum : val := λ: "xs",
    let: "s" := ref #0 in
    prog_sum_loop "s" "xs";; !"s".

    (* This is probably a strong enough specification of the
  incrementing closure to be used in the application of for_each. *)
  Lemma prog_increment_closure_wp (ls : loc) (lx : loc) (n : Z) (k : Z):
    {{{ ls ↦ #n ∗ lx ↦ #k }}}
      prog_increment_closure ls #lx
    {{{ RET #(); ls ↦ #(n + k) ∗ lx ↦ #(k + 1) }}}.
  Proof.
    iIntros (Φ) "[Hls Hlx] HΦ".
    wp_rec. repeat (wp_load || wp_store || wp_pure _).
    iApply "HΦ". by iFrame.
  Qed.

  Definition num_to_ref (x : Z) (v : val) : iProp Σ :=
    (∃(l : loc), ⌜v = #l⌝ ∗ l ↦ #x)%I.

  Definition nums_to_refs (xs : list Z) : list (val -> iProp Σ) :=
    map num_to_ref xs.

  Lemma prog_sum_for_each (ls : loc) (f : loc -> val) (v : val) (xs : list Z) (n : Z):
    {{{ is_list v (nums_to_refs xs) ∗ ls ↦ #n
      ∗ ∀ ls lx (n k : Z),
            {{{ ls ↦ #n ∗ lx ↦ #k }}}
              f ls #lx
            {{{ RET #(); ls ↦ #(n + k) ∗ lx ↦ #(k + 1) }}}
    }}}
      prog_for_each (f ls) v
    {{{ RET #(); is_list v (nums_to_refs (map (λ x : Z, x + 1) xs)) ∗ ls ↦ #(foldr Z.add 0 xs + n) }}}.
  Proof.
    iIntros (Φ) "[Hv [Hls #Hf]] HΦ".
    iInduction xs as [|k xs'] "IH" forall (n v Φ); simpl.
    - iDestruct "Hv" as "%"; subst.
      wp_rec. wp_pures.
      iApply "HΦ".
      replace (0 + n) with (n) by omega.
      by iFrame "Hls".
    - iDestruct "Hv" as (lh x vt ->) "(Hlh & Hk & Hvt)".
      iDestruct "Hk" as (lx ->) "Hlx".
      wp_rec. repeat (wp_load || wp_store || wp_pure _).
      wp_apply ("Hf" with "[$Hls $Hlx]").
      iIntros "[Hls Hlx]".
      wp_seq. wp_load. wp_proj.
      iApply ("IH" with "Hvt Hls"). iModIntro.
      iIntros "[Hvt Hls]".
      iApply "HΦ".
      replace (foldr Z.add 0 xs' + (n + k)) with (k + foldr Z.add 0 xs' + n) by omega. iFrame.
      iExists lh, (#lx)%V, vt.
      iFrame.
      iSplitR. done.
      iExists lx. iFrame. done.
  Qed.

  Lemma prog_sum_loop_wp (ls : loc) (n : Z) (v : val) (xs : list Z):
    {{{ is_list v (nums_to_refs xs) ∗ ls ↦ #n }}}
      prog_sum_loop #ls v
    {{{ RET #(); is_list v (nums_to_refs (map (fun x => x + 1) xs)) ∗ ls ↦ #(fold_right Z.add 0 xs + n) }}}.
  Proof.
    iIntros (Φ) "[Hv Hls] HΦ".
    wp_rec; wp_pures.
  Admitted.

  (* Idea: you should not be able to assume that the list will be
  processed in any particular order in the mapping function that is
  supplied as the argument. *)
  Lemma prog_sum_wp (v : val) (xs : list Z):
    {{{ is_list v (nums_to_refs xs) }}}
      prog_sum v
    {{{ r, RET r; is_list v (nums_to_refs (map (fun x => x + 1) xs)) ∗ ⌜r = #(fold_right Z.add 0 xs)⌝ }}}.
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
