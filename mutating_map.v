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

Section MutatingMap.
  Context `{heapG Σ}.

  Definition prog_for_each : val :=
    rec: "for_each" "f" "xs" :=
      match: "xs" with
        InjL "unit" => Skip
      | InjR "cons" => "f" (Fst !"cons");; "for_each" "f" (Snd !"cons")
      end.

  Lemma prog_for_each_loop_wp
        (v : val)
        (Ψs : list ((val -> iProp Σ) * (val -> iProp Σ)))
        (I : list (val -> iProp Σ) -> iProp Σ)
        (past : list (val -> iProp Σ))
        (f : val):
    {{{ is_list v (map fst Ψs)
      ∗ I past
      ∗ [∗ list] P ∈ Ψs, (∀ x xs, {{{ P.1 x ∗ I xs }}} f x {{{ RET #(); P.2 x ∗ I (xs ++ [P.2]) }}})
    }}}
      prog_for_each f v
    {{{ RET #(); is_list v (map snd Ψs) ∗ I (past ++ map snd Ψs) }}}.
  Proof.
    iIntros (Φ) "(Hv & HI & Hf) HΦ".
    iInduction Ψs as [|P Ψs'] "IH" forall (v Φ past); simpl.
    - iDestruct "Hv" as "%"; subst.
      wp_rec. wp_pures.
      iApply "HΦ".
      rewrite app_nil_r.
      by iFrame.
    - iDestruct "Hv" as (lh x vt ->) "(Hlh & HP1 & Hvt)".
      iDestruct "Hf" as "[Hf0 Hfr]".
      wp_rec. wp_pures. wp_load. wp_pures.
      iSpecialize ("Hf0" $! x past).
      wp_apply ("Hf0" with "[$HP1 $HI]").
      iIntros "[HP2 HI]".
      wp_seq. wp_load. wp_proj.
      iSpecialize ("IH" $! vt Φ (past ++ [P.2]) with "Hvt HI Hfr").
      wp_apply "IH".
      iIntros "[Hvt HI]".
      iApply "HΦ".
      replace ((past ++ [P.2]) ++ map snd Ψs') with (past ++ P.2 :: map snd Ψs').
      + iFrame.
        iExists lh, x, vt. by iFrame.
      + rewrite app_assoc_reverse. simpl. done.
  Qed.

  Definition prog_for_each_wp v Ψs I f := prog_for_each_loop_wp v Ψs I [] f.

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
