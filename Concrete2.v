From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

Section Concrete2.
  Context `{heapG Σ}.

  Inductive mylist : Set :=
  | mynil : mylist
  | mycons : Z → mylist → mylist.

  Fixpoint is_mylist (v : val) (xs : mylist) : iProp Σ :=
    match xs with
    | mynil => ⌜v = InjLV #()⌝
    | mycons n xs' => ∃(tail : loc) (vtail : val), ⌜v = InjRV (#n,#tail)⌝ ∗ tail ↦ vtail ∗ is_mylist vtail xs'
  end%I.

  Fixpoint all_even (xs : mylist) : bool :=
    match xs with
    | mynil => true
    | mycons n xs' => andb (bool_decide (Z.rem n 2 = 0)) (all_even xs')
    end.

  Definition all_even_loop : val :=
    rec: "all_even_loop" "xs" "state" :=
      match: "xs" with
        InjL "unit" => Skip
      | InjR "cons" =>
        let: "current" := (Fst "cons") `rem` #2 = #0 in
        "state" <- !"state" && "current";;
        "all_even_loop" !(Snd "cons") "state"
      end.

  Definition all_even_prog : val := λ: "xs",
    let: "state" := ref #true in
    all_even_loop "xs" "state";;
    !"state".

  Lemma all_even_loop_wp v xs l (b : bool):
    [[{ l ↦ #b ∗ is_mylist v xs }]]
      all_even_loop v #l
      [[{ RET #(); l ↦ #(all_even xs && b) ∗ is_mylist v xs }]].
  Proof.
    iIntros (Φ) "[Hl Hxs] HΦ".
    iInduction xs as [|n xs'] "IH" forall (v b Φ); simpl; wp_rec; wp_let.
    - iDestruct "Hxs" as "%"; subst. wp_match.
      wp_lam.
      (* iApply ("HΦ" with "[Hl]"). iFrame. done. *)
      (* by iApply ("HΦ" with "[$Hl]"). *)
      iApply ("HΦ" with "[$Hl //]").
    - iDestruct "Hxs" as (tail vtail ->) "(Hltail & Hxtail)".
      wp_match. wp_proj. wp_op. wp_op. wp_let. wp_load.
      destruct b.
      + (* b = true *) wp_if_true. wp_store. wp_proj. wp_load.
        wp_apply ("IH" with "Hl Hxtail"). iIntros "[Hl Hxtail]".
        iApply "HΦ". iSplitL "Hl".
        * replace (bool_decide (n `rem` 2 = 0) && all_even xs' && true) with (all_even xs' && bool_decide (#(n `rem` 2) = #0)). done. admit. (* ADMITTED: boolean manipulations. if these were numbers I would have used omega here *)
        * iExists tail, vtail. by iFrame.
      + (* b = false *) wp_if_false. wp_store. wp_proj. wp_load.
        wp_apply ("IH" with "Hl Hxtail"). iIntros "[Hl Hxtail]".
        iApply "HΦ". iSplitL "Hl".
        * admit. (* ADMITTED: more boolean manipulations. *)
        * iExists tail, vtail. by iFrame.
  Admitted.

  Lemma all_even_prog_wp v xs:
    [[{ is_mylist v xs }]]
      all_even_prog v
    [[{ RET #(all_even xs); is_mylist v xs }]].
  Proof.
    iIntros (Φ) "Hxs HΦ".
    wp_lam. wp_alloc s as "Hs". wp_let.
    wp_apply (all_even_loop_wp with "[$Hs $Hxs]").
    iIntros "[Hs Hxs]".
    wp_seq.
    replace (all_even xs && true) with (all_even xs).
    - wp_load. by iApply "HΦ".
    - admit. (* ADMITTED: more boolean manipulations *)
  Admitted.

  Check all_even_prog_wp.
End Concrete2.
