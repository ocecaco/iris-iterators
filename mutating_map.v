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

Definition list_const {Σ} (xs : list val) : list (val -> iProp Σ) :=
  (map (fun x v => ⌜v = x⌝%I) xs).

Section MutatingMap.
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

  Definition prog_for_each : val :=
    rec: "for_each" "f" "xs" :=
      match: "xs" with
        InjL "unit" => Skip
      | InjR "cons" => "f" (Fst !"cons");; "for_each" (Snd !"cons")
      end.

  Lemma prog_for_each_wp
        (v : val)
        (Ψs : list ((val -> iProp Σ) * (val -> iProp Σ)))
        (I : list val -> iProp Σ)
        (f : val):
    {{{ is_list v (map fst Ψs)
      ∗ I []
      ∗ [∗ list] P ∈ Ψs, (∀ x xs, {{{ fst P x ∗ I xs }}} f x {{{ RET #(); snd P x ∗ I (x :: xs) }}})
    }}}
      prog_for_each f v
    {{{ RET #(); is_list v (map snd Ψs) }}}.
  Proof.
  Admitted.

  Definition test_preds (ls : loc) : list ((val -> iProp Σ) * (val -> iProp Σ)) :=
    [(fun v => (⌜v = #ls⌝ ∗ ls ↦ #2)%I, fun v => (⌜v = #ls⌝ ∗ ls ↦ #3)%I)].

  Definition prog_sum : val := λ: "xs",
    let: "s" := ref #0 in
    let: "f" := λ: "x", "s" <- !"s" + !"x";; "x" <- !"x" + #1 in
    prog_for_each "f" "xs";; !"s".

  (* This is what the closure looks like after some beta
  reductions. There are not actually any free variables on the object
  language level. *)
  Definition prog_increment_closure (ls : loc) : val :=
    λ: "x", #ls <- !#ls + !"x";; "x" <- !"x" + #1.

  Definition nums_to_refs (xs : list Z) : list (val -> iProp Σ) :=
    map (fun (x : Z) (v : val) => ∃(l : loc), ⌜v = #l⌝ ∗ l ↦ #x)%I xs.

  (* Definition loop_invariant (ls : loc) (xs : list val) : iProp Σ := *)
  (*   (∃(xs' : list Z), ⌜xs = nums_to_refs xs'⌝ ∗ ls ↦ #(fold_right Z.add 0 xs'))%I. *)

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
    wp_rec. wp_pures.
    iInduction xs as [|n xs'] "IH" forall (v Φ); simpl.
    - iDestruct "Hv" as "%". rewrite H0.
      wp_match. wp_pures.
      wp_load.
      by iApply "HΦ".
    - iDestruct "Hv" as (lh x vt ->) "(Hlh & Hn & Hvt)".
      iDestruct "Hn" as (lx ->) "Hlx".
      wp_match. repeat (wp_load || wp_store || wp_pure _).
  Admitted.

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

End MutatingMap.
