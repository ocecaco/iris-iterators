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
    iExists lc2.
    iExists (#lc1)%V.
    iExists (InjLV #())%V.
    iFrame.
    iSplitR. done.
    iSplitL. iExists lc1. iFrame. done.
    done.
  Qed.

End MutatingMap.
