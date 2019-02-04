From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export notation lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.
From iris.base_logic.lib Require Export invariants.
Require Export IncRA.
Set Default Proof Using "Type".

Section GhostStateSimple.
  Context `{!heapG Σ, !incG Σ}.

  Definition inc_invariant γ (l : loc) (n : Z) : iProp Σ := (∃(k:Z), l ↦ #k ∗ ((own γ S ∧ ⌜k >= n⌝) ∨ (own γ F ∧ ⌜k >= n + 1⌝)))%I.

  Definition prog_inc (l : loc) : expr :=
    #l <- !#l + #1.

  Lemma prog_inc_wp N γ l n:
    inv N (inc_invariant γ l n) -∗ {{{ ⌜True ⌝}}} prog_inc l {{{ v, RET v; own γ F }}}.
  Proof.
    iIntros "#Hinv".
    iIntros (Φ). iModIntro.
    iIntros "_ HΦ".
    rewrite /prog_inc.
    (* open the invariant to read from the location *)
    wp_bind (! _)%E.
    iInv N as "Hl" "cl".
    iMod "Hl".
    iDestruct "Hl" as (k) "(Hl & Hghost)".
    iAssert (⌜k >= n⌝)%I as "%".
    { iDestruct "Hghost" as "[[Htok Hbound]|[Htok Hbound]]";
        iDestruct "Hbound" as %Hbound; (* Coq hung here if I used "%",
        probably because there is another branch using the same name
        Hbound *)
        iPureIntro;
        omega. }
    wp_load.
    (* now close the invariant again after the read *)
    iMod ("cl" with "[Hl Hghost]") as "_".
    (* re-establish the invariant, easy because we have only read from
    the location at this point *)
    { iModIntro. iExists k. iFrame. }
    iModIntro.
    wp_op.
    (* open the invariant again to write to the location *)
    iInv N as "Hl" "cl".
    iMod "Hl".
    iDestruct "Hl" as (k') "(Hl & Hghost)".
    wp_store.
    assert (k + 1 >= n + 1) by omega.
    iDestruct "Hghost" as "[[Htok _]|[Htok _]]".
    - (* own S *)
      (* this is where we perform the frame preserving update from S
         to F, which we are allowed to do (?) because of the update
         modality in the goal *)
      iMod (own_update γ S F with "[$Htok]") as "Htok".
      (* show that this update is frame-preserving *)
      { apply incRA_S_F_update. }
      (* we now have the desired own F token! Since it is duplicable,
      we can make a copy of it to close the invariant, and another
      copy to pass around. *)
      iPoseProof (incRA_F_duplicable with "[$Htok]") as "[Htok1 Htok2]".
      (* close the invariant using Htok2 *)
      iMod ("cl" with "[Hl Htok2]") as "_".
      { iModIntro. iExists (k + 1). iFrame. auto. }
      iApply ("HΦ" with "[$Htok1]").
    - (* own F: no need to do a frame preserving update since we can
      just duplicate our token. *)
      iPoseProof (incRA_F_duplicable with "[$Htok]") as "[Htok1 Htok2]".
      iMod ("cl" with "[Hl Htok2]") as "_".
      { iModIntro. iExists (k + 1). iFrame. auto. }
      iApply ("HΦ" with "[$Htok1]").
  Qed.

  Lemma prog_client_wp (l : loc) (n : Z):
    {{{ l ↦ #n }}} prog_inc l;; !#l {{{ v, RET v; ⌜∃k:Z, v = #k ∧ k >= n + 1⌝ }}}.
  Proof using incG0. (* not sure what this is for, but Coq was complaining about it *)
    iIntros (Φ) "Hl HΦ".
    (* allocate ghost state token, for which we have to show ✓ S. *)
    iMod (own_alloc S) as (γ) "Htok"; first split.
    (* allocate the invariant *)
    iMod (inv_alloc (nroot.@"client") _ (inc_invariant γ l n) with "[Hl Htok]") as "#Hinv".
    { (* initially establish invariant *)
      assert (n >= n) by omega. iModIntro. rewrite /inc_invariant.
      iExists n. iFrame. auto. }
    wp_bind (prog_inc l)%E.
    iApply prog_inc_wp; try done.
    iModIntro.
    iIntros (v) "Htok".
    wp_seq.
    (* wasn't able to open the invariant again to show the conclusion
    if I didn't put the skip instruction after prog_inc. Makes sense
    because we need an atomic instruction. *)
    iInv "Hinv" as "Hl" "cl".
    iMod "Hl".
    rewrite /inc_invariant.
    iDestruct "Hl" as (k) "[Hl [[Htok1 Hbound]|[Htok2 Hbound]]]".
    - (* own S and own F are incompatible, hence we cannot be in this case *)
      iApply (incRA_S_F_incompatible with "[$Htok1 $Htok]").
    - (* Here we have the desired bound due to the case of the invariant we are in *)
      iDestruct "Hbound" as "%".
      wp_load.
      iMod ("cl" with "[Htok2 Hl]") as "_".
      { iModIntro. iExists k. iFrame. auto. }
      iModIntro.
      iApply "HΦ".
      iPureIntro.
      by exists k.
  Qed.

End GhostStateSimple.
