From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export notation lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Export frac.
Require Export IncRA.
Require Export QArith.
Require Export QArith.Qcanon.

Section GhostStateFrac.
  Class fracG Σ := FracG { fracG_inG :> inG Σ fracR }.
  Definition fracΣ : gFunctors := #[GFunctor fracR].

  Instance subG_fracΣ {Σ} : subG fracΣ Σ -> fracG Σ.
  Proof. solve_inG. Qed.

  Context `{!heapG Σ, !fracG Σ, !incG Σ}.

  Definition half : frac := 1/2.
  Definition one : frac := 1.

  Definition inc_invariant γ1 γ2 (n : Z) (l : loc) :=
    ((l ↦ #n ∗ own γ1 S) ∨ (l ↦ #(n + 1) ∗ own γ1 F ∗ own γ2 half) ∨ (l ↦ #(n + 2) ∗ own γ1 F ∗ own γ2 one))%I.

  Definition prog_inc (l : loc) : expr :=
    #l <- !#l + #1.

  Lemma half_one_impossible γ Φ:
    own γ half ∗ own γ one -∗ Φ.
  Proof.
    iIntros "[Hhalf Hone]".
    iExFalso.
    iCombine "Hhalf" "Hone" as "Htok".
    iDestruct (own_valid with "Htok") as "HV".
    iDestruct "HV" as %HV.
    iPureIntro.
    auto.
  Qed.

  (* It seems to me that the fractional resource algebra allows you to
  reason about how many ghost updates the other threads out there can
  do. If you have 1/2 of the resources, then you know the rest has at
  most 1/2 as well. Hence the other thread can at worst only take one
  state transition, just like you. That is why the variable could
  never be incremented 3 times. *)
  Lemma prog_inc_wp N γ1 γ2 (n : Z) (l : loc):
    inv N (inc_invariant γ1 γ2 n l) -∗ {{{ own γ2 half }}} prog_inc l {{{ v, RET v; own γ1 F }}}.
  Proof.
    iIntros "#Hinv".
    iIntros (Φ). iModIntro. (* why is this box there all of a sudden *)
    iIntros "Hhalf HΦ".
    rewrite /prog_inc.
    (* open the invariant for reading *)
    wp_bind (! _)%E.
    iInv "Hinv" as "Hl" "cl". iMod "Hl". rewrite /inc_invariant.

    iDestruct "Hl" as "[Htok|[Htok|Htok]]";
      iDestruct "Htok" as "[Hl Htok]";
      try iDestruct "Htok" as "[Htok1 Htok2]".

    - wp_load. (* reading n *)
      iMod ("cl" with "[Hl Htok]") as "_".
      { iModIntro. iCombine "Hl" "Htok" as "Htok". auto. }
      iModIntro. wp_op.
      (* open the invariant for writing *)
      iInv "Hinv" as "Hl" "cl". iMod "Hl".

      iDestruct "Hl" as "[Htok|[Htok|Htok]]";
        iDestruct "Htok" as "[Hl Htok]";
        try iDestruct "Htok" as "[Htok1 Htok2]".

      + wp_store.
        (* update ghost variable now since we have incremented *)
        iMod (own_update γ1 S F with "[$Htok]") as "Htok".
        { apply incRA_S_F_update. }
        iDestruct (incRA_F_duplicable with "Htok") as "[Htok Htok2]".
        iMod ("cl" with "[Hl Htok2 Hhalf]") as "_".
        { iModIntro. iRight. iLeft. iFrame. }
        by iApply "HΦ".

      + wp_store.
        (* no need to do ghost variable update, just copy the F *)
        iDestruct (incRA_F_duplicable with "Htok1") as "[Htok Htok1]".
        iMod ("cl" with "[Hl Htok1 Htok2]") as "_".
        { iModIntro. iRight. iLeft. iFrame. }
        iModIntro. iApply "HΦ". iFrame.

      + iApply (half_one_impossible with "[$Hhalf $Htok2]").

    - wp_load. (* reading n + 1 *)
      iMod ("cl" with "[Hl Htok1 Htok2]") as "_".
      { iModIntro. iRight. iLeft. iFrame. }
      iModIntro. wp_op.
      (* open the invariant for writing *)
      iInv "Hinv" as "Hl" "cl". iMod "Hl".

      iDestruct "Hl" as "[Htok|[Htok|Htok]]";
        iDestruct "Htok" as "[Hl Htok]";
        try iDestruct "Htok" as "[Htok1 Htok2]".

      + admit.

      + wp_store.
        iDestruct (incRA_F_duplicable with "Htok1") as "[HtokF1 HtokF2]".
        iCombine "Hhalf" "Htok2" as "Htok".
        replace (n + 1 + 1)%Z with (n + 2)%Z by omega.
        iMod ("cl" with "[Hl Htok HtokF2]") as "_".
        { iModIntro. iRight. iRight. iFrame. }
        iModIntro. iApply "HΦ". by iFrame.

      + iApply (half_one_impossible with "[$Hhalf $Htok2]").

    - (* reading n + 2, impossible *) iApply (half_one_impossible with "[$Hhalf $Htok2]").
  Admitted.
End GhostStateFrac.
