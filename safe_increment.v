From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export notation lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang.lib Require Import par.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Export frac.
Require Export IncRA.
Set Default Proof Using "Type".

Section SafeIncrement.
  Class fracG Σ := FracG { fracG_inG :> inG Σ fracR }.
  Definition fracΣ : gFunctors := #[GFunctor fracR].

  Instance subG_fracΣ {Σ} : subG fracΣ Σ -> fracG Σ.
  Proof. solve_inG. Qed.

  Context `{!heapG Σ, !fracG Σ, !incG Σ}.

  Definition prog_safe_inc : val :=
    λ: "x", FAA "x" #1.

  Lemma prog_safe_inc_wp (l : loc):
    {{{ l ↦ #0 }}}
      prog_safe_inc #l
    {{{ RET #0; l ↦ #1 }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    wp_lam. wp_faa.
    replace (0 + 1)%Z with 1%Z by omega.
    iApply "HΦ".
    by iFrame.
  Qed.

  Definition prog_inc_par : expr :=
    let: "s" := ref #0 in
    prog_safe_inc "s" ||| prog_safe_inc "s";;
    !"s".

  Definition half : frac := 1/2.
  Definition one : frac := 1.

  Definition inc_invariant γ1 γ2 (l : loc) : iProp Σ :=
    ((own γ1 S ∗ l ↦ #0) ∨ (own γ1 S ∗ own γ2 half ∗ l ↦ #1) ∨ (own γ1 F ∗ own γ2 one ∗ l ↦ #2))%I.

  Lemma prog_safe_frac N γ1 γ2 (s : loc):
    inv N (inc_invariant γ1 γ2 s) -∗ {{{ own γ2 half }}} prog_safe_inc #s {{{ v, RET v; own γ2 one }}}.
  Proof.
  Admitted.

  Lemma prog_safe_inc_par_wp (l : loc):
    {{{ ⌜True⌝ }}} prog_inc_par {{{ v, RET v; ⌜v = #2⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /prog_inc_par.
    wp_alloc s as "Hs".
    iMod (own_alloc S) as (γ1) "Htok1"; first split.
    iMod (own_alloc one) as (γ2) "Htok2"; first admit.
    iMod (inv_alloc (nroot.@"client") _ (inc_invariant γ1 γ2 s) with "[Htok1 Hs]") as "#Hinv".
    { iModIntro. rewrite /inc_invariant. iLeft. iFrame. }
    iAssert (own γ2 half ∗ own γ2 half)%I with "[Htok2]" as "[Htok2_a Htok2_b]".
    { iApply own_op. admit. }
    wp_let.
    wp_bind (_ ||| _)%E.
    iPoseProof (prog_safe_frac with "Hinv") as "Hbranch".
    iApply (wp_par _ _ _ _ Φ with "[Htok2_a] [Htok2_b]").
    - wp_apply ("Hbranch" with "[$Htok2_a]"). admit.
    - wp_apply ("Hbranch" with "[$Htok2_b]"). admit.
  Admitted.

End SafeIncrement.
