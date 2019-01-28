From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export notation lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang.lib Require Import par.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import frac_auth.
From iris.algebra Require Export cmra.
Set Default Proof Using "Type".

Section SafeIncrement.
  Local Set Default Proof Using "Type*".

  Class myG Σ := MyG { myG_inG :> inG Σ (frac_authR natR) }.
  Definition myΣ : gFunctors := #[GFunctor (frac_authR natR)].

  Instance subG_myΣ {Σ} : subG myΣ Σ -> myG Σ.
  Proof. solve_inG. Qed.

  Context `{!heapG Σ, !myG Σ, !spawnG Σ}.

  Definition prog_safe_inc : val :=
    λ: "x", FAA "x" #1%nat.

  Lemma prog_safe_inc_wp (l : loc):
    {{{ l ↦ #0%nat }}}
      prog_safe_inc #l
    {{{ RET #0; l ↦ #1%nat }}}.
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

  Definition counter_inv γ (l : loc) : iProp Σ :=
    (∃k:nat, l ↦ #k ∗ own γ (●! k))%I.

  Definition is_counter N γ (l : loc) (q : frac) (n : nat) : iProp Σ :=
    (own γ (◯!{q} n) ∗ inv N (counter_inv γ l))%I.

  Lemma prog_safe_frac N γ (s : loc):
    {{{ is_counter N γ s (1/2) 0 }}} prog_safe_inc #s {{{ v, RET v; own γ (◯!{1/2} 1%nat) }}}.
  Proof.
    iIntros (Φ) "Hcounter HΦ".
    rewrite /is_counter.
    iDestruct "Hcounter" as "[Hfrag #Hinv]".
    wp_lam.
    iInv "Hinv" as ">Hauth" "cl".
    iDestruct "Hauth" as (k) "(Hs & Htrue)".
    wp_faa.
    iCombine "Htrue" "Hfrag" as "Hcomb".
    iMod (own_update γ _ ((●! (k + 1)%nat) ⋅ (◯!{1/2} 1%nat)) with "[$Hcomb]") as "Hcomb".
    { apply frac_auth_update, (nat_local_update _ _ (k + 1)%nat 1%nat). by rewrite -plus_n_O. }
    rewrite own_op.
    iDestruct "Hcomb" as "[Hauth Hfrag]".
    iMod ("cl" with "[Hs Hauth]") as "_".
    { iModIntro. iExists (k + 1)%nat. iFrame. by rewrite Nat2Z.inj_add. }
    iModIntro. iApply "HΦ". iFrame.
  Qed.

  Lemma prog_safe_inc_par_wp:
    {{{ ⌜True⌝ }}} prog_inc_par {{{ v, RET v; ⌜v = #2⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /prog_inc_par.
    wp_alloc s as "Hs".
    wp_let.
    wp_bind (_ ||| _)%E.
    iMod (own_alloc (●! 0%nat ⋅ ◯! 0%nat)) as (γ) "[Hauth Hfrag]"; first done.
    iAssert (own γ (◯!{1/2} 0%nat) ∗ own γ (◯!{1/2} 0%nat))%I with "[Hfrag]" as "[Hfrag1 Hfrag2]".
    { by rewrite -own_op -frac_auth_frag_op Qp_half_half. }
    iMod (inv_alloc (nroot.@"par") _ (counter_inv γ s) with "[Hs Hauth]") as "#Hinv".
    { iModIntro. rewrite /counter_inv. iExists 0%nat. iFrame. }
    iApply (wp_par
              (fun v => own γ (◯!{1/2} 1%nat))
              (fun v => own γ (◯!{1/2} 1%nat))
              with "[Hfrag1] [Hfrag2]").
    - iAssert (is_counter _ _ _ _ _)%I with "[Hinv Hfrag1]" as "Hcounter".
      rewrite /is_counter. iSplitL "Hfrag1". iAssumption. iAssumption.
      wp_apply (prog_safe_frac with "[$Hcounter]").
      iIntros (v) "Hfrag". iExact "Hfrag".
    - iAssert (is_counter _ _ _ _ _)%I with "[Hinv Hfrag2]" as "Hcounter".
      rewrite /is_counter. iSplitL "Hfrag2". iAssumption. iAssumption.
      wp_apply (prog_safe_frac with "[$Hcounter]").
      iIntros (v) "Hfrag". iExact "Hfrag".
    - iIntros (v1 v2) "[Hfrag1 Hfrag2]".
      iCombine "Hfrag1" "Hfrag2" as "Hfrag".
      replace (1 + 1)%nat with 2%nat. 2: { simpl. reflexivity. }
      iModIntro.
      wp_seq.
      iInv "Hinv" as ">Hauth" "cl".
      rewrite /counter_inv.
      iDestruct "Hauth" as (k) "[Hs Htrue]".
      iCombine "Htrue" "Hfrag" as "Hcomb".
      iAssert (⌜k = 2%nat⌝)%I as "%".
      + iAssert (✓ (●! k ⋅ ◯! 2%nat))%I as "%".
        { iApply own_valid. iExact "Hcomb". }
        iPureIntro.
        apply frac_auth_agree in H.
        done.
      + subst.
        wp_load.
        iMod ("cl" with "[Hs Hcomb]") as "_".
        { iModIntro. iExists 2%nat. iFrame.
          iDestruct "Hcomb" as "[Hauth Hfrag]".
          iFrame. }
        iModIntro.
        iApply "HΦ".
        done.
  Qed.

End SafeIncrement.
