From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export notation lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.
From iris.base_logic.lib Require Export invariants.
Set Default Proof Using "Type".

Section Recursion.
  Context `{!heapG Σ}.

  Definition myrec : val :=
    λ: "f", let: "r" := ref (λ: "x", "x") in "r" <- (λ: "x", "f" (!"r") "x");; !"r".

  Definition F : val :=
    λ: "f" "x", if: "x" = #0 then #1 else "x" * "f" ("x" - #1).

  Definition fac : expr := myrec F.

  Lemma test_fac_wp:
    (WP fac #2 {{ v, ⌜v = #2⌝}})%I.
  Proof.
    iStartProof.
    wp_rec.
    wp_alloc r as "Hr".
    by repeat (wp_load || wp_store || wp_rec || wp_pure _).
  Qed.

  Fixpoint factorial (n : nat) : nat :=
    match n with
    | O => 1
    | S n' => n * factorial n'
    end.

  Lemma fac_wp (n : nat):
     {{{ ⌜True⌝ }}} fac #(Z.of_nat n) {{{ v, RET v; ⌜v = #(factorial n)⌝ }}}.
  Proof.
    iStartProof.
    iIntros (Φ) "_ HΦ".
    wp_rec.
    wp_alloc r as "Hr".
    wp_let.
    wp_store.
    wp_load.
    wp_lam.
    iMod (inv_alloc (nroot.@"fib") _ _ with "[Hr]") as "#inv".
    { iModIntro. iExact "Hr". }
    iInduction n as [|n'] "IH" forall (Φ).
    - wp_bind (! _)%E.
      iInv (nroot.@"fib") as "Hr" "cl".
      wp_load.
      iMod ("cl" with "[Hr]") as "_"; first done. iModIntro.
      wp_lam. wp_pures. iApply "HΦ". by simpl.
    - wp_bind (! _)%E.
      iInv (nroot.@"fib") as "Hr" "cl".
      wp_load.
      iMod ("cl" with "[Hr]") as "_"; first done. iModIntro.
      wp_rec. wp_pures.
      replace (S n' - 1) with (n' : Z) by admit.
      wp_apply "IH".
      iIntros (v2 ->).
      wp_op.
      replace (S n' * factorial n') with (factorial (S n') : Z) by admit.
      by iApply "HΦ".
  Admitted.

End Recursion.
