From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export notation lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.
Set Default Proof Using "Type".

Section YCombinator.
  Context `{!heapG Σ}.

  Definition prog_omega (F : val) : val := λ: "r", F (λ: "x", "r" "r" "x").

  Definition prog_theta (F : val) : expr := (prog_omega F) (prog_omega F).

  Definition prog_infinite_loop : val := λ: "n",
    (prog_theta (λ: "f" "n", "f" ("n" - #1))) "n".

  (* Show that the above program never terminates using Löb
  induction. *)
  Lemma prog_simple_loop_wp (n : Z):
    (WP prog_infinite_loop #n {{ v, ⌜False⌝ }})%I.
  Proof.
    wp_rec.
    iLöb as "IH" forall (n).
    (* applying this removes the ▷ modality in the
       hypotheses, presumably since we have taken an
       operational step *)
    wp_rec.
    wp_pures.
    wp_rec.
    wp_pures.
    iApply "IH".
  Qed.

  (* It seems to me that Löb induction is not necessary in many cases,
  since we can use an induction hypothesis from ordinary induction
  when we have a structurally decreasing argument. *)

End YCombinator.
