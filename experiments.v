From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

Section Concrete.
  Context `{heapG Σ}.

  Definition incrementer (l : expr) : expr := l <- !l + #1.

  Lemma simple_assign l (n : Z):
    [[{ l ↦ #n }]]
      incrementer #l
      [[{ RET #(); l ↦ #(n + 1) }]].
  Proof.
    iIntros (Φ) "Hloc HΦ".
    rewrite /incrementer.
    wp_load.
    wp_store.
    by iApply "HΦ".
  Qed.

  Check simple_assign.

  (* Questions/remarks: *)

  (* The Σ here in the type of simple_assign is determined by Coq, presumably by looking for a type that matches the typeclass constraint heapG? *)

  (* Compared to the lecture notes, there seems to be no need to invoke a "wp_bind" rule for getting to the right part of an evaluation context. We can just use wp_load and wp_store right away. *)

  (* Unset Printing Notations. *)

  Lemma simple_assign2 l (n : Z):
    [[{ l ↦ #n }]]
      (incrementer #l);; (incrementer #l)
      [[{ RET #(); l ↦ #(n + 2) }]].
  Proof.
    iIntros (Φ) "Hloc HΦ".
    (* wp_seq. *)
    wp_apply (simple_assign with "Hloc").
    iIntros "Hloc".
    wp_seq.
    wp_apply (simple_assign with "Hloc").
    iIntros "Hloc".
    iApply "HΦ".
    replace (n + 1 + 1) with (n + 2).
    - done.
    - omega.
  Qed.

  (* loop n = if n = 0 then 0 else loop (n - 1) + 1

  This is simply the identity function for non-negative integers,
  implemented in a roundabout fashion. *)
  Definition simple_loop : val :=
    rec: "loop" "n" :=
      if: "n" = #0
      then #0
      else "loop" ("n" - #1%nat) + #1.

  (* The error message you get when you forget the heapG Σ is somewhat
  cryptic. I just put it in the Context now so I cannot forget
  anymore. *)

  (* If I make simple_loop an expr then wp_rec (understandably) fails
  to work with a cryptic error message. Presumably I have to "reduce"
  the left-hand side of the application to a value first. *)

  Lemma spec_simple_loop (n : nat):
    WP simple_loop #n {{ v, ⌜v = #n⌝}}%I.
  Proof.
    iInduction n as [|n'] "IH"; rewrite /simple_loop; wp_rec.
    - wp_op. wp_if_true. done.
    - wp_op. wp_if_false. wp_op.
  Admitted.

End Concrete.
