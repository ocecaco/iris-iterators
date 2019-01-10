From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

Definition incrementer (l : expr) : expr := l <- !l + #1.

Lemma simple_assign `{!heapG Σ} l (n : Z):
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

Lemma simple_assign2 `{!heapG Σ} l (n : Z):
  [[{ l ↦ #n }]]
    (incrementer #l);; (incrementer #l)
  [[{ RET #(); l ↦ #(n + 2) }]].
Proof.
  iIntros (Φ) "Hloc HΦ".
  (* wp_seq. *)
  (* wp_apply simple_assign. *)
Admitted.
