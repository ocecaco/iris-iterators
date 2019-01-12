From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

Fixpoint forallI {Σ} {A} (P : A -> iProp Σ) (xs : list A) : iProp Σ :=
  match xs with
  | [] => ⌜True⌝
  | x :: xs' => P x ∗ forallI P xs'
  end%I.

Section Foldr.
  Context `{heapG Σ}.

  (* Is it really necessary to store the values inside the list behind the pointer lx? *)
  Fixpoint is_list (v : val) (xs : list val) :=
    match xs with
    | [] => ⌜v = InjLV #()⌝
    | x :: xs' => ∃(lx lt : loc) (vt : val), ⌜v = InjRV (#lx, #lt)⌝ ∗ lx ↦ x ∗ lt ↦ vt ∗ is_list vt xs'
    end%I.

  Definition prog_foldr : val :=
    rec: "foldr" "f" "a" "xs" :=
      match: "xs" with
        InjL "unit" => "a"
      | InjR "cons" =>
        (* Slightly different from lecture notes, maybe there is a
        typo in there since ! and Fst were
        swapped *)
        let: "h" := !(Fst "cons") in
        let: "t" := !(Snd "cons") in
        "f" "h" ("foldr" "f" "a" "t")
      end.

  (* Observation: Instead of specifying the foldr with respect to a
  foldr implemented in Coq, this specification uses a predicate I
  which could be instantiated with something like

  I xs r := foldr (+) 0 xs = r

  Therefore this version seems more general and is not linked to a
  specific Coq reference implementation. *)
  Theorem prog_foldr_wp P (I : list val -> val -> iProp Σ) (f : val) acc v xs:
    [[{ is_list v xs
      ∗ forallI P xs
      ∗ I [] acc
      ∗ ∀ x acc' ys, [[{ P x ∗ I ys acc' }]] f x acc' [[{ r, RET r; I (x :: ys) r }]] }]]
      prog_foldr f acc v
    [[{ r, RET r; is_list v xs ∗ I xs r }]].
  Proof.
  Admitted.

End Foldr.
