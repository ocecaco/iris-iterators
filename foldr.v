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

  Fixpoint is_list (v : val) (xs : list val) :=
    match xs with
    | [] => ⌜v = InjLV #()⌝
    | x :: xs' => ∃(lt : loc) (vt : val), ⌜v = InjRV (x, #lt)⌝ ∗ lt ↦ vt ∗ is_list vt xs'
    end%I.

  Definition prog_foldr : val :=
    rec: "foldr" "f" "a" "xs" :=
      match: "xs" with
        InjL "unit" => "a"
      | InjR "cons" =>
        (* Slightly different from lecture notes, maybe there is a
        typo in there since ! and Fst were
        swapped *)
        let: "h" := (Fst "cons") in
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
    (* Had to move Hf into the intuitionistic context to be able to re-use it *)
    iIntros (Φ) "[Hv [HP [HI #Hf]]] HΦ".
    (* Observation: Contrary to the lecture notes, wp_rec does not
    seem to replace all recursive calls of prog_foldr by a different
    function nor does it introduce any hypothesis about the replaced
    function. *)
    iInduction xs as [|x xs'] "IH" forall (v acc Φ); simpl; wp_rec; wp_let; wp_let.
    - iDestruct "Hv" as "%"; subst. wp_match.
      iApply ("HΦ" with "[$HI //]").
    - iDestruct "HP" as "[HPx HPxs']".
      iDestruct "Hv" as (lt vt ->) "(Hlt & Hvt)".
      wp_match.
      wp_proj.
      wp_let.
      wp_load.
      wp_let.
      (* not sure if necessary, but couldn't get it to work otherwise *)
      wp_bind (((prog_foldr f) acc) vt)%E.
      (* Had to generalize over Φ in the IH to get this to work, which
      makes sense *)
      iApply ("IH" with "Hvt HPxs' HI").
      iIntros (v) "[Hvt HI]".
      wp_apply ("Hf" with "[$HPx $HI]").
      iIntros (r) "HI".
      iApply "HΦ".
      iFrame.
      iExists lt, vt. by iFrame.
  Qed.

  Check prog_foldr_wp.
End Foldr.
