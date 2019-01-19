From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export notation lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.
Set Default Proof Using "Type".

Section GhostStateSimple.
  Inductive incRAT : Type :=
  | S : incRAT
  | F : incRAT
  | Bot : incRAT.

  (* From what I've read, this roughly speaking allows the Coq type
  inference to view incRAT as a particular kind of OFE, which has some
  additional structure. *)
  Canonical Structure incRAC := leibnizC incRAT.

  (* Supply the resource algebra operation by giving an instance of
  the Op type class. *)
  Instance incRAop : Op incRAT :=
    λ p1 p2,
    match (p1, p2) with
    | (F, F) => F
    | _ => Bot
    end.

  Instance incRAvalid : Valid incRAT :=
    λ p,
    match p with
    | Bot => False
    | _ => True
    end.

  Instance incRAcore : PCore incRAT :=
    λ p, None.

  (* Combine all the components of the RA and prove that it is an
  RA *)
  Definition incRA_mixin : RAMixin incRAT.
  Proof.
    split; try apply _; try done.
    - (* associativity, simply show by case analysis *)
      rewrite /op. rewrite /incRAop.
      intros [] [] []; reflexivity.
    - (* commutativity *)
      rewrite /op. rewrite /incRAop.
      intros [] []; reflexivity.
    - (* validity of combination implies validity of parts *)
      intros [] [] HV; try done.
    (* there were a bunch more properties, such as the relation
       between validity and extension order but apparently it could
       automatically proof those. *)
  Qed.

  Canonical Structure incRA := discreteR incRAT incRA_mixin.

  (* Let Coq know that our CMRA is discrete. *)
  Instance incRA_cmra_discrete : CmraDiscrete incRA.
  Proof. apply discrete_cmra_discrete. Qed.

  (* Use an instantiation of Iris that has my new resource algebra. *)
  Class incG Σ := IncG { inc_inG :> inG Σ incRA }.
  Definition incΣ : gFunctors := #[GFunctor incRA].

  Instance subG_incΣ {Σ} : subG incΣ Σ -> incG Σ.
  Proof. solve_inG. Qed.

  Context `{!heapG Σ, !incG Σ}.

  Lemma incRA_F_duplicable γ: own γ F -∗ (own γ F ∗ own γ F).
  Proof.
    iIntros "HF".
    iApply own_op.
    iExact "HF".
  Qed.

  Lemma incRA_S_unique γ: own γ S ∗ own γ S -∗ ⌜False⌝.
  Proof.
    iIntros "HS".
    rewrite -own_op.
    iDestruct (own_valid with "HS") as "HV".
    iDestruct "HV" as %HV.
    iPureIntro.
    exact HV.
  Qed.

  Lemma incRA_S_F_incompatible γ: own γ S ∗ own γ F -∗ ⌜False⌝.
  Proof.
    iIntros "HR".
    rewrite -own_op.
    iDestruct (own_valid with "HR") as "HV".
    iDestruct "HV" as %HV.
    iPureIntro.
    exact HV.
  Qed.

End GhostStateSimple.
