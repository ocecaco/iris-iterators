From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export notation lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.
Set Default Proof Using "Type".

Fixpoint forallI {Σ} {A} (P : A -> iProp Σ) (xs : list A) : iProp Σ :=
  match xs with
  | [] => ⌜True⌝
  | x :: xs' => P x ∗ forallI P xs'
  end%I.

Section Foldr.
  Context `{!heapG Σ}.

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
        let: "h" := (Fst "cons") in
        let: "t" := !(Snd "cons") in
        "f" "h" ("foldr" "f" "a" "t")
      end.

  Theorem prog_foldr_wp P (I : list val -> val -> iProp Σ) (f : val) acc v xs:
    {{{ is_list v xs
      ∗ forallI P xs
      ∗ I [] acc
      (* This was in the precondition in the lecture notes, but
      perhaps it would be more idiomatic when using the Coq
      implementation of Iris to put it outside the precondition
      somehow. *)
      ∗ ∀ x acc' ys, {{{ P x ∗ I ys acc' }}} f x acc' {{{ r, RET r; I (x :: ys) r }}} }}}
      prog_foldr f acc v
    {{{ r, RET r; is_list v xs ∗ I xs r }}}.
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
      wp_pures. wp_load. wp_pures.
      (* not sure if necessary to use wp_bind, but couldn't get it to work otherwise *)
      wp_bind (((prog_foldr f) acc) vt)%E.
      (* Had to generalize over Φ in the IH to get this to work, which
      makes sense *)
      iApply ("IH" with "Hvt HPxs' HI"). iModIntro. iIntros (v) "[Hvt HI]".
      wp_apply ("Hf" with "[$HPx $HI]"). iIntros (r) "HI".
      iApply "HΦ".
      iFrame.
      iExists lt, vt. by iFrame.
  Qed.

  Check prog_foldr_wp.

  (* Verify sum_list client, similar to the lecture notes *)
  Definition prog_add : val :=
    λ: "x" "y", "x" + "y".

  Definition prog_sum_list : val := λ: "xs",
    let: "f" := prog_add in
    prog_foldr "f" #0 "xs".

  Definition is_number (v : val) : iProp Σ :=
    ⌜∃(k : Z), v = #k⌝%I.

  Definition unwrap_val (v : val) : Z :=
    match v with
    | LitV (LitInt n) => n
    | _ => 0 (* get rid of this somehow, we should be able to prove
      this never occurs, using the fact that the list of val consists
      only of numbers *)
    end.

  Fixpoint sum_list (xs : list val) : Z :=
    match xs with
    | [] => 0
    | x :: xs' => unwrap_val x + sum_list xs'
    end.

  Definition sum_invariant (xs : list val) (r : val) : iProp Σ :=
    ⌜r = #(sum_list xs)⌝%I.

  (* I seem to not be inside the Iris proof mode here (there is no --*
  line), and the done tactic will not work. *)
  Lemma sum_invariant_empty_failed_attempt:
    (sum_invariant [] #0)%I.
  Proof.
    iIntros "".
    rewrite /sum_invariant /=.
    done.
  Qed.

  Lemma prog_add_wp x ys acc:
    {{{ is_number x ∗ sum_invariant ys acc }}}
      prog_add x acc
    {{{ v, RET v; sum_invariant (x :: ys) v }}}.
  Proof.
    iIntros (Φ) "[Hx HI] HΦ".
    wp_rec. wp_let.
    iDestruct "Hx" as "%".
    destruct H. rewrite H.
    iDestruct "HI" as "%".
    rewrite H0.
    wp_pures.
    iApply "HΦ".
    rewrite /sum_invariant.
    simpl. done.
  Qed.

  Lemma prog_sum_list_wp v xs:
    (* Would like to use the proof that all of the elements of xs are
    numbers to make the pattern matching in sum_list always work and
    avoid the use of unwrap_val. However, the proof that all elements
    are numbers is not "in scope" in the postcondition, it seems. I
    would like to provide the proof that all elements of the list are
    numbers to the sum_list function. *)
    {{{ is_list v xs ∗ forallI is_number xs }}}
      prog_sum_list v
    {{{ r, RET r; is_list v xs ∗ ⌜r = #(sum_list xs)⌝ }}}.
  Proof.
    iIntros (Φ) "[Hv Hnums] HΦ".
    wp_rec. wp_pures.
    iAssert (sum_invariant [] #0) as "Hbase".
    { by rewrite /sum_invariant /=. }
    (* doesn't work: wp_apply (prog_foldr_wp with "[$Hv $Hnums $Hbase]" prog_add_wp). *)
    (* instead I am only able to apply prog_add_wp and Hbase after some additional steps *)
    wp_apply (prog_foldr_wp with "[$Hv $Hnums Hbase]").
    iSplitL "Hbase".
    - iAssumption.
    - iIntros (x acc' ys Φ').
      iModIntro.
      iApply prog_add_wp.
    - iIntros (r) "[Hv HI]".
      iApply "HΦ". by iFrame.
  Qed.

End Foldr.
