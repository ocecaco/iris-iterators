From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Export par.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import frac_auth.
Set Default Proof Using "Type".

(* notice that is_list itself is of the form A -> val -> iProp for some A! *)
Fixpoint is_list `{!heapG Σ} {A} (res : A -> val -> iProp Σ) (xs : list A) (vs : val) : iProp Σ :=
  match xs with
  | [] => ⌜vs = InjLV #()⌝
  | x :: xs' => ∃(lh : loc) (v vs' : val), ⌜vs = InjRV #lh⌝ ∗ lh ↦ (v, vs') ∗ res x v ∗ is_list res xs' vs'
end%I.

Section MutatingMap.
  Local Set Default Proof Using "Type*".

  Context `{heapG Σ, spawnG Σ}.

  Definition prog_for_each : val :=
    rec: "for_each" "f" "xs" :=
      match: "xs" with
        InjL <> => Skip
      | InjR "cons" =>
        let: "head" := Fst !"cons" in
        let: "rest" := Snd !"cons" in
        "f" "head" ||| "for_each" "f" "rest"
      end.

  Lemma prog_for_each_wp {A}
        (f_coq : A -> A)
        (res : A -> val -> iProp Σ)
        (xs : list A)
        (f : val)
        (vs : val):
    {{{ is_list res xs vs
      ∗ (∀ (y : A) (vy : val), {{{ res y vy }}} f vy {{{ q, RET q; res (f_coq y) vy }}})
    }}}
      prog_for_each f vs
    {{{ w, RET w; is_list res (f_coq <$> xs) vs }}}.
  Proof.
    iIntros (Φ) "(Hxs & #Hf) HΦ".
    iInduction xs as [|x xs'] "IH" forall (vs Φ); simpl; wp_rec; wp_let.
    - iDestruct "Hxs" as "%"; subst. wp_pures.
      iApply "HΦ".
      by iFrame.
    - iDestruct "Hxs" as (lh v vs' ->) "(Hlh & Hres & Hxs')".
      wp_match.
      wp_load. wp_proj. wp_let.
      wp_load. wp_proj. wp_let.
      iApply (wp_par
                (fun _ => res (f_coq x) v)%I
                (fun _ => is_list res (f_coq <$> xs') vs')%I
                with "[Hres] [Hxs']").
      + (* left fork *) iApply ("Hf" with "[$Hres]").
        iModIntro. iIntros (_) "Hres". by iFrame.
      + (* right fork *) iSpecialize ("IH" $! vs' with "[$Hxs']").
        iApply "IH".
        iModIntro. iIntros (_) "Hres". iFrame.
      + (* after join *)
        iIntros (w1 w2) "[Hres1 Hres2]".
        iModIntro.
        iApply "HΦ".
        iExists lh, v, vs'. by iFrame.
  Qed.

End MutatingMap.

Section SumExample.
  Class myG Σ := MyG { myG_inG :> inG Σ (frac_authR natR) }.
  Definition myΣ : gFunctors := #[GFunctor (frac_authR natR)].

  Instance subG_myΣ {Σ} : subG myΣ Σ -> myG Σ.
  Proof. solve_inG. Qed.

  Context `{!heapG Σ, !spawnG Σ, !myG Σ}.
  Local Set Default Proof Using "Type*".

  Definition prog_mapper : val := λ: "s" "x", FAA "s" (!"x");; "x" <- !"x" + #1%nat.

  Definition prog_sum_loop : val := λ: "s" "xs",
    let: "f" := prog_mapper "s" in
    prog_for_each "f" "xs".

  Definition prog_sum : val := λ: "xs",
    let: "s" := ref #0%nat in
    prog_sum_loop "s" "xs";; !"s".

  Definition is_num_ref (x : nat) (v : val) : iProp Σ :=
    (∃(l : loc), ⌜v = #l⌝ ∗ l ↦ #x)%I.

  Record rich_num := mkRichNum
                       { value : nat
                         ; ghost_name : gname
                         ; fraction : frac
                         ; bound : nat
                       }.

  (* this is a reference to a number that also holds a fragment of an
  authoritative RA *)
  Definition is_rich_num_ref (x : rich_num) (v : val) : iProp Σ :=
    match x with
      {| value := n; ghost_name := γ; fraction := q; bound := k |} => is_num_ref n v ∗ own γ (◯!{q} k)
    end%I.

  Definition add_one (x : nat) : nat := x + 1.

  Definition rich_add_one (x : rich_num) : rich_num :=
    match x with
      {| value := n; ghost_name := γ; fraction := q; bound := k |} => mkRichNum (n + 1) γ q (n + k)
    end.

  Definition sum (xs : list nat) : nat := fold_right Nat.add 0%nat xs.

  (* Lemma foldr_sum x xs: *)
  (*   foldr Z.add x xs = x + foldr Z.add 0 xs. *)
  (* Proof. *)
  (*   induction xs as [|x' xs']. *)
  (*   - simpl. omega. *)
  (*   - simpl. rewrite IHxs'. omega. *)
  (* Qed. *)

  Fixpoint divide_fragments (γ : gname) (fraction : frac) (bound : nat) (xs : list nat) : list rich_num :=
    match xs with
    | [] => []
    | x :: xs' => mkRichNum x γ (fraction / 2) bound :: divide_fragments γ (fraction / 2) bound xs'
    end.

  Lemma enrich_list γ q k xs v:
    own γ (◯!{q} k) ∗ is_list is_num_ref xs v -∗ is_list is_rich_num_ref (divide_fragments γ q k xs) v.
  Proof.
  Admitted.

  (* Lemma derich_list γ q k xs v: *)
  (*   is_list is_rich_num_ref (divide_fragments γ q k xs) *)

  Definition sum_invariant γ (l : loc) : iProp Σ :=
    (∃k:nat, l ↦ #k ∗ own γ (●! k))%I.

  Lemma prog_sum_loop_wp (ls : loc) (n : nat) (v : val) (xs : list nat):
    {{{ is_list is_num_ref xs v ∗ ls ↦ #n }}}
      prog_sum_loop #ls v
    {{{ RET #(); is_list is_num_ref (add_one <$> xs) v ∗ ls ↦ #(sum xs + n)%nat }}}.
  Proof.
    iIntros (Φ) "[Hxs Hls] HΦ".
    wp_rec; wp_pures. wp_lam. wp_pures.
    iMod (own_alloc (●! n%nat ⋅ ◯! n%nat)) as (γ) "[Htrue Hfrag]"; first done.
    iMod (inv_alloc (nroot.@"sum_loop") _ (sum_invariant γ ls) with "[Hls Htrue]") as "#Hinv".
    { iModIntro. rewrite /sum_invariant. iExists n. iFrame. }
    iPoseProof (enrich_list with "[$Hfrag $Hxs]") as "Hrich".
    iApply (prog_for_each_wp rich_add_one with "[$Hrich]").
    - (* prove Texan triple for f *)
      iIntros (y vy Φ'). iModIntro.
      iIntros "Hy HΦ'".
      rewrite /is_rich_num_ref.
      destruct y as [num γ' q bound].
      iDestruct "Hy" as "[Hnum Hfrag]".
      wp_lam.
      rewrite /is_num_ref. iDestruct "Hnum" as (lnum ->) "Hnum".
      wp_load.
      wp_bind (FAA _ _).
      iInv "Hinv" as ">Hauth" "cl".
      rewrite /sum_invariant.
      iDestruct "Hauth" as (k) "[Hls Htrue]".
      wp_faa.
      (* now update our ghost variables after adding *)
      iMod (own_update γ' (●! k ⋅ ◯!{q} bound) (●! (k + num)%nat ⋅ ◯!{q} (bound + num)%nat) with "[Htrue Hfrag]") as "[Htrue Hfrag]".
      { apply frac_auth_update, (nat_local_update _ _ (k + num)%nat (bound + num)%nat). omega. }
      { rewrite own_op. iFrame. }
  Admitted.

          (**)
  Lemma prog_sum_wp (v : val) (xs : list nat):
    {{{ is_list is_num_ref xs v }}}
      prog_sum v
    {{{ s, RET s; is_list is_num_ref (add_one <$> xs) v ∗ ⌜s = #(sum xs)⌝}}}.
  Proof.
    iIntros (Φ) "Hxs HΦ".
    wp_lam. wp_alloc s as "Hs". wp_let.
    wp_apply (prog_sum_loop_wp with "[$Hxs $Hs]").
    iIntros "[Hxs Hs]".
    wp_seq. wp_load.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    by rewrite -plus_n_O.
  Qed.

End SumExample.
