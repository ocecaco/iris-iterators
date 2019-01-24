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

  (* for_each on empty list behaves like Skip *)
  Lemma prog_for_each_empty_wp {A} (res : A -> val -> iProp Σ) (f : val) (v : val):
    {{{ is_list res [] v }}} prog_for_each f v {{{ w, RET w; is_list res [] v }}}.
  Proof.
    iIntros (Φ) "Hv HΦ". iDestruct "Hv" as "%"; subst.
    wp_lam. wp_pures. iApply "HΦ".
    rewrite /is_list. done.
  Qed.

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
    prog_for_each "f" "xs";; !"s".

  Definition prog_sum : val := λ: "xs",
    let: "s" := ref #0%nat in
    prog_sum_loop "s" "xs".

  Definition is_num_ref (x : nat) (v : val) : iProp Σ :=
    (∃(l : loc), ⌜v = #l⌝ ∗ l ↦ #x)%I.

  Record rich_num := mkRichNum
                       { value : nat
                         ; fraction : frac
                         ; bound : nat
                       }.

  (* this is a reference to a number that also holds a fragment of an
  authoritative RA *)
  Definition is_rich_num_ref (γ : gname) (x : rich_num) (v : val) : iProp Σ :=
    match x with
      {| value := n; fraction := q; bound := k |} => is_num_ref n v ∗ own γ (◯!{q} k)
    end%I.

  Definition add_one (x : nat) : nat := x + 1.

  Definition rich_add_one (x : rich_num) : rich_num :=
    match x with
      {| value := n; fraction := q; bound := k |} => mkRichNum (n + 1) q (n + k)
    end.

  Definition sum (xs : list nat) : nat := fold_right Nat.add 0%nat xs.

  Fixpoint divide_fragments (fraction : frac) (xs : list nat) : list rich_num :=
    match xs with
    | [] => []
    | [x] => [mkRichNum x fraction 0%nat]
    | x :: xs' => (mkRichNum x (fraction / 2) 0%nat) :: divide_fragments (fraction / 2) xs'
    end.

  Lemma enrich_list γ q xs vs:
    own γ (◯!{q} 0%nat) ∗ is_list is_num_ref xs vs -∗ is_list (is_rich_num_ref γ) (divide_fragments q xs) vs.
  Proof.
    iIntros "[Hfrag Hxs]".
    iInduction xs as [|x xs'] "IH" forall (q vs); simpl.
    - iDestruct "Hxs" as "%"; subst. by iFrame.
    - iDestruct "Hxs" as (lh v vs' ->) "(Hlh & Hx & Hxs')".
      destruct xs'; simpl.
      + iExists lh, v, vs'. by iFrame.
      + iExists lh, v, vs'.
        iAssert (own γ (◯!{q/2} 0%nat) ∗ own γ (◯!{q/2} 0%nat))%I with "[Hfrag]" as "[Hfrag1 Hfrag2]".
        { rewrite -own_op -frac_auth_frag_op.
          replace (q / 2 + q /2)%Qp with q%Qp.
          - done.
          - by rewrite Qp_div_2. }
        iFrame.
        iDestruct "Hxs'" as (lh' v' vs'' ->) "(Hlh' & Hx' & Hxs'')".
        iSplitR. { done. }
        iApply ("IH" with "[Hfrag1] [Hlh' Hx' Hxs'']").
        { auto. }
        { iExists lh', v', vs''. by iFrame. }
  Qed.

  Lemma derich_list (γ : gname) (xs : list nat) (vs : val) (q : frac):
    (⌜xs ≠ []⌝ ∗ is_list (is_rich_num_ref γ) (rich_add_one <$> divide_fragments q xs) vs
     -∗ is_list is_num_ref (add_one <$> xs) vs ∗ own γ (◯!{q} (sum xs)%nat))%I.
  Proof.
    iIntros "[Hone Hrich]".
    iDestruct "Hone" as %Hone.
    iInduction xs as [|x xs'] "IH" forall (vs q); simpl.
    - exfalso. apply Hone. reflexivity.
    - destruct xs'; simpl.
      + iDestruct "Hrich" as (lh v vs' ->) "(Hlh & [Hx Hfrag] & Hvs')".
        iFrame.
        iExists lh, v, vs'.
        by iFrame.
      + iDestruct "Hrich" as (lh v vs' ->) "(Hlh & [Hx Hfrag] & Hvs')".
        iAssert (⌜n :: xs' ≠ []⌝)%I as "Hone'".
        { iPureIntro. intros Hfoo. inversion Hfoo. }
        iDestruct ("IH" with "Hone' Hvs'") as "[IH' Hfrag']".
        iCombine "Hfrag" "Hfrag'" as "Hfrag".
        replace (x + 0 + (n + sum xs'))%nat with (x + (n + sum xs'))%nat. 2: { rewrite <- (plus_n_O x). reflexivity. }
        iFrame.
        iExists lh, v, vs'.
        by iFrame.
  Qed.

  Definition sum_invariant γ (l : loc) : iProp Σ :=
    (∃k:nat, l ↦ #k ∗ own γ (●! k))%I.

  Lemma prog_mapper_wp N γ l:
    ∀y vy,
    inv N (sum_invariant γ l) -∗
    {{{ is_rich_num_ref γ y vy }}}
      (λ: "x", FAA #l ! "x";; "x" <- ! "x" + #1%nat)%V vy
      {{{ w, RET w; is_rich_num_ref γ (rich_add_one y) vy }}}.
  Proof.
    iIntros (y vy).
    iIntros "#Hinv".
    iIntros (Φ). iModIntro.
    iIntros "Hy HΦ".
    rewrite /is_rich_num_ref.
    destruct y as [num q bound]; simpl.
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
    iMod (own_update γ (●! k ⋅ ◯!{q} bound) (●! (k + num)%nat ⋅ ◯!{q} (bound + num)%nat) with "[Htrue Hfrag]") as "[Htrue Hfrag]".
    { apply frac_auth_update, (nat_local_update _ _ (k + num)%nat (bound + num)%nat). omega. }
    { rewrite own_op. iFrame. }
    iMod ("cl" with "[Hls Htrue]") as "_".
    { iModIntro. iExists (k + num)%nat. iFrame.
      by rewrite Nat2Z.inj_add. }
    iModIntro.
    wp_seq.
    wp_load. wp_op. wp_store. iApply "HΦ".
    iSplitR "Hfrag".
    + iExists lnum. iSplitR.
      * done.
      * by rewrite Nat2Z.inj_add.
    + by rewrite plus_comm.
  Qed.

  Lemma prog_sum_loop_wp (ls : loc) (v : val) (xs : list nat):
    {{{ is_list is_num_ref xs v ∗ ls ↦ #0 }}}
      prog_sum_loop #ls v
    {{{ RET #((sum xs)%nat); is_list is_num_ref (add_one <$> xs) v }}}.
  Proof.
    iIntros (Φ) "[Hxs Hls] HΦ".
    wp_rec; wp_pures. wp_lam. wp_pures.
    destruct xs. (* use different triple for empty list *)
    { wp_apply (prog_for_each_empty_wp with "Hxs").
      iIntros (w) "Hxs". wp_seq. wp_load.
      iApply "HΦ".
      simpl.
      done. }
    (* from this point on we know the list is non-empty *)
    iMod (own_alloc (●! 0%nat ⋅ ◯! 0%nat)) as (γ) "[Htrue Hfrag]"; first done.
    iMod (inv_alloc (nroot.@"sum_loop") _ (sum_invariant γ ls) with "[Hls Htrue]") as "#Hinv".
    { iModIntro. rewrite /sum_invariant. iExists 0%nat. iFrame. }
    iPoseProof (enrich_list with "[$Hfrag $Hxs]") as "Hrich".
    wp_apply (prog_for_each_wp rich_add_one with "[$Hrich]").
    - (* prove Texan triple for f, very roundabout way, but couldn't
      manage to directly apply prog_mapper_wp *)
      iIntros (y vy Φ'). iModIntro.
      iIntros "Hnum HΦ'".
      iPoseProof (prog_mapper_wp _ _ _ y vy with "Hinv") as "Hmapper".
      iSpecialize ("Hmapper" $! Φ' with "Hnum HΦ'").
      (* I get these sometimes, not sure why they are in there *)
      unlock.
      iExact "Hmapper".

    - iIntros (w) "Hrich".
      wp_seq.
      iAssert (⌜n :: xs ≠ []⌝)%I as "Hnonempty".
      { iPureIntro. intros. discriminate. }
      iPoseProof (derich_list with "[$Hnonempty $Hrich]") as "[Hderich Hfrag]".
      iInv "Hinv" as ">Hauth" "cl".
      rewrite /sum_invariant.
      iDestruct "Hauth" as (k) "[Hls Htrue]".
      iCombine "Htrue" "Hfrag" as "Hauth".
      iAssert (⌜k = (sum (n :: xs))%nat⌝)%I as "%".
      { rewrite own_valid. iDestruct "Hauth" as "%". iPureIntro.
        apply frac_auth_agreeL.
        exact H. }
      subst.
      iDestruct "Hauth" as "[Htrue Hfrag]".
      wp_load.
      iMod ("cl" with "[Hls Htrue]") as "_".
      { iModIntro. iExists (sum (n :: xs))%nat. iFrame. }
      iModIntro. iApply "HΦ".
      iFrame.
  Qed.

  Lemma prog_sum_wp (v : val) (xs : list nat):
    {{{ is_list is_num_ref xs v }}}
      prog_sum v
    {{{ s, RET s; is_list is_num_ref (add_one <$> xs) v ∗ ⌜s = #(sum xs)⌝}}}.
  Proof.
    iIntros (Φ) "Hxs HΦ".
    wp_lam. wp_alloc s as "Hs". wp_let.
    wp_apply (prog_sum_loop_wp with "[$Hxs $Hs]").
    iIntros "Hnums".
    iApply "HΦ".
    by iFrame.
  Qed.

End SumExample.
