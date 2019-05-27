From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import tactics.
From iris_ni.logrel Require Import types typemap.
From iris_ni.proofmode Require Import dwp_tactics.
From iris.heap_lang Require Import lang proofmode.
From Equations Require Import Equations.

Record lrel Σ := LRel {
  lrel_car :> slevel → val → val → iProp Σ;
  lrel_persistent ξ v1 v2 : Persistent (lrel_car ξ v1 v2)
}.
Arguments LRel {_} _%I {_}.
Arguments lrel_car {_} _ _ _ : simpl never.
Bind Scope lrel_scope with lrel.
Delimit Scope lrel_scope with lrel.
Existing Instance lrel_persistent.

(* The COFE structure on semantic types *)
Section lrel_ofe.
  Context `{Σ : gFunctors}.

  Instance lrel_equiv : Equiv (lrel Σ) := λ A B, ∀ ξ w1 w2, A ξ w1 w2 ≡ B ξ w1 w2.
  Instance lrel_dist : Dist (lrel Σ) := λ n A B, ∀ ξ w1 w2, A ξ w1 w2 ≡{n}≡ B ξ w1 w2.
  Lemma lrel_ofe_mixin : OfeMixin (lrel Σ).
  Proof. by apply (iso_ofe_mixin (lrel_car : lrel Σ → (slevel -c> val -c> val -c> iProp Σ))). Qed.
  Canonical Structure lrelC := OfeT (lrel Σ) lrel_ofe_mixin.

  Global Instance lrel_cofe : Cofe lrelC.
  Proof.
    apply (iso_cofe_subtype' (λ A : slevel -c> val -c> val -c> iProp Σ, ∀ ξ w1 w2, Persistent (A ξ w1 w2)) (@LRel _) lrel_car)=>//.
    - apply _.
    - apply limit_preserving_forall=> ξ.
      apply limit_preserving_forall=> w1.
      apply limit_preserving_forall=> w2.
      apply bi.limit_preserving_Persistent.
      intros n P Q HPQ. apply (HPQ ξ w1 w2).
  Qed.

  Global Instance lrel_inhabited : Inhabited (lrel Σ) := populate (LRel inhabitant).

  Global Instance lrel_car_ne n : Proper (dist n ==> (=) ==> (=) ==> (=) ==> dist n) lrel_car.
  Proof. by intros A A' ? ? ? <- w1 w2 <- ? ? <-. Qed.
  Global Instance lrel_car_proper : Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (≡)) lrel_car.
  Proof.
    repeat lazymatch goal with
    | |- Proper _ _ => intros ???
    | |- (_ ==> _)%signature _ _ => intros ???
    | |- pointwise_relation _ _ _ _ => intros ?
    end; simplify_eq;
    solve [repeat first [done | eassumption | apply equiv_dist=>? |
                         match goal with
                         | [H : _ ≡ _ |- _] => setoid_rewrite equiv_dist in H; rewrite H
                         end] ].
  Qed.

End lrel_ofe.

Arguments lrelC : clear implicits.

Section semtypes.
  Context `{!heapDG Σ, !typemapG (loc*loc) Σ}.

  Implicit Types e : expr.
  Implicit Types E : coPset.
  Implicit Types A B : lrel Σ.

  Definition locsN := nroot.@"locsinv".

  Definition locs_inv ξ (I : type → lrel Σ) :=
    (∃ (f : gmap (loc*loc) (type*slevel)), typemap_ctx f ∗
       [∗ map] ll ↦ τl ∈ f, ∃ v1 v2, ll.1 ↦ₗ v1 ∗ ll.2 ↦ᵣ v2 ∗
                                      I (curry stamp τl) ξ v1 v2)%I.

  Definition lrel_unit : lrel Σ := LRel (λ _ w1 w2, ⌜ w1 = #() ∧ w2 = #() ⌝%I).
  Definition lrel_int (l : slevel) : lrel Σ := LRel (λ ξ w1 w2,
      ∃ n1 n2 : Z, ⌜w1 = #n1⌝ ∧ ⌜w2 = #n2⌝ ∧ ⌜l ⊑ ξ → n1 = n2⌝)%I.
  Definition lrel_bool (l : slevel) : lrel Σ := LRel (λ ξ w1 w2,
      ∃ b1 b2 : bool, ⌜w1 = #b1⌝ ∧ ⌜w2 = #b2⌝ ∧ ⌜l ⊑ ξ → b1 = b2⌝)%I.

  Definition lrel_prod (A B : lrel Σ) : lrel Σ := LRel (λ ξ w1 w2,
    ∃ v1 v2 v1' v2', ⌜w1 = (v1,v1')%V⌝ ∧ ⌜w2 = (v2,v2')%V⌝ ∧
        A ξ v1 v2 ∗ B ξ v1' v2')%I.


  (* TODO: DF: use the level `l`? *)
  Definition lrel_arr (A1 A2 : lrel Σ) (l : slevel) : lrel Σ := LRel (λ ξ w1 w2,
    □ ∀ v1 v2, A1 ξ v1 v2 -∗ DWP (w1 v1) & (w2 v2) : A2 ξ)%I.


  (* There might be tempation to define
     ⟦ tref τ l ⟧ (v1,v2) as ∃ l1 l2, v1 = #l1 ∧ v2 = #l2 ∧
                          inv N (∃ w1 w2, l1 ↦ₗ w1 ∗ l2 ↦ᵣ w2 ∗ ⟦ τ ⊔ l ⟧ (w1, w2)

   but then we will not be able to prove that reference are monotone in the label
   (because invariants are, well, invariant)
   *)
  Definition lrel_ref (τ : type) l : lrel Σ := LRel (λ ξ w1 w2,
    ∃ l1 l2: loc, ⌜w1 = #l1⌝ ∧ ⌜w2 = #l2⌝ ∧
      has_type (l1,l2) τ l)%I.

  Equations interp (τ : type) : lrel Σ
    by wf (type_measure τ) :=
  interp tunit := lrel_unit;
  interp (tint l) := lrel_int l;
  interp (tbool l) := lrel_bool l;
  interp (tarrow s t l) :=
    lrel_arr (interp s) (interp (stamp t l)) l;
  (* TODO: is this stamp needed here? *)
  interp (tprod τ1 τ2) := lrel_prod (interp τ1) (interp τ2);
  interp (tref τ l) := lrel_ref τ l.
  Next Obligation. lia. Qed.
  Next Obligation. rewrite -stamp_measure. lia. Qed.
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.
  (* Next Obligation. lia. Qed. *)

  Lemma interp_eq τ :
    interp τ =
    match τ with
    | tunit => lrel_unit
    | tint l => lrel_int l
    | tbool l => lrel_bool l
    | tarrow s t l =>
      lrel_arr (interp s) (interp (stamp t l)) l
    | tprod τ1 τ2 => lrel_prod (interp τ1) (interp τ2)
    | tref τ l => lrel_ref τ l
    end.
  Proof. by funelim (interp τ). Qed.

  Lemma interp_sub_mono τ1 τ2 ξ v1 v2 :
    τ1 <: τ2 →
    interp τ1 ξ v1 v2 -∗ interp τ2 ξ v1 v2.
  Proof.
    intros Hsub. revert v1 v2. induction Hsub.
    - (* Reflexivity *) done.
    - (* Transitivity *) intros v1 v2. by rewrite -IHHsub2.
    - (* Int *) intros v1 v2.
      rewrite !interp_eq.
      iDestruct 1 as (i1 i2 -> ->) "H".
      iExists i1,i2.
      lazymatch goal with
      | [H: _ ⊑ _ |- _ ] => rewrite H
      end.
      eauto with iFrame.
    - (* Bool *) intros v1 v2.
      rewrite !interp_eq.
      iDestruct 1 as (i1 i2 -> ->) "H".
      iExists i1,i2.
      lazymatch goal with
      | [H: _ ⊑ _ |- _ ] => rewrite H
      end.
      eauto with iFrame.
    - (* Arrow *)
      iIntros (f1 f2). rewrite !(interp_eq (tarrow _ _ _)).
      iIntros "#IH". iModIntro. iIntros (v1 v2) "H".
      rewrite IHHsub1. iSpecialize ("IH" with "H").
      iApply (dwp_wand with "IH"). iIntros (w1 w2).
      (* Here we should be using the types_measure function
         somehow that ignores all the levels *)
      (* Or separately prove that monotonicity of interp
         is preserved by stamping. But morally this is "correct" *)
      (* rewrite IHHsub2. *)
      admit.
    - (* Product *)
      iIntros (uwu owo). rewrite !(interp_eq (tprod _ _)).
      iDestruct 1 as (v1 v2 w1 w2 -> ->) "[Hv Hw]".
      rewrite IHHsub1 IHHsub2. iExists _,_,_,_. repeat iSplit; eauto.
    - (* References *)
      iIntros (v1 v2).
      rewrite !(interp_eq (tref _ _)).
      iDestruct 1 as (r1 r2 -> ->) "#Hrs".
      iExists r1,r2. repeat iSplit; eauto.
      by iApply (has_type_weaken with "Hrs").
  Admitted.

  Definition refines (e1 e2 : expr) (A : lrel Σ) ξ : iProp Σ :=
    (inv locsN (locs_inv ξ interp) -∗ DWP e1 & e2 : A ξ)%I.

End semtypes.

Notation "⟦ τ ⟧" := (interp τ).

Section rules.
  Context `{!heapDG Σ, !typemapG (loc*loc) Σ}.

  Lemma dwp_int ξ (i : Z) l :
    refines #i #i ⟦ tint l ⟧ ξ.
  Proof.
    iIntros "#Hinv".
    iApply dwp_value. iModIntro.
    iExists i, i. iPureIntro. naive_solver.
  Qed.

  Lemma dwp_int_high ξ (i1 i2 : Z) l :
    ¬ (l ⊑ ξ) →
    refines (of_val #i1) (of_val #i2) ⟦ tint l ⟧ ξ.
  Proof.
    iIntros (?) "#Hinv". iApply dwp_value. iModIntro.
    iExists i1, i2. iPureIntro. naive_solver.
  Qed.

  Lemma dwp_unit ξ :
    refines (of_val #()) (of_val #()) ⟦ tunit ⟧ ξ.
  Proof.
    iIntros "#Hinv".
    iApply dwp_value. iModIntro.
    iPureIntro. eauto.
  Qed.

  Lemma dwp_bool ξ (b : bool) l :
    refines #b #b ⟦ tbool l ⟧ ξ.
  Proof.
    iIntros "#Hinv".
    iApply dwp_value. iModIntro.
    iExists b, b. iPureIntro. naive_solver.
  Qed.

  Lemma dwp_bool_high ξ (b1 b2 : bool) l :
    ¬ (l ⊑ ξ) →
    DWP (of_val #b1) & (of_val #b2) : ⟦ tbool l ⟧ ξ.
  Proof.
    iIntros (?). iApply dwp_value. iModIntro.
    iExists b1, b2. iPureIntro. naive_solver.
  Qed.

  (* TODO: is the stamping needed here? *)
  Lemma dwp_if ξ (e1 e2 t1 t2 u1 u2 : expr) (τ : type) l :
    (DWP e1 & e2 : ⟦ tbool l ⟧ ξ) -∗
    ((DWP t1 & t2 : ⟦ stamp τ l ⟧ ξ) ∧
        (⌜¬ l ⊑ ξ⌝ → DWP u1 & t2 : ⟦ stamp τ l ⟧ ξ)) -∗
    ((DWP u1 & u2 : interp (stamp τ l) ξ) ∧
        (⌜¬ l ⊑ ξ⌝ → DWP t1 & u2 : ⟦ stamp τ l ⟧ ξ)) -∗
    DWP (if: e1 then t1 else u1) & (if: e2 then t2 else u2) : interp (stamp τ l) ξ.
  Proof.
    iIntros "He Ht Hu".
    dwp_bind e1 e2.
    iApply (dwp_wand with "He"). iIntros (v1 v2 Hv).
    destruct Hv as (b1 & b2 & -> & -> & Hb1b2).
    destruct (decide (l ⊑ ξ)) as [Hlvl | Hlvl]; try specialize (Hb1b2 Hlvl); simplify_eq/=.
    - destruct b2; dwp_pures.
      + by iDestruct "Ht" as "[$ _]".
      + by iDestruct "Hu" as "[$ _]".
    - destruct b1, b2; dwp_pures.
      + by iDestruct "Ht" as "[$ _]".
      + iDestruct "Hu" as "[_ H]". by iApply "H".
      + iDestruct "Ht" as "[_ H]". by iApply "H".
      + by iDestruct "Hu" as "[$ _]".
  Qed.

  Lemma dwp_lam ξ x e1 e2 τ1 τ2 l :
    □ (∀ v1 v2, ⟦ τ1 ⟧ ξ v1 v2 -∗ DWP subst' x v1 e1 & subst' x v2 e2 : ⟦ stamp τ2 l ⟧ ξ) -∗
    DWP (λ: x, e1)%V & (λ: x, e2)%V : ⟦ tarrow τ1 τ2 l ⟧ ξ.
  Proof.
    iIntros "#H".
    iApply dwp_value. rewrite (interp_eq (tarrow _ _ _)). iModIntro.
    iModIntro. iIntros (v1 v2) "Hτ1". dwp_pures. simpl.
    by iApply "H".
  Qed.

  Lemma dwp_app ξ e1 e2 e1' e2' τ1 τ2 l :
    (DWP e1 & e2 : ⟦ tarrow τ1 τ2 l ⟧ ξ) -∗
    (DWP e1' & e2' : ⟦ τ1 ⟧ ξ) -∗
    DWP e1 e1' & e2 e2' : ⟦ stamp τ2 l ⟧ ξ.
  Proof.
    iIntros "H1 H2".
    dwp_bind e1' e2'.
    iApply (dwp_wand with "H2"). iIntros (v1 v2) "Hv".
    dwp_bind e1 e2.
    iApply (dwp_wand with "H1"). iIntros (f1 f2) "Hf".
    rewrite (interp_eq (tarrow _ _ _)) {2}/lrel_car /=.
    iDestruct "Hf" as "#Hf". iApply ("Hf" with "Hv").
  Qed.

  Lemma dwp_seq ξ e1 e2 e1' e2' A τ2 :
    (DWP e1 & e2 : A) -∗
    (DWP e1' & e2' : ⟦ τ2 ⟧ ξ) -∗
    DWP (e1;; e1') & (e2;; e2') : ⟦ τ2 ⟧ ξ.
  Proof.
    iIntros "H1 H2".
    dwp_bind e1 e2.
    iApply (dwp_wand with "H1").
    iIntros (??) "_". dwp_pures. simpl.
    iApply "H2".
  Qed.

  Lemma dwp_fork ξ e1 e2 :
    (DWP e1 & e2 : ⟦ tunit ⟧ ξ) -∗
    (DWP Fork e1 & Fork e2 : ⟦ tunit ⟧ ξ).
  Proof.
    iIntros "H". iApply (dwp_fork with "[H]").
    - iNext. iApply (dwp_wand with "H"); auto.
    - iNext. eauto.
  Qed.

  (* TODO: we can relax the interpretation of tref here????
     do it without stamping and get a stronger spec *)
  Lemma dwp_alloc ξ e1 e2 τ l :
    (refines e1 e2 ⟦ τ ⟧ ξ) -∗
    refines (ref e1) (ref e2) ⟦ tref τ l ⟧ ξ.
  Proof.
    iIntros "He #Hinv". iSpecialize ("He" with "Hinv").
    dwp_bind e1 e2.
    iApply (dwp_wand with "He").
    iIntros (v1 v2) "#Hv".
    pose (Φ1 := (λ v, ∃ (l : loc), ⌜v = #l⌝ ∗ l ↦ₗ v1)%I).
    pose (Φ2 := (λ v, ∃ (l : loc), ⌜v = #l⌝ ∗ l ↦ᵣ v2)%I).
    iApply (dwp_atomic_lift_wp _ _ Φ1 Φ2%I); try done.
    iModIntro. repeat iSplitR.
    - rewrite /WP1 /Φ1. wp_alloc l1 as "Hl". eauto with iFrame.
    - rewrite /WP2 /Φ2. wp_alloc l1 as "Hl". eauto with iFrame.
    - iIntros (? ?). iDestruct 1 as (l1 ->) "Hl1".
      iDestruct 1 as (l2 ->) "Hl2".
      iInv locsN as (f) "[>Hf Hlocs]" "Hcl".
      assert (f !! (l1, l2) = None).
      { (* otherwise we can extract l1 ↦ .. from the Hlocs and get a
      contradiction *) admit. }
      iMod (typemap_alloc f (l1,l2) τ l with "Hf") as "[Hf Hll]"; auto.
      iMod ("Hcl" with "[-Hll]") as "_".
      { iNext. iExists _. iFrame.
        rewrite big_sepM_insert=>//. iFrame.
        iExists _,_. simpl. iFrame.
        iApply (interp_sub_mono with "Hv"). apply stamp_sub. }
      iModIntro. iNext. iExists _,_. repeat iSplit; eauto.
  Admitted.

  Lemma dwp_load ξ e1 e2 τ l :
    (refines e1 e2 ⟦ tref τ l ⟧ ξ) -∗
    refines !e1 !e2 ⟦ stamp τ l ⟧ ξ.
  Proof.
    iIntros "He #Hinv". iSpecialize ("He" with "Hinv").
    dwp_bind e1 e2.
    iApply (dwp_wand with "He").
    iIntros (v1 v2). rewrite interp_eq /lrel_car /=.
    iDestruct 1 as (l1 l2 -> ->) "#Hll".

    pose (Φ1 := (λ v, l1 ↦ₗ{1/2} v)%I).
    pose (Φ2 := (λ v, l2 ↦ᵣ{1/2} v)%I).

    iApply (dwp_atomic_lift_wp _ _ Φ1 Φ2); try done.
    iInv locsN as (f) "[>Hf Hlocs]" "Hcl".
    iDestruct (typemap_lookup with "Hf Hll") as %[l' [Hf Hl']].
    rewrite (big_sepM_lookup_acc _ f (l1,l2))=>//.
    iDestruct "Hlocs" as "[Hl1l2 Hlocs]".
    iDestruct "Hl1l2" as (v1 v2) "(>Hl1 & >Hl2 & #Hτ')".
    iModIntro. iSimpl in "Hl1". iSimpl in "Hl2".
    iDestruct "Hl1" as "[Hl1 Hl1']".
    iDestruct "Hl2" as "[Hl2 Hl2']".
    iSplitL "Hl1"; [|iSplitL "Hl2"].
    - rewrite /WP1. wp_load. done.
    - rewrite /WP2. wp_load. done.
    - iIntros (w1 w2) "Hl1 Hl2".
      iDestruct (mapsto_agree with "Hl1 Hl1'") as %->.
      iCombine "Hl1 Hl1'" as "Hl1".
      iDestruct (mapsto_agree with "Hl2 Hl2'") as %->.
      iCombine "Hl2 Hl2'" as "Hl2".
      iMod ("Hcl" with "[-]") as "_".
      { iNext. iExists _. iFrame. iApply "Hlocs".
        eauto with iFrame. }
      iModIntro. iNext. simpl. iApply (interp_sub_mono with "Hτ'").
      (* TODO: need stamp_mono_2 *)
      admit.
  Admitted.

  Lemma dwp_store ξ e1 e2 t1 t2 τ l :
    (refines e1 e2 ⟦ tref τ l ⟧ ξ) -∗
    (refines t1 t2 ⟦ τ ⟧ ξ) -∗
    refines (e1 <- t1) (e2 <- t2) ⟦ tunit ⟧ ξ.
  Proof.
    iIntros "He Ht #Hinv".
    iSpecialize ("He" with "Hinv").
    iSpecialize ("Ht" with "Hinv").
    dwp_bind t1 t2. iApply (dwp_wand with "Ht").
    iIntros (w1 w2) "Hw".
    dwp_bind e1 e2. iApply (dwp_wand with "He").
    iIntros (? ?). iDestruct 1 as (r1 r2 -> ->) "Hr".

    pose (Φ1 := (λ v, ⌜v = #()⌝ ∧ r1 ↦ₗ w1)%I).
    pose (Φ2 := (λ v, ⌜v = #()⌝ ∧ r2 ↦ᵣ w2)%I).

    iApply (dwp_atomic_lift_wp _ _ Φ1 Φ2); try done.
    iInv locsN as (f) "[>Hf Hlocs]" "Hcl".
    iDestruct (typemap_lookup with "Hf Hr") as %[l' [Hf Hl']].
    rewrite (big_sepM_lookup_acc _ f (r1,r2))=>//.
    iDestruct "Hlocs" as "[Hr1r2 Hlocs]".
    iDestruct "Hr1r2" as (v1 v2) "(>Hr1 & >Hr2 & #Hτ')".
    iModIntro. iSimpl in "Hr1". iSimpl in "Hr2".
    iSplitL "Hr1"; [|iSplitL "Hr2"].
    - rewrite /WP1 /Φ1. wp_store. eauto.
    - rewrite /WP2 /Φ2. wp_store. eauto.
    - iIntros (? ?) "[-> Hr1] [-> Hr2]".
      iMod ("Hcl" with "[-]") as "_".
      { iNext. iExists _. iFrame. iApply "Hlocs".
        iExists _, _. iFrame.
        iApply (interp_sub_mono with "Hw").
        simpl. apply stamp_sub. }
      iModIntro. eauto.
  Qed.

  (*****************************************************************)
  Definition prog (r r' : loc) (h : bool) : expr :=
    #r <- #true;;
    #r' <- #true;;
    let: "x" := if: #h then #r else #r' in
    (* we wouldn't be able to prog even the program without this assignment *)
    "x" <- #false;;
    !#r'.

  Definition bad_example (r1 r2 r1' r2' : loc) (h1 h2 : bool) :
    ⟦ tref (tbool Low) Low ⟧ Low #r1 #r2 -∗
    ⟦ tref (tbool Low) Low ⟧ Low #r1' #r2' -∗
    ⟦ tbool High ⟧ Low #h1 #h2 -∗
    refines (prog r1 r1' h1) (prog r2 r2' h2) ⟦ tbool Low ⟧ Low.
  Proof.
    iIntros "#Hr #Hr' #Hh #Hinv".
    iApply dwp_seq.
    { iApply (dwp_store Low _ _ _ _ (tbool Low)); auto.
      - iIntros "_". iApply dwp_value. iModIntro. iApply "Hr".
      - iIntros "_". by iApply dwp_bool. }
    iApply dwp_seq.
    { iApply (dwp_store Low _ _ _ _ (tbool Low)); auto.
      - iIntros "_". iApply dwp_value. iModIntro. iApply "Hr'".
      - iIntros "_". by iApply dwp_bool. }
    (* Attempt by structural reasoning (will fail at `let x = ..`) *)
    dwp_bind (if: _ then _ else _)%E (if: _ then _ else _)%E.
    iApply (dwp_wand with "[]").
    { iApply (dwp_if _ _ _ _ _ _ _ (tref (tbool Low) Low)).
      - iApply dwp_value. iApply "Hh".
      - iSplit.
        + iApply dwp_value. simpl.
          iApply (interp_sub_mono with "Hr").
          apply type_sub_ref. eauto.
        + iIntros (?).
    (* Attempt by symbolic execution (will fail at the store) *)
    (* destruct h1, h2. *)
    (* { dwp_pures. simpl. admit. } *)
  Abort.

  Definition prog_good (r r' : loc) (h : bool) : expr :=
    #r <- #true;;
    #r' <- #true;;
    let: "x" := if: #h then #r else #r' in
    !#r'.

  Definition good_example (r1 r2 r1' r2' : loc) (h1 h2 : bool) :
    ⟦ tref (tbool Low) Low ⟧ Low #r1 #r2 -∗
    ⟦ tref (tbool Low) Low ⟧ Low #r1' #r2' -∗
    ⟦ tbool High ⟧ Low #h1 #h2 -∗
    refines (prog_good r1 r1' h1) (prog_good r2 r2' h2) ⟦ tbool Low ⟧ Low.
  Proof.
    iIntros "#Hr #Hr' #Hh #Hinv".
    iApply dwp_seq.
    { iApply (dwp_store Low _ _ _ _ (tbool Low)); auto.
      - iIntros "_". iApply dwp_value. iModIntro. iApply "Hr".
      - iIntros "_". by iApply dwp_bool. }
    iApply dwp_seq.
    { iApply (dwp_store Low _ _ _ _ (tbool Low)); auto.
      - iIntros "_". iApply dwp_value. iModIntro. iApply "Hr'".
      - iIntros "_". by iApply dwp_bool. }
    destruct h1, h2.
    { dwp_pures. simpl. iApply (dwp_mono with "[]"); last first.
      { iApply dwp_load; eauto. iIntros "_". iApply dwp_value.
        iApply "Hr'". }
      simpl. eauto. }
    { dwp_pures. simpl. iApply (dwp_mono with "[]"); last first.
      { iApply dwp_load; eauto. iIntros "_". iApply dwp_value.
        iApply "Hr'". }
      simpl. eauto. }
    { dwp_pures. simpl. iApply (dwp_mono with "[]"); last first.
      { iApply dwp_load; eauto. iIntros "_". iApply dwp_value.
        iApply "Hr'". }
      simpl. eauto. }
    { dwp_pures. simpl. iApply (dwp_mono with "[]"); last first.
      { iApply dwp_load; eauto. iIntros "_". iApply dwp_value.
        iApply "Hr'". }
      simpl. eauto. }
  Qed.
End rules.
