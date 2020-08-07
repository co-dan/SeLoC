From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types.
From iris_ni.program_logic Require Export dwp heap_lang_lifting.
From iris.proofmode Require Import tactics.
From iris_ni.logrel Require Import types.
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
  Proof. by apply (iso_ofe_mixin (lrel_car : lrel Σ → (slevel -d> val -d> val -d> iPropO Σ))). Qed.
  Canonical Structure lrelC := OfeT (lrel Σ) lrel_ofe_mixin.

  Global Instance lrel_cofe : Cofe lrelC.
  Proof.
    apply (iso_cofe_subtype' (λ A : slevel -d> val -d> val -d> iPropO Σ, ∀ ξ w1 w2, Persistent (A ξ w1 w2)) (@LRel _) lrel_car)=>//.
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
  Context `{!heapDG Σ}.

  Implicit Types e : expr.
  Implicit Types E : coPset.
  Implicit Types A B : lrel Σ.

  Definition locsN := nroot.@"locsinv".

  Definition lrel_unit : lrel Σ := LRel (λ _ w1 w2, ⌜ w1 = #() ∧ w2 = #() ⌝%I).

  Definition lrel_int (l : slevel) : lrel Σ := LRel (λ ξ w1 w2,
      ∃ n1 n2 : Z, ⌜w1 = #n1⌝ ∧ ⌜w2 = #n2⌝ ∧ ⌜l ⊑ ξ → n1 = n2⌝)%I.

  Definition lrel_bool (l : slevel) : lrel Σ := LRel (λ ξ w1 w2,
      ∃ b1 b2 : bool, ⌜w1 = #b1⌝ ∧ ⌜w2 = #b2⌝ ∧ ⌜l ⊑ ξ → b1 = b2⌝)%I.

  Definition lrel_prod (A B : lrel Σ) : lrel Σ := LRel (λ ξ w1 w2,
      ∃ v1 v2 v1' v2', ⌜w1 = (v1,v1')%V⌝ ∧ ⌜w2 = (v2,v2')%V⌝ ∧
        A ξ v1 v2 ∗ B ξ v1' v2')%I.

  Definition lrel_option (A : lrel Σ) (l : slevel) : lrel Σ := LRel (λ ξ w1 w2,
      (⌜l ⊑ ξ⌝ → ((⌜w1 = NONEV⌝ ∗ ⌜w2 = NONEV⌝)
                  ∨ ∃ v1 v2, (⌜w1 = SOMEV v1⌝ ∗ ⌜w2 = SOMEV v2⌝ ∗ A ξ v1 v2)))
      ∧ (⌜¬ (l ⊑ ξ)⌝ → (⌜w1 = NONEV⌝ ∨ ∃ v1, ⌜w1 = SOMEV v1⌝ ∗ A ξ v1 v1)
                        ∗ (⌜w2 = NONEV⌝ ∨ ∃ v2, ⌜w2 = SOMEV v2⌝ ∗ A ξ v2 v2)))%I.

  Definition lrel_arr (A1 A2 : lrel Σ) (l : slevel) : lrel Σ := LRel (λ ξ w1 w2,
    □ ∀ v1 v2, A1 ξ v1 v2 -∗ DWP (w1 v1) & (w2 v2) : A2 ξ)%I.

  Definition lrel_ref (A : lrel Σ) : lrel Σ := LRel (λ ξ w1 w2,
    ∃ l1 l2: loc, ⌜w1 = #l1⌝ ∧ ⌜w2 = #l2⌝ ∧
      inv (locsN.@(l1,l2)) (∃ v1 v2, l1 ↦ₗ v1 ∗ l2 ↦ᵣ v2 ∗ A ξ v1 v2))%I.

  Equations interp (τ : type) : lrel Σ
    by wf (type_measure τ) :=
  interp tunit := lrel_unit;
  interp (tint l) := lrel_int l;
  interp (tbool l) := lrel_bool l;
  interp (tintoption il l) := lrel_option (lrel_int il) l;
  interp (tarrow s t l) :=
    lrel_arr (interp s) (interp (stamp t l)) l;
  interp (tprod τ1 τ2) := lrel_prod (interp τ1) (interp τ2);
  interp (tref τ) := lrel_ref (interp τ).
  Next Obligation. lia. Qed.
  Next Obligation. rewrite -stamp_measure. lia. Qed.
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.

  Lemma interp_eq τ :
    interp τ =
    match τ with
    | tunit => lrel_unit
    | tint l => lrel_int l
    | tbool l => lrel_bool l
    | tintoption il l => lrel_option (lrel_int il) l
    | tarrow s t l =>
      lrel_arr (interp s) (interp (stamp t l)) l
    | tprod τ1 τ2 => lrel_prod (interp τ1) (interp τ2)
    | tref τ => lrel_ref (interp τ)
    end.
  Proof. by funelim (interp τ). Qed.

  Lemma flat_type_interp τ ξ :
    (ξ ≠ High) →
    flat_type τ →
    ⊢ ∀ v1 v2 w1 w2, interp τ ξ v1 v2 -∗ interp τ ξ w1 w2 -∗ interp τ ξ v1 w2.
  Proof.
    intros ?. induction 1.
    - iIntros (v1 v2 w1 w2). rewrite interp_eq.
      iDestruct 1 as (k1 k1' ? ?) "H1".
      iDestruct 1 as (k2 k2' ? ?) "H2".
      simplify_eq/=.
      iExists _, _. repeat iSplit; eauto.
      iPureIntro. destruct ξ; compute; naive_solver.
    - iIntros (v1 v2 w1 w2). rewrite interp_eq.
      iDestruct 1 as (k1 k1' ? ?) "H1".
      iDestruct 1 as (k2 k2' ? ?) "H2".
      simplify_eq/=.
      iExists _, _. repeat iSplit; eauto.
      iPureIntro. destruct ξ; compute; naive_solver.
    - iIntros (v1 v2 w1 w2). rewrite interp_eq.
      iDestruct 1 as "[% %]".
      iDestruct 1 as "[% %]". simplify_eq/=.
      iSplit; eauto.
    - iIntros (v1 v2 p1 p2). rewrite interp_eq.
      iDestruct 1 as (w1 w1' u1 u1' ? ?) "[Hw1 Hu1]".
      iDestruct 1 as (w2 w2' u2 u2' ? ?) "[Hw2 Hu2]".
      simplify_eq/=.
      iExists _,_,_,_. repeat iSplit; eauto.
      + iApply (IHflat_type1 with "Hw1 Hw2").
      + iApply (IHflat_type2 with "Hu1 Hu2").
  Qed.

  Lemma flat_type_quasi_refl τ v1 v2 ξ :
    flat_type τ →
    (interp τ ξ v1 v2 ⊢ interp τ ξ v1 v1 ∗ interp τ ξ v2 v2)%I.
  Proof.
    intros Hft. revert v1 v2. induction Hft=>v1 v2.
    - rewrite interp_eq.
      iDestruct 1 as (a1 a2 -> ->) "Ha".
      iSplit; iExists _,_; repeat iSplit; eauto.
    - rewrite interp_eq.
      iDestruct 1 as (a1 a2 -> ->) "Ha".
      iSplit; iExists _,_; repeat iSplit; eauto.
    - rewrite interp_eq.
      iDestruct 1 as "[-> ->]".
      iSplit; repeat iSplit; eauto.
    - rewrite interp_eq.
      iDestruct 1 as (a1 a2 b1 b2 -> ->) "[Ha Hb]".
      rewrite IHHft1 IHHft2.
      iDestruct "Ha" as "[Ha1 Ha2]".
      iDestruct "Hb" as "[Hb1 Hb2]".
      iSplitL "Ha1 Hb1"; iExists _,_,_,_; eauto with iFrame.
  Qed.

  Local Hint Constructors flat_type.

  Lemma interp_label_mono τ l1 l2 ξ v1 v2 :
    l1 ⊑ l2 →
    interp (stamp τ l1) ξ v1 v2 -∗ interp (stamp τ l2) ξ v1 v2.
  Proof.
    revert v1 v2 l1 l2. induction τ=>v1 v2 l1 l2 Hlab; rewrite !interp_eq /=.
    - reflexivity.
    - iDestruct 1 as (i1 i2 -> ->) "H". iDestruct "H" as %HH.
      iExists i1,i2.
      repeat iSplit; eauto with iFrame. iPureIntro.
      intros ?. apply HH. transitivity (l ⊔ l2); eauto.
      by apply join_mono_r.
    - iDestruct 1 as (i1 i2 -> ->) "H". iDestruct "H" as %HH.
      iExists i1,i2.
      repeat iSplit; eauto with iFrame. iPureIntro.
      intros ?. apply HH. transitivity (l ⊔ l2); auto.
      by apply join_mono_r.
    - iIntros "#H". iAlways. iIntros (w1 w2) "Hw".
      iSpecialize ("H" with "Hw").
      iApply (dwp_wand with "H").
      iIntros (x1 x2) "H". iApply (IHτ2 with "H").
      by apply join_mono_r.
    - iDestruct 1 as (x1 x2 y1 y2 -> ->) "[H1 H2]".
      iExists _,_,_,_.
      repeat iSplit; eauto with iFrame.
      + iApply IHτ1; eauto.
      + iApply IHτ2; eauto.
    - iIntros "H". iSplit.
      + iIntros (Hl2).
        iDestruct "H" as "[H _]".
        rewrite Hlab.
        iApply ("H" $! Hl2).
      + iIntros (Hl2).
        destruct (decide ((l ⊔ l1 ⊑ ξ))) as [Hl1|Hl1].
        * iDestruct "H" as "[H _]". iSpecialize ("H" $! Hl1).
          iDestruct "H" as "[[-> ->]|H]"; first by eauto.
          iDestruct "H" as (w1 w2 -> ->) "HI".
          iSplit; iRight; eauto.
          ** iExists _. iSplit; eauto.
             iDestruct "HI" as (a1 ? -> ->) "_".
             iExists a1, a1; eauto with iFrame.
          ** iExists _. iSplit; eauto.
             iDestruct "HI" as (? a2 -> ->) "_".
             iExists a2, a2; eauto with iFrame.
        * iDestruct "H" as "[_ H]". iApply ("H" $! Hl1).
    - reflexivity.
  Qed.

  Lemma interp_sub_mono_general (τ1 τ2 : type) l1 l2 ξ v1 v2 :
    τ1 <: τ2 →
    l1 ⊑ l2 →
    interp (stamp τ1 l1) ξ v1 v2 -∗ interp (stamp τ2 l2) ξ v1 v2.
  Proof.
    intros Hsub. revert l1 l2 v1 v2. induction Hsub=>l1' l2' v1 v2 Hlab.
    - (* Reflexivity *) by apply interp_label_mono.
    - (* Transitivity *) rewrite -IHHsub2; eauto.
    - (* Int *)
      replace (stamp (tint l1) l1') with (stamp (tint Low) (l1 ⊔ l1'))
        by (simpl; by rewrite left_id).
      replace (stamp (tint l2) l2') with (stamp (tint Low) (l2 ⊔ l2'))
        by (simpl; by rewrite left_id).
      apply interp_label_mono.
      etrans; [ by apply join_mono_l | by apply join_mono_r ].
    - (* Bool *)
      replace (stamp (tbool l1) l1') with (stamp (tbool Low) (l1 ⊔ l1'))
        by (simpl; by rewrite left_id).
      replace (stamp (tbool l2) l2') with (stamp (tbool Low) (l2 ⊔ l2'))
        by (simpl; by rewrite left_id).
      apply interp_label_mono.
      etrans; [ by apply join_mono_l | by apply join_mono_r ].
    - (* Option *)
      simpl.
      change (tintoption il (l1 ⊔ l1')) with
                  (stamp (tintoption il l1) l1').
      replace (tintoption il (l2 ⊔ l2')) with
                  (stamp (tintoption il l1) (l2 ⊔ l2')); last first.
      { simpl. f_equal.
        rewrite assoc (leq_join_max_2 l1 l2) //. }
      apply interp_label_mono.
      transitivity l2'; eauto using join_leq_r.
    - (* Arrow *)
      rewrite !interp_eq /=. iIntros "#IH". iAlways.
      iIntros (w1 w2) "Hw".
      replace ((interp τ'₁) ξ w1 w2) with ((interp (stamp τ'₁ Low)) ξ w1 w2)
        by by rewrite stamp_low.
      rewrite (IHHsub1 Low Low); eauto.
      rewrite stamp_low.
      iSpecialize ("IH" with "Hw").
      iApply (dwp_wand with "IH"). iIntros (x1 x2).
      iIntros "H". iApply (IHHsub2 with "H").
      etrans; [ by apply join_mono_l | by apply join_mono_r ].
    - (* Product *)
      rewrite !interp_eq /=.
      iDestruct 1 as (x1 x2 y1 y2 -> ->) "[Hv Hw]".
      rewrite IHHsub1; eauto.
      rewrite IHHsub2; eauto.
      iExists _,_,_,_. repeat iSplit; eauto.
  Qed.

  Lemma interp_sub_mono τ1 τ2 ξ v1 v2 :
    τ1 <: τ2 →
    interp τ1 ξ v1 v2 -∗ interp τ2 ξ v1 v2.
  Proof.
    intros Hsub. rewrite -(stamp_low τ1) -(stamp_low τ2).
    by apply interp_sub_mono_general; eauto.
  Qed.
End semtypes.

Notation "⟦ τ ⟧" := (interp τ).

Section rules.
  Context `{!heapDG Σ}.
  Implicit Types τ σ : type.
  Implicit Types A B : val → val → iProp Σ.
  Implicit Types ξ : slevel.
  Implicit Types e t s : expr.
  Implicit Types v w : val.

  Local Hint Constructors flat_type.
  Local Hint Constructors type_sub.

  Lemma logrel_sub ξ e1 e2 τ τ' :
    τ <: τ' →
    (DWP e1 & e2 : ⟦ τ ⟧ ξ) -∗
    DWP e1 & e2 : ⟦ τ' ⟧ ξ.
  Proof.
    iIntros (Hsub) "He".
    iApply (dwp_wand with "He").
    iIntros (??). by iApply interp_sub_mono.
  Qed.

  Lemma logrel_int ξ (i : Z) l :
    ⊢ DWP #i & #i : ⟦ tint l ⟧ ξ.
  Proof.
    iApply dwp_value. iModIntro.
    iExists i, i. iPureIntro. naive_solver.
  Qed.

  Lemma logrel_int_high ξ (i1 i2 : Z) l :
    ¬ (l ⊑ ξ) →
    ⊢ DWP (of_val #i1) & (of_val #i2) : ⟦ tint l ⟧ ξ.
  Proof.
    iIntros (?). iApply dwp_value. iModIntro.
    iExists i1, i2. iPureIntro. naive_solver.
  Qed.

  Lemma logrel_unit ξ :
    ⊢ DWP (of_val #()) & (of_val #()) : ⟦ tunit ⟧ ξ.
  Proof.
    iApply dwp_value. iModIntro.
    iPureIntro. eauto.
  Qed.

  Lemma logrel_bool ξ (b : bool) l :
    ⊢ DWP #b & #b : ⟦ tbool l ⟧ ξ.
  Proof.
    iApply dwp_value. iModIntro.
    iExists b, b. iPureIntro. naive_solver.
  Qed.

  Lemma logrel_bool_high ξ (b1 b2 : bool) l :
    ¬ (l ⊑ ξ) →
    ⊢ DWP (of_val #b1) & (of_val #b2) : ⟦ tbool l ⟧ ξ.
  Proof.
    iIntros (?). iApply dwp_value. iModIntro.
    iExists b1, b2. iPureIntro. naive_solver.
  Qed.

  Lemma logrel_binop_int e1 e2 t1 t2 l1 l2 ξ op :
    bin_op_int op →
    (DWP e1 & e2 : ⟦ tint l1 ⟧ ξ) -∗
    (DWP t1 & t2 : ⟦ tint l2 ⟧ ξ) -∗
    DWP BinOp op e1 t1 & BinOp op e2 t2 : ⟦ tint (l1 ⊔ l2) ⟧ ξ.
  Proof.
    iIntros (Hop) "He Ht".
    dwp_bind t1 t2. iApply (dwp_wand with "Ht").
    iIntros (w1 w2) "Hw".

    dwp_bind e1 e2. iApply (dwp_wand with "He").
    iIntros (v1 v2) "Hv".

    iDestruct "Hw" as (m1 m2 -> ->) "%".
    iDestruct "Hv" as (n1 n2 -> ->) "%".
    destruct (bin_op_int_safe n1 m1 _ Hop) as [z1 Hz1].
    destruct (bin_op_int_safe n2 m2 _ Hop) as [z2 Hz2].
    dwp_pures.
    iApply dwp_value. iModIntro.
    iExists _,_. iPureIntro. repeat split; eauto.
    intros ?%join_leq. naive_solver.
  Qed.

  Lemma logrel_binop_bool e1 e2 t1 t2 l1 l2 ξ op :
    bin_op_bool op →
    (DWP e1 & e2 : ⟦ tbool l1 ⟧ ξ) -∗
    (DWP t1 & t2 : ⟦ tbool l2 ⟧ ξ) -∗
    DWP BinOp op e1 t1 & BinOp op e2 t2 : ⟦ tbool (l1 ⊔ l2) ⟧ ξ.
  Proof.
    iIntros (Hop) "He Ht".
    dwp_bind t1 t2. iApply (dwp_wand with "Ht").
    iIntros (w1 w2) "Hw".

    dwp_bind e1 e2. iApply (dwp_wand with "He").
    iIntros (v1 v2) "Hv".

    iDestruct "Hw" as (m1 m2 -> ->) "%".
    iDestruct "Hv" as (n1 n2 -> ->) "%".
    destruct (bin_op_bool_safe n1 m1 _ Hop) as [z1 Hz1].
    destruct (bin_op_bool_safe n2 m2 _ Hop) as [z2 Hz2].
    dwp_pures.
    iApply dwp_value. iModIntro.
    iExists _,_. iPureIntro. repeat split; eauto.
    intros ?%join_leq. naive_solver.
  Qed.

  Lemma logrel_binop_int_bool e1 e2 t1 t2 l1 l2 ξ op :
    bin_op_int_bool op →
    (DWP e1 & e2 : ⟦ tint l1 ⟧ ξ) -∗
    (DWP t1 & t2 : ⟦ tint l2 ⟧ ξ) -∗
    DWP BinOp op e1 t1 & BinOp op e2 t2 : ⟦ tbool (l1 ⊔ l2) ⟧ ξ.
  Proof.
    iIntros (Hop) "He Ht".
    dwp_bind t1 t2. iApply (dwp_wand with "Ht").
    iIntros (w1 w2) "Hw".

    dwp_bind e1 e2. iApply (dwp_wand with "He").
    iIntros (v1 v2) "Hv".

    iDestruct "Hw" as (m1 m2 -> ->) "%".
    iDestruct "Hv" as (n1 n2 -> ->) "%".
    destruct (bin_op_int_bool_safe n1 m1 _ Hop) as [b1 Hb1].
    destruct (bin_op_int_bool_safe n2 m2 _ Hop) as [b2 Hb2].
    dwp_pures.
    iApply dwp_value. iModIntro.
    iExists _,_. iPureIntro. repeat split; eauto.
    intros ?%join_leq. naive_solver.
  Qed.

  Lemma logrel_prod ξ e1 e2 t1 t2 τ τ' :
    (DWP e1 & e2 : ⟦ τ ⟧ ξ) -∗
    (DWP t1 & t2 : ⟦ τ' ⟧ ξ) -∗
    DWP (e1, t1) & (e2, t2) : ⟦ τ * τ' ⟧ ξ.
  Proof.
    iIntros "He Ht".
    dwp_bind t1 t2.
    iApply (dwp_wand with "Ht").
    iIntros (v1 v2) "#Hv".
    dwp_bind e1 e2.
    iApply (dwp_wand with "He").
    iIntros (w1 w2) "#Hw".
    dwp_pures.
    iApply dwp_value.
    iModIntro. rewrite (interp_eq (tprod _ _)).
    iExists _,_,_,_. repeat iSplit; eauto.
  Qed.

  Lemma logrel_fst ξ e1 e2 τ τ' :
    (DWP e1 & e2 : ⟦ τ * τ' ⟧ ξ) -∗
    DWP Fst e1 & Fst e2 : ⟦ τ ⟧ ξ.
  Proof.
    iIntros "He". dwp_bind e1 e2.
    iApply (dwp_wand with "He").
    iIntros (z1 z2). rewrite interp_eq.
    iDestruct 1 as (v1 v2 w1 w2 -> ->) "[#Hv #Hw]".
    dwp_pures. by iApply dwp_value.
  Qed.

  Lemma logrel_snd ξ e1 e2 τ τ' :
    (DWP e1 & e2 : ⟦ τ * τ' ⟧ ξ) -∗
    DWP Snd e1 & Snd e2 : ⟦ τ' ⟧ ξ.
  Proof.
    iIntros "He". dwp_bind e1 e2.
    iApply (dwp_wand with "He").
    iIntros (z1 z2). rewrite interp_eq.
    iDestruct 1 as (v1 v2 w1 w2 -> ->) "[#Hv #Hw]".
    dwp_pures. by iApply dwp_value.
  Qed.

  Lemma logrel_if ξ A e1 e2 t1 t2 u1 u2 l :
    (DWP e1 & e2 : ⟦ tbool l ⟧ ξ) -∗
    ((DWP t1 & t2 : A)
     ∧ (DWP u1 & u2 : A)
     ∧ (⌜¬ l ⊑ ξ⌝ → DWP u1 & t2 : A)
     ∧ (⌜¬ l ⊑ ξ⌝ → DWP t1 & u2 : A)) -∗
    DWP (if: e1 then t1 else u1) & (if: e2 then t2 else u2) : A.
  Proof.
    iIntros "He Htu".
    dwp_bind e1 e2.
    iApply (dwp_wand with "He"). iIntros (v1 v2 Hv).
    destruct Hv as (b1 & b2 & -> & -> & Hb1b2).
    destruct (decide (l ⊑ ξ)) as [Hlvl | Hlvl]; try specialize (Hb1b2 Hlvl); simplify_eq/=.
    - destruct b2; dwp_pures.
      + by iDestruct "Htu" as "[$ _]".
      + by iDestruct "Htu" as "[_ [$ _]]".
    - destruct b1, b2; dwp_pures.
      + by iDestruct "Htu" as "[$ _]".
      + iDestruct "Htu" as "[_ [_ [_ Htu]]]". by iApply "Htu".
      + iDestruct "Htu" as "[_ [_ [Htu _]]]". by iApply "Htu".
      + by iDestruct "Htu" as "[_ [$ _]]".
  Qed.

  Lemma subst_prime_val (v w : val) (b : binder) :
    subst' b v w = w.
  Proof. by destruct b. Qed.

  Lemma logrel_if_flat ξ τ e1 e2 (t1 t2 u1 u2 : val):
    (ξ ≠ High) →
    flat_type τ →
    (DWP e1 & e2 : ⟦ tbool High ⟧ ξ) -∗
    (DWP t1 & t2 : ⟦ τ ⟧ ξ) -∗
    (DWP u1 & u2 : ⟦ τ ⟧ ξ) -∗
    DWP (if: e1 then t1 else u1) & (if: e2 then t2 else u2) : ⟦ τ ⟧ ξ.
  Proof.
    iIntros (??) "He Ht Hu".
    iApply (logrel_if with "He").
    repeat iSplit; eauto.
    - iIntros (?).
      rewrite !dwp_value_inv'.
      iApply dwp_value.
      iMod "Ht" as "Ht". iMod "Hu" as "Hu". iModIntro.
      iApply (flat_type_interp with "Hu Ht"); eauto.
    - iIntros (?). rewrite !dwp_value_inv'.
      iApply dwp_value.
      iMod "Ht" as "Ht". iMod "Hu" as "Hu". iModIntro.
      iApply (flat_type_interp with "Ht Hu"); eauto.
  Qed.

  Lemma logrel_if_low ξ A e1 e2 t1 t2 u1 u2 l :
    l ⊑ ξ →
    (DWP e1 & e2 : ⟦ tbool l ⟧ ξ) -∗
    (DWP t1 & t2 : A) -∗
    (DWP u1 & u2 : A) -∗
    DWP (if: e1 then t1 else u1) & (if: e2 then t2 else u2) : A.
  Proof.
    iIntros (Hl) "He Ht Hu".
    iApply (logrel_if with  "He [Ht Hu]").
    repeat iSplit; try done.
    - iIntros (?). by exfalso.
    - iIntros (?). by exfalso.
  Qed.

  Lemma logrel_none il l ξ :
    ⊢ DWP NONEV & NONEV : ⟦ tintoption il l ⟧ ξ.
  Proof.
    iApply dwp_value; eauto. iModIntro.
    iSplit; eauto.
  Qed.

  Lemma logrel_some v1 v2 il l ξ :
    (DWP v1 & v2 : ⟦ tint il ⟧ ξ) -∗
    DWP SOMEV v1 & SOMEV v2 : ⟦ tintoption il l ⟧ ξ.
  Proof.
    iIntros "Hv". rewrite dwp_value_inv'.
    iApply dwp_value. iMod "Hv" as "Hv". iModIntro.
    rewrite (interp_eq (tintoption _ _)).
    iSplit; iIntros (Hl).
    - iRight; iExists v1,v2. repeat iSplit; eauto.
    - iSplit; iRight; iExists _; iSplit; eauto; rewrite interp_eq.
      + iDestruct "Hv" as (a1 ? -> ->) "_".
        iExists a1,a1; eauto.
      + iDestruct "Hv" as (? a2 -> ->) "_".
        iExists a2,a2; eauto.
  Qed.

  Lemma logrel_match e1 e2 x1 x2 t1 t2 s1 s2 il A E ξ :
    (* the premises can also be joined by ∧ *)
    (DWP e1 & e2 @ E : ⟦ tintoption il Low ⟧ ξ) -∗
    (DWP t1 & t2 @ E : A) -∗
    (∀ v1 v2, ⟦ tint il ⟧ ξ v1 v2 -∗
              DWP subst' x1 v1 s1 & subst' x2 v2 s2 @ E : A) -∗
    DWP match: e1 with
          NONE => t1
        | SOME x1 => s1
        end
      & match: e2 with
          NONE => t2
        | SOME x2 => s2
        end
      @ E : A.
  Proof.
    iIntros "He Ht Hs".
    dwp_bind e1 e2.
    iApply (dwp_wand with "He"). iIntros (v1 v2) "Hv".
    rewrite (interp_eq (tintoption _ _)).
    iDestruct "Hv" as "[Hv _]". iSpecialize ("Hv" with "[]").
    { by destruct ξ. }
    iDestruct "Hv" as "[[-> ->]|H]".
    - dwp_pures. iApply "Ht".
    - iDestruct "H" as (v1' v2' -> ->) "H". dwp_pures.
      iApply "Hs". iApply "H".
  Qed.

  (* TODO: move somewhere else *)
  Instance singleton_binder : Singleton binder (gset string) :=
    λ x, match x with
         | BAnon => ∅
         | BNamed s => {[s]}
         end.
  Lemma elem_of_singleton_binder (s : string) (x : binder) :
    s ∈ ({[x]} : gset string) → x = BNamed s.
  Proof. destruct x; rewrite ?elem_of_singleton; set_solver. Qed.
  Lemma almost_val_subst (x : binder) (v : val) (e : expr) :
    almost_val {[x]} e →
    ∃ (w : val), subst' x v e = w.
  Proof.
    inversion 1; simplify_eq/=.
    - exists v0. destruct x; eauto.
    - apply elem_of_singleton_binder in H0.
      rewrite H0. exists v. simpl. rewrite decide_left. done.
  Qed.

  Lemma logrel_match_flat ξ il τ (x1 x2 : binder)
        e1 e2 (v1 v2 : val) u1 u2 :
    (ξ ≠ High) →
    flat_type τ →
    almost_val {[x1]} u1 →
    almost_val {[x2]} u2 →
    (DWP e1 & e2 : ⟦ tintoption il High ⟧ ξ) -∗
    (DWP v1 & v2 : ⟦ τ ⟧ ξ) -∗
    (∀ i1 i2, ⟦ tint High ⟧ ξ i1 i2 -∗
       DWP subst' x1 i1 u1 & subst' x2 i2 u2 : ⟦ τ ⟧ ξ) -∗
    DWP match: e1 with
          NONE => v1
        | SOME x1 => u1
        end
      & match: e2 with
          NONE => v2
        | SOME x2 => u2
        end
      : ⟦ τ ⟧ ξ.
  Proof.
    iIntros (?? Hu1 Hu2) "He Ht Hu".
    dwp_bind e1 e2. iApply (dwp_wand with "He").
    iIntros (o1 o2) "Ho".
    iDestruct "Ho" as "[_ Ho]".
    iDestruct ("Ho" with "[]") as "[Ho1 Ho2]".
    { destruct ξ; eauto. }
    iDestruct "Ho1" as "[->|Ho1]";
      try (iDestruct "Ho1" as (w1 ->) "Hw1");
      iDestruct "Ho2" as "[->|Ho2]";
      try (iDestruct "Ho2" as (w2 ->) "Hw2");
      dwp_pures; eauto with iFrame.
    - rewrite (interp_sub_mono (tint il) (tint High)); eauto.
      iSpecialize ("Hu" with "Hw2").
      destruct (almost_val_subst _ w2 _ Hu1) as [uu1 ->].
      destruct (almost_val_subst _ w2 _ Hu2) as [uu2 ->].
      rewrite !dwp_value_inv'. iApply dwp_value.
      iMod "Ht" as "Ht"; iMod "Hu" as "Hu"; iModIntro.
      iApply (flat_type_interp with "Ht Hu"); eauto.
    - rewrite (interp_sub_mono (tint il) (tint High)); last by constructor.
      iSpecialize ("Hu" with "Hw1").
      destruct (almost_val_subst _ w1 _ Hu1) as [uu1 ->].
      destruct (almost_val_subst _ w1 _ Hu2) as [uu2 ->].
      rewrite !dwp_value_inv'. iApply dwp_value.
      iMod "Ht" as "Ht"; iMod "Hu" as "Hu"; iModIntro.
      iApply (flat_type_interp with "Hu Ht"); eauto.
    - rewrite !(interp_sub_mono (tint il) (tint High)); eauto.
      iApply ("Hu" $! w1 w2 with "[Hw1 Hw2]").
      iApply (flat_type_interp with "Hw1 Hw2"); eauto.
  Qed.


  Lemma logrel_rec ξ f x e1 e2 τ1 τ2 l :
    □ (∀ f1 f2 v1 v2, ⟦ tarrow τ1 τ2 l ⟧ ξ f1 f2 -∗
         ⟦ τ1 ⟧ ξ v1 v2 -∗
         DWP subst' x v1 (subst' f f1 e1)
           & subst' x v2 (subst' f f2 e2) : ⟦ stamp τ2 l ⟧ ξ) -∗
    DWP (rec: f x := e1)%V & (rec: f x := e2)%V : ⟦ tarrow τ1 τ2 l ⟧ ξ.
  Proof.
    iIntros "#H".
    iApply dwp_value. iModIntro. iLöb as "IH".
    rewrite {3}(interp_eq (tarrow _ _ _)).
    iModIntro. iIntros (v1 v2) "Hτ1". dwp_pures. simpl.
    by iApply "H".
  Qed.

  Lemma logrel_lam ξ x e1 e2 τ1 τ2 l :
    □ (∀ v1 v2, ⟦ τ1 ⟧ ξ v1 v2 -∗
         DWP subst' x v1 e1 & subst' x v2 e2 : ⟦ stamp τ2 l ⟧ ξ) -∗
    DWP (λ: x, e1)%V & (λ: x, e2)%V : ⟦ tarrow τ1 τ2 l ⟧ ξ.
  Proof.
    iIntros "#H". iApply logrel_rec. iModIntro.
    iIntros (? ? v1 v2) "_ Hτ". by iApply "H".
  Qed.

  Lemma logrel_app ξ e1 e2 e1' e2' τ1 τ2 l :
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

  Lemma logrel_seq ξ e1 e2 e1' e2' A τ2 :
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

  Lemma logrel_fork ξ e1 e2 :
    (DWP e1 & e2 : ⟦ tunit ⟧ ξ) -∗
    (DWP Fork e1 & Fork e2 : ⟦ tunit ⟧ ξ).
  Proof.
    iIntros "H". iApply (dwp_fork with "[H]").
    - iNext. iApply (dwp_wand with "H"); auto.
    - iNext. eauto.
  Qed.

  Lemma interp_ref_alloc ξ (l1 l2 : loc) v1 v2 τ E :
    l1 ↦ₗ v1 -∗
    l2 ↦ᵣ v2 -∗
    ⟦ τ ⟧ ξ v1 v2 ={E}=∗
    ⟦ tref τ ⟧ ξ #l1 #l2.
  Proof.
    iIntros "Hl1 Hl2 Hv".
    iMod (inv_alloc (locsN.@(l1,l2)) _
         (∃ v1 v2, l1 ↦ₗ v1 ∗ l2 ↦ᵣ v2 ∗ ⟦ τ ⟧ ξ v1 v2)%I with "[-]")
      as "#Hinv".
    { iNext. iExists _,_. eauto with iFrame. }
    iModIntro. rewrite (interp_eq (tref τ)).
    iExists _,_. repeat iSplit; eauto.
  Qed.

  Lemma logrel_alloc ξ e1 e2 τ :
    (DWP e1 & e2 : ⟦ τ ⟧ ξ) -∗
    DWP (ref e1) & (ref e2) : ⟦ tref τ ⟧ ξ.
  Proof.
    iIntros "He".
    dwp_bind e1 e2.
    iApply (dwp_wand with "He").
    iIntros (v1 v2) "#Hv".
    pose (Φ1 := (λ v, ∃ (l : loc), ⌜v = #l⌝ ∗ l ↦ₗ v1)%I).
    pose (Φ2 := (λ v, ∃ (l : loc), ⌜v = #l⌝ ∗ l ↦ᵣ v2)%I).
    iApply dwp_fupd.
    iApply (dwp_atomic_lift_wp Φ1 Φ2%I); try done.
    repeat iSplitR.
    - rewrite /TWP1 /Φ1. wp_alloc l1 as "Hl". eauto with iFrame.
    - rewrite /TWP2 /Φ2. wp_alloc l1 as "Hl". eauto with iFrame.
    - iIntros (? ?). iDestruct 1 as (l1 ->) "Hl1".
      iDestruct 1 as (l2 ->) "Hl2".
      iNext. iMod (interp_ref_alloc with "Hl1 Hl2 Hv") as "$". done.
  Qed.

  Lemma logrel_deref ξ e1 e2 τ :
    (DWP e1 & e2 : ⟦ tref τ ⟧ ξ) -∗
    DWP !e1 & !e2 : ⟦ τ ⟧ ξ.
  Proof.
    iIntros "He".
    dwp_bind e1 e2.
    iApply (dwp_wand with "He").
    iIntros (v1 v2). rewrite interp_eq /lrel_car /=.
    iDestruct 1 as (l1 l2 -> ->) "#Hll".

    pose (Φ1 := (λ v, l1 ↦ₗ{1/2} v)%I).
    pose (Φ2 := (λ v, l2 ↦ᵣ{1/2} v)%I).

    iApply dwp_atomic.
    iInv (locsN.@(l1,l2)) as (v1 v2) "(>Hl1 & >Hl2 & #Hv)" "Hcl".
    iDestruct "Hl1" as "[Hl1 Hl1']".
    iDestruct "Hl2" as "[Hl2 Hl2']".
    iApply (dwp_atomic_lift_wp Φ1 Φ2 with "[Hl1] [Hl2] [Hl1' Hl2' Hcl]").
    - rewrite /TWP1. wp_load. done.
    - rewrite /TWP2. wp_load. done.
    - iIntros (w1 w2) "Hl1 Hl2".
      rewrite /Φ1 /Φ2.
      iDestruct (gen_heap.mapsto_agree with "Hl1 Hl1'") as %?.
      simplify_eq/=.
      iCombine "Hl1 Hl1'" as "Hl1".
      iDestruct (gen_heap.mapsto_agree with "Hl2 Hl2'") as %?.
      simplify_eq/=.
      iCombine "Hl2 Hl2'" as "Hl2".
      iNext. iMod ("Hcl" with "[-]") as "_".
      { iNext. iExists _,_. by iFrame. }
      iModIntro. simpl. iApply "Hv".
  Qed.

  Lemma logrel_store ξ e1 e2 t1 t2 τ E :
    ↑locsN ⊆ E →
    (DWP e1 & e2 @ E : ⟦ tref τ ⟧ ξ) -∗
    (DWP t1 & t2 @ E : ⟦ τ ⟧ ξ) -∗
    DWP (e1 <- t1) & (e2 <- t2) @ E : ⟦ tunit ⟧ ξ.
  Proof.
    iIntros (?) "He Ht".
    dwp_bind t1 t2. iApply (dwp_wand with "Ht").
    iIntros (w1 w2) "Hw".
    dwp_bind e1 e2. iApply (dwp_wand with "He").
    iIntros (? ?). rewrite (interp_eq (tref _)).
    iDestruct 1 as (r1 r2 -> ->) "Hr".

    pose (Φ1 := (λ v, ⌜v = #()⌝ ∧ r1 ↦ₗ w1)%I).
    pose (Φ2 := (λ v, ⌜v = #()⌝ ∧ r2 ↦ᵣ w2)%I).

    iApply dwp_atomic.
    iInv (locsN.@(r1,r2)) as (v1 v2) "(>Hr1 & >Hr2 & #Hv)" "Hcl".
    iApply (dwp_atomic_lift_wp Φ1 Φ2 with "[Hr1] [Hr2] [-]").
    - rewrite /TWP1 /Φ1. wp_store. eauto.
    - rewrite /TWP2 /Φ2. wp_store. eauto.
    - iIntros (? ?) "[-> Hr1] [-> Hr2]".
      iNext. iMod ("Hcl" with "[-]") as "_".
      { iNext. iExists _,_. by iFrame. }
      iModIntro. eauto.
  Qed.

  Lemma logrel_faa e1 e2 t1 t2 α E ξ :
    ↑locsN ⊆ E →
    (DWP e1 & e2 @ E : ⟦ tref (tint α) ⟧ ξ) -∗
    (DWP t1 & t2 @ E : ⟦ tint α ⟧ ξ) -∗
    DWP FAA e1 t1 & FAA e2 t2 @ E : ⟦ tint α ⟧ ξ.
  Proof.
    iIntros (?) "He Ht".
    dwp_bind t1 t2. iApply (dwp_wand with "Ht").
    iIntros (v1 v2) "Hv".
    dwp_bind e1 e2. iApply (dwp_wand with "He").
    iIntros (? ?). rewrite (interp_eq (tref _)).
    iDestruct 1 as (r1 r2 -> ->) "Hr".
    iInv (locsN.@(r1, r2)) as (w1 w2) "(>Hr1 & >Hr2 & >Hw)".
    iDestruct "Hw" as (n1 n2 -> ->) "%".
    iDestruct "Hv" as (m1 m2 -> ->) "%".
    pose (Φ1 := (λ v, ⌜v = #n1⌝ ∧ r1 ↦ₗ #(n1+m1))%I).
    pose (Φ2 := (λ v, ⌜v = #n2⌝ ∧ r2 ↦ᵣ #(n2+m2))%I).
    iApply (dwp_atomic_lift_wp Φ1 Φ2 with "[Hr1] [Hr2] [-]").
    - rewrite /TWP1 /Φ1. wp_faa. eauto.
    - rewrite /TWP2 /Φ2. wp_faa. eauto.
    - iIntros (? ?) "[-> Hr1] [-> Hr2]".
      iNext. iModIntro. iSplitL.
      + iNext. iExists _,_. iFrame "Hr1 Hr2".
        iExists _,_. repeat iSplit; eauto. iPureIntro.
        naive_solver.
      + iExists _,_. repeat iSplit; eauto.
  Qed.

End rules.
