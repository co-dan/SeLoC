From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
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
  Proof. by apply (iso_ofe_mixin (lrel_car : lrel Σ → (slevel -d> val -d> val -d> iProp Σ))). Qed.
  Canonical Structure lrelC := OfeT (lrel Σ) lrel_ofe_mixin.

  Global Instance lrel_cofe : Cofe lrelC.
  Proof.
    apply (iso_cofe_subtype' (λ A : slevel -d> val -d> val -d> iProp Σ, ∀ ξ w1 w2, Persistent (A ξ w1 w2)) (@LRel _) lrel_car)=>//.
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

  (* TODO: use the level `l`?
     DF: we use it in the actual interpretation of arrows *)
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
  interp (tarrow s t l) :=
    lrel_arr (interp s) (interp (stamp t l)) l;
  (* TODO: is this stamp needed here? *)
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
    | tarrow s t l =>
      lrel_arr (interp s) (interp (stamp t l)) l
    | tprod τ1 τ2 => lrel_prod (interp τ1) (interp τ2)
    | tref τ => lrel_ref (interp τ)
    end.
  Proof. by funelim (interp τ). Qed.

  Lemma interp_label_mono τ l1 l2 ξ v1 v2 :
    l1 ⊑ l2 →
    interp (stamp τ l1) ξ v1 v2 -∗ interp (stamp τ l2) ξ v1 v2.
  Proof.
    revert v1 v2 l1 l2. induction τ=>v1 v2 l1 l2 Hlab; rewrite !interp_eq /=.
    - reflexivity.
    - iDestruct 1 as (i1 i2 -> ->) "H". iDestruct "H" as %HH.
      iExists i1,i2.
      repeat iSplit; eauto with iFrame. iPureIntro.
      intros ?. apply HH. transitivity (l ⊔ l2); auto.
    - iDestruct 1 as (i1 i2 -> ->) "H". iDestruct "H" as %HH.
      iExists i1,i2.
      repeat iSplit; eauto with iFrame. iPureIntro.
      intros ?. apply HH. transitivity (l ⊔ l2); auto.
    - iIntros "#H". iAlways. iIntros (w1 w2) "Hw".
      iSpecialize ("H" with "Hw").
      iApply (dwp_wand with "H").
      iIntros (x1 x2) "H". iApply (IHτ2 with "H").
      eauto.
    - iDestruct 1 as (x1 x2 y1 y2 -> ->) "[H1 H2]".
      iExists _,_,_,_.
      repeat iSplit; eauto with iFrame.
      + iApply IHτ1; eauto.
      + iApply IHτ2; eauto.
    - reflexivity.
  Qed.

  Lemma interp_sub_mono_general τ1 τ2 l1 l2 ξ v1 v2 :
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
    DWP #i & #i : ⟦ tint l ⟧ ξ.
  Proof.
    iApply dwp_value. iModIntro.
    iExists i, i. iPureIntro. naive_solver.
  Qed.

  Lemma logrel_int_high ξ (i1 i2 : Z) l :
    ¬ (l ⊑ ξ) →
    DWP (of_val #i1) & (of_val #i2) : ⟦ tint l ⟧ ξ.
  Proof.
    iIntros (?). iApply dwp_value. iModIntro.
    iExists i1, i2. iPureIntro. naive_solver.
  Qed.

  Lemma logrel_unit ξ :
    DWP (of_val #()) & (of_val #()) : ⟦ tunit ⟧ ξ.
  Proof.
    iApply dwp_value. iModIntro.
    iPureIntro. eauto.
  Qed.

  Lemma logrel_bool ξ (b : bool) l :
    DWP #b & #b : ⟦ tbool l ⟧ ξ.
  Proof.
    iApply dwp_value. iModIntro.
    iExists b, b. iPureIntro. naive_solver.
  Qed.

  Lemma logrel_bool_high ξ (b1 b2 : bool) l :
    ¬ (l ⊑ ξ) →
    DWP (of_val #b1) & (of_val #b2) : ⟦ tbool l ⟧ ξ.
  Proof.
    iIntros (?). iApply dwp_value. iModIntro.
    iExists b1, b2. iPureIntro. naive_solver.
  Qed.

  Lemma logrel_binop e1 e2 t1 t2 l1 l2 ξ :
    (DWP e1 & e2 : ⟦ tint l1 ⟧ ξ) -∗
    (DWP t1 & t2 : ⟦ tint l2 ⟧ ξ) -∗
    DWP e1 + t1 & e2 + t2 : ⟦ tint (l1 ⊔ l2) ⟧ ξ.
  Proof.
    iIntros "He Ht".
    dwp_bind t1 t2. iApply (dwp_wand with "Ht").
    iIntros (w1 w2) "Hw".

    dwp_bind e1 e2. iApply (dwp_wand with "He").
    iIntros (v1 v2) "Hv".

    iDestruct "Hw" as (m1 m2 -> ->) "%".
    iDestruct "Hv" as (n1 n2 -> ->) "%".
    dwp_pures.
    iApply dwp_value. iModIntro.
    iExists _,_. iPureIntro. repeat split; eauto.
    intros ?%join_leq. naive_solver.
  Qed.

  Lemma logrel_if ξ A (e1 e2 t1 t2 u1 u2 : expr) l :
    (DWP e1 & e2 : ⟦ tbool l ⟧ ξ) -∗
    ((DWP t1 & t2 : A ξ) ∧
        (⌜¬ l ⊑ ξ⌝ → DWP u1 & t2 : A ξ)) -∗
    ((DWP u1 & u2 : A ξ) ∧
        (⌜¬ l ⊑ ξ⌝ → DWP t1 & u2 : A ξ)) -∗
    DWP (if: e1 then t1 else u1) & (if: e2 then t2 else u2) : A ξ.
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

  Lemma logrel_if_low ξ A (e1 e2 t1 t2 u1 u2 : expr) l :
    l ⊑ ξ →
    (DWP e1 & e2 : ⟦ tbool l ⟧ ξ) -∗
    (DWP t1 & t2 : A ξ) -∗
    (DWP u1 & u2 : A ξ) -∗
    DWP (if: e1 then t1 else u1) & (if: e2 then t2 else u2) : A ξ.
  Proof.
    iIntros (Hl) "He Ht Hu".
    iApply (logrel_if with  "He [Ht] [Hu]").
    - iSplit; first done. iIntros (?). by exfalso.
    - iSplit; first done. iIntros (?). by exfalso.
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
    - rewrite /WP1 /Φ1. wp_alloc l1 as "Hl". eauto with iFrame.
    - rewrite /WP2 /Φ2. wp_alloc l1 as "Hl". eauto with iFrame.
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
    - rewrite /WP1. wp_load. done.
    - rewrite /WP2. wp_load. done.
    - iIntros (w1 w2) "Hl1 Hl2".
      iDestruct (mapsto_agree with "Hl1 Hl1'") as %->.
      iCombine "Hl1 Hl1'" as "Hl1".
      iDestruct (mapsto_agree with "Hl2 Hl2'") as %->.
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
    - rewrite /WP1 /Φ1. wp_store. eauto.
    - rewrite /WP2 /Φ2. wp_store. eauto.
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
    iInv (locsN.@(r1, r2)) as (w1 w2) "(Hr1 & Hr2 & >Hw)".
    iDestruct "Hw" as (n1 n2 -> ->) "%".
    iDestruct "Hv" as (m1 m2 -> ->) "%".
    pose (Φ1 := (λ v, ⌜v = #n1⌝ ∧ r1 ↦ₗ #(n1+m1))%I).
    pose (Φ2 := (λ v, ⌜v = #n2⌝ ∧ r2 ↦ᵣ #(n2+m2))%I).
    iApply (dwp_atomic_lift_wp Φ1 Φ2 with "[Hr1] [Hr2] [-]").
    - rewrite /WP1 /Φ1. wp_faa. eauto.
    - rewrite /WP2 /Φ2. wp_faa. eauto.
    - iIntros (? ?) "[-> Hr1] [-> Hr2]".
      iNext. iModIntro. iSplitL.
      + iNext. iExists _,_. iFrame "Hr1 Hr2".
        iExists _,_. repeat iSplit; eauto. iPureIntro.
        naive_solver.
      + iExists _,_. repeat iSplit; eauto.
  Qed.

  (*****************************************************************)
  Definition prog (r r' : loc) (h : bool) : expr :=
    #r <- #true;;   (* r : (ref bool^low)^low *)
    #r' <- #true;;  (* r' : (ref bool^low)^low *)
    let: "x" := if: #h then #r else #r' in   (* x : (ref bool^low)^high *)
    (* DWP #r_1 & #r'_2 { ... }

     ⟦ τ^high ⟧ (v1, v2) == ⟦ τ ⟧(v1) ∧ ⟦ τ ⟧(v2)
    *)
    (* we wouldn't be able to prog even the program without this assignment *)
    "x" <- #false;;   (* false : bool^low , x : (ref bool^low)^high ==> high <= low *)
    !#r'.

  Definition bad_example (r1 r2 r1' r2' : loc) (h1 h2 : bool) :
    ⟦ tref (tbool Low) ⟧ Low #r1 #r2 -∗
    ⟦ tref (tbool Low) ⟧ Low #r1' #r2' -∗
    ⟦ tbool High ⟧ Low #h1 #h2 -∗
    DWP (prog r1 r1' h1) & (prog r2 r2' h2) : ⟦ tbool Low ⟧ Low.
  Proof.
    iIntros "#Hr #Hr' #Hh".
    iApply logrel_seq.
    { iApply (logrel_store Low _ _ _ _ (tbool Low)); auto.
      - iApply dwp_value. iModIntro. iApply "Hr".
      - by iApply logrel_bool. }
    iApply logrel_seq.
    { iApply (logrel_store Low _ _ _ _ (tbool Low)); auto.
      - iApply dwp_value. iModIntro. iApply "Hr'".
      - by iApply logrel_bool. }
    (* Attempt by structural reasoning (will fail at `let x = ..`) *)
    dwp_bind (if: _ then _ else _)%E (if: _ then _ else _)%E.
    iApply (dwp_wand with "[]").
    { iApply logrel_if.
      - iApply dwp_value. iApply "Hh".
      - iSplit.
        + iApply dwp_value. simpl.
          iApply "Hr".
        + iIntros (?).
    (* Attempt by symbolic execution (will fail at the store) *)
    (* destruct h1, h2. *)
    (* { logrel_pures. simpl. admit. } *)
  Abort.

  Definition prog_good (r r' : loc) (h : bool) : expr :=
    #r <- #true;;
    #r' <- #true;;
    let: "x" := if: #h then #r else #r' in
    !#r'.

  Definition good_example (r1 r2 r1' r2' : loc) (h1 h2 : bool) :
    ⟦ tref (tbool Low) ⟧ Low #r1 #r2 -∗
    ⟦ tref (tbool Low) ⟧ Low #r1' #r2' -∗
    ⟦ tbool High ⟧ Low #h1 #h2 -∗
    DWP (prog_good r1 r1' h1) & (prog_good r2 r2' h2) : ⟦ tbool Low ⟧ Low.
  Proof.
    iIntros "#Hr #Hr' #Hh".
    iApply logrel_seq.
    { iApply (logrel_store Low _ _ _ _ (tbool Low)); auto.
      - iApply dwp_value. iModIntro. iApply "Hr".
      - by iApply logrel_bool. }
    iApply logrel_seq.
    { iApply (logrel_store Low _ _ _ _ (tbool Low)); auto.
      - iApply dwp_value. iModIntro. iApply "Hr'".
      - by iApply logrel_bool. }
    destruct h1, h2.
    { dwp_pures. simpl. iApply (dwp_mono with "[]"); last first.
      { iApply logrel_deref; eauto. iApply dwp_value.
        iApply "Hr'". }
      simpl. eauto. }
    { dwp_pures. simpl. iApply (dwp_mono with "[]"); last first.
      { iApply logrel_deref; eauto. iApply dwp_value.
        iApply "Hr'". }
      simpl. eauto. }
    { dwp_pures. simpl. iApply (dwp_mono with "[]"); last first.
      { iApply logrel_deref; eauto. iApply dwp_value.
        iApply "Hr'". }
      simpl. eauto. }
    { dwp_pures. simpl. iApply (dwp_mono with "[]"); last first.
      { iApply logrel_deref; eauto. iApply dwp_value.
        iApply "Hr'". }
      simpl. eauto. }
  Qed.
End rules.
