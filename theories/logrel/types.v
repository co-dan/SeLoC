From iris.algebra Require Import cmra.

(** * Security lattice *)
Inductive slevel := Low | High.
Instance slevel_eqdec : EqDecision slevel.
Proof. solve_decision. Qed.
Canonical Structure slevelO := leibnizO slevel.

Instance slevel_join : Join slevel := λ lv1 lv2,
  match lv1, lv2 with
  | High,_ => High
  | _,High => High
  | _,_ => Low
  end.
Instance slevel_meet : Meet slevel := λ lv1 lv2,
  match lv1, lv2 with
  | Low,_ => Low
  | _,Low => Low
  | High,High => High
  end.

Instance slevel_join_assoc : Assoc (=) slevel_join.
Proof. by intros [] [] []. Qed.
Instance slevel_join_comm : Comm (=) slevel_join.
Proof. by intros [] []. Qed.
Instance slevel_join_leftid : LeftId (=) Low slevel_join.
Proof. by intros []. Qed.
Instance slevel_join_rightid : RightId (=) Low slevel_join.
Proof. by intros []. Qed.
Instance slevel_join_idem : IdemP (=) slevel_join.
Proof. by intros []. Qed.

Instance slevel_meet_assoc : Assoc (=) slevel_meet.
Proof. by intros [] [] []. Qed.
Instance slevel_meet_comm : Comm (=) slevel_meet.
Proof. by intros [] []. Qed.
Instance slevel_meet_leftid : LeftId (=) High slevel_meet.
Proof. by intros []. Qed.
Instance slevel_meet_rightid : RightId (=) High slevel_meet.
Proof. by intros []. Qed.
Instance slevel_meet_idem : IdemP (=) slevel_meet.
Proof. by intros []. Qed.

Definition slevel_leb (lv1 lv2 : slevel) : bool :=
  match lv2 with
  | High => true
  | Low => if lv1 is Low then true else false
  end.
Instance slevel_le : SqSubsetEq slevel := slevel_leb.
Instance slevel_le_po : PreOrder slevel_le.
Proof. split; by repeat intros []. Qed.

Lemma join_mono_l (l1 l2 l3 : slevel) :
  l1 ⊑ l2 → l1 ⊔ l3 ⊑ l2 ⊔ l3.
Proof. by destruct l1,l2,l3. Qed.
Lemma join_mono_r (l1 l2 l3 : slevel) :
  l2 ⊑ l3 → l1 ⊔ l2 ⊑ l1 ⊔ l3.
Proof. by destruct l1,l2,l3. Qed.
Lemma join_leq_l (l1 l2 : slevel) : l1 ⊑ l1 ⊔ l2.
Proof. by destruct l1,l2. Qed.
Lemma join_leq_r (l1 l2 : slevel) : l1 ⊑ l2 ⊔ l1.
Proof. by destruct l1,l2. Qed.
Lemma meet_geq_l (l1 l2 : slevel) : l1 ⊓ l2 ⊑ l1.
Proof. by destruct l1,l2. Qed.
Lemma meet_geq_r (l1 l2 : slevel) : l1 ⊓ l2 ⊑ l2.
Proof. by destruct l1,l2. Qed.

Lemma leq_meet_min_1 (l1 l2 : slevel) :
  l1 ⊑ l2 → l1 ⊓ l2 = l1.
Proof. by destruct l1,l2; inversion 1. Qed.
Lemma leq_meet_min_2 (l1 l2 : slevel) :
  l2 ⊑ l1 → l1 ⊓ l2 = l2.
Proof. by destruct l1,l2; inversion 1. Qed.

Hint Resolve join_leq_l join_leq_r join_mono_l join_mono_r.
Hint Resolve meet_geq_l meet_geq_r leq_meet_min_1 leq_meet_min_2.

Section slevelR_cmra.
  Implicit Types l : slevelO.
  Instance slevelO_valid : Valid slevelO := λ x, True.
  Instance slevelO_validN : ValidN slevelO := λ n x, True.
  Instance slevelO_pcore : PCore slevelO := Some.
  Instance slevelO_op : Op slevelO := slevel_meet.
  Definition slevelO_op_meet l1 l2 : l1 ⋅ l2 = l1 ⊓ l2 := eq_refl.

  Instance slevelO_equiv : Equiv slevelO := (=).
  Instance slevelO_leibniz_equiv : LeibnizEquiv slevelO.
  Proof. intros ???. eauto. Qed.

  Lemma slevelR_included l1 l2 : l1 ≼ l2 ↔ l2 ⊑ l1.
  Proof.
    split.
    - intros [σ ->]. eauto.
    - exists l2. rewrite slevelO_op_meet.
      fold_leibniz. symmetry. eauto.
  Qed.

  Lemma slevelO_ra_mixin : RAMixin slevelO.
  Proof.
    apply ra_total_mixin; try by eauto; try apply _.
    - intros x. apply idemp. apply _.
  Qed.

  Canonical Structure slevelR : cmraT := discreteR slevelO slevelO_ra_mixin.

  Global Instance slevelR_cmra_discrete : CmraDiscrete slevelR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance slevelR_core_id (l : slevelR) : CoreId l.
  Proof. by constructor. Qed.

  Global Instance slevelR_cmra_total : CmraTotal slevelR.
  Proof. intro x. compute. eauto. Qed.
End slevelR_cmra.


(** * Types *)
Inductive type :=
| tunit : type
| tint (l : slevel) : type
| tbool (l : slevel) : type
| tarrow (s t : type) (l : slevel)
| tprod (t1 t2 : type)
| tref (t : type) (l : slevel).

Instance type_eqdec : EqDecision type.
Proof. solve_decision. Qed.

Fixpoint type_measure (τ : type) : nat :=
  match τ with
  | tunit => 0
  | tint _ => 0
  | tbool _ => 0
  | tarrow s t _ => type_measure s + type_measure t + 1
  | tprod τ1 τ2 => type_measure τ1 + type_measure τ2 + 1
  | tref τ _ => type_measure τ + 1
  end.

(* stamp τ l = τ ⊔ l *)
Fixpoint stamp (τ : type) (l : slevel) : type :=
  match τ with
  | tunit => tunit
  | tint l2 => tint (l2 ⊔ l)
  | tbool l2 => tbool (l2 ⊔ l)
  | tprod τ1 τ2 => tprod (stamp τ1 l) (stamp τ2 l)
  | tarrow s t l2 => tarrow s t (l2 ⊔ l)
  | tref τ l2 => tref τ (l2 ⊔ l)
  end.
Lemma stamp_measure (τ : type) (l : slevel) :
  type_measure τ = type_measure (stamp τ l).
Proof. induction τ; naive_solver. Qed.

(** The subtyping relation <: *)
Reserved Notation "τ '<:' σ" (at level 50).
Inductive type_sub : type → type → Prop :=
| type_sub_refl τ :
    τ <: τ
| type_sub_trans τ₁ τ₂ τ₃ :
    τ₁ <: τ₂ →
    τ₂ <: τ₃ →
    τ₁ <: τ₃
| type_sub_int l1 l2 :
    l1 ⊑ l2 →
    tint l1 <: tint l2
| type_sub_bool l1 l2 :
    l1 ⊑ l2 →
    tbool l1 <: tbool l2
| type_sub_arrow τ₁ τ₂ τ'₁ τ'₂ l l' :
    τ'₁ <: τ₁   →
    τ₂  <: τ'₂  →
    l   ⊑  l'   →
    tarrow τ₁ τ₂ l <: tarrow τ'₁ τ'₂ l'
| type_sub_prod τ₁ τ₂ σ₁ σ₂ :
    τ₁ <: τ₂ →
    σ₁ <: σ₂ →
    tprod τ₁ σ₁ <: tprod τ₂ σ₂
| type_sub_ref τ l1 l2 :
    l1 ⊑ l2 →
    tref τ l1 <: tref τ l2
where "τ '<:' σ" := (type_sub τ σ).

Hint Constructors type_sub.

Instance type_sub_reflexive : Reflexive type_sub.
Proof. by constructor. Qed.
Instance type_sub_transitive : Transitive type_sub.
Proof. intros ?????. by econstructor. Qed.
Instance type_sub_preorder : PreOrder type_sub.
Proof. split; apply _. Qed.

Lemma stamp_sub τ l : τ <: stamp τ l.
Proof. induction τ; simpl; eauto. Qed.

Lemma stamp_mono_2 τ l l' :
  l ⊑ l' →
  stamp τ l <: stamp τ l'.
Proof. intros. induction τ; simpl; eauto. Qed.

