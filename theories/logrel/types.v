From iris.algebra Require Import cmra.
From iris.heap_lang Require Import lang metatheory.
From stdpp Require Import fin_sets gmap stringmap.

(** * Security lattice *)
Inductive slevel := Low | High.
Instance slevel_eqdec : EqDecision slevel.
Proof. solve_decision. Qed.
Instance slevel_inhabited: Inhabited slevel := populate Low.
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
Lemma meet_mono_l (l1 l2 l3 : slevel) :
  l1 ⊑ l2 → l1 ⊓ l3 ⊑ l2 ⊓ l3.
Proof. by destruct l1,l2,l3. Qed.
Lemma meet_mono_r (l1 l2 l3 : slevel) :
  l2 ⊑ l3 → l1 ⊓ l2 ⊑ l1 ⊓ l3.
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

Lemma leq_join_max_2 (l1 l2 : slevel) :
  l1 ⊑ l2 → l1 ⊔ l2 = l2.
Proof. by destruct l1,l2; inversion 1. Qed.
Lemma leq_join_max_1 (l1 l2 : slevel) :
  l2 ⊑ l1 → l1 ⊔ l2 = l1.
Proof. by destruct l1,l2; inversion 1. Qed.

Lemma join_leq (l1 l2 l3 : slevel) :
  l1 ⊔ l2 ⊑ l3 → l1 ⊑ l3 ∧ l2 ⊑ l3.
Proof. by destruct l1,l2,l3; inversion 1. Qed.

Section local.

Local Hint Resolve join_leq_l join_leq_r join_mono_l join_mono_r.
Local Hint Resolve leq_join_max_1 leq_join_max_2.
Local Hint Resolve meet_geq_l meet_geq_r leq_meet_min_1 leq_meet_min_2.

Global Instance slevel_leb_rewriterelation : RewriteRelation ((⊑) : relation slevel) := _.

Global Instance slevel_join_proper : Proper ((⊑) ==> (⊑) ==> (⊑)) (join (A:=slevel)).
Proof.
  intros l1 l1' H1 l2 l2' H2.
  etrans; [ apply join_mono_l | ]; eauto.
Qed.
Global Instance slevel_join_proper_flip :
  Proper (flip (⊑) ==> flip (⊑) ==> flip (⊑)) (join (A:=slevel)).
Proof.
  intros l1 l1' H1 l2 l2' H2.
  etrans; [ apply join_mono_l | apply join_mono_r ]; done.
Qed.
Global Instance slevel_meet_proper : Proper ((⊑) ==> (⊑) ==> (⊑)) (meet (A:=slevel)).
Proof.
  intros l1 l1' H1 l2 l2' H2.
  etrans; [ apply meet_mono_l | apply meet_mono_r ]; done.
Qed.
Global Instance slevel_meet_proper_flip :
  Proper (flip (⊑) ==> flip (⊑) ==> flip (⊑)) (meet (A:=slevel)).
Proof.
  intros l1 l1' H1 l2 l2' H2.
  etrans; [ apply meet_mono_l | apply meet_mono_r ]; done.
Qed.


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

  Global Instance slevelO_unit : Unit slevelO := High.

  Lemma slevelO_ucmra_mixin : UcmraMixin slevelO.
  Proof.
    split; try done.
    intro x. destruct x; cbv; done.
  Qed.

  Canonical Structure slevelUR : ucmraT := UcmraT slevelO slevelO_ucmra_mixin.

End slevelR_cmra.


(** * Types *)
Inductive type :=
| tunit : type
| tint (l : slevel) : type
| tbool (l : slevel) : type
| tarrow (s t : type) (l : slevel)
| tprod (t1 t2 : type)
| tintoption (il l : slevel)
| tref (t : type).

(* "Flat types" are types τ for which the following typing rule is
sound:

  ⊢ v, w : τ      ⊢ e : bool high
------------------------------------
    ⊢ if e then v else w : τ
*)
Inductive  flat_type : type → Prop :=
| tint_flat : flat_type (tint High)
| tbool_flat : flat_type (tbool High)
| tunit_flat : flat_type tunit
| tprod_flat τ τ' : flat_type τ →
                    flat_type τ' →
                    flat_type (tprod τ τ').

Definition tmutex_aux : seal (tref (tbool Low)). by eexists. Qed.
Definition tmutex : type := tmutex_aux.(unseal).
Definition tmutex_eq : tmutex = tref (tbool Low) := tmutex_aux.(seal_eq).

Global Instance type_eqdec : EqDecision type.
Proof. solve_decision. Qed.

Fixpoint type_measure (τ : type) : nat :=
  match τ with
  | tunit => 0
  | tint _ => 0
  | tbool _ => 0
  | tarrow s t _ => type_measure s + type_measure t + 1
  | tprod τ1 τ2 => type_measure τ1 + type_measure τ2 + 1
  | tintoption _ _ => 0
  | tref τ => type_measure τ + 1
  end.

(* stamp τ l = τ ⊔ l *)
Fixpoint stamp (τ : type) (l : slevel) : type :=
  match τ with
  | tunit => tunit
  | tint l2 => tint (l2 ⊔ l)
  | tbool l2 => tbool (l2 ⊔ l)
  | tprod τ1 τ2 => tprod (stamp τ1 l) (stamp τ2 l)
  | tarrow s t l2 => tarrow s t (l2 ⊔ l)
  | tintoption il l2 => tintoption il (l2 ⊔ l)
  | tref τ => tref τ
  end.
Lemma stamp_measure (τ : type) (l : slevel) :
  type_measure τ = type_measure (stamp τ l).
Proof. induction τ; naive_solver. Qed.

(* [lbl τ] is a "level approximation" of a type *)
Fixpoint lbl (τ : type) : slevel :=
  match τ with
  | tunit => Low
  | tint α => α
  | tbool α => α
  | tprod τ1 τ2 => lbl τ1 ⊔ lbl τ2
  | tarrow s t β => lbl t ⊔ β
  | tintoption il α => il ⊔ α
  | tref τ => lbl τ
  end.

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
| type_sub_option il l1 l2:
    l1 ⊑ l2 →
    tintoption il l1 <: tintoption il l2
| type_sub_arrow τ₁ τ₂ τ'₁ τ'₂ l l' :
    τ'₁ <: τ₁   →
    τ₂  <: τ'₂  →
    l   ⊑  l'   →
    tarrow τ₁ τ₂ l <: tarrow τ'₁ τ'₂ l'
| type_sub_prod τ₁ τ₂ σ₁ σ₂ :
    τ₁ <: τ₂ →
    σ₁ <: σ₂ →
    tprod τ₁ σ₁ <: tprod τ₂ σ₂
where "τ '<:' σ" := (type_sub τ σ).

Local Hint Constructors type_sub.

Global Instance type_sub_reflexive : Reflexive type_sub.
Proof. by constructor. Qed.
Global Instance type_sub_transitive : Transitive type_sub.
Proof. intros ?????. by econstructor. Qed.
Global Instance type_sub_preorder : PreOrder type_sub.
Proof. split; apply _. Qed.

Lemma stamp_sub τ l : τ <: stamp τ l.
Proof. induction τ; simpl; eauto. Qed.

Lemma stamp_mono_2 τ l l' :
  l ⊑ l' →
  stamp τ l <: stamp τ l'.
Proof. intros. induction τ; simpl; eauto. Qed.

Lemma stamp_low τ : stamp τ Low = τ.
Proof.
  induction τ; simpl; rewrite ?right_id; eauto;
  by (rewrite IHτ1 IHτ2 || rewrite IHτ).
Qed.

End local.

Inductive almost_val : gset string → expr → Prop :=
| is_a_value Γ v : almost_val Γ (Val v)
| is_a_variable (x : string) Γ :
    x ∈ Γ →
    almost_val Γ (Var x).

Lemma almost_val_mono Γ Γ' e :
  Γ ⊆ Γ' →
  almost_val Γ e →
  almost_val Γ' e.
Proof.
  induction 2; constructor; set_solver.
Qed.

Lemma almost_val_subst_map X γ e :
  almost_val X e →
  X = dom _ γ →
  ∃ (w : val), subst_map γ e = Val w.
Proof.
  intros Hv ->. inversion Hv; simplify_eq/=.
  - eexists; eauto.
  - apply elem_of_dom in H. destruct H as [w ->].
    eexists; eauto.
Qed.

Lemma almost_val_union X Y γ e :
  almost_val (X ∪ Y) e →
  Y = dom _ γ →
  almost_val X (subst_map γ e).
Proof.
  intros He ->.
  inversion He; simplify_eq/=; first by constructor.
  destruct (γ !! x) as [v|] eqn:Hx; first by constructor.
  econstructor. apply (not_elem_of_dom (D:=stringset)) in Hx.
  set_solver.
Qed.

Inductive bin_op_int : bin_op → Prop :=
| bin_op_int_plus : bin_op_int PlusOp
| bin_op_int_mult : bin_op_int MultOp
| bin_op_int_sub : bin_op_int MinusOp
| bin_op_int_div : bin_op_int QuotOp.

Lemma bin_op_int_safe (i1 i2 : Z) op :
  bin_op_int op →
  ∃ (z : Z), bin_op_eval op (LitV (LitInt i1)) (LitV (LitInt i2)) = Some (LitV (LitInt z)).
Proof.
  destruct op; inversion 1; eauto.
Qed.

Inductive bin_op_int_bool : bin_op → Prop :=
| bin_op_int_lt : bin_op_int_bool LtOp
| bin_op_int_le : bin_op_int_bool LeOp
| bin_op_int_eq : bin_op_int_bool EqOp.

Lemma bin_op_int_bool_safe (i1 i2 : Z) op :
  bin_op_int_bool op →
  ∃ (b : bool), bin_op_eval op (LitV (LitInt i1)) (LitV (LitInt i2)) = Some (LitV (LitBool b)).
Proof.
  destruct op; inversion 1; eauto.
Qed.

Inductive bin_op_bool : bin_op → Prop :=
| bin_op_bool_and : bin_op_bool AndOp
| bin_op_bool_or : bin_op_bool OrOp.

Lemma bin_op_bool_safe (b1 b2 : bool) op :
  bin_op_bool op →
  ∃ (b : bool), bin_op_eval op (LitV (LitBool b1)) (LitV (LitBool b2)) = Some (LitV (LitBool b)).
Proof.
  destruct op; inversion 1; eauto.
Qed.


Delimit Scope FType_scope with ty.
Bind Scope FType_scope with type.
Infix "*" := tprod : FType_scope.
Notation "(*)" := tprod (only parsing) : FType_scope.
Notation "A '→' B" := (tarrow A B Low) : FType_scope.
Notation "τ '<:' σ" := (type_sub τ σ) (at level 50).

