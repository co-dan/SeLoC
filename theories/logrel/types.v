From iris.algebra Require Import cmra.
From iris.heap_lang Require Import lang metatheory.
From stdpp Require Import fin_sets gmap stringmap.
From iris_ni.logrel Require Export slevel.

(** * Types *)
Inductive type :=
| tunit : type
| tint (l : slevel) : type
| tbool (l : slevel) : type
| tarrow (s t : type) (l : slevel)
| tprod (t1 t2 : type)
| tintoption (il l : slevel)
| tref (t : type).

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

(* "Flat types" are types τ for which the following typing rule is
sound:

  ⊢ v, w : τ      ⊢ e : bool high
------------------------------------
    ⊢ if e then v else w : τ
*)
Inductive  flat_type : type → Prop :=
| tint_flat l : flat_type (tint l)
| tbool_flat l : flat_type (tbool l)
| tunit_flat : flat_type tunit
| tprod_flat τ τ' : flat_type τ →
                    flat_type τ' →
                    flat_type (tprod τ τ').

(* "Unboxed types" are types which values are unboxed *)
Inductive  unboxed_type : type → Prop :=
| tint_unboxed l : unboxed_type (tint l)
| tbool_unboxed l : unboxed_type (tbool l)
| tunit_unboxed : unboxed_type tunit
| tref_unboxed τ : unboxed_type (tref τ)
(* | tintoption_unboxed il l : unboxed_type (tintoption il l) *)
.


Definition tmutex_aux : seal (tref (tbool Low)). by eexists. Qed.
Definition tmutex : type := tmutex_aux.(unseal).
Definition tmutex_eq : tmutex = tref (tbool Low) := tmutex_aux.(seal_eq).

(* [lbl τ] is a "level approximation" of a type *)
Fixpoint lbl (τ : type) : slevel :=
  match τ with
  | tunit => Low
  | tint α => α
  | tbool α => α
  | tprod τ1 τ2 => lbl τ1 ⊔ lbl τ2
  | tarrow s t β => lbl t ⊔ β
  | tintoption il α => il ⊔ α
  | tref τ => Low
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

(* Typing for binary operations *)
Inductive bin_op_int : bin_op → Prop :=
| bin_op_int_plus : bin_op_int PlusOp
| bin_op_int_mult : bin_op_int MultOp
| bin_op_int_sub : bin_op_int MinusOp
| bin_op_int_div : bin_op_int QuotOp.

Inductive bin_op_int_bool : bin_op → Prop :=
| bin_op_int_lt : bin_op_int_bool LtOp
| bin_op_int_le : bin_op_int_bool LeOp
| bin_op_int_eq : bin_op_int_bool EqOp.

Inductive bin_op_bool : bin_op → Prop :=
| bin_op_bool_and : bin_op_bool AndOp
| bin_op_bool_or : bin_op_bool OrOp.


Inductive almost_val : gset string → expr → Prop :=
| is_a_value Γ v : almost_val Γ (Val v)
| is_a_variable (x : string) Γ :
    x ∈ Γ →
    almost_val Γ (Var x).


(**********************************************************************)
(***** Properties *)

Section local.

Local Hint Resolve join_leq_l join_leq_r join_mono_l join_mono_r : core.
Local Hint Resolve leq_join_max_1 leq_join_max_2 : core.
Local Hint Resolve meet_geq_l meet_geq_r leq_meet_min_1 leq_meet_min_2 : core.
Local Hint Constructors type_sub : core.

Global Instance type_eqdec : EqDecision type.
Proof. solve_decision. Qed.

Lemma stamp_measure (τ : type) (l : slevel) :
  type_measure τ = type_measure (stamp τ l).
Proof. induction τ; naive_solver. Qed.

Lemma lbl_stamp_leq_general τ l : lbl (stamp τ (lbl τ ⊔ l)) ⊑ lbl τ ⊔ l.
Proof.
  revert l. induction τ=>α; simpl;
                           try (by rewrite assoc idemp //);
                           rewrite ?idemp //.
  + sl_lattice_switch_goal. done.
  + rewrite -{1}(assoc _ (lbl τ1) (lbl τ2) α).
    rewrite IHτ1.
    rewrite (comm _ (lbl τ1) (lbl τ2)).
    rewrite -{1}(assoc _ (lbl τ2) (lbl τ1) α).
    rewrite IHτ2.
    sl_lattice_switch_goal. done.
  + sl_lattice_switch_goal. done.
Qed.

Lemma lbl_stamp_leq τ : lbl (stamp τ (lbl τ)) ⊑ lbl τ.
Proof.
  rewrite -(right_id Low (⊔) (lbl τ)).
  apply lbl_stamp_leq_general.
Qed.

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

Lemma stamp_idemp τ l : stamp (stamp τ l) l = stamp τ l.
Proof.
  induction τ; simpl; rewrite -?assoc // ?(idemp (⊔) l) //.
  by rewrite IHτ1 IHτ2.
Qed.

Lemma flat_type_stamp τ l : flat_type τ → flat_type (stamp τ l).
Proof. induction 1; econstructor; eauto. Qed.

Lemma unboxed_type_stamp τ l : unboxed_type τ → unboxed_type (stamp τ l).
Proof. induction 1; econstructor; eauto. Qed.

Lemma unboxed_type_stamp_lbl τ : unboxed_type τ → τ = stamp τ (lbl τ).
Proof. by induction 1; simpl; rewrite ?idemp_L //. Qed.

End local.

(**********************************************************************)

Lemma bin_op_int_safe (i1 i2 : Z) op :
  bin_op_int op →
  ∃ (z : Z), bin_op_eval op (LitV (LitInt i1)) (LitV (LitInt i2)) = Some (LitV (LitInt z)).
Proof.
  destruct op; inversion 1; eauto.
Qed.

Lemma bin_op_int_bool_safe (i1 i2 : Z) op :
  bin_op_int_bool op →
  ∃ (b : bool), bin_op_eval op (LitV (LitInt i1)) (LitV (LitInt i2)) = Some (LitV (LitBool b)).
Proof.
  destruct op; inversion 1; eauto.
Qed.

Lemma bin_op_bool_safe (b1 b2 : bool) op :
  bin_op_bool op →
  ∃ (b : bool), bin_op_eval op (LitV (LitBool b1)) (LitV (LitBool b2)) = Some (LitV (LitBool b)).
Proof.
  destruct op; inversion 1; eauto.
Qed.

(****** almost_val and its properties *)

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

Delimit Scope FType_scope with ty.
Bind Scope FType_scope with type.
Infix "*" := tprod : FType_scope.
Notation "(*)" := tprod (only parsing) : FType_scope.
Notation "A '→' B" := (tarrow A B Low) : FType_scope.
Notation "τ '<:' σ" := (type_sub τ σ) (at level 50).

