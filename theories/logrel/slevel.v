(** * Security lattice *)
From iris.algebra Require Import cmra.

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

(**************************************************)
(** Simple reflection for (⊔, ⊑) *)
Section reflection.
  Inductive btree :=
  | bnode : btree → btree → btree
  | bleaf : nat → btree. (* nat points to the slevel in the context *)

  Fixpoint btree_interp (ctx : list slevel) (t : btree) : slevel :=
    match t with
    | bleaf i => ctx !!! i
    | bnode t1 t2 => btree_interp ctx t1 ⊔ btree_interp ctx t2
    end.

  Fixpoint list_interp (ctx : list slevel) (e : list nat) {struct e} : slevel :=
    match e with
    | i :: acc =>
      ctx !!! i  ⊔  list_interp ctx acc
    | [] => Low
    end.

  Fixpoint flatten_btree_aux (t : btree) (acc : list nat) : list nat :=
    match t with
    | bleaf i =>  i :: acc
    | bnode t1 t2 => flatten_btree_aux t1 (flatten_btree_aux t2 acc)
    end.

  Fixpoint flatten_btree (t : btree) :=
    match t with
    | bleaf i => [i]
    | bnode t1 t2 => flatten_btree_aux t1 (flatten_btree t2)
    end.

  Fixpoint insert_list (j : nat) (e : list nat) :=
    match e with
    | i::e =>
      if Nat.leb i j
      then i::(insert_list j e)
      else j::i::e
    | _ => [j]
    end.

  Fixpoint sort_list (e : list nat) :=
    match e with
    | i::e => insert_list i (sort_list e)
    | [] => []
    end.

  Fixpoint dedup_list_aux (i : nat) (e : list nat) :=
    match e with
    | [] => []
    | j::e =>
      let e' := dedup_list_aux i e in
      if Nat.eqb i j then e'
      else j::e'
    end.

  Fixpoint dedup_list (e : list nat) :=
    match e with
    | [] => []
    | i::e => i::(dedup_list_aux i (dedup_list e))
    end.

  Lemma flatten_btree_aux_correct ctx t acc :
    list_interp ctx (flatten_btree_aux t acc) = btree_interp ctx t ⊔ list_interp ctx acc.
  Proof.
    revert acc. induction t=>acc /=; try done.
    rewrite IHt1 IHt2 -assoc /= //.
  Qed.

  Lemma flatten_btree_correct ctx t :
    list_interp ctx (flatten_btree t) = btree_interp ctx t.
  Proof.
    induction t; simpl; try by rewrite right_id.
    by rewrite flatten_btree_aux_correct IHt2.
  Qed.

  Lemma do_flatten_leq ctx1 ctx2 t1 t2 :
    list_interp ctx1 (flatten_btree t1) ⊑ list_interp ctx2 (flatten_btree t2) →
    btree_interp ctx1 t1 ⊑ btree_interp ctx2 t2.
  Proof. by rewrite !flatten_btree_correct. Qed.

  Lemma insert_list_correct ctx n t :
    list_interp ctx (insert_list n t) = (ctx !!! n) ⊔ list_interp ctx t.
  Proof.
    induction t as [|i t Ht]; simpl; first done.
    destruct (i <=? n); simpl; try done.
    rewrite Ht. rewrite !assoc.
    by rewrite (comm _ (ctx !!! i)).
  Qed.

  Lemma sort_list_correct ctx t :
    list_interp ctx (sort_list t) = list_interp ctx t.
  Proof.
    induction t as [|i t Ht]; simpl; first done.
    by rewrite insert_list_correct Ht.
  Qed.

  Lemma do_sort_leq ctx1 ctx2 t1 t2 :
    list_interp ctx1 (sort_list t1) ⊑ list_interp ctx2 (sort_list t2) →
    list_interp ctx1 t1 ⊑ list_interp ctx2 t2.
  Proof. by rewrite !sort_list_correct. Qed.

  Lemma dedup_list_aux_correct ctx i t :
    ctx !!! i ⊔ list_interp ctx (dedup_list_aux i t) =
    ctx !!! i ⊔ list_interp ctx t.
  Proof.
    induction t as [|j t Ht]; simpl; first done.
    destruct (decide (i = j)) as [->|?]; simpl.
    - rewrite Nat.eqb_refl Ht.
      rewrite assoc idemp //.
    - assert ((i =? j)%nat = false) as ->.
      { by apply Nat.eqb_neq. }
      simpl. rewrite !assoc (comm _ (ctx !!! i) (ctx !!! j)) -!assoc.
      by rewrite Ht.
  Qed.

  Lemma dedup_list_correct ctx t :
    list_interp ctx (dedup_list t) = list_interp ctx t.
  Proof.
    induction t as [|j t Ht]; simpl; first done.
    by rewrite dedup_list_aux_correct Ht.
  Qed.

  Lemma do_dedup_leq ctx1 ctx2 t1 t2 :
    list_interp ctx1 (dedup_list t1) ⊑ list_interp ctx2 (dedup_list t2) →
    list_interp ctx1 t1 ⊑ list_interp ctx2 t2.
  Proof. by rewrite !dedup_list_correct. Qed.

End reflection.

Ltac lookup_ctx_aux ctx n v :=
  match ctx with
  | ?x::?ctxr =>
    let ctx := constr:(ctxr) in
    match constr:(x = v) with
    | (?z = ?z) => n
    | _ => lookup_ctx_aux ctx (S n) v
    end
  end.

Ltac lookup_ctx ctx v := lookup_ctx_aux ctx 0 v.

Ltac model_contex ctx v :=
  match v with
  | (?α ⊔ ?β) =>
    let ctx1 := model_contex ctx α in
    model_contex ctx1 β
  | ?α => (* if variable is already present *)
    let n := lookup_ctx ctx α in
    constr:(ctx)
  | ?α => (* otherwise add a new one *)
    constr:( α :: ctx )
  end.

Ltac model_aux ctx v :=
  match v with
  | (?α ⊔ ?β) =>
    let r1 := model_aux ctx α in
    let r2 := model_aux ctx β in
    constr:(bnode r1 r2)
  | ?α =>
    let n := lookup_ctx ctx α in
    constr:(bleaf n)
  end.

Ltac model v :=
  let ctx := model_contex ([] : list slevel) v in
  let t := model_aux ctx v in
  constr:(pair ctx t).

Ltac sl_lattice_switch_goal :=
  match goal with
  | [ |- (?α ⊑ ?β) ] =>
    let ctx := model_contex ([] : list slevel) (α ⊔ β) in
    let r1 := model_aux ctx α in
    let r2 := model_aux ctx β in
    change (btree_interp ctx r1 ⊑ btree_interp ctx r2);
    apply do_flatten_leq;
    apply do_sort_leq;
    apply do_dedup_leq;
    lazy beta iota zeta delta
       [flatten_btree flatten_btree_aux
        insert_list sort_list
        dedup_list dedup_list_aux
        Nat.leb Nat.eqb
        lookup_total list_lookup_total
        list_interp btree_interp ]
  end.

Lemma test (l1 l2 l3 : slevel) :
  l1 ⊔ l1 ⊔ l2 ⊑ l2 ⊔ l1 ⊔ (l2 ⊔ l1) ⊔ l3.
Proof.
  sl_lattice_switch_goal. auto.
  apply join_leq_r.
Qed.

Section local.

Local Hint Resolve join_leq_l join_leq_r join_mono_l join_mono_r : core.
Local Hint Resolve leq_join_max_1 leq_join_max_2 : core.
Local Hint Resolve meet_geq_l meet_geq_r leq_meet_min_1 leq_meet_min_2 : core.

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

  Canonical Structure slevelR : cmra := discreteR slevelO slevelO_ra_mixin.

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

  Canonical Structure slevelUR : ucmra := Ucmra slevelO slevelO_ucmra_mixin.

End slevelR_cmra.

End local.
