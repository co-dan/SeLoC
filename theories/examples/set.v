From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types interp.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import tactics.
From iris_ni.proofmode Require Import dwp_tactics.
From iris.heap_lang Require Import lang array proofmode.
From iris.algebra Require Import excl.

From iris_ni.logrel Require Import array typing.
From iris_ni.examples Require Import lock.

Definition set_t : type :=
  tprod (tarrow (tint High) tunit Low)
        (tarrow (tint High) (tbool High) Low).

(* cap : int Low → int Low *)
Definition cap : expr := rec: "cap" "k" :=
  if: "k" = #0
  then #0
  else #1 + #2 * ("cap" ("k" - #1)).

(* eq_option : option (int High) High → int High → bool High *)
Definition eq_option : expr := λ: "o" "v2",
  let: "v1" := "v2"+#1 in
  let: "v1" := match: "o" with NONE => "v1" | SOME "v" => "v" end in
  "v1" = "v2".

(* lte_option : option (int High) High → int High → bool High *)
Definition lte_option : expr := λ: "o" "v2",
  let: "v1" := match: "o" with NONE => #0 | SOME "v" => "v" end in
  let: "is_none" := match: "o" with NONE => #true | SOME <> => #false end in
  (BinOp AndOp "is_none" ("v1" ≤ "v2")).


(* lookup_loop : refN (option (int high)) -> int low ->
                 int high -> int high -> int high -> bool high -> bool high *)
Definition lookup_loop : expr :=
  rec: "lookup_loop" "arr" "k" "l" "r" "x" "is_found" :=
  if: "k" = #0 then "is_found"
  else let: "i" := BinOp QuotOp ("l" + "r") #2 in
       let: "elem" := "get" "arr" "i" in
       let: "lr1" := ("i"+#1, "r") in
       let: "lr2" := ("l", "i"-#1) in
       let: "lr" := if: (lte_option "elem" "x")
                    then "lr1"
                    else "lr2" in
       let: "l" := Fst "lr" in
       let: "r" := Snd "lr" in
       let: "is_found" := BinOp OrOp "is_found" (eq_option "elem" "x") in
       "lookup_loop" "arr" ("k"-#1) "l" "r" "x" "is_found".




Lemma BinOp_int_typed' 𝔏 ξ Γ e1 e2 l2 l3 op :
  bin_op_int op →
  has_type 𝔏 ξ Γ e1 (tint l2) →
  l2 ⊑ l3 →
  has_type 𝔏 ξ Γ e2 (tint l2) →
  has_type 𝔏 ξ Γ (BinOp op e1 e2) (tint l3).
Proof.
  intros ?? Hsub ?.
  eapply Sub_typed; last first.
  { apply type_sub_int, Hsub. }
  rewrite -(idemp_L (⊔) l2).
  by apply BinOp_int_typed.
Qed.

Lemma BinOp_int_bool_typed' 𝔏 ξ Γ e1 e2 l2 l3 op :
  bin_op_int_bool op →
  has_type 𝔏 ξ Γ e1 (tint l2) →
  l2 ⊑ l3 →
  has_type 𝔏 ξ Γ e2 (tint l2) →
  has_type 𝔏 ξ Γ (BinOp op e1 e2) (tbool l3).
Proof.
  intros ?? Hsub ?.
  eapply Sub_typed; last first.
  { apply type_sub_bool, Hsub. }
  rewrite -(idemp_L (⊔) l2).
  by apply BinOp_int_bool_typed.
Qed.

Lemma BinOp_bool_typed' 𝔏 ξ Γ e1 e2 l2 l3 op :
  bin_op_bool op →
  has_type 𝔏 ξ Γ e1 (tbool l2) →
  l2 ⊑ l3 →
  has_type 𝔏 ξ Γ e2 (tbool l2) →
  has_type 𝔏 ξ Γ (BinOp op e1 e2) (tbool l3).
Proof.
  intros ?? Hsub ?.
  eapply Sub_typed; last first.
  { apply type_sub_bool, Hsub. }
  rewrite -(idemp_L (⊔) l2).
  by apply BinOp_bool_typed.
Qed.


Lemma If_typed_flat' 𝔏 ξ Γ e1 e2 e3 τ :
  ξ ≠ High →
  almost_val (dom stringset Γ) e2 →
  almost_val (dom stringset Γ) e3 →
  has_type 𝔏 ξ Γ e2 τ →
  flat_type τ →
  has_type 𝔏 ξ Γ e3 τ →
  has_type 𝔏 ξ Γ e1 (tbool High) →
  has_type 𝔏 ξ Γ (if: e1 then e2 else e3) τ.
Proof.
  intros. by apply If_typed_flat.
Qed.

Lemma If_typed' 𝔏 ξ Γ e1 e2 e3 τ :
  has_type 𝔏 ξ Γ e1 (tbool Low) →
  has_type 𝔏 ξ Γ e2 τ →
  has_type 𝔏 ξ Γ e3 τ →
  has_type 𝔏 ξ Γ (if: e1 then e2 else e3) τ.
Proof.
  intros. eapply If_typed; try done. by destruct ξ.
Qed.



Existing Instance singleton_binder.
Existing Instance insert_binder.
Lemma Match_typed_flat' 𝔏 ξ Γ e t1 t2 x il τ :
  almost_val (dom stringset Γ) t1 →
  almost_val ({[x]} ∪ dom stringset Γ) t2 →
  ξ ≠ High →
  has_type 𝔏 ξ Γ e (tintoption il High) →
  has_type 𝔏 ξ Γ t1 τ →
  has_type 𝔏 ξ (<[x:=tint High]>Γ) t2 τ →
  flat_type τ →
  has_type 𝔏 ξ Γ (match: e with InjL <> => t1 | InjR x => t2 end) τ.
Proof.
  intros. by eapply Match_typed_flat.
Qed.

Lemma App_typed' 𝔏 ξ Γ e1 e2 τ τ' :
  has_type 𝔏 ξ Γ e2 τ →
  has_type 𝔏 ξ Γ e1 (τ → τ')%ty →
  has_type 𝔏 ξ Γ (App e1 e2) τ'.
Proof.
  intros. rewrite -(stamp_low τ').
  by eapply App_typed.
Qed.

Lemma Rec_typed' 𝔏 ξ Γ e f x τ τ' :
  has_type 𝔏 ξ (<[f:=(τ → τ')%ty]> (<[x:=τ]> Γ)) e τ' →
  has_type 𝔏 ξ Γ (rec: f x := e) (τ → τ').
Proof.
  intros. eapply Rec_typed.
  by rewrite stamp_low.
Qed.

Lemma insert_empty_binder (m : stringmap type) τ :
  <[<>%binder:=τ]>m = m.
Proof. by compute. Qed.

Lemma insert_string_binder (m : stringmap type) (x : string) τ :
  <[BNamed x:=τ]>m = <[x:=τ]>m.
Proof. done. Qed.

Create HintDb typed.
Hint Constructors has_type : typed.
Hint Constructors bin_op_int : typed.
Hint Constructors bin_op_bool : typed.
Hint Constructors bin_op_int_bool : typed.
Hint Constructors flat_type : typed.
Hint Constructors almost_val : typed.

Hint Extern 10 (<[_:=_]>_ !! _ = Some _) =>
  rewrite ?insert_empty_binder ?insert_string_binder ;
  eapply lookup_insert : typed.
Hint Extern 20 (<[_:=_]>_ !! _ = Some _) =>
  rewrite ?insert_empty_binder ?insert_string_binder ;
  rewrite lookup_insert_ne; last done : typed.

Hint Extern 20 (_ ∈ _) =>
  rewrite ?insert_empty_binder ?insert_string_binder ;
  (apply elem_of_union_l || apply elem_of_union_r) ;
  set_solver : typed.

Hint Extern 1 (_ ∈ dom _ _) =>
  (* rewrite ?insert_empty_binder ?insert_string_binder; *)
  apply elem_of_dom ; simplify_map_eq ; eexists ; done : typed.

Hint Extern 10 (_ ⊔ _ ⊑ _) => rewrite (left_id Low); reflexivity.
Hint Extern 10 (_ ⊔ _ ⊑ _) => rewrite (right_id Low); reflexivity.
Hint Extern 20 (_ ⊑ _) => reflexivity.

Remove Hints Sub_typed : typed.
Remove Hints BinOp_int_typed : typed.
Hint Resolve BinOp_int_typed' : typed.
Remove Hints BinOp_bool_typed : typed.
Hint Resolve BinOp_bool_typed' : typed.
Remove Hints BinOp_int_bool_typed : typed.
Hint Resolve BinOp_int_bool_typed' : typed.
Remove Hints If_typed : typed.
Hint Resolve If_typed' | 20 : typed.
Remove Hints If_typed_flat : typed.
Hint Resolve If_typed_flat' : typed.
Remove Hints Match_typed_flat : typed.
Hint Resolve Match_typed_flat' : typed.
Remove Hints App_typed : typed.
Hint Resolve App_typed' : typed.
Remove Hints Rec_typed : typed.
Hint Resolve Rec_typed' : typed.

Section typed.

  Variable 𝔏 : gset loc.
  Variable arr_t : type.
  Definition ctx : stringmap type :=
    <["get":=(arr_t → tint High → tintoption High High)%ty]>{["make":=(tunit → arr_t)%ty]}.

  Definition ctx_ Γ : stringmap type :=
    <["get":=(arr_t → tint High → tintoption High High)%ty]>(<["make":=(tunit → arr_t)%ty]>Γ).

  Lemma cap_typed Γ : has_type 𝔏 Low Γ cap (tint Low → tint Low).
  Proof.
    unfold cap. eauto 500 with typed.
  Qed.

  Lemma eq_option_typed Γ : has_type 𝔏 Low Γ eq_option
                                   (tintoption High High →
                                    tint High →
                                    tbool High).
  Proof.
    unfold eq_option. eauto 30 with typed.
  Qed.

  Lemma lte_option_typed Γ : has_type 𝔏 Low Γ lte_option
                                   (tintoption High High →
                                    tint High →
                                    tbool High).
  Proof.
    unfold lte_option. eauto 30 with typed.
  Qed.

  Hint Resolve cap_typed : typed.
  Hint Resolve eq_option_typed : typed.
  Hint Resolve lte_option_typed : typed.

  Lemma lookup_loop_typed Γ :
    Γ !! "get" = Some (arr_t → tint High → tintoption High High)%ty →
    has_type 𝔏 Low Γ lookup_loop
             (arr_t → tint Low → tint High → tint High → tint High → tbool High → tbool High).
  Proof.
    intros. unfold lookup_loop.
    repeat eapply Rec_typed'.
    eapply If_typed';[eauto 10 with typed..|].
    eapply App_typed'; first eauto 10 with typed.
    eapply Rec_typed'.
    eapply App_typed'; eauto 500 with typed.
  Qed.


End typed.
