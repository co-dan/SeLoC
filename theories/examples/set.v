From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types interp.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import proofmode.
From iris_ni.proofmode Require Import dwp_tactics.
From iris.heap_lang Require Import lang array proofmode.
From iris.algebra Require Import excl.

From iris_ni.logrel Require Import typing.
From iris_ni.examples Require Import array lock.

(** aux. function for copying contents from one array to another;
   kind of like Array.blit in ocaml, but slower *)
(* copy : (arr_t → arr_t → tint Low → tunit) *)
Definition array_copy : expr := rec: "copy" "arr1" "arr2" "n" :=
  if: ("n" ≤ #0)
  then #()
  else let: "x" := "get" "arr1" "n" in
       "set" "arr2" "n" "x";;
       "copy" "arr1" "arr2" ("n"-#1).

(** The set ADT that we are implementing *)
Definition set_t : type :=
  ((tint High → tunit)
  * (tint High → tbool High))%ty.

(* cap : int Low → int Low *)
Definition cap : expr := rec: "cap" "k" :=
  if: "k" = #0
  then #0
  else #1 + #2 * ("cap" ("k" - #1)).

(* eq_option : option (int High) High → int High → bool High *)
Definition eq_option : expr := λ: "o" "v2",
  let: "w" := "v2"+#1 in (* pick something that is different from v2 *)
  let: "v1" := match: "o" with NONE => "w" | SOME "v" => "v" end in
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
       let: "elem" := "get_" "arr" "i" in
       let: "lr1" := ("i"+#1, "r") in
       let: "lr2" := ("l", "i"-#1) in
       let: "lr" := if: (lte_option "elem" "x")
                    then "lr1"
                    else "lr2" in
       let: "l" := Fst "lr" in
       let: "r" := Snd "lr" in
       let: "is_found" := BinOp OrOp "is_found" (eq_option "elem" "x") in
       "lookup_loop" "arr" ("k"-#1) "l" "r" "x" "is_found".


(* insert_loop : ref (refN (option (int high))) -> ref (int low) →
                 int low -> int low -> int high -> unit *)
Definition insert_loop : expr :=
  rec: "insert_loop" "arr_r" "k_r" "i" "sz" "x" :=
  (* sz (= cap(k)), i just goes from 0 to sz
     technically, we can recalculate sz from !k_r, but
     we just pass it directly
   *)
  if: ("sz" ≤ "i")
  then (* we need to resize the underlying array *)
    "k_r" <- !"k_r"+#1;;
    let: "arr2" := "make" (cap (!"k_r")) NONE in
    array_copy !"arr_r" "arr2" "sz";;
    "set" "arr2" "i" (SOME "x");;
    "arr_r" <- "arr2"
  else
    let: "r" := "get" (!"arr_r") "i" in
    match: "r" with
    (* the current position is availabe *)
      NONE => "set" (!"arr_r") "i" (SOME "x")
    | SOME "v" =>
       (* NB: we have to keep duplicates when inserting! otherwise
              an attacker can learn the contents of the array by
              trying to force the resize operation and see if they
              succeed. *)
       (* We also pre-allocate both tuples even though we are going to
          use only one of them . *)
      (* the first project is what we are going to insert at the current position,
         the second element is what we are going to push further in the array *)
      let: "xv" := ("x", "v") in
      let: "vx" := ("v", "x") in
      let: "pp" := if: ("x" ≤ "v") then "xv" else "vx" in
      let: "p1" := Fst "pp" in
      let: "p2" := Snd "pp" in
      "set" (!"arr_r") "i" (SOME "p1");;
      "insert_loop" "arr_r" "k_r" ("i"+#1) "sz" "p2"
    end.

(* new_set : unit → set_t *)
(* takes array functions as arguments *)
Definition new_set : expr := λ: "make" "get" "get_" "set" <>,
  let: "lk" := newlock #() in
  let: "k" := ref #1 in  (* low integer *)
  (* the size of the underlying array is always cap(k) *)
  let: "arr_r" := ref ("make" #1 NONE) in
  let: "insert" := λ: "x",
    acquire "lk";;
    insert_loop "arr_r" "k" #0 (cap !"k") "x";;
    release "lk" in
  let: "lookup" := λ: "x",
    acquire "lk";;
    let: "res" := lookup_loop (!"arr_r") (!"k") #0 (cap (!"k")) "x" #false in
    release "lk";;
    "res" in
  ("insert", "lookup").

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
  has_type 𝔏 ξ Γ (if: e1 then e2 else e3) (stamp τ High).
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
  has_type 𝔏 ξ Γ (match: e with InjL <> => t1 | InjR x => t2 end) (stamp τ High).
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

Lemma Seq_typed 𝔏 ξ Γ e1 e2 τ :
  has_type 𝔏 ξ Γ e1 tunit →
  has_type 𝔏 ξ Γ e2 τ →
  has_type 𝔏 ξ Γ (e1;; e2) τ.
Proof.
  intros. rewrite -(stamp_low τ).
  eapply App_typed; last done.
  eapply Rec_typed. rewrite stamp_low. by compute.
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
#[global] Hint Constructors has_type : typed.
#[global] Hint Constructors bin_op_int : typed.
#[global] Hint Constructors bin_op_bool : typed.
#[global] Hint Constructors bin_op_int_bool : typed.
#[global] Hint Constructors flat_type : typed.
#[global] Hint Constructors almost_val : typed.

#[global] Hint Extern 10 (<[_:=_]>_ !! _ = Some _) =>
  rewrite ?insert_empty_binder ?insert_string_binder ;
  eapply lookup_insert : typed.
#[global] Hint Extern 20 (<[_:=_]>_ !! _ = Some _) =>
  rewrite ?insert_empty_binder ?insert_string_binder ;
  rewrite lookup_insert_ne; last done : typed.

#[global] Hint Extern 20 (_ ∈ _) =>
  rewrite ?insert_empty_binder ?insert_string_binder ;
  (apply elem_of_union_l || apply elem_of_union_r) ;
  set_solver : typed.

#[global] Hint Extern 1 (_ ∈ dom _ _) =>
  (* rewrite ?insert_empty_binder ?insert_string_binder; *)
  apply elem_of_dom ; simplify_map_eq ; eexists ; done : typed.

#[global] Hint Extern 10 (_ ⊔ _ ⊑ _) => rewrite (left_id Low); reflexivity : typed.
#[global] Hint Extern 10 (_ ⊔ _ ⊑ _) => rewrite (right_id Low); reflexivity : typed.
#[global] Hint Extern 20 (_ ⊑ _) => reflexivity : typed.

#[global] Remove Hints Sub_typed : typed.
#[global] Remove Hints BinOp_int_typed : typed.
#[global] Hint Resolve BinOp_int_typed' : typed.
#[global] Remove Hints BinOp_bool_typed : typed.
#[global] Hint Resolve BinOp_bool_typed' : typed.
#[global] Remove Hints BinOp_int_bool_typed : typed.
#[global] Hint Resolve BinOp_int_bool_typed' : typed.
#[global] Remove Hints If_typed : typed.
#[global] Hint Resolve If_typed' | 20 : typed.
#[global] Remove Hints If_typed_flat : typed.
#[global] Hint Resolve If_typed_flat' : typed.
#[global] Remove Hints Match_typed_flat : typed.
#[global] Hint Resolve Match_typed_flat' : typed.
#[global] Remove Hints App_typed : typed.
#[global] Hint Resolve App_typed' : typed.
#[global] Remove Hints Rec_typed : typed.
#[global] Hint Resolve Rec_typed' : typed.

#[global] Hint Resolve Seq_typed : typed.

Section typed.

  Variable 𝔏 : gset loc.
  Variable arr_t : type.


  Lemma array_copy_typed Γ ξ :
    Γ !! "get" = Some (arr_t → tint Low → tintoption High ξ)%ty →
    Γ !! "set" = Some (arr_t → tint Low → tintoption High ξ → tunit)%ty →
    has_type 𝔏 Low Γ array_copy
      (arr_t → arr_t → tint Low → tunit)%ty.
  Proof.
    intros. unfold array_copy.
    repeat eapply Rec_typed'.
    eapply If_typed'; [eauto with typed..|].
    eapply App_typed'.
    { eapply App_typed'; eauto 20 with typed. }
    eapply Rec_typed'.
    eapply Seq_typed; last eauto 50 with typed.
    eapply App_typed'; first eauto with typed.
    eapply App_typed'; eauto 20 with typed.
  Qed.

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
  Hint Resolve array_copy_typed : typed.

  Lemma lookup_loop_typed Γ :
    Γ !! "get_" = Some (arr_t → tint High → tintoption High High)%ty →
    has_type 𝔏 Low Γ lookup_loop
             (arr_t → tint Low → tint High → tint High → tint High → tbool High → tbool High).
  Proof.
    intros. unfold lookup_loop.
    repeat eapply Rec_typed'.
    eapply If_typed';[eauto 10 with typed..|].
    eapply App_typed'; first eauto 10 with typed.
    eapply Rec_typed'.
    eapply App_typed'; first eauto 50 with typed.
    eapply Rec_typed'.
    eapply App_typed'; first eauto 50 with typed.
    eapply Rec_typed'.
    eapply App_typed'; first eauto 50 with typed.
    eapply Rec_typed'.
    eapply App_typed'.
    { eapply If_typed_flat'; try done.
      (* TODO: eauto with typed should handle this *)
      - econstructor.
        apply elem_of_dom. rewrite !insert_empty_binder.
        repeat (rewrite lookup_insert // || rewrite lookup_insert_ne //).
      - econstructor.
        apply elem_of_dom. rewrite !insert_empty_binder.
        repeat (rewrite lookup_insert // || rewrite lookup_insert_ne //).
      - eauto with typed.
      - eauto with typed.
      - eauto with typed.
      - eauto 200 with typed. }
    repeat (eapply Rec_typed';
            eapply App_typed'; first eauto 50 with typed).
    eauto 200 with typed.
  Qed.

  Lemma insert_loop_typed Γ :
    Γ !! "get" = Some (arr_t → tint Low → tintoption High Low)%ty →
    Γ !! "set" = Some (arr_t → tint Low → tintoption High Low → tunit)%ty →
    Γ !! "make" = Some (tint Low → tintoption High Low → arr_t)%ty →
    has_type 𝔏 Low Γ insert_loop
      (tref arr_t → tref (tint Low) → tint Low → tint Low → tint High → tunit)%ty.
  Proof.
    intros.
    unfold insert_loop.
    repeat eapply Rec_typed'.
    eapply If_typed';[eauto 10 with typed..|].
    - eapply Seq_typed; first eauto 20 with typed.
      eapply App_typed'.
      { eapply App_typed'; eauto 50 with typed. }
      eapply Rec_typed'.
      eapply Seq_typed.
      { repeat (eapply App_typed'; first eauto 20 with typed).
        eapply array_copy_typed; eauto 20 with typed. }
      eapply Seq_typed.
      { eapply App_typed'; first eauto 50 with typed.
        eapply App_typed'; eauto 50 with typed. }
      eauto 50 with typed.
    - eapply App_typed'; first by eauto 100 with typed.
      eapply Rec_typed'.
      eapply Match_typed; first by eauto with typed.
      { eapply App_typed'; first by eauto with typed.
        eapply App_typed'; eauto 50 with typed. }
      eapply App_typed'; first by eauto 50 with typed.
      eapply Rec_typed'.
      eapply App_typed'; first eauto 50 with typed.
      eapply Rec_typed'.
      eapply App_typed'.
      { eapply If_typed_flat'; try done.
      (* TODO: eauto with typed should handle this *)
        - econstructor.
          apply elem_of_dom. rewrite !insert_empty_binder.
          repeat (rewrite lookup_insert // || rewrite lookup_insert_ne //).
        - econstructor.
          apply elem_of_dom. rewrite !insert_empty_binder.
          repeat (rewrite lookup_insert // || rewrite lookup_insert_ne //).
        - eauto with typed.
        - eauto with typed.
        - eauto with typed.
        - eauto 200 with typed. }
      eapply Rec_typed'.
      eapply App_typed'; first eauto 50 with typed.
      eapply Rec_typed'.
      eapply App_typed'; first eauto 50 with typed.
      eapply Rec_typed'.
      eapply Seq_typed.
      + eapply App_typed'; first eauto with typed.
        eapply App_typed'; eauto 50 with typed.
      + eauto 100 with typed.
  Qed.

  Hint Resolve insert_loop_typed : typed.
  Hint Resolve lookup_loop_typed : typed.

  Lemma new_set_typed Γ :
    has_type 𝔏 Low Γ new_set
    ((* make *) (tint Low → tintoption High Low → arr_t) →
     (* get *) (arr_t → tint Low → tintoption High Low) →
     (* get_ *) (arr_t → tint High → tintoption High High) →
     (* set *) (arr_t → tint Low → tintoption High Low → tunit) →
     tunit → set_t)%ty.
  Proof.
    unfold new_set.
    repeat eapply Rec_typed'.
    eapply App_typed'; first by eauto with typed.
    eapply Rec_typed'.
    eapply App_typed'; first by eauto with typed.
    eapply Rec_typed'.
    eapply App_typed'; first by eauto 50 with typed.
    eapply Rec_typed'.
    eapply App_typed'.
    { eapply Rec_typed'.
      eapply Seq_typed; first by eauto 50 with typed.
      eapply Seq_typed; last by eauto 50 with typed.
      eapply App_typed'; first by eauto 50 with typed.
      eapply App_typed'; first by eauto 50 with typed.
      eapply App_typed'; first by eauto 50 with typed.
      eapply App_typed'; first by eauto 50 with typed.
      eapply App_typed'; first by eauto 50 with typed.
      eapply insert_loop_typed; eauto 50 with typed. }
    eapply Rec_typed'.
    eapply App_typed'.
    { eapply Rec_typed'.
      eapply Seq_typed; first by eauto 50 with typed.
      eapply App_typed'; last by eauto 50 with typed.
      eapply App_typed'; first by eauto 50 with typed.
      eapply App_typed'; first by eauto 50 with typed.
      eapply App_typed'.
      { eapply Sub_typed. (*XXX*)
        - eauto 50 with typed.
        - apply (type_sub_int _ High). done. }
      eapply App_typed'; first by eauto 50 with typed.
      eapply App_typed'; first by eauto 50 with typed.
      eapply App_typed'; first by eauto 50 with typed.
      eapply lookup_loop_typed; eauto 50 with typed. }
    eauto 200 with typed.
  Qed.

End typed.

Section composed.
  Context `{!heapDG Σ}.

  Opaque new_set array.make array.get array.set.
  (* so that simpl subst doesn't go through *)

  Definition arr_t :=
    ((tint High → tintoption High High)
    * (tint Low → tintoption High Low)
    * (tint Low → tintoption High Low → tunit))%ty.

  (** The next two lemmas show that we can store terms of the
  [tintoption High Low] type in the arrays *)
  Lemma option_pseudo_refl :
    pseudo_refl ⟦ tintoption High High ⟧ Low.
  Proof.
    rewrite (interp_eq (tintoption _ _)).
    iIntros (o1 o2). iDestruct 1 as "[_ Hv]".
    iSpecialize ("Hv" with "[]").
    { iPureIntro. naive_solver. }
    iDestruct "Hv" as "[Hv1 Hv2]".
    iDestruct "Hv1" as "[-> | Hv1]";
      iDestruct "Hv2" as "[-> | Hv2]".
    - iSplit; iSplit; iIntros (Hi); try by (exfalso ; naive_solver).
      + iSplit; iLeft; eauto.
      + iSplit; iLeft; eauto.
    - iDestruct "Hv2" as (v2 ->) "#H".
      iSplit; iSplit; iIntros (Hi); try by (exfalso ; naive_solver).
      + iSplit; iLeft; eauto.
      + iSplit; iRight; iExists _; eauto with iFrame.
    - iDestruct "Hv1" as (v1 ->) "#H".
      iSplit; iSplit; iIntros (Hi); try by (exfalso ; naive_solver).
      + iSplit; iRight; iExists _; eauto with iFrame.
      + iSplit; iLeft; eauto.
    - iDestruct "Hv1" as (v1 ->) "#H1".
      iDestruct "Hv2" as (v2 ->) "#H2".
      iSplit; iSplit; iIntros (Hi); try by (exfalso ; naive_solver).
      + iSplit; iRight; iExists _; eauto with iFrame.
      + iSplit; iRight; iExists _; eauto with iFrame.
  Qed.
  Lemma option_contractible :
    contractible ⟦ tintoption High High ⟧ Low.
  Proof.
    rewrite (interp_eq (tintoption _ _)).
    iIntros (o1 o2) "[H1 H2]".
    iDestruct "H1" as "[_ H1]".
    iSpecialize ("H1" with "[]").
    { naive_solver. }
    iDestruct "H2" as "[_ H2]".
    iSpecialize ("H2" with "[]").
    { naive_solver. }
    iDestruct "H1" as "[[-> | H1] H1']";
      iDestruct "H2" as "[[-> | H2] H2']".
    - iSplit; iIntros (Hi); try by (exfalso ; naive_solver).
      iSplit; iLeft; eauto.
    - iSplit; iIntros (Hi); try by (exfalso ; naive_solver).
      iDestruct "H2" as (v2 ->) "H2".
      iSplit.
      + iLeft; eauto.
      + iRight. iExists _; eauto with iFrame.
    - iSplit; iIntros (Hi); try by (exfalso ; naive_solver).
      iDestruct "H1" as (v2 ->) "H1".
      iSplit.
      + iRight. iExists _; eauto with iFrame.
      + iLeft; eauto.
    - iSplit; iIntros (Hi); try by (exfalso ; naive_solver).
      iDestruct "H1" as (v1 ->) "H1".
      iDestruct "H2" as (v2 ->) "H2".
      iSplit; iRight; iExists _; eauto with iFrame.
  Qed.

  Definition make : val := λ: "sz" "dummy",
    let: "a" := array.make "sz" "dummy" in
    (λ: "i", array.get "a" "i",
     λ: "i", array.get "a" "i",
     λ: "i" "x", array.set "a" "i" "x").

  Definition get_ : val := λ: "x", Fst (Fst "x").
  Definition get : val := λ: "x", Snd (Fst "x").
  Definition set : val := λ: "x", Snd "x".

  Lemma make_typed :
    ⊢ DWP make & make : ⟦ tint Low → tintoption High Low → arr_t ⟧ Low.
  Proof.
    iApply dwp_value. iModIntro.
    rewrite interp_eq. iModIntro.
    iIntros (? ?). iDestruct 1 as (sz0 sz -> ->) "%".
    assert (sz0 = sz) as -> by eauto.
    dwp_rec. dwp_pures.
    iApply dwp_value. iModIntro.
    rewrite (interp_eq (tarrow _ _ _)). iModIntro.
    iIntros (d1 d2) "#Hd".
    dwp_rec. dwp_bind (array.make _ _) (array.make _ _).
    iApply dwp_wand.
    { iApply (make_spec with "Hd"). }
    iIntros (a1 a2) "#Ha".
    dwp_pures. iApply dwp_value.
    iModIntro. rewrite (interp_eq (tprod _ _)).
    iExists _,_,_,_. repeat iSplit; eauto.
    rewrite (interp_eq (tprod _ _)).
    iExists _,_,_,_. repeat iSplit; eauto.
    - rewrite (interp_eq (tarrow _ _ _)).
      iModIntro. iIntros (v1 v2) "#Hv". dwp_pures.
      rewrite !right_id.
      (* rewrite (interp_sub_mono (tintoption High Low) (tintoption High High)); last by constructor. *)
      iApply (get_spec with "Ha"); eauto with iFrame;
        simpl; rewrite left_id.
      apply option_pseudo_refl.
      apply option_contractible.
    - rewrite (interp_eq (tarrow _ _ _)).
      iModIntro. iIntros (v1 v2) "#Hv". dwp_pures.
      rewrite !right_id.
      iApply get_spec_low; eauto.
    - rewrite (interp_eq (tarrow _ _ _)).
      iModIntro. iIntros (v1 v2) "#Hv". dwp_pures.
      iApply dwp_value. iModIntro.
      rewrite (interp_eq (tarrow _ _ _)).
      iModIntro. iIntros (w1 w2) "#Hw". dwp_pures.
      iApply set_spec_low; eauto.
  Qed.

  Lemma get_typed :
    ⊢ DWP get & get : ⟦ arr_t → tint Low → tintoption High Low ⟧ Low.
  Proof.
    iApply dwp_value. iModIntro.
    rewrite interp_eq. iModIntro.
    iIntros (a1 a2). rewrite /arr_t interp_eq.
    iDestruct 1 as (r1 r2 set1 set2 -> ->) "[H Hset]".
    iDestruct "H" as (get_1 get_2 get1 get2 -> ->) "[Hget_ Hget]".
    dwp_rec. dwp_pures. iApply dwp_value.
    iApply "Hget".
  Qed.

  Lemma get__typed :
    ⊢ DWP get_ & get_ : ⟦ arr_t → tint High → tintoption High High ⟧ Low.
  Proof.
    iApply dwp_value. iModIntro.
    rewrite interp_eq. iModIntro.
    iIntros (a1 a2). rewrite /arr_t interp_eq.
    iDestruct 1 as (r1 r2 set1 set2 -> ->) "[H Hset]".
    iDestruct "H" as (get_1 get_2 get1 get2 -> ->) "[Hget_ Hget]".
    dwp_rec. dwp_pures. iApply dwp_value.
    iApply "Hget_".
  Qed.

  Lemma set_typed :
    ⊢ DWP set & set : ⟦ arr_t → tint Low → tintoption High Low → tunit ⟧ Low.
  Proof.
    iApply dwp_value. iModIntro.
    rewrite interp_eq. iModIntro.
    iIntros (a1 a2). rewrite /arr_t interp_eq.
    iDestruct 1 as (r1 r2 set1 set2 -> ->) "[H Hset]".
    iDestruct "H" as (get_1 get_2 get1 get2 -> ->) "[Hget_ Hget]".
    dwp_rec. dwp_pures. iApply dwp_value.
    iApply "Hset".
  Qed.

  Lemma new_set_composed_typed 𝔏 Γ :
    sem_typed 𝔏 Low Γ
        (new_set
         make get get_ set)
        (tunit → set_t).
  Proof.
    iIntros (γ) "#HΓ #Hout".
    rewrite /subst_valid.
    iDestruct (big_sepM2_dom with "HΓ") as %Hdom.
    simpl.
    rewrite -(stamp_low (_ → set_t)%ty).
    iApply logrel_app; last first.
    { iApply set_typed. }
    rewrite -(stamp_low (_ → _ → set_t)%ty).
    iApply logrel_app; last first.
    { iApply get__typed. }
    rewrite -(stamp_low (_ → _ → _ → set_t)%ty).
    iApply logrel_app; last first.
    { iApply get_typed. }
    rewrite -(stamp_low (_ → _ → _ → _ → set_t)%ty).
    iApply logrel_app; last first.
    { iApply make_typed. }
    iApply fundamental;
      first apply new_set_typed; eauto.
  Qed.

End composed.
