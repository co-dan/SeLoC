(** This example demonstrates and approach to handling delimited information release in SeLoC.

It is based on the example from  "A Separation Logic for Enforcing DeclarativeInformation Flow Control Policies" by David Costanzo and Zhong Shao.
*)
From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import lang proofmode.
From iris_ni.proofmode Require Import dwp_tactics.
From iris_ni.logrel Require Import interp.
From iris_ni.examples Require Import lock.

(** The idea behind this example, is that a person A. has a calendar,
(which we model as a linked list), and each day is marked eiter with 0
(meaining that the day is free, and there are no meetings) or with a
positive integer t (meatning that there is a meeting at time t).

If someone wants to set up their appointment with A., they have to see
which days are they available. In order to do so, A. must be able to
disclose the days on which they are free, without disclosing any other
information (e.g. times of other meetings).

The program that discloses the avilablility of A. is the
`available_dates` below.

We show non-interference with a form of delimited control.
Specifically, we show that if an attacker already knows the days on
which A. is available, then the attacker cannot learn any further
information.
 *)

(* Iterate a function `f` over the linked list `hd`
   `f` is called with `f i x` where `x` is `i`-th element in the list.
 *)
Definition iter_loop : val :=
  rec: "loop" "i" "hd" "f" :=
    match: "hd" with
      NONE => #()
    | SOME "l" =>
      let: "tmp1" := Fst !"l" in
      let: "tmp2" := Snd !"l" in
      "f" "i" "tmp1";;
      "loop" ("i"+#1) "tmp2" "f"
    end.
Definition iter : val := λ: "hd" "f", iter_loop #0 "hd" "f".


Definition available_dates (out : loc) : val := λ: "cal",
  iter "cal" (λ: "i" "x", if: "x" = #0 then #out <- "i" else Skip).

(* Meta-function (macro) : create a HeapLang linked list out of a Coq list *)
Fixpoint make_llist (xs : list val) : expr :=
  match xs with
  | [] => NONE
  | (x::xs) =>
    SOME (ref (x, make_llist xs))
  end.

Section calendar.
  Context `{!heapDG Σ}.

  (* Predicate describing that `hd1` and `hd2` point to lists `xs1` and `xs2`, respectively *)
  Fixpoint is_list (hd1 : val) (hd2 : val) (xs1 xs2 : list val) : iProp Σ :=
    match xs1,xs2 with
    | [],[] => ⌜hd1 = NONEV⌝ ∗ ⌜hd2 = NONEV⌝
    | x1 :: xs1, x2 :: xs2 => ∃ (l1:loc) (l2 :loc) hd1' hd2',
         ⌜hd1 = SOMEV #l1⌝ ∗ ⌜hd2 = SOMEV #l2⌝ ∗ l1 ↦ₗ (x1,hd1') ∗ l2 ↦ᵣ (x2,hd2')
         ∗ is_list hd1' hd2' xs1 xs2
    | _, _ => False
    end%I.

  Lemma make_llist_spec (xs1 xs2 : list val) :
    length xs1 = length xs2 →
    ⊢ DWP make_llist xs1 & make_llist xs2 : λ hd1 hd2, is_list hd1 hd2 xs1 xs2.
  Proof using Type.
    revert xs2. induction xs1 as [|x1 xs1]=>xs2; simpl.
    - intros Hxs2. symmetry in Hxs2. eapply nil_length_inv in Hxs2.
      simplify_eq/=. dwp_pures.
      iApply dwp_value. eauto.
    - destruct xs2 as [|x2 xs2]; simpl.
      { inversion 1. }
      intros Hlen. simplify_eq/=.
      dwp_bind (make_llist xs1) (make_llist xs2).
      iApply (dwp_wand with "[]").
      { by iApply IHxs1. }
      iIntros (t1 t2) "Ht". dwp_pures.
      dwp_bind (ref _)%E (ref _)%E.
      iApply dwp_alloc. iIntros (hd1 hd2) "Hhd1 Hhd2". iNext.
      dwp_pures. iApply dwp_value. iModIntro.
      iExists _,_,_,_. eauto with iFrame.
  Qed.

  (* Specifications for the iter function *)
  Lemma iter_loop_spec P (i : Z) (f1 f2 :val) hd1 hd2 xs1 xs2 ξ :
    Forall2 P xs1 xs2 →
    is_list hd1 hd2 xs1 xs2 -∗
    □(∀ x1 x2 (i : Z), ⌜P x1 x2⌝ → DWP (App f1 #i x1) & (App f2 #i x2) : ⟦ tunit ⟧ ξ) -∗
    DWP iter_loop #i hd1 f1
      & iter_loop #i hd2 f2 : ⟦ tunit ⟧ ξ.
  Proof using Type.
    iIntros (Hxs) "Hlst #Hf". iRevert (Hxs).
    iLöb as "IH" forall (i hd1 hd2 xs1 xs2). iIntros (Hxs).
    dwp_rec. dwp_pures.
    destruct xs1 as [|x1 xs1], xs2 as [|x2 xs2]; iSimpl in "Hlst"; try by iExFalso.
    - iDestruct "Hlst" as "[-> ->]". dwp_pures. iApply logrel_unit.
    - iDestruct "Hlst" as (l1 l2 hd1' hd2' -> ->) "(Hl1 & Hl2 & Hlst)".
      apply Forall2_cons_1 in Hxs. destruct Hxs.
      dwp_pures. dwp_bind (! _)%E (! _)%E. iApply (dwp_load with "Hl1 Hl2"). iIntros "Hl1 Hl2". iNext.
      dwp_pures. dwp_bind (! _)%E (! _)%E. iApply (dwp_load with "Hl1 Hl2"). iIntros "Hl1 Hl2". iNext.
      dwp_pures. dwp_bind (f1 #i x1) (f2 #i x2). iApply (dwp_wand with "[Hf]").
      { iApply "Hf". iPureIntro. naive_solver. }
      iIntros (??) "_". dwp_pures.
      iApply ("IH" $! (i+1)%Z with "Hlst [%//]").
  Qed.

  Lemma iter_spec P (f1 f2 :val) hd1 hd2 xs1 xs2 ξ :
    Forall2 P xs1 xs2 →
    is_list hd1 hd2 xs1 xs2 -∗
    □(∀ x1 x2 (i : Z), ⌜P x1 x2⌝ → DWP (App f1 #i x1) & (App f2 #i x2) : ⟦ tunit ⟧ ξ) -∗
    DWP iter hd1 f1 & iter hd2 f2 : ⟦ tunit ⟧ ξ.  (* TODO: return is_list *)
  Proof using Type.
    iIntros (Hxs) "Hlst #Hf". dwp_rec. dwp_pures.
    iApply (iter_loop_spec with "Hlst Hf"); eauto.
  Qed.

  Lemma available_dates_spec (out : loc) hd1 hd2 xs1 xs2 :
    Forall2 (λ x1 x2, x1 = #0 ↔ x2 = #0) xs1 xs2 →
    ⟦ tref (tint Low) ⟧ Low #out #out -∗
    is_list hd1 hd2 xs1 xs2 -∗
    DWP available_dates out hd1 & available_dates out hd2 : ⟦ tunit ⟧ Low.
  Proof using Type.
    iIntros (HP) "#Hout Hlst". dwp_rec. dwp_pures.
    iApply (iter_spec with "Hlst [-]"); eauto.
    iModIntro. iIntros (x1 x2 i Hxs).
    dwp_pures.
    case_bool_decide; case_bool_decide; try by (exfalso; naive_solver).
    - dwp_pures.
      iApply logrel_store ; eauto; iApply dwp_value; eauto.
      iModIntro. iExists _,_. eauto.
    - dwp_pures. iApply logrel_unit.
  Qed.

End calendar.

From iris_ni Require Import program_logic.dwp_adequacy.

(* Adequacy statement *)
(* xs1 xs2 are calendars *)
Lemma available_dates_secure (out : loc) (xs1 xs2 : list val) σ1 σ2 (n : Z):
    Forall2 (λ x1 x2, x1 = #0 ↔ x2 = #0) xs1 xs2 →
    σ1.(heap) !! out = Some (Some #n) →
    σ2.(heap) !! out = Some (Some #n) →
    dwp_adequacy.R heapDΣ {[out]}
                   ([let: "hd1" := make_llist xs1 in available_dates out "hd1"]%E,σ1)
                   ([let: "hd2" := make_llist xs2 in available_dates out "hd2"]%E,σ2).
Proof using Type.
  intros Hxs Hσ1 Hσ2.
  apply tc_once. simpl.
  eapply dwp_lift_bisim_singleton; eauto.
  iIntros (HG) "Ho".
  dwp_bind (make_llist xs1) (make_llist xs2).
  iApply (dwp_wand with "[]").
  { iApply make_llist_spec. by eapply Forall2_length. }
  iIntros (hd1 hd2) "Hhd". dwp_pures.
  iApply (dwp_wand with "[-]").
  { by iApply (available_dates_spec with "Ho Hhd"). }
  iIntros (v1 v2). iDestruct 1 as "[-> ->]".
  eauto.
Qed.
