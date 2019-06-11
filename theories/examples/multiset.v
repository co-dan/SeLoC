From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang proofmode.
From iris_ni.proofmode Require Import dwp_tactics.
From iris_ni.logrel Require Import typemap interp.
From iris_ni.examples Require Import lock.

Definition cons : val := λ: "hd" "tl", SOME ("hd", "tl").
Definition nil : val := NONEV.

Definition list_match : val := λ: "ls" "f" "g",
  match: "ls" with
    NONE     => "f" #()
  | SOME "x" =>
    let: "hd" := Fst "x" in
    let: "tl" := Snd "x" in
    "g" "hd" "tl"
  end.

Definition insert_high : val := λ: "ls" "v",
  cons ("v", #true) "ls".

Definition insert_low : val := rec: "insert" "ls" "v" :=
  list_match
    "ls"
    (λ: <>, cons "v" nil)
    (λ: "hd" "tl", let: "sensitivity" := Snd "hd" in
                   let: "hd" := Fst "hd" in
                   if: "sensitivity"
                   (* If we are still in the high security part of the list *)
                   then "insert" "tl" "v"
                   else if: "v" ≤ "hd"
                        then cons ("v", #false) "ls"
                        else "insert" "tl" "v").

Definition size : val := λ: "ls",
  let: "loop" :=
     (rec: "loop" "ls" "n" :=
          list_match
            "ls"
            (λ: <>, "n")
            (λ: "hd" "tl", "loop" "tl" ("n"+#1))) in
  "loop" "ls" #0.

Fixpoint is_list (hd : val) (xs : list val) : Prop :=
  match xs with
  | [] => hd = NONEV
  | x :: xs => ∃ hd', hd = SOMEV (x,hd') ∧ is_list hd' xs
  end.

(* Two specifications/invariants:
   1. we can insert arbitrary elements into the list, only length is secure.
   2. we can insert only low security elements into the list, then lookup is also sequre *)

Section proof.
  Context `{!heapDG Σ, !typemapG (loc*loc) Σ, !lockG Σ}.

  Definition cell_rel (v1 v2 : val) (ξ : slevel) : iProp Σ :=
    (∃ (w1 w2 : val) (b : bool),
        ⌜v1 = (w1, #b)%V⌝ ∗ ⌜v2 = (w2, #b)%V⌝ ∗
        ⟦ tint (if b then High else Low) ⟧ ξ w1 w2)%I.

  Definition ls_inv (l1 l2 : loc) (ξ : slevel) :=
    (∃ hd1 hd2 (xs1 xs2 : list val), l1 ↦ₗ hd1 ∗ l2 ↦ᵣ hd2 ∗
                        ([∗ list] v1; v2 ∈ xs1;xs2, cell_rel v1 v2 ξ) ∗
                        ⌜is_list hd1 xs1⌝ ∗ ⌜is_list hd2 xs2⌝ ∗
                        ⌜length xs1 = length xs2⌝)%I.


  Lemma insert_high_spec l1 l2 v1 v2 ξ Φ :
    ls_inv l1 l2 ξ -∗
    ⟦ tint High ⟧ ξ v1 v2 -∗
    ▷ (ls_inv l1 l2 ξ -∗ Φ #() #()) -∗
    DWP #l1 <- insert_high !#l1 v1 &
        #l2 <- insert_high !#l2 v2 : Φ.
  Proof.
    iDestruct 1 as (hd1 hd2 xs1 xs2) "(Hl1 & Hl2 & Hvs & #Hr)".
    iIntros "#Hvv HΦ".
    dwp_bind (! _)%E (! _)%E. iApply (dwp_load with "Hl1 Hl2").
    iNext. iIntros "[Hl1 Hl2]".
    dwp_bind (insert_high _ v1) (insert_high _ v2).
    dwp_rec. dwp_pures. dwp_rec.
    dwp_pures. iApply dwp_value.
    iModIntro.
    iApply (heap_lang_lifting.dwp_store with "Hl1 Hl2").
    iIntros "Hl1 Hl2". iNext. iApply "HΦ".
    iExists _,_,((v1,#true)%V::xs1),((v2,#true)%V::xs2). iFrame.
    iSplitL.
    { iExists _,_,true. iFrame "Hvv". eauto with iFrame. }
    iDestruct "Hr" as %[Hxs1 [Hxs2 Hlen]].
    repeat iSplit; iPureIntro; naive_solver.
  Qed.

  Lemma size_spec l1 l2 ξ Φ :
    ls_inv l1 l2 ξ -∗
    ▷ (∀ v1 v2, ⟦ tint Low ⟧ ξ v1 v2 -∗ ls_inv l1 l2 ξ -∗ Φ v1 v2) -∗
    DWP size !#l1 & size !#l2 : Φ.
  Proof.
    iDestruct 1 as (hd1 hd2 xs1 xs2) "(Hl1 & Hl2 & Hvs & #Hr)".
    iIntros "HΦ".
    dwp_bind (! _)%E (! _)%E. iApply (dwp_load with "Hl1 Hl2").
    iNext. iIntros "[Hl1 Hl2]".
    iAssert (∀ v1 v2, ⟦ tint Low ⟧ ξ v1 v2 -∗ Φ v1 v2)%I with "[HΦ Hvs Hl1 Hl2]" as "HΦ".
    { iIntros (v1 v2) "H". iApply ("HΦ" with "H").
      iExists _,_,_,_. by iFrame. }
    dwp_rec. dwp_pure _ _=>/=. dwp_pure _ _=>/=. dwp_pure _ _=>/=.
    generalize 0. intros n. dwp_pures.
    iRevert "Hr". iLöb as "IH" forall (n hd1 hd2 xs1 xs2).
    iIntros "#Hr". iDestruct "Hr" as %[Hxs1 [Hxs2 Hlen]].
    dwp_rec. dwp_pures.
    destruct xs1 as [|x1 xs1'].
    - assert (xs2 = []) as ->.
      { destruct xs2; naive_solver. }
      rewrite Hxs1 Hxs2.
      dwp_pures. iApply dwp_value. iModIntro. iApply "HΦ".
      iExists n,n. eauto with iFrame.
    - assert (∃ x2 xs2', xs2 = x2::xs2') as [x2 [xs2' ->]].
      { destruct xs2; naive_solver. }
      simpl in Hxs1, Hxs2.
      destruct Hxs1 as [hd1' [-> Hhd1']].
      destruct Hxs2 as [hd2' [-> Hhd2']].
      dwp_pures.
      iApply ("IH" $! (n+1) with "HΦ").
      iAlways. repeat iSplit; eauto with iFrame.
  Qed.

End proof.
