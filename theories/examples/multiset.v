From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang proofmode.
From iris_ni.proofmode Require Import dwp_tactics.
From iris_ni.logrel Require Import typemap interp.
From iris_ni.examples Require Import lock.

(*
    type node = NONE | SOME int*list
and type list = ref node
*)

Definition cons : val := λ: "v" "tl",
   ref (SOME ("v", "tl")).
Definition nil : expr := ref NONEV.

Definition insert_unordered : val := λ: "hd" "v",
  "hd" <- SOME ("v", ref !"hd").

Definition insert_loop : val := rec: "loop" "hd" "v" :=
  match: !"hd" with
    NONE => "hd" <- SOME ("v", nil)
  | SOME "x" =>
    let: "w" := Fst "x" in
    let: "tl" := Snd "x" in
    if: "w" ≤ "v"
    then "hd" <- SOME ("v", ref (SOME ("w", "tl")))
    else "loop" "hd" "v"
  end.

Definition insert_ordered : val := λ: "hd" "v",
  insert_loop "hd" "v".

Definition insert : val := λ: "l" "v" "f",
  let: "x" := !"l" in
  let: "l-high" := Fst "x" in
  let: "l-low" := Snd "x" in
  if: "f"
  then insert_unordered "l-high" "v"
  else insert_ordered "l-low" "v".

Definition size_loop : val := rec: "loop" "hd" "n" :=
  match: !"hd" with
    NONE => "n"
  | SOME "x" =>
    let: "tl" := Snd "x" in
    "loop" "tl" ("n"+#1)
  end.

Definition size : val := λ: "l",
  let: "x" := !"l" in
  let: "l-high" := Fst "x" in
  let: "l-low" := Snd "x" in
  size_loop "l-low" #0 + size_loop "l-high" #0.

Definition new_ms : val := λ: <>,
  let: "hs" := ref NONE in
  let: "ls" := ref NONE in
  let: "ms" := ref ("hs", "ls") in
  let: "lk" := newlock #() in
  let: "insert" := λ: "v" "b",
    acquire "lk";; insert "ms" "v" "b";; release "lk"
  in
  let: "size" := λ: <>,
    acquire "lk";; let: "n" := size "ms" in release "lk";; "n"
  in ("insert", "size").

Section proof.
  Context `{!heapDG Σ, !typemapG (loc*loc) Σ, !lockG Σ}.

  Program Definition joint_list_pre (P : val -> val -> iProp Σ) :
    (locC -n> locC -n> iProp Σ) -n> (locC -n> locC -n> iProp Σ)
    := (λne R hd1 hd2,
        (hd1 ↦ₗ NONEV ∗ hd2 ↦ᵣ NONEV)
       ∨ (∃ v1 v2 (tl1 tl2 : loc), hd1 ↦ₗ SOMEV (v1, #tl1) ∗
                           hd2 ↦ᵣ SOMEV (v2, #tl2) ∗
                           P v1 v2 ∗
                           ▷ (R tl1 tl2)))%I.
  Next Obligation. solve_proper. Qed.

  Instance joint_list_pre_contractive P : Contractive (joint_list_pre P).
  Proof. solve_contractive. Qed.

  Definition joint_list P := fixpoint (joint_list_pre P).
  Lemma joint_list_unfold P hd1 hd2 :
    joint_list P hd1 hd2 ≡
       ((hd1 ↦ₗ NONEV ∗ hd2 ↦ᵣ NONEV)
       ∨ (∃ v1 v2 (tl1 tl2 : loc), hd1 ↦ₗ SOMEV (v1, #tl1) ∗
                           hd2 ↦ᵣ SOMEV (v2, #tl2) ∗
                           P v1 v2 ∗
                           ▷ (joint_list P tl1 tl2)))%I.
  Proof.
    rewrite {1}/joint_list.
    transitivity (joint_list_pre P (fixpoint (joint_list_pre P)) hd1 hd2).
    { f_equiv. f_equiv. apply fixpoint_unfold. }
    reflexivity.
  Qed.

  Definition sec_list (hd1 hd2 : loc) (l ξ : slevel) :=
    (joint_list (⟦ tint l ⟧ ξ) hd1 hd2)%I.

  Definition ls_inv (l1 l2 : loc) (ξ : slevel) :=
    (∃ (hdh1 hdh2 hdl1 hdl2 : loc),
        l1 ↦ₗ (#hdh1, #hdl1) ∗ l2 ↦ᵣ (#hdh2, #hdl2) ∗
        sec_list hdh1 hdh2 High ξ ∗
        sec_list hdl1 hdl2 Low ξ)%I.

  Lemma insert_unordered_spec (hd1 hd2 : loc) v1 v2 ξ Φ :
    ⟦ tint High ⟧ ξ v1 v2 -∗
    sec_list hd1 hd2 High ξ -∗
    ▷ (sec_list hd1 hd2 High ξ -∗ Φ #() #()) -∗
    DWP insert_unordered #hd1 v1
      & insert_unordered #hd2 v2 : Φ.
  Proof.
    iIntros "#Hvv Hls HΦ".
    dwp_rec. dwp_pures.
    dwp_pures. rewrite {1}/sec_list joint_list_unfold.
    dwp_bind (! _)%E (! _)%E.
    iDestruct "Hls" as "[[Hhd1 Hhd2]|Hls]".
    - iApply (heap_lang_lifting.dwp_load with "Hhd1 Hhd2").
      iNext. iIntros "[Hhd1 Hhd2]".

      dwp_pures. dwp_bind (ref _)%E (ref _)%E.
      iApply heap_lang_lifting.dwp_alloc.
      iIntros (nil1 nil2) "Hnil1 Hnil2". iNext.

      dwp_pures. iApply (heap_lang_lifting.dwp_store with "Hhd1 Hhd2").
      iIntros "Hhd1 Hhd2". iNext.

      iApply "HΦ". rewrite /sec_list.
      rewrite joint_list_unfold.
      iRight. iExists _,_,_,_. iFrame "Hhd1 Hhd2 Hvv".
      iNext. rewrite joint_list_unfold.
      iLeft; by iFrame.
    - iDestruct "Hls" as (w1 w2 tl1 tl2) "(Hhd1 & Hhd2 & #Hww & Hls)".
      iApply (heap_lang_lifting.dwp_load with "Hhd1 Hhd2").
      iNext. iIntros "[Hhd1 Hhd2]".

      dwp_pures. dwp_bind (ref _)%E (ref _)%E.
      iApply heap_lang_lifting.dwp_alloc.
      iIntros (hd1' hd2') "Hhd1' Hhd2'". iNext.

      dwp_pures. iApply (heap_lang_lifting.dwp_store with "Hhd1 Hhd2").
      iIntros "Hhd1 Hhd2". iNext.

      iApply "HΦ". rewrite /sec_list.
      rewrite (joint_list_unfold _ hd1 hd2).
      iRight. iExists _,_,_,_. iFrame "Hhd1 Hhd2 Hvv".
      iNext. rewrite (joint_list_unfold _ hd1').
      iRight. iExists _,_,_,_. by iFrame.
  Qed.

  Lemma insert_ordered_spec (hd1 hd2 : loc) v1 v2 ξ Φ :
    ⟦ tint Low ⟧ ξ v1 v2 -∗
    sec_list hd1 hd2 Low ξ -∗
    ▷ (sec_list hd1 hd2 Low ξ -∗ Φ #() #()) -∗
    DWP insert_ordered #hd1 v1
      & insert_ordered #hd2 v2 : Φ.
  Proof.
    iIntros "#Hvv Hls HΦ".
    dwp_rec. dwp_pures.
    iLöb as "IH" forall (hd1 hd2).
    dwp_rec. dwp_pures.
    dwp_bind (! _)%E (! _)%E.
    rewrite {1}/(sec_list hd1 hd2) joint_list_unfold.
    iDestruct "Hls" as "[[Hhd1 Hhd2]|Hls]".
    - iApply (heap_lang_lifting.dwp_load with "Hhd1 Hhd2").
      iNext. iIntros "[Hhd1 Hhd2]".

      dwp_pures. dwp_bind (ref (InjLV #()))%E (ref (InjLV #()))%E.
      iApply heap_lang_lifting.dwp_alloc.
      iIntros (nil1 nil2) "Hnil1 Hnil2". iNext.

      dwp_pures. iApply (heap_lang_lifting.dwp_store with "Hhd1 Hhd2").
      iIntros "Hhd1 Hhd2". iNext.

      iApply "HΦ". rewrite /sec_list.
      rewrite joint_list_unfold.
      iRight. iExists _,_,_,_. iFrame "Hhd1 Hhd2 Hvv".
      iNext. rewrite joint_list_unfold.
      iLeft; by iFrame.
    - iDestruct "Hls" as (w1 w2 tl1 tl2) "(Hhd1 & Hhd2 & #Hww & Hls)".
      iApply (heap_lang_lifting.dwp_load with "Hhd1 Hhd2").
      iNext. iIntros "[Hhd1 Hhd2]".

      dwp_pures.

      (* w1 w2, v1 v2 are integers *)
      iDestruct "Hww" as (? w -> ->) "H".
      iDestruct "H" as %Hw.
      assert (Low ⊑ ξ) as Hξ.
      { by destruct ξ. }
      rewrite (Hw Hξ).
      iDestruct "Hvv" as (? v -> ->) "H".
      iDestruct "H" as %Hv.
      rewrite (Hv Hξ).
      (* now we can continue symbolic execution *)

      dwp_pures. case_bool_decide; dwp_pures.
      + (* Insert the element here *)
        dwp_bind (ref _)%E (ref _)%E.
        iApply heap_lang_lifting.dwp_alloc.
        iIntros (hd1' hd2') "Hhd1' Hhd2'". iNext.

        dwp_pures. iApply (heap_lang_lifting.dwp_store with "Hhd1 Hhd2").
        iIntros "Hhd1 Hhd2". iNext.

        iApply "HΦ". rewrite /sec_list.
        rewrite (joint_list_unfold _ hd1 hd2).
        iRight. iExists _,_,_,_. iFrame "Hhd1 Hhd2".
        iSplitR.
        { iExists _,_. eauto with iFrame. }
        iNext. rewrite (joint_list_unfold _ hd1' hd2').
        iRight. iExists _,_,_,_. iFrame "Hhd1' Hhd2' Hls".
        iExists _,_. eauto with iFrame.
      + (* Continue with the recursion. *)
        iApply ("IH" with "[-HΦ] HΦ").
        rewrite /sec_list (joint_list_unfold _ hd1 hd2).
        iRight. iExists _,_,_,_. iFrame.
        iExists _. eauto with iFrame.
  Qed.

  (* TODO: Question: can the b's here be different? *)
  Lemma insert_spec l1 l2 v1 v2 (b : bool) ξ Φ :
    ls_inv l1 l2 ξ -∗
    ⟦ tint (if b then High else Low) ⟧ ξ v1 v2 -∗
    ▷ (ls_inv l1 l2 ξ -∗ Φ #() #()) -∗
    DWP insert #l1 v1 #b & insert #l2 v2 #b : Φ.
  Proof.
    iDestruct 1 as (hdh1 hdh2 hdl1 hdl2) "(Hl1 & Hl2 & Hhs & Hls)".
    iIntros "#Hvv HΦ".

    dwp_rec. dwp_pures.
    dwp_bind (! _)%E (! _)%E. iApply (dwp_load with "Hl1 Hl2").
    iNext. iIntros "[Hl1 Hl2]".

    dwp_pures. destruct b; dwp_pures.
    - (* High-security *)
      iApply (insert_unordered_spec with "Hvv Hhs").
      iNext. iIntros "Hhs". iApply "HΦ".
      iExists _,_,_,_. iFrame.
    - (* Low-security *)
      iApply (insert_ordered_spec with "Hvv Hls").
      iNext. iIntros "Hls". iApply "HΦ".
      iExists _,_,_,_. iFrame.
  Qed.

  (* TODO: move to logrel/interp.v *)
  Lemma dwp_binop e1 e2 t1 t2 l ξ :
    (DWP e1 & e2 : ⟦ tint l ⟧ ξ) -∗
    (DWP t1 & t2 : ⟦ tint l ⟧ ξ) -∗
    DWP e1 + t1 & e2 + t2 : ⟦ tint l ⟧ ξ.
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
    iExists _,_. iPureIntro. naive_solver.
  Qed.

  Lemma size_loop_spec (hd1 hd2 : loc) n1 n2 l ξ Φ :
    ⟦ tint Low ⟧ ξ n1 n2 -∗
    sec_list hd1 hd2 l ξ -∗
    (∀ v1 v2, sec_list hd1 hd2 l ξ -∗ ⟦ tint Low ⟧ ξ v1 v2 -∗ Φ v1 v2) -∗
    DWP size_loop #hd1 n1 & size_loop #hd2 n2 : Φ.
  Proof.
    iIntros "Hns Hls HΦ".
    iLöb as "IH" forall (n1 n2 hd1 hd2).
    iDestruct "Hns" as "#Hns". dwp_rec. dwp_pures.
    dwp_bind (! _)%E (! _)%E.
    rewrite {1}/(sec_list hd1 hd2) (joint_list_unfold _ hd1 hd2).
    iDestruct "Hls" as "[[Hhd1 Hhd2]|Hls]".
    - iApply (heap_lang_lifting.dwp_load with "Hhd1 Hhd2").
      iNext. iIntros "[Hhd1 Hhd2]".

      dwp_pures. iApply dwp_value.
      iModIntro. iApply ("HΦ" with "[-Hns] Hns").
      iClear "IH". rewrite /sec_list joint_list_unfold.
      iLeft. by iFrame.
    - iDestruct "Hls" as (w1 w2 tl1 tl2) "(Hhd1 & Hhd2 & #Hww & Hls)".
      iApply (heap_lang_lifting.dwp_load with "Hhd1 Hhd2").
      iNext. iIntros "[Hhd1 Hhd2]".
      dwp_pures.

      dwp_bind (_ + _)%E (_ + _)%E.
      iApply dwp_wand.
      { iApply dwp_binop; iApply dwp_value; first by iFrame.
        iModIntro. iExists _; eauto with iFrame. }

      iIntros (z1 z2) "Hz".
      iApply ("IH" with "Hz Hls [-]").
      iClear "IH". iIntros (v1 v2) "Hls Hvv".
      iApply ("HΦ" with "[-Hvv] Hvv").
      rewrite /sec_list (joint_list_unfold _ hd1 hd2).
      iRight. iExists _,_,_,_. by iFrame.
  Qed.

  Lemma size_spec l1 l2 ξ Φ :
    ls_inv l1 l2 ξ -∗
    ▷ (∀ v1 v2, ⟦ tint Low ⟧ ξ v1 v2 -∗ ls_inv l1 l2 ξ -∗ Φ v1 v2) -∗
    DWP size #l1 & size #l2 : Φ.
  Proof.
    iDestruct 1 as (hdh1 hdh2 hdl1 hdl2) "(Hl1 & Hl2 & Hhs & Hls)".
    iIntros "HΦ".
    dwp_rec.
    dwp_bind (! _)%E (! _)%E. iApply (dwp_load with "Hl1 Hl2").
    iNext. iIntros "[Hl1 Hl2]".

    dwp_pures. dwp_bind (size_loop _ _) (size_loop _ _).
    iApply (size_loop_spec with "[] Hhs").
    { iExists _; eauto with iFrame. }
    iIntros (n1 n2) "Hhs #Hn".

    dwp_bind (size_loop _ _) (size_loop _ _).
    iApply (size_loop_spec with "[] Hls").
    { iExists _; eauto with iFrame. }
    iIntros (m1 m2) "Hls #Hm".

    iApply dwp_wand.
    { iApply dwp_binop; iApply dwp_value; eauto with iFrame. }

    iIntros (z1 z2) "Hz".
    iApply ("HΦ" with "Hz [-]").
    iExists _,_,_,_. by iFrame "Hl1 Hl2 Hhs Hls".
  Qed.

  Lemma multiset_spec ξ Φ :
    (∀ (ins1 ins2 siz1 siz2 : val),
        □ (∀ (b: bool) v1 v2,
           ⟦ tint (if b then High else Low) ⟧ ξ v1 v2 -∗
           DWP ins1 v1 #b & ins2 v2 #b : ⟦ tunit ⟧ ξ) -∗
        ⟦ tarrow tunit (tint Low) Low ⟧ ξ siz1 siz2 -∗
        Φ (ins1, siz1)%V (ins2, siz2)%V) -∗
    DWP new_ms #() & new_ms #() : Φ.
  Proof.
    iIntros "HΦ".
    dwp_rec. dwp_pures.
    dwp_bind (ref _)%E (ref _)%E.
    iApply heap_lang_lifting.dwp_alloc.
    iIntros (hs1 hs2) "Hhs1 Hhs2". iNext.

    dwp_pures. dwp_bind (ref _)%E (ref _)%E.
    iApply heap_lang_lifting.dwp_alloc.
    iIntros (ls1 ls2) "Hls1 Hls2". iNext.

    dwp_pures. dwp_bind (ref _)%E (ref _)%E.
    iApply heap_lang_lifting.dwp_alloc.
    iIntros (ms1 ms2) "Hms1 Hms2". iNext.

    dwp_pures. dwp_bind (newlock _) (newlock _).
    pose (N:=nroot.@"あ").
    iApply (newlock_spec N (ls_inv ms1 ms2 ξ) with "[-HΦ]").
    { iExists _,_,_,_. iFrame.
      iSplitL "Hhs1 Hhs2";
      rewrite /sec_list joint_list_unfold; iLeft; by iFrame. }
    iIntros (γ lk1 lk2) "#Hlock".

    dwp_pures. iApply dwp_value. iModIntro.
    iApply "HΦ".
    - iAlways. iIntros (b v1 v2) "Hv".
      dwp_pures. dwp_bind (acquire _) (acquire _).
      iApply (acquire_spec with "Hlock").
      iIntros "Hlk Hls".

      dwp_pures. dwp_bind (insert _ _ _) (insert _ _ _).
      iApply (insert_spec with "Hls Hv").
      iNext. iIntros "Hls".

      dwp_pures. iApply (release_spec with "Hlock Hlk Hls").

      eauto with iFrame.
    - rewrite interp_eq /= /lrel_car /=. iAlways.
      iIntros (??) "_". dwp_rec.
      dwp_bind (acquire _) (acquire _).
      iApply (acquire_spec with "Hlock").
      iIntros "Hlk Hls".

      dwp_pures. dwp_bind (size _) (size _).
      iApply (size_spec with "Hls").
      iNext. iIntros (v1 v2) "Hv Hls".

      dwp_pures. dwp_bind (release _) (release _).
      iApply (release_spec with "Hlock Hlk Hls").

      dwp_pures. iApply dwp_value. iModIntro.
      iSimpl. iFrame "Hv".
  Qed.

End proof.
