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

Definition insert_unordered : val := λ: "ls" "v",
  cons "v" "ls".

Definition insert_ordered : val := rec: "insert" "ls" "v" :=
  list_match
    "ls"
    (λ: <>, cons "v" nil)
    (λ: "hd" "tl", if: "v" ≤ "hd"
                   then cons "v" "ls"
                   else cons "hd" ("insert" "tl" "v")).

Definition insert : val := λ: "l" "v" "f",
  let: "x" := !"l" in
  let: "l-high" := Fst "x" in
  let: "l-low" := Snd "x" in
  if: "f"
  then "l" <- (insert_unordered "l-high" "v",
               "l-low")
  else "l" <- ("l-high",
               insert_ordered "l-low" "v").

Definition contains_unorderd : val := rec: "contains" "ls" "v" :=
  list_match
    "ls"
    (λ: <>, #false)
    (λ: "hd" "tl", if: "v" = "hd"
                   then #true
                   else "contains" "tl" "v").

Definition contains_ordered : val := rec: "contains" "ls" "v" :=
  list_match
    "ls"
    (λ: <>, #false)
    (λ: "hd" "tl", if: "v" = "hd"
                   then #true
                   else if: "hd" < "v"
                        then #false
                        else "contains" "tl" "v").

Definition contains : val := λ: "l" "v",
  let: "x" := !"l" in
  let: "l-high" := Fst "x" in
  let: "l-low" := Snd "x" in
  if: contains_unorderd "l-high" "v"
  then #true
  else contains_ordered "l-low" "v".

Definition size_loop : val := λ: "ls",
  let: "loop" :=
     (rec: "loop" "ls" "n" :=
          list_match
            "ls"
            (λ: <>, "n")
            (λ: "hd" "tl", "loop" "tl" ("n"+#1))) in
  "loop" "ls" #0.

Definition size : val := λ: "l",
  let: "x" := !"l" in
  let: "l-high" := Fst "x" in
  let: "l-low" := Snd "x" in
  size_loop "l-low" + size_loop "l-high".

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

  Definition sec_list hd1 hd2 (l ξ : slevel) :=
    (∃ xs1 xs2, ⌜is_list hd1 xs1⌝ ∗ ⌜is_list hd2 xs2⌝ ∗
                 ([∗ list] v1; v2 ∈ xs1;xs2, ⟦ tint l ⟧ ξ v1 v2))%I.

  Definition ls_inv (l1 l2 : loc) (ξ : slevel) :=
    (∃ hdh1 hdh2 hdl1 hdl2,
        l1 ↦ₗ (hdh1, hdl1) ∗ l2 ↦ᵣ (hdh2, hdl2) ∗
        sec_list hdh1 hdh2 High ξ ∗
        sec_list hdl1 hdl2 Low ξ)%I.

  Lemma insert_low_helper v1 v2 hd1 hd2 xs1 xs2 ξ :
    ⟦ tint Low ⟧ ξ v1 v2 -∗
    ([∗ list] v1; v2 ∈ xs1;xs2, ⟦ tint Low ⟧ ξ v1 v2) -∗
    ⌜is_list hd1 xs1⌝ -∗ ⌜is_list hd2 xs2⌝ -∗
    DWP insert_ordered hd1 v1 & insert_ordered hd2 v2
      : λ hd1 hd2, ∃ xs1 xs2, ([∗ list] v1; v2 ∈ xs1;xs2, ⟦ tint Low ⟧ ξ v1 v2) ∗ ⌜is_list hd1 xs1⌝ ∗ ⌜is_list hd2 xs2⌝.
  Proof.
    iIntros "#Hvv Hvs".
    iLöb as "IH" forall (hd1 hd2 xs1 xs2).
    iDestruct (big_sepL2_length with "Hvs") as %Hlen.
    iIntros "#Hr1 #Hr2".
    iDestruct "Hr1" as %Hxs1. iDestruct "Hr2" as %Hxs2.
    dwp_rec. dwp_pures. dwp_rec. dwp_pures.
    destruct xs1 as [|x1 xs1'].
    - assert (xs2 = []) as ->.
      { destruct xs2; naive_solver. }
      rewrite Hxs1 Hxs2.
      dwp_pures. dwp_rec. dwp_pures.
      iApply dwp_value. iModIntro.
      iExists [v1],[v2].
      iFrame "Hvv Hvs".
      repeat iSplit; iPureIntro; try naive_solver.
    - assert (∃ x2 xs2', xs2 = x2::xs2') as [x2 [xs2' ->]].
      { destruct xs2; naive_solver. }
      simpl in Hxs1, Hxs2.
      destruct Hxs1 as [hd1' [-> Hhd1']].
      destruct Hxs2 as [hd2' [-> Hhd2']].
      iSimpl in "Hvs". iDestruct "Hvs" as "[H Hvs]".
      dwp_pures.
      (* x1 x2, v1 v2 are integers *)
      iDestruct "H" as (? x -> ->) "H".
      iDestruct "H" as %Hx.
      assert (Low ⊑ ξ) as Hξ.
      { by destruct ξ. }
      rewrite (Hx Hξ).
      iDestruct "Hvv" as (? v -> ->) "H".
      iDestruct "H" as %Hv.
      rewrite (Hv Hξ).
      (* now we can continue symbolic execution *)
      dwp_pures. case_bool_decide; dwp_pures.
      + dwp_rec. dwp_pures.
        iApply dwp_value.
        iModIntro. iExists (#v::#x::xs1'),(#v::#x::xs2').
        iSimpl. iFrame "Hvs". iSplitL.
        { iSplit; iExists _,_; eauto with iFrame. }
        iSplit; iPureIntro; naive_solver.
      + dwp_bind (insert_ordered _ _) (insert_ordered _ _).
        iApply (dwp_wand with "[Hvs]").
        { iApply ("IH" with "Hvs"); iPureIntro; done. }
        clear Hhd1' Hhd2' hd1' hd2' xs1' xs2' Hlen.
        iIntros (hd1' hd2'). iDestruct 1 as (xs1' xs2') "[Hvs [%%]]".
        dwp_rec. dwp_pures. iApply dwp_value.
        iModIntro. iExists (#x::xs1'),(#x::xs2').
        iSimpl. iFrame. iSplitL.
        { iExists _,_; eauto with iFrame. }
        iSplit; iPureIntro; naive_solver.
  Qed.

  (* Question: can the b's here be different? *)
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
      dwp_bind (insert_unordered _ v1) (insert_unordered _ v2).
      dwp_rec. dwp_pures. dwp_rec.
      dwp_pures. iApply dwp_value.
      iModIntro. dwp_pures.

      iApply (heap_lang_lifting.dwp_store with "Hl1 Hl2").
      iIntros "Hl1 Hl2". iNext.

      iApply "HΦ". iExists _,_,_,_. iFrame.
      rewrite /sec_list.
      iDestruct "Hhs" as (xs1' xs2' Hxs1' Hxs2') "Hvs".
      iExists (v1::xs1'), (v2::xs2'). iSimpl. iFrame "Hvs Hvv".
      iSplit; iPureIntro; naive_solver.
    - (* Low-security *)
      dwp_bind (insert_ordered _ v1) (insert_ordered _ v2).
      iApply (dwp_wand with "[Hls]").
      { iDestruct "Hls" as (hd1 hd2 ??) "Hls".
        iApply (insert_low_helper with "Hvv Hls [//] [//]"). }
      iIntros (hdl1' hdl2'). iDestruct 1 as (xs1' xs2') "(Hxs & H1 & H2)".
      dwp_pures.

      iApply (heap_lang_lifting.dwp_store with "Hl1 Hl2").
      iIntros "Hl1 Hl2". iNext.

      iApply ("HΦ" with "[-]"). iExists _,_,_,_. iFrame.
      iExists _,_. iFrame.
  Qed.

  Lemma size_helper hd1 hd2 l ξ Φ :
    sec_list hd1 hd2 l ξ -∗
    (∀ v1 v2, sec_list hd1 hd2 l ξ -∗ ⟦ tint Low ⟧ ξ v1 v2 -∗ Φ v1 v2) -∗
    DWP size_loop hd1 & size_loop hd2 : Φ.
  Proof.
    iIntros "Hls HΦ".
    iDestruct "Hls" as (xs1 xs2) "Hr".
    dwp_rec.
    generalize 0. intros n. dwp_pures.
    iRevert "Hr". iLöb as "IH" forall (n hd1 hd2 xs1 xs2).
    iIntros "(Hxs1 & Hxs2 & Hls)".
    iDestruct (big_sepL2_length with "Hls") as %Hlen.
    iDestruct "Hxs1" as %Hxs1.
    iDestruct "Hxs2" as %Hxs2.
    dwp_rec. dwp_pures.
    destruct xs1 as [|x1 xs1'].
    - assert (xs2 = []) as ->.
      { destruct xs2; naive_solver. }
      rewrite Hxs1 Hxs2.
      dwp_pures. iApply dwp_value. iModIntro.
      iApply ("HΦ" with "[-]").
      { iExists [],[]. iFrame. iSplit; iPureIntro; naive_solver. }
      iExists n,n. eauto with iFrame.
    - assert (∃ x2 xs2', xs2 = x2::xs2') as [x2 [xs2' ->]].
      { destruct xs2; naive_solver. }
      simpl in Hxs1, Hxs2.
      destruct Hxs1 as [hd1' [-> Hhd1']].
      destruct Hxs2 as [hd2' [-> Hhd2']].
      dwp_pures.
      iDestruct "Hls" as "[#Hxx Hls]".
      iApply ("IH" $! (n+1) with "[HΦ] [-]").
      { iIntros (v1 v2) "Hhd' Hvv".
        iApply ("HΦ" with "[-Hvv] Hvv").
        iDestruct "Hhd'" as (xs1 xs2) "(%&%&?)".
        iExists (x1::xs1),(x2::xs2). iSimpl.
        iFrame. iFrame "Hxx". iSplit; iPureIntro; naive_solver. }
      iFrame "Hls". iSplit; iPureIntro; naive_solver.
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

    dwp_pures. dwp_bind (size_loop _) (size_loop _).
    iApply (size_helper with "Hhs").
    iIntros (n1 n2) "Hhs #Hn".

    dwp_bind (size_loop _) (size_loop _).
    iApply (size_helper with "Hls").
    iIntros (m1 m2) "Hls #Hm".

    iApply dwp_wand.
    { iApply dwp_binop; iApply dwp_value; eauto with iFrame. }

    iIntros (z1 z2) "Hz".
    iApply ("HΦ" with "Hz [-]").
    iExists _,_,_,_. by iFrame "Hl1 Hl2 Hhs Hls".
  Qed.

End proof.
