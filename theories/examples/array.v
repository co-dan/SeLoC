From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types interp.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import tactics.
From iris_ni.proofmode Require Import dwp_tactics.
From iris.heap_lang Require Import lang array proofmode lib.arith.

(* make : int^low → array τ *)
Definition make : val := λ: "n" "dummy",
  let: "n" := maximum "n" #0 in
  (AllocN (#1 + "n") "dummy", "n").

(* length : array τ → int^low *)
Definition length : val := λ: "arr",
  Snd "arr".

(* set : array τ → int^α → τ → unit *)
Definition set : val := λ: "arr" "i" "v",
  let: "a" := Fst "arr" in
  let: "n" := Snd "arr" in
  let: "ii" := "i" + #1 in
  let: "iii" := if: BinOp AndOp (#0 ≤ "i") ("i" < "n") then "ii" else #0 in
  "a" +ₗ "iii" <- "v".

(* get : array τ → int^α → τ *)
Definition get : val := λ: "arr" "i",
  let: "a" := Fst "arr" in
  let: "n" := Snd "arr" in
  let: "ii" := "i" + #1 in
  let: "iii" := if: BinOp AndOp (#0 ≤ "i") ("i" < "n") then "ii" else #0 in
  !("a" +ₗ "iii").

Section lookup_total.
  Context {A : Type}.
  Context `{!Inhabited A}.
  Implicit Types x y z : A.
  Implicit Types l k : list A.

  Lemma list_lookup_total_insert l (i : nat) x :
    i < List.length l → <[i:=x]>l !!! i = x.
  Proof.
    intros Hlen.
    rewrite list_lookup_total_alt list_lookup_insert //.
  Qed.
  Lemma list_lookup_total_insert_ne l (i j : nat) x :
    i ≠ j → <[i:=x]>l !!! j = l !!! j.
  Proof.
    intros Hij.
    rewrite !list_lookup_total_alt list_lookup_insert_ne //.
  Qed.
End lookup_total.

Section spec.
  Context `{!heapDG Σ}.
  Implicit Types A B : lrel Σ.
  Implicit Types n : nat.
  Implicit Types i j : Z.
  Implicit Types v w : val.

  Hint Extern 0 (_ !! _ = _) =>
    apply list_lookup_lookup_total_lt; lia : core.

  (** The array specs are valid only for arrays over the semantic
  types satisfying those conditions. All "flat" types satisfy those.
  *)
  Definition pseudo_refl A ξ :=
    (∀ v1 v2, A ξ v1 v2 -∗ A ξ v1 v1 ∗ A ξ v2 v2).

  Definition contractible A ξ :=
    (∀ v1 v2, A ξ v1 v1 ∗ A ξ v2 v2 -∗ A ξ v1 v2).

  (* XXX: use vectors instead of lists? *)
  Definition array_inv τ ξ l1 l2 n :=
    inv (locsN.@(l1,l2))
        (∃ vs1 vs2, ⌜List.length vs1 = n⌝ ∗
                    ⌜List.length vs2 = n⌝ ∗
                    l1 ↦ₗ∗ vs1 ∗ l2 ↦ᵣ∗ vs2 ∗
                    [∗ list] i ↦ v1;v2 ∈ vs1;vs2, ⟦ τ ⟧ ξ v1 v2)%I.
  Definition lrel_array τ : lrel Σ := LRel (λ ξ w1 w2,
    ∃ (l1 l2 : loc) (n : nat),
      ⌜w1 = (#l1, #n)%V⌝ ∧ ⌜w2 = (#l2, #n)%V⌝ ∧
      array_inv τ ξ l1 l2 (S n))%I.

  (** * Make typing *)
  Lemma make_spec (n : Z) v1 v2 τ ξ :
    ⟦ τ ⟧ ξ v1 v2 -∗
    DWP make #n v1 & make #n v2 : lrel_array τ ξ.
  Proof.
    iIntros "#Hv".
    iAssert (∀ n : Z, ⌜ (0 ≤ n)%Z ⌝ →
      DWP (AllocN #(1 + n) v1, #n) & (AllocN #(1 + n) v2, #n) : lrel_array τ ξ)%I as "H"; last first.
    { rewrite /make /maximum. dwp_pures.
      case_bool_decide; dwp_pures; iApply "H"; auto with lia. }
    clear n. iIntros (n' Hn).
    assert (∃ n : nat, n' = n) as [n ->].
    { exists (Z.to_nat n'). rewrite Z2Nat.id; lia. }
    rewrite -(Nat2Z.inj_add 1) /=.
    dwp_bind (AllocN _ _) (AllocN _ _).
    (* allocN spec *)
    pose (Ψ1 v := (∃ l : loc, ⌜v = #l⌝ ∗ l ↦ₗ∗ replicate (S n) v1)%I).
    pose (Ψ2 v := (∃ l : loc, ⌜v = #l⌝ ∗ l ↦ᵣ∗ replicate (S n) v2)%I).
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2).
    { iApply twp_allocN; try done.
      iIntros (l) "[Hl _]". iExists l. rewrite !Nat2Z.id. by iSplit. }
    { iApply twp_allocN; try done.
      iIntros (l) "[Hl _]". iExists l. rewrite !Nat2Z.id. by iSplit. }
    iDestruct 1 as (l1 ->) "Hl1"; iDestruct 1 as (l2 ->) "Hl2".
    (* / allocN spec *)
    iNext. dwp_pures. iApply dwp_value.
    iMod (inv_alloc (locsN.@(l1,l2)) _ (∃ vs1 vs2,
                      ⌜List.length vs1 = S n⌝ ∗
                      ⌜List.length vs2 = S n⌝ ∗
                      l1 ↦ₗ∗ vs1 ∗ l2 ↦ᵣ∗ vs2 ∗
                      [∗ list] i ↦ v1;v2 ∈ vs1;vs2, ⟦τ⟧ ξ v1 v2)%I with "[-]")
      as "#Hinv".
    { iNext. iExists (replicate (S n) v1), (replicate (S n) v2). iFrame.
      rewrite !replicate_length. do 2 (iSplit; [done|]).
      induction (S n); simpl; eauto with iFrame. }
    iModIntro. iEval rewrite /lrel_car /=. eauto 20 with iFrame.
  Qed.

  (** * Length typing *)
  Lemma length_spec v1 v2 τ ξ :
    lrel_array τ ξ v1 v2 -∗
    DWP length v1 & length v2 : ⟦ tint Low ⟧ ξ.
  Proof.
    iDestruct 1 as (l1 l2 n -> ->) "Ha".
    dwp_rec. dwp_pures. iApply logrel_int.
  Qed.

  (** * Get typing *)
  Lemma array_get_both τ ξ l1 l2 i1 i2 n :
    pseudo_refl (⟦ stamp τ High ⟧) ξ →
    contractible (⟦ stamp τ High ⟧) ξ →
    (0 ≤ i1 < n)%Z →
    (0 ≤ i2 < n)%Z →
    array_inv τ ξ l1 l2 n -∗
    DWP !#(l1 +ₗ i1) & !#(l2 +ₗ i2) : ⟦ stamp τ High ⟧ ξ.
  Proof.
    iIntros (PR C Hi1 Hi2) "Ha".
    assert (∃ i1' : nat, i1 = i1' ∧ i1' < n)%nat as (i1' & -> & ?).
    (* XXX on Coq 8.9 lia doesn't solve these goals... *)
    { exists (Z.to_nat i1). rewrite !Z2Nat.id; last lia.
      split; first done. rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; lia. }
    assert (∃ i2' : nat, i2 = i2' ∧ i2' < n)%nat as (i2' & -> & ?).
    { exists (Z.to_nat i2). rewrite !Z2Nat.id; last lia.
      split; first done. rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; lia. }
    iApply dwp_atomic.
    iInv (locsN.@(l1, l2)) as
        (vs1 vs2) "(>% & >% & >Hl1 & >Hl2 & HAs)" "Hcl".
    iModIntro.
    pose (Ψ1 := (λ v, ⌜v = vs1 !!! i1'⌝ ∗ l1 ↦ₗ∗ vs1)%I).
    pose (Ψ2 := (λ v, ⌜v = vs2 !!! i2'⌝ ∗ l2 ↦ᵣ∗ vs2)%I).
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[Hl1] [Hl2] [-]").
    { rewrite /TWP1 /Ψ1.
      iApply (twp_load_offset (heapG0:=heapG1) with "Hl1"); eauto. }
    { rewrite /TWP2 /Ψ2.
      iApply (twp_load_offset (heapG0:=heapG2) with "Hl2"); eauto. }
    iDestruct 1 as (->) "Hl1"; iDestruct 1 as (->) "Hl2". iNext.
    iAssert (⟦ τ ⟧ ξ (vs1 !!! i1') (vs2 !!! i1')) as "#HvsA".
    { by iApply (big_sepL2_lookup with "HAs"). }
    iAssert (⟦ τ ⟧ ξ (vs1 !!! i2') (vs2 !!! i2')) as "#HvsA'".
    { by iApply (big_sepL2_lookup with "HAs"). }
    iMod ("Hcl" with "[-]") as "_".
    { iNext. iExists _,_. iFrame "Hl1 Hl2 HAs".
      repeat iSplit; eauto with iFrame. }
    iModIntro. rewrite -(stamp_low τ).
    repeat rewrite (interp_label_mono τ Low High)//.
    rewrite stamp_low.
    iApply C. iSplit.
    - rewrite (PR (vs1 !!! i1')).
      iDestruct "HvsA" as "[$ _]".
    - rewrite (PR (vs1 !!! i2')).
      iDestruct "HvsA'" as "[_ $]".
  Qed.

  Lemma array_get_same τ ξ l1 l2 i1 n :
    (0 ≤ i1 < n)%Z →
    array_inv τ ξ l1 l2 n -∗
    DWP !#(l1 +ₗ i1) & !#(l2 +ₗ i1) : ⟦ τ ⟧ ξ.
  Proof.
    iIntros (Hi1) "Ha".
    assert (∃ i1' : nat, i1 = i1' ∧ i1' < n)%nat as (i1' & -> & ?).
    (* XXX on Coq 8.9 lia doesn't solve these goals... *)
    { exists (Z.to_nat i1). rewrite !Z2Nat.id; last lia.
      split; first done. rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; lia. }
    iApply dwp_atomic.
    iInv (locsN.@(l1, l2)) as
        (vs1 vs2) "(>% & >% & >Hl1 & >Hl2 & HAs)" "Hcl".
    iModIntro.
    pose (Ψ1 := (λ v, ⌜v = vs1 !!! i1'⌝ ∗ l1 ↦ₗ∗ vs1)%I).
    pose (Ψ2 := (λ v, ⌜v = vs2 !!! i1'⌝ ∗ l2 ↦ᵣ∗ vs2)%I).
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[Hl1] [Hl2] [-]").
    { rewrite /TWP1 /Ψ1.
      iApply (twp_load_offset (heapG0:=heapG1) with "Hl1"); eauto. }
    { rewrite /TWP2 /Ψ2.
      iApply (twp_load_offset (heapG0:=heapG2) with "Hl2"); eauto. }
    iDestruct 1 as (->) "Hl1"; iDestruct 1 as (->) "Hl2". iNext.
    iAssert (⟦ τ ⟧ ξ (vs1 !!! i1') (vs2 !!! i1')) as "#H".
    { by iApply (big_sepL2_lookup with "HAs"). }
    iMod ("Hcl" with "[-]") as "_".
    { iNext. iExists _,_. iFrame "Hl1 Hl2 HAs".
      repeat iSplit; eauto with iFrame. }
    iModIntro. done.
  Qed.

  (** ** Main 'get' typing *)
  Lemma get_spec (a1 a2 : val) v1 v2 τ ξ :
    pseudo_refl ⟦ stamp τ High ⟧ ξ →
    contractible ⟦ stamp τ High ⟧ ξ →
    lrel_array τ ξ a1 a2 -∗
    ⟦ tint High ⟧ ξ v1 v2 -∗
    DWP get a1 v1 & get a2 v2 : ⟦ stamp τ High ⟧ ξ.
  Proof.
    iIntros (PR C).
    iDestruct 1 as (l1 l2 n -> ->) "Ha".
    iDestruct 1 as (i1 i2 -> ->) "_".
    rewrite /get. dwp_pures.
    repeat case_bool_decide; dwp_pures; iApply (array_get_both with "Ha"); auto with lia.
  Qed.

  Lemma get_spec_low (a1 a2 : val) v1 v2 τ ξ :
    lrel_array τ ξ a1 a2 -∗
    ⟦ tint Low ⟧ ξ v1 v2 -∗
    DWP get a1 v1 & get a2 v2 : ⟦ τ ⟧ ξ.
  Proof.
    iDestruct 1 as (l1 l2 n -> ->) "Ha".
    iDestruct 1 as (i1 i2 -> ->) "%".
    assert (i1 = i2) as -> by (destruct ξ; eauto).
    rewrite /get. dwp_pures.
    repeat case_bool_decide; dwp_pures; iApply (array_get_same with "Ha"); auto with lia.
  Qed.

  (** * Set typing *)
  Lemma lrel_list_update_both A ξ vs1 vs2 (i1 i2 : nat) v1 v2 :
    pseudo_refl A ξ →
    contractible A ξ →
    (i1 < List.length vs1)%nat →
    (i2 < List.length vs2)%nat →
    A ξ v1 v2 -∗
    ([∗ list] v0;v3 ∈ vs1;vs2, A ξ v0 v3) -∗
    [∗ list] v0;v3 ∈ <[i1:=v1]>vs1;<[i2:=v2]>vs2, A ξ v0 v3.
  Proof.
    iIntros (PR C Hi1 Hi2) "#Hv HAs".
    iDestruct (big_sepL2_length with "HAs") as %Hfoo.
    destruct (decide (i1 = i2)) as [<-|Hi1i2].
    - (* If the indices at which we insert are the same,
         then it's fairly straightforward *)
      rewrite (big_sepL2_insert_acc _ _ _ i1) //.
      iDestruct "HAs" as "[#HvsA HAs]".
      iApply ("HAs" $! v1 v2 with "Hv").
    - (* Otherwise we need to do two insertions *)
      rewrite (big_sepL2_insert_acc _ _ _ i1) //.
      iDestruct "HAs" as "[#HvsA HAs]".
      iSpecialize ("HAs" $! v1 (vs2 !!! i1) with "[]").
      { iApply C. iSplit.
        - rewrite (PR v1 v2). iDestruct "Hv" as "[$ _]".
        - rewrite (PR (vs1 !!! _)). iDestruct "HvsA" as "[_ $]". }
      rewrite (list_insert_id vs2) //.
      iClear "HvsA".
      rewrite (big_sepL2_insert_acc _ _ _ i2) //; last first.
      { by rewrite list_lookup_insert_ne. }
      iDestruct "HAs" as "[#HvsA HAs]".
      iSpecialize ("HAs" $! (<[i1:=v1]> vs1 !!! i2) v2 with "[]").
      { assert (<[i1:=v1]> vs1 !!! i2 = vs1 !!! i2) as ->.
        { by rewrite list_lookup_total_insert_ne. }
        iApply C. iSplit.
        - rewrite (PR (vs1 !!! _)). iDestruct "HvsA" as "[$ _]".
        - rewrite (PR v1 v2). iDestruct "Hv" as "[_ $]". }
      rewrite (list_insert_id (<[i1:=v1]> vs1)) //.
      apply list_lookup_lookup_total_lt.
      rewrite insert_length. lia.
  Qed.

  Lemma lrel_list_update_same A ξ vs1 vs2 (i1 : nat) v1 v2 :
    (i1 < List.length vs1)%nat →
    A ξ v1 v2 -∗
    ([∗ list] v0;v3 ∈ vs1;vs2, A ξ v0 v3) -∗
    [∗ list] v0;v3 ∈ <[i1:=v1]>vs1;<[i1:=v2]>vs2, A ξ v0 v3.
  Proof.
    iIntros (Hi1) "#Hv HAs".
    iDestruct (big_sepL2_length with "HAs") as %Hfoo.
    rewrite (big_sepL2_insert_acc _ _ _ i1) //.
    iDestruct "HAs" as "[Hv' HAs]".
    iApply ("HAs" with "Hv").
  Qed.

  Lemma array_set_both τ ξ v1 v2 l1 l2 i1 i2 n :
    pseudo_refl ⟦ τ ⟧ ξ →
    contractible ⟦ τ ⟧ ξ →
    (0 ≤ i1 < n)%Z →
    (0 ≤ i2 < n)%Z →
    ⟦ τ ⟧ ξ v1 v2 -∗
    array_inv τ ξ l1 l2 n -∗
    DWP #(l1 +ₗ i1) <- v1 & #(l2 +ₗ i2) <- v2 : ⟦ tunit ⟧ ξ.
  Proof.
    iIntros (PR C Hi1 Hi2) "#Hv Ha".
    assert (∃ i1' : nat, i1 = i1' ∧ i1' < n)%nat as (i1' & -> & ?).
    { exists (Z.to_nat i1). rewrite !Z2Nat.id; last lia.
      split; first done. rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; lia. }
    assert (∃ i2' : nat, i2 = i2' ∧ i2' < n)%nat as (i2' & -> & ?).
    { exists (Z.to_nat i2). rewrite !Z2Nat.id; last lia.
      split; first done. rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; lia. }
    iApply dwp_atomic.
    iInv (locsN.@(l1, l2)) as
          (vs1 vs2) "(>% & >% & >Hl1 & >Hl2 & HAs)" "Hcl".
    iModIntro.
    pose (Ψ1 v := (⌜v = #()⌝ ∗ l1 ↦ₗ∗ <[i1':=v1]>vs1)%I).
    pose (Ψ2 v := (⌜v = #()⌝ ∗ l2 ↦ᵣ∗ <[i2':=v2]>vs2)%I).
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[Hl1] [Hl2] [-]").
    { rewrite /TWP1 /Ψ1.
     iApply (twp_store_offset (heapG0:=heapG1) with "Hl1"); eauto. }
    { rewrite /TWP2 /Ψ2.
      iApply (twp_store_offset (heapG0:=heapG2) with "Hl2"); eauto. }
    iDestruct 1 as (->) "Hl1". iDestruct 1 as (->) "Hl2". iNext.

    iDestruct (lrel_list_update_both _ _ _ _ i1' i2' with "Hv HAs") as "HAs";
      eauto with lia.

    iMod ("Hcl" with "[-]") as "_".
    { iNext. iExists _,_. iFrame "HAs Hl1".
      rewrite !insert_length. eauto 10. }
    iModIntro. rewrite interp_eq; eauto.
  Qed.

  Lemma array_set_same τ ξ v1 v2 l1 l2 i1 n :
    (0 ≤ i1 < n)%Z →
    ⟦ τ ⟧ ξ v1 v2 -∗
    array_inv τ ξ l1 l2 n -∗
    DWP #(l1 +ₗ i1) <- v1 & #(l2 +ₗ i1) <- v2 : ⟦ tunit ⟧ ξ.
  Proof.
    iIntros (Hi1) "#Hv Ha".
    assert (∃ i1' : nat, i1 = i1' ∧ i1' < n)%nat as (i1' & -> & ?).
    { exists (Z.to_nat i1). rewrite !Z2Nat.id; last lia.
      split; first done. rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; lia. }
    iApply dwp_atomic.
    iInv (locsN.@(l1, l2)) as
          (vs1 vs2) "(>% & >% & >Hl1 & >Hl2 & HAs)" "Hcl".
    iModIntro.
    pose (Ψ1 v := (⌜v = #()⌝ ∗ l1 ↦ₗ∗ <[i1':=v1]>vs1)%I).
    pose (Ψ2 v := (⌜v = #()⌝ ∗ l2 ↦ᵣ∗ <[i1':=v2]>vs2)%I).
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[Hl1] [Hl2] [-]").
    { rewrite /TWP1 /Ψ1.
     iApply (twp_store_offset (heapG0:=heapG1) with "Hl1"); eauto. }
    { rewrite /TWP2 /Ψ2.
      iApply (twp_store_offset (heapG0:=heapG2) with "Hl2"); eauto. }
    iDestruct 1 as (->) "Hl1". iDestruct 1 as (->) "Hl2". iNext.

    iDestruct (lrel_list_update_same _ _ _ _ i1' with "Hv HAs") as "HAs";
      eauto with lia.

    iMod ("Hcl" with "[-]") as "_".
    { iNext. iExists _,_. iFrame "HAs Hl1".
      rewrite !insert_length. eauto 10. }
    iModIntro. rewrite interp_eq; eauto.
  Qed.

  (** ** The main 'set' typing *)
  Lemma set_spec (a1 a2 : val) iv1 iv2 v1 v2 τ ξ :
    pseudo_refl ⟦ τ ⟧ ξ →
    contractible ⟦ τ ⟧ ξ →
    lrel_array τ ξ a1 a2 -∗
    ⟦ tint High ⟧ ξ iv1 iv2 -∗
    ⟦ τ ⟧ ξ v1 v2 -∗
    DWP (set a1 iv1 v1) & (set a2 iv2 v2) : ⟦ tunit ⟧ ξ.
  Proof.
    iIntros (PR C).
    iDestruct 1 as (l1 l2 n -> ->) "Ha".
    iDestruct 1 as (i1 i2 -> ->) "_".
    iIntros "#Hd".
    rewrite /set. dwp_pures.
    repeat case_bool_decide; dwp_pures;
      iApply (array_set_both with "Hd Ha"); auto with lia.
  Qed.

  Lemma set_spec_low (a1 a2 : val) iv1 iv2 v1 v2 τ ξ :
    lrel_array τ ξ a1 a2 -∗
    ⟦ tint Low ⟧ ξ iv1 iv2 -∗
    ⟦ τ ⟧ ξ v1 v2 -∗
    DWP (set a1 iv1 v1) & (set a2 iv2 v2) : ⟦ tunit ⟧ ξ.
  Proof.
    iDestruct 1 as (l1 l2 n -> ->) "Ha".
    iDestruct 1 as (i1 i2 -> ->) "%".
    assert (i1 = i2) as -> by (destruct ξ; eauto).
    iIntros "#Hd".
    rewrite /set. dwp_pures.
    repeat case_bool_decide; dwp_pures;
      iApply (array_set_same with "Hd Ha"); auto with lia.
  Qed.

End spec.
