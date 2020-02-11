From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types interp.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import tactics.
From iris_ni.proofmode Require Import dwp_tactics.
From iris.heap_lang Require Import lang array proofmode.

(* make : int^low → array τ *)
(* XXX: how to handle the side condition that n > 0 ? *)
Definition make : val := λ: "n" "dummy",
  (AllocN "n" "dummy", "n").

(* length : array τ → int^low *)
Definition length : val := λ: "arr",
  Snd "arr".

(* set : array τ → int^α → τ → unit *)
Definition set : val := λ: "arr" "i" "v",
  let: "a" := Fst "arr" in
  let: "n" := Snd "arr" in
  let: "p" := "a" +ₗ "i" in
  (* XXX: the || is lazy, so we have to ANF this.. *)
  let: "b1" := ("i" < #0) in
  if: (("n" ≤ "i") || "b1")
  then Skip
  else "p" <- "v".

(* get : array τ → int^α → τ → τ *)
Definition get : val := λ: "arr" "i" "dummy",
  let: "a" := Fst "arr" in
  let: "n" := Snd "arr" in
  (* XXX: the || is lazy, so we have to ANF this.. *)
  let: "b1" := ("i" < #0) in
  if: (("n" ≤ "i") || "b1") then
    let: "v" := "dummy" in "v"
  else !("a" +ₗ "i").

Section lookup_total.
  Context {A : Type}.
  Context `{!Inhabited A}.
  Implicit Types x y z : A.
  Implicit Types l k : list A.

  Lemma list_lookup_total_insert l (i : nat) x :
    i < List.length l → <[i:=x]>l !!! i = x.
  Proof.
    intros Hlen.
    rewrite list_lookup_total_alt list_lookup_insert //. lia.
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

  (** The array specs are valid only for arrays over the semantic
  types satisfying those conditions. All "flat" types satisfy those.
  *)
  Definition pseudo_refl A ξ :=
    (∀ v1 v2, A ξ v1 v2 -∗ A ξ v1 v1 ∗ A ξ v2 v2).

  Definition contractible A ξ :=
    (∀ v1 v2, A ξ v1 v1 ∗ A ξ v2 v2 -∗ A ξ v1 v2).


  (** * Interpretation *)
  Definition lrel_list (A : lrel Σ) ξ (vs1 vs2 : list val) :=
    ([∗ list] i ↦ v1;v2 ∈ vs1;vs2, A ξ v1 v2)%I.

  (* XXX: use vectors instead of lists? *)
  Definition array_inv A ξ l1 l2 n :=
    inv (locsN.@(l1,l2))
        (∃ vs1 vs2, ⌜List.length vs1 = n⌝ ∗
                    ⌜List.length vs2 = n⌝ ∗
                     l1 ↦ₗ∗ vs1 ∗ l2 ↦ᵣ∗ vs2 ∗
                     lrel_list A ξ vs1 vs2)%I.
  Definition lrel_array (A : lrel Σ) : lrel Σ := LRel (λ ξ w1 w2,
    ∃ (l1 l2 : loc) (n : nat), ⌜w1 = (#l1, #n)%V⌝ ∧ ⌜w2 = (#l2, #n)%V⌝ ∧
     array_inv A ξ l1 l2 n)%I.

  (** * Make typing *)
  Lemma make_spec (n : nat) v1 v2 A ξ :
    0 < n →
    A ξ v1 v2 -∗
    DWP make #n v1 & make #n v2 : lrel_array A ξ.
  Proof.
    iIntros (?) "#Hv". dwp_rec. dwp_pures.
    dwp_bind (AllocN _ _) (AllocN _ _).
    (* allocN spec *)
    set (meta_token1 := @meta_token _ _ _ _ _ heapDG_gen_heapG1).
    set (meta_token2 := @meta_token _ _ _ _ _ heapDG_gen_heapG2).
    pose (Ψ1 := (λ v, ∃ l : loc, ⌜v = #l⌝ ∗ l ↦ₗ∗ replicate n v1 ∗
                 ([∗ list] i ∈ seq 0 n, meta_token1 (l +ₗ Z.of_nat i) ⊤))%I).
    pose (Ψ2 := (λ v, ∃ l : loc, ⌜v = #l⌝ ∗ l ↦ᵣ∗ replicate n v2 ∗
                 ([∗ list] i ∈ seq 0 n, meta_token2 (l +ₗ Z.of_nat i) ⊤))%I).
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2).
    { iApply twp_allocN; try done.
      iIntros (l) "[Hl Hmeta]". iExists l.
      iSplit; eauto.
      rewrite !Nat2Z.id. iSplitL "Hl".
      iExact "Hl". iFrame. }
    { iApply twp_allocN; try done.
      iIntros (l) "[Hl Hmeta]". iExists l.
      iSplit; eauto.
      rewrite !Nat2Z.id. iSplitL "Hl".
      iExact "Hl". iFrame. }
    iIntros (? ?). iDestruct 1 as (l1) "[-> [Hl1 Hmeta1]]".
    iDestruct 1 as (l2) "[-> [Hl2 Hmeta2]]".
    (* / allocN spec *)
    iClear "Hmeta1 Hmeta2".

    iNext. dwp_pures. iApply dwp_value.
    iMod (inv_alloc (locsN.@(l1,l2)) _ (∃ vs1 vs2,
                      ⌜List.length vs1 = n⌝ ∗
                      ⌜List.length vs2 = n⌝ ∗
                      l1 ↦ₗ∗ vs1 ∗ l2 ↦ᵣ∗ vs2 ∗
                      lrel_list A ξ vs1 vs2)%I with "[-]")
      as "#Hinv".
    { iNext. iExists _,_. iFrame.
      rewrite !replicate_length; repeat iSplit; try done.
      rewrite /lrel_list. clear.
      induction n; simpl; eauto with iFrame. }
    iModIntro. iExists _,_,_. repeat iSplit; eauto with iFrame.
  Qed.

  (** * Length typing *)
  Lemma length_spec v1 v2 A ξ :
    lrel_array A ξ v1 v2 -∗
    DWP length v1 & length v2 : ⟦ tint Low ⟧ ξ.
  Proof.
    iDestruct 1 as (l1 l2 n -> ->) "Ha".
    dwp_rec. dwp_pures. iApply logrel_int.
  Qed.

  (** * Get typing *)

  (** ** For the case when the index is a low integer *)
  Lemma get_spec_low (a1 a2 : val) v1 v2 d1 d2 A ξ :
    lrel_array A ξ a1 a2 -∗
    ⟦ tint Low ⟧ ξ v1 v2 -∗
    A ξ d1 d2 -∗
    DWP get a1 v1 d1 & get a2 v2 d2 : A ξ.
  Proof.
    iDestruct 1 as (l1 l2 n -> ->) "Ha".
    iDestruct 1 as (i1 i2 -> ->) "%".
    assert (i1 = i2) as ->.
    { by destruct ξ; eauto. }
    iIntros "Hdummy".
    dwp_rec. dwp_pures.
    repeat case_bool_decide; dwp_pures;
     try by iApply dwp_value.
    iApply dwp_atomic.
    iInv (locsN.@(l1, l2)) as
        (vs1 vs2) "(>% & >% & >Hl1 & >Hl2 & HAs)" "Hcl".
    rewrite /lrel_list.
    assert (vs1 !! Z.to_nat i2 = Some (vs1 !!! Z.to_nat i2)) as Hvs1.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite H2. rewrite -(Nat2Z.id n).
      apply Z2Nat.inj_lt; try lia. }
    assert (vs2 !! Z.to_nat i2 = Some (vs2 !!! Z.to_nat i2)) as Hvs2.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite H3. rewrite -(Nat2Z.id n).
      apply Z2Nat.inj_lt; try lia. }
    pose (Ψ1 := (λ v, ⌜v = vs1 !!! Z.to_nat i2⌝ ∗ l1 ↦ₗ∗ vs1)%I).
    pose (Ψ2 := (λ v, ⌜v = vs2 !!! Z.to_nat i2⌝ ∗ l2 ↦ᵣ∗ vs2)%I).
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[Hl1] [Hl2] [-]").
    { rewrite /TWP1 /Ψ1.
      (* TODO: why do I have to specify heapG here? *)
      iPoseProof (twp_load_offset
                    (heapG0:=heapG1) with "Hl1") as "HH"; first done.
      rewrite Z2Nat.id; try lia. iApply "HH". eauto with iFrame. }
    { rewrite /TWP2 /Ψ2.
      iPoseProof (twp_load_offset
                    (heapG0:=heapG2) with "Hl2") as "HH"; first done.
      rewrite Z2Nat.id; try lia. iApply "HH". eauto with iFrame. }
    iIntros (??). iDestruct 1 as (->) "Hl1". iDestruct 1 as (->) "Hl2".
    iNext.
    iAssert (A ξ (vs1 !!! Z.to_nat i2) (vs2 !!! Z.to_nat i2)) as "#HvsA".
    { iApply (big_sepL2_lookup with "HAs").
      apply Hvs1. apply Hvs2. }
    iMod ("Hcl" with "[-]") as "_".
    { iNext. iExists _,_. iFrame "Hl1 Hl2 HAs".
      repeat iSplit; eauto with iFrame. }
    done.
  Qed.

  Local Instance id_beta_val_atomic (v : val) :
    Atomic StronglyAtomic ((λ: "v", "v")%V v).
  Proof.
    apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].
  Qed.

  (** ** Helper lemmas *)
  Lemma array_get_rhs A ξ (d1 d2 : val) l1 l2 i2 n :
    pseudo_refl A ξ →
    contractible A ξ →
    0 ≤ i2 < n →
    A ξ d1 d2 -∗
    array_inv A ξ l1 l2 n -∗
    DWP (λ: "v", "v")%V d1 & !#(l2 +ₗ i2) : A ξ.
  Proof.
    iIntros (PR C Hi2) "#Hdummy Ha".
    iApply dwp_atomic.
    iInv (locsN.@(l1, l2)) as
        (vs1 vs2) "(>% & >% & >Hl1 & >Hl2 & HAs)" "Hcl".
    rewrite /lrel_list.
    assert (vs1 !! Z.to_nat i2 = Some (vs1 !!! Z.to_nat i2)) as Hvs1.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite H. rewrite -(Nat2Z.id n).
      apply Z2Nat.inj_lt; try lia. }
    assert (vs2 !! Z.to_nat i2 = Some (vs2 !!! Z.to_nat i2)) as Hvs2.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite H0. rewrite -(Nat2Z.id n).
      apply Z2Nat.inj_lt; try lia. }
    iModIntro.
    pose (Ψ1 := (λ v, ⌜v = d1⌝ : iProp Σ)%I).
    pose (Ψ2 := (λ v, ⌜v = vs2 !!! Z.to_nat i2⌝ ∗ l2 ↦ᵣ∗ vs2)%I).
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[] [Hl2] [-]").
    { rewrite /TWP1 /Ψ1. wp_pures. done. }
    { rewrite /TWP2 /Ψ2.
      assert (i2 < n) by lia.
      iPoseProof (twp_load_offset
                    (heapG0:=heapG2) with "Hl2") as "HH"; first done.
      rewrite Z2Nat.id; try lia. (*XXX*)
      iApply "HH"; eauto. }
    iIntros (v1 v2 ->). iDestruct 1 as (->) "Hl2".
    iNext.
    iAssert (A ξ (vs1 !!! Z.to_nat i2) (vs2 !!! Z.to_nat i2)) as "#HvsA".
    { iApply (big_sepL2_lookup with "HAs").
      apply Hvs1. apply Hvs2. }
    iMod ("Hcl" with "[-]") as "_".
    { iNext. iExists _,_. iFrame "Hl1 Hl2 HAs".
      repeat iSplit; eauto with iFrame. }
    iModIntro. iApply C. iSplit.
    - rewrite (PR d1 d2). iDestruct "Hdummy" as "[$ _]".
    - rewrite (PR (vs1 !!! _)). iDestruct "HvsA" as "[_ $]".
  Qed.

  Lemma array_get_lhs A ξ (d1 d2 : val) l1 l2 i1 n :
    pseudo_refl A ξ →
    contractible A ξ →
    0 ≤ i1 < n →
    A ξ d1 d2 -∗
    array_inv A ξ l1 l2 n -∗
    DWP !#(l1 +ₗ i1) & (λ: "v", "v")%V d2 : A ξ.
  Proof.
    iIntros (PR C Hi1) "#Hdummy Ha".
    iApply dwp_atomic.
    iInv (locsN.@(l1, l2)) as
        (vs1 vs2) "(>% & >% & >Hl1 & >Hl2 & HAs)" "Hcl".
    rewrite /lrel_list.
    assert (vs1 !! Z.to_nat i1 = Some (vs1 !!! Z.to_nat i1)) as Hvs1.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite H. rewrite -(Nat2Z.id n).
      apply Z2Nat.inj_lt; try lia. }
    assert (vs2 !! Z.to_nat i1 = Some (vs2 !!! Z.to_nat i1)) as Hvs2.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite H0. rewrite -(Nat2Z.id n).
      apply Z2Nat.inj_lt; try lia. }
    iModIntro.
    pose (Ψ1 := (λ v, ⌜v = vs1 !!! Z.to_nat i1⌝ ∗ l1 ↦ₗ∗ vs1)%I).
    pose (Ψ2 := (λ v, ⌜v = d2⌝ : iProp Σ)%I).
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[Hl1] [] [-]").
    { rewrite /TWP1 /Ψ1.
      assert (i1 < n) by lia.
      iPoseProof (twp_load_offset
                    (heapG0:=heapG1) with "Hl1") as "HH"; first done.
      rewrite Z2Nat.id; try lia. (*XXX*)
      iApply "HH"; eauto. }
    { rewrite /TWP2 /Ψ2. wp_pures. done. }

    iIntros (v1 v2). iDestruct 1 as (->) "Hl1". iIntros (->).
    iNext.
    iAssert (A ξ (vs1 !!! Z.to_nat i1) (vs2 !!! Z.to_nat i1)) as "#HvsA".
    { iApply (big_sepL2_lookup with "HAs").
      apply Hvs1. apply Hvs2. }
    iMod ("Hcl" with "[-]") as "_".
    { iNext. iExists _,_. iFrame "Hl1 Hl2 HAs".
      repeat iSplit; eauto with iFrame. }
    iModIntro. iApply C. iSplit.
    - rewrite (PR (vs1 !!! _)). iDestruct "HvsA" as "[$ _]".
    - rewrite (PR d1 d2). iDestruct "Hdummy" as "[_ $]".
  Qed.

  Lemma array_get_both A ξ l1 l2 i1 i2 n :
    pseudo_refl A ξ →
    contractible A ξ →
    0 ≤ i1 < n →
    0 ≤ i2 < n →
    array_inv A ξ l1 l2 n -∗
    DWP !#(l1 +ₗ i1) & !#(l2 +ₗ i2) : A ξ.
  Proof.
    iIntros (PR C Hi1 Hi2) "Ha".
    iApply dwp_atomic.
    iInv (locsN.@(l1, l2)) as
        (vs1 vs2) "(>% & >% & >Hl1 & >Hl2 & HAs)" "Hcl".
    rewrite /lrel_list.
    assert (vs1 !! Z.to_nat i1 = Some (vs1 !!! Z.to_nat i1)) as Hvs1.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite H. rewrite -(Nat2Z.id n).
      apply Z2Nat.inj_lt; try lia. }
    assert (vs2 !! Z.to_nat i1 = Some (vs2 !!! Z.to_nat i1)) as Hvs2.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite H0. rewrite -(Nat2Z.id n).
      apply Z2Nat.inj_lt; try lia. }
    assert (vs1 !! Z.to_nat i2 = Some (vs1 !!! Z.to_nat i2)) as Hvs1'.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite H. rewrite -(Nat2Z.id n).
      apply Z2Nat.inj_lt; try lia. }
    assert (vs2 !! Z.to_nat i2 = Some (vs2 !!! Z.to_nat i2)) as Hvs2'.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite H0. rewrite -(Nat2Z.id n).
      apply Z2Nat.inj_lt; try lia. }

    iModIntro.
    pose (Ψ1 := (λ v, ⌜v = vs1 !!! Z.to_nat i1⌝ ∗ l1 ↦ₗ∗ vs1)%I).
    pose (Ψ2 := (λ v, ⌜v = vs2 !!! Z.to_nat i2⌝ ∗ l2 ↦ᵣ∗ vs2)%I).
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[Hl1] [Hl2] [-]").
    { rewrite /TWP1 /Ψ1.
      assert (i1 < n) by lia.
      iPoseProof (twp_load_offset _ _ _ (Z.to_nat i1)
                    (heapG0:=heapG1) with "Hl1") as "HH"; first done.
      rewrite Z2Nat.id; try lia. (*XXX*)
      iApply "HH"; eauto. }
    { rewrite /TWP2 /Ψ2.
      assert (i2 < n) by lia.
      iPoseProof (twp_load_offset _ _ _ (Z.to_nat i2)
                    (heapG0:=heapG2) with "Hl2") as "HH"; first done.
      rewrite Z2Nat.id; try lia. (*XXX*)
      iApply "HH"; eauto. }

    iIntros (v1 v2). iDestruct 1 as (->) "Hl1". iDestruct 1 as (->) "Hl2".
    iNext.
    iAssert (A ξ (vs1 !!! Z.to_nat i1) (vs2 !!! Z.to_nat i1)) as "#HvsA".
    { iApply (big_sepL2_lookup with "HAs").
      apply Hvs1. apply Hvs2. }
    iAssert (A ξ (vs1 !!! Z.to_nat i2) (vs2 !!! Z.to_nat i2)) as "#HvsA'".
    { iApply (big_sepL2_lookup with "HAs").
      apply Hvs1'. apply Hvs2'. }
    iMod ("Hcl" with "[-]") as "_".
    { iNext. iExists _,_. iFrame "Hl1 Hl2 HAs".
      repeat iSplit; eauto with iFrame. }
    iModIntro. iApply C. iSplit.
    - rewrite (PR (vs1 !!! Z.to_nat i1)).
      iDestruct "HvsA" as "[$ _]".
    - rewrite (PR (vs1 !!! Z.to_nat i2)).
      iDestruct "HvsA'" as "[_ $]".
  Qed.

  (** ** Main 'get' typing *)
  Lemma get_spec (a1 a2 : val) v1 v2 d1 d2 A ξ :
    pseudo_refl A ξ →
    contractible A ξ →
    lrel_array A ξ a1 a2 -∗
    ⟦ tint High ⟧ ξ v1 v2 -∗
    A ξ d1 d2 -∗
    DWP get a1 v1 d1 & get a2 v2 d2 : A ξ.
  Proof.
    iIntros (PR C).
    iDestruct 1 as (l1 l2 n -> ->) "Ha".
    iDestruct 1 as (i1 i2 -> ->) "_".
    iIntros "#Hdummy".
    dwp_rec. dwp_pures.
    repeat case_bool_decide; dwp_pures;
      try by iApply dwp_value.
    - iApply array_get_rhs; eauto. lia.
    - iApply array_get_rhs; eauto. lia.
    - iApply array_get_rhs; eauto. lia.
    - iApply array_get_lhs; eauto. lia.
    - iApply array_get_lhs; eauto. lia.
    - iApply array_get_lhs; eauto. lia.
    - iApply array_get_both; eauto; lia.
  Qed.

  (** * Set typing *)

  (** ** Helper lemmas *)
  Lemma array_set_rhs A ξ v1 v2 l1 l2 i2 n :
    pseudo_refl A ξ →
    contractible A ξ →
    0 ≤ i2 < n →
    A ξ v1 v2 -∗
    array_inv A ξ l1 l2 n -∗
    DWP Skip & #(l2 +ₗ i2) <- v2 : ⟦ tunit ⟧ ξ.
  Proof.
    iIntros (PR C Hi2) "#Hv Ha".
    iApply dwp_atomic.
    iInv (locsN.@(l1, l2)) as
          (vs1 vs2) "(>% & >% & >Hl1 & >Hl2 & HAs)" "Hcl".
    rewrite /lrel_list.

    assert (vs1 !! Z.to_nat i2 = Some (vs1 !!! Z.to_nat i2)) as Hvs1.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite H. rewrite -(Nat2Z.id n).
      apply Z2Nat.inj_lt; try lia. }
    assert (vs2 !! Z.to_nat i2 = Some (vs2 !!! Z.to_nat i2)) as Hvs2.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite H0. rewrite -(Nat2Z.id n).
      apply Z2Nat.inj_lt; try lia. }

    iModIntro.
    pose (vs2' := <[Z.to_nat i2:=v2]>vs2).
    pose (Ψ1 := (λ v, ⌜v = #()⌝ : iProp Σ)%I).
    pose (Ψ2 := (λ v, ⌜v = #()⌝ ∗ l2 ↦ᵣ∗ vs2')%I).
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[] [Hl2] [-]").
    { rewrite /TWP1 /Ψ1. wp_pures. done. }
    { rewrite /TWP2 /Ψ2.
      assert (i2 < n) by lia.
      iPoseProof (twp_store_offset _ _ _ (Z.to_nat i2)
                                   (heapG0:=heapG2) with "Hl2") as "HH".
      { rewrite Hvs2. eauto. }
      rewrite Z2Nat.id; try lia. (*XXX*)
      iApply "HH"; eauto. }
    iIntros (?? ->). iDestruct 1 as (->) "Hl2".
    iNext.

    rewrite (big_sepL2_insert_acc _ _ _ (Z.to_nat i2) _) //.
    iDestruct "HAs" as "[#HvsA HAs]".
    iSpecialize ("HAs" $! (vs1 !!! Z.to_nat i2) v2 with "[]").
    { iApply C. iSplit.
      - rewrite (PR (vs1 !!! _)). iDestruct "HvsA" as "[$ _]".
      - rewrite (PR v1 v2). iDestruct "Hv" as "[_ $]". }

    iMod ("Hcl" with "[-]") as "_".
    { iNext. iExists _,_. iFrame "HAs Hl2".
      rewrite !insert_length.
      repeat iSplit; eauto.
      rewrite list_insert_id //. }
    iModIntro. rewrite interp_eq ; eauto.
  Qed.

  Lemma array_set_lhs A ξ v1 v2 l1 l2 i1 n :
    pseudo_refl A ξ →
    contractible A ξ →
    0 ≤ i1 < n →
    A ξ v1 v2 -∗
    array_inv A ξ l1 l2 n -∗
    DWP #(l1 +ₗ i1) <- v1 & Skip : ⟦ tunit ⟧ ξ.
  Proof.
    iIntros (PR C Hi2) "#Hv Ha".
    iApply dwp_atomic.
    iInv (locsN.@(l1, l2)) as
          (vs1 vs2) "(>% & >% & >Hl1 & >Hl2 & HAs)" "Hcl".
    rewrite /lrel_list.

    assert (vs1 !! Z.to_nat i1 = Some (vs1 !!! Z.to_nat i1)) as Hvs1.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite H. rewrite -(Nat2Z.id n).
      apply Z2Nat.inj_lt; try lia. }
    assert (vs2 !! Z.to_nat i1 = Some (vs2 !!! Z.to_nat i1)) as Hvs2.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite H0. rewrite -(Nat2Z.id n).
      apply Z2Nat.inj_lt; try lia. }

    iModIntro.
    pose (vs1' := <[Z.to_nat i1:=v1]>vs1).
    pose (Ψ1 := (λ v, ⌜v = #()⌝ ∗ l1 ↦ₗ∗ vs1')%I).
    pose (Ψ2 := (λ v, ⌜v = #()⌝ : iProp Σ)%I).
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[Hl1] [] [-]").
    { rewrite /TWP1 /Ψ1.
      assert (i1 < n) by lia.
      iPoseProof (twp_store_offset _ _ _ (Z.to_nat i1)
                                   (heapG0:=heapG1) with "Hl1") as "HH".
      { rewrite Hvs1. eauto. }
      rewrite Z2Nat.id; try lia. (*XXX*)
      iApply "HH"; eauto. }
    { rewrite /TWP2 /Ψ2. by wp_pures. }
    iIntros (??). iDestruct 1 as (->) "Hl1". iIntros (->).
    iNext.

    rewrite (big_sepL2_insert_acc _ _ _ (Z.to_nat i1) _) //.
    iDestruct "HAs" as "[#HvsA HAs]".
    iSpecialize ("HAs" $! v1 (vs2 !!! Z.to_nat i1) with "[]").
    { iApply C. iSplit.
      - rewrite (PR v1 v2). iDestruct "Hv" as "[$ _]".
      - rewrite (PR (vs1 !!! _)). iDestruct "HvsA" as "[_ $]". }

    iMod ("Hcl" with "[-]") as "_".
    { iNext. iExists _,_. iFrame "HAs Hl1".
      rewrite !insert_length.
      repeat iSplit; eauto.
      rewrite list_insert_id //. }
    iModIntro. rewrite interp_eq ; eauto.
  Qed.

  Lemma lrel_list_update_both A ξ vs1 vs2 i1 i2 v1 v2 :
    pseudo_refl A ξ →
    contractible A ξ →
    0 ≤ i1 < List.length vs1 →
    0 ≤ i2 < List.length vs2 →
    A ξ v1 v2 -∗
    ([∗ list] v0;v3 ∈ vs1;vs2, A ξ v0 v3) -∗
    [∗ list] v0;v3 ∈ <[Z.to_nat i1:=v1]>vs1;<[Z.to_nat i2:=v2]>vs2, A ξ v0 v3.
  Proof.
    iIntros (PR C Hi1 Hi2) "#Hv HAs".
    iDestruct (big_sepL2_length with "HAs") as %Hfoo.

    assert (vs1 !! Z.to_nat i1 = Some (vs1 !!! Z.to_nat i1)) as Hvs1.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite -(Nat2Z.id (List.length vs1)).
      apply Z2Nat.inj_lt; try lia. }
    assert (vs1 !! Z.to_nat i2 = Some (vs1 !!! Z.to_nat i2)) as Hvs1'.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite -(Nat2Z.id (List.length vs1)).
      apply Z2Nat.inj_lt; try lia. }
    assert (vs2 !! Z.to_nat i1 = Some (vs2 !!! Z.to_nat i1)) as Hvs2.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite -(Nat2Z.id (List.length vs2)).
      apply Z2Nat.inj_lt; try lia. }
    assert (vs2 !! Z.to_nat i2 = Some (vs2 !!! Z.to_nat i2)) as Hvs2'.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite -(Nat2Z.id (List.length vs2)).
      apply Z2Nat.inj_lt; try lia. }

    destruct (decide (i1 = i2)) as [<-|Hi1i2].
    - (* If the indices at which we insert are the same,
         then it's fairly straightforward *)
      rewrite (big_sepL2_insert_acc _ _ _ (Z.to_nat i1) _) //.
      iDestruct "HAs" as "[#HvsA HAs]".
      iApply ("HAs" $! v1 v2 with "Hv").
    - (* Otherwise we need to do two insertions *)
      rewrite (big_sepL2_insert_acc _ _ _ (Z.to_nat i1) _) //.
      iDestruct "HAs" as "[#HvsA HAs]".
      iSpecialize ("HAs" $! v1 (vs2 !!! Z.to_nat i1) with "[]").
      { iApply C. iSplit.
        - rewrite (PR v1 v2). iDestruct "Hv" as "[$ _]".
        - rewrite (PR (vs1 !!! _)). iDestruct "HvsA" as "[_ $]". }
      rewrite (list_insert_id vs2) //.
      iClear "HvsA".
      pose (vs1' := <[Z.to_nat i1:=v1]> vs1).

      rewrite (big_sepL2_insert_acc _ _ _ (Z.to_nat i2) _) //; last first.
      { rewrite list_lookup_insert_ne //. intros ?%Z2Nat.inj; lia. }
      iDestruct "HAs" as "[#HvsA HAs]".
      iSpecialize ("HAs" $! (vs1'!!!Z.to_nat i2) v2 with "[]").
      { assert (vs1' !!! Z.to_nat i2 = vs1 !!! Z.to_nat i2) as ->.
        { rewrite list_lookup_total_insert_ne//.
          intros ?%Z2Nat.inj; lia. }
        iApply C. iSplit.
        - rewrite (PR (vs1 !!! _)). iDestruct "HvsA" as "[$ _]".
        - rewrite (PR v1 v2). iDestruct "Hv" as "[_ $]". }
      rewrite (list_insert_id vs1') //.
      apply list_lookup_lookup_total_lt.
      rewrite insert_length. rewrite Hfoo.
      rewrite -(Nat2Z.id (List.length vs2)).
      apply Z2Nat.inj_lt; try lia.
  Qed.

  Lemma array_set_both A ξ v1 v2 l1 l2 i1 i2 n :
    pseudo_refl A ξ →
    contractible A ξ →
    0 ≤ i1 < n →
    0 ≤ i2 < n →
    A ξ v1 v2 -∗
    array_inv A ξ l1 l2 n -∗
    DWP #(l1 +ₗ i1) <- v1 & #(l2 +ₗ i2) <- v2 : ⟦ tunit ⟧ ξ.
  Proof.
    iIntros (PR C Hi1 Hi2) "#Hv Ha".
    iApply dwp_atomic.
    iInv (locsN.@(l1, l2)) as
          (vs1 vs2) "(>% & >% & >Hl1 & >Hl2 & HAs)" "Hcl".
    rewrite /lrel_list.

    assert (vs1 !! Z.to_nat i1 = Some (vs1 !!! Z.to_nat i1)) as Hvs1.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite H. rewrite -(Nat2Z.id n).
      apply Z2Nat.inj_lt; try lia. }
    assert (vs2 !! Z.to_nat i2 = Some (vs2 !!! Z.to_nat i2)) as Hvs2.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite H0. rewrite -(Nat2Z.id n).
      apply Z2Nat.inj_lt; try lia. }
    assert (vs2 !! Z.to_nat i1 = Some (vs2 !!! Z.to_nat i1)) as Hvs2'.
    { apply list_lookup_lookup_total_lt.
      (* TODO: lia doesn't work here *)
      rewrite H0. rewrite -(Nat2Z.id n).
      apply Z2Nat.inj_lt; try lia. }

    iModIntro.
    pose (vs1' := <[Z.to_nat i1:=v1]>vs1).
    pose (vs2' := <[Z.to_nat i2:=v2]>vs2).
    pose (Ψ1 := (λ v, ⌜v = #()⌝ ∗ l1 ↦ₗ∗ vs1')%I).
    pose (Ψ2 := (λ v, ⌜v = #()⌝ ∗ l2 ↦ᵣ∗ vs2')%I).
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[Hl1] [Hl2] [-]").
    { rewrite /TWP1 /Ψ1.
      assert (i1 < n) by lia.
      iPoseProof (twp_store_offset _ _ _ (Z.to_nat i1)
                                   (heapG0:=heapG1) with "Hl1") as "HH".
      { rewrite Hvs1. eauto. }
      rewrite Z2Nat.id; try lia. (*XXX*)
      iApply "HH"; eauto. }
    { rewrite /TWP2 /Ψ2.
      assert (i2 < n) by lia.
      iPoseProof (twp_store_offset _ _ _ (Z.to_nat i2)
                                   (heapG0:=heapG2) with "Hl2") as "HH".
      { rewrite Hvs2. eauto. }
      rewrite Z2Nat.id; try lia. (*XXX*)
      iApply "HH"; eauto. }

    iIntros (??). iDestruct 1 as (->) "Hl1". iDestruct 1 as (->) "Hl2".
    iNext.

    iDestruct (lrel_list_update_both _ _ _ _ i1 i2 with "Hv HAs") as "HAs";
      (lia || eauto).

    iMod ("Hcl" with "[-]") as "_".
    { iNext. iExists _,_. iFrame "HAs Hl1".
      rewrite !insert_length.
      repeat iSplit; eauto. }
    iModIntro. rewrite interp_eq ; eauto.
  Qed.

  (** ** The main 'set' typing *)
  Lemma set_spec (a1 a2 : val) iv1 iv2 v1 v2 A ξ :
    pseudo_refl A ξ →
    contractible A ξ →
    lrel_array A ξ a1 a2 -∗
    ⟦ tint High ⟧ ξ iv1 iv2 -∗
    A ξ v1 v2 -∗
    DWP (set a1 iv1 v1) & (set a2 iv2 v2) : ⟦ tunit ⟧ ξ.
  Proof.
    iIntros (PR C).
    iDestruct 1 as (l1 l2 n -> ->) "Ha".
    iDestruct 1 as (i1 i2 -> ->) "_".
    iIntros "#Hv".
    dwp_rec. dwp_pures.
    repeat case_bool_decide; dwp_pures;
      try iApply logrel_unit.
    - iApply (array_set_rhs with "Hv Ha"); eauto. lia.
    - iApply (array_set_rhs with "Hv Ha"); eauto. lia.
    - iApply (array_set_rhs with "Hv Ha"); eauto. lia.
    - iApply (array_set_lhs with "Hv Ha"); eauto. lia.
    - iApply (array_set_lhs with "Hv Ha"); eauto. lia.
    - iApply (array_set_lhs with "Hv Ha"); eauto. lia.
    - iApply (array_set_both with "Hv Ha"); eauto; lia.
  Qed.

End spec.
