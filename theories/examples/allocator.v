(* TODO: ressurect this file later *)
From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types interp.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import tactics.
From iris_ni.proofmode Require Import dwp_tactics.
From iris.heap_lang Require Import lang array proofmode.
From iris.algebra Require Import excl.

From iris_ni.examples Require Import lock.

Definition allocator_alloc : val :=
  λ: "arr" "i" "sz" "v",
  let: "pos" := !"i" in
  if: ("sz" ≤ "pos")
  then NONE
  else "i" <- "pos" + #1;;
       let: "c" := "arr" +ₗ "pos" in
       "c" <- "v";;
       SOME "c".

Definition new_allocator : val :=
  λ: "z",
  let: "arr" := AllocN "z" NONE in
  let: "i" := ref #0 in
  let: "lk" := newlock #() in
  (λ: "v", acquire "lk";;
           let: "c" := allocator_alloc "arr" "i" "z" "v" in
           release "lk";; "c").


Section proof.
  Context `{!heapDG Σ, !lockG Σ}.

  Definition aN := nroot.@"allocator".

  Definition allocator_inv l1 l2 i1 i2 sz : iProp Σ :=
    (∃ i : Z, ⌜0 ≤ i ≤ sz⌝ ∗
               (l1 +ₗ i) ↦ₗ∗ replicate (Z.to_nat (sz-i)) NONEV ∗
               (l2 +ₗ i) ↦ᵣ∗ replicate (Z.to_nat (sz-i)) NONEV ∗
               i1 ↦ₗ #i ∗ i2 ↦ᵣ #i)%I.


  Lemma new_allocator_spec (sz : Z) ξ Φ :
    0 < sz →
    (∀ (a1 a2 : val),
        (∀ (α : slevel), ⟦ tarrow (tint α) (toption (tref (tint α))) Low ⟧ ξ a1 a2) -∗
        Φ a1 a2) -∗
    DWP new_allocator #sz & new_allocator #sz : Φ.
  Proof.
    iIntros (Hsz) "H".
    dwp_rec. dwp_pures.
    dwp_bind (AllocN _ _) (AllocN _ _).
    (* allocN spec *)
    set (meta_token1 := @meta_token _ _ _ _ _ heapDG_gen_heapG1).
    set (meta_token2 := @meta_token _ _ _ _ _ heapDG_gen_heapG2).
    pose (Ψ1 := (λ v, ∃ l : loc, ⌜v = #l⌝ ∗ l ↦ₗ∗ replicate (Z.to_nat sz) NONEV ∗
                 ([∗ list] i ∈ seq 0 (Z.to_nat sz), meta_token1 (l +ₗ Z.of_nat i) ⊤))%I).
    pose (Ψ2 := (λ v, ∃ l : loc, ⌜v = #l⌝ ∗ l ↦ᵣ∗ replicate (Z.to_nat sz) NONEV ∗
                 ([∗ list] i ∈ seq 0 (Z.to_nat sz), meta_token2 (l +ₗ Z.of_nat i) ⊤))%I).
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2).
    - iApply twp_allocN; try done.
      iIntros (l) "[Hl Hmeta]". iExists l.
      iSplit; eauto. iSplitL "Hl". iExact "Hl". iFrame.
    - iApply twp_allocN; try done.
      iIntros (l) "[Hl Hmeta]". iExists l.
      iSplit; eauto. iSplitL "Hl". iExact "Hl". iFrame.
    - iIntros (? ?). iDestruct 1 as (l1) "[-> [Hl1 Hmeta1]]".
      iDestruct 1 as (l2) "[-> [Hl2 Hmeta2]]".
      (* / allocN spec *)
      iClear "Hmeta1 Hmeta2".

      iNext. dwp_pures.
      dwp_bind (ref _)%E (ref _)%E.
      iApply dwp_alloc. iIntros (i1 i2) "Hi1 Hi2". iNext. dwp_pures.

      dwp_bind (newlock #()) (newlock #()).
      iApply (newlock_spec aN (allocator_inv l1 l2 i1 i2 sz) with "[Hl1 Hl2 Hi1 Hi2]").
      { iExists 0. rewrite !loc_add_0. assert (sz - 0 = sz) as -> by lia.
        iFrame. iPureIntro. lia. }
      iIntros (γ lk1 lk2) "#Hlk". dwp_pures.

      iApply dwp_value. iModIntro. iApply "H". iIntros (α).
      rewrite interp_eq. iModIntro. iIntros (v1 v2) "#Hv".
      dwp_pures.

      dwp_bind (acquire _)%E (acquire _)%E.
      iApply (acquire_spec with "Hlk"). iIntros "Hlocked".
      iDestruct 1 as (i Hi) "(Hl1&Hl2&Hi1&Hi2)".

      dwp_pures. dwp_rec. dwp_pures.
      dwp_bind (! _)%E (! _)%E. iApply (dwp_load with "Hi1 Hi2").
      iIntros "Hi1 Hi2". iNext. dwp_pures.
      case_bool_decide; dwp_pures.
      + dwp_bind (release _)%E (release _)%E.
        iApply (release_spec with "Hlk Hlocked [Hl1 Hl2 Hi1 Hi2]").
        { iExists i. iSplit. done. iFrame. }
        dwp_pures. iApply logrel_none.
      + dwp_bind (_ <- _)%E (_ <- _)%E.
        iApply (dwp_store with "Hi1 Hi2"). iIntros "Hi1 Hi2".
        iNext. dwp_pures.
        assert (Z.to_nat (sz - i) = S (Z.to_nat (sz - (i + 1)))) as ->.
        { destruct Hi. rewrite -Z2Nat.inj_succ; last by lia.
          f_equal. lia. }
        simpl. rewrite array1_cons array2_cons.
        iDestruct "Hl1" as "[Hcell1 Hl1]".
        iDestruct "Hl2" as "[Hcell2 Hl2]".
        dwp_bind (_ <- _)%E (_ <- _)%E.
        iApply (dwp_store with "Hcell1 Hcell2").
        iIntros "Hcell1 Hcell2". iNext. dwp_pures.

        dwp_bind (release _) (release _).
        iApply (release_spec with "Hlk Hlocked [Hl1 Hl2 Hi1 Hi2]").
        { iExists (i+1). iSplit.
          - iPureIntro; lia.
          - iFrame. rewrite !loc_add_assoc. iFrame. }
        dwp_pures. iApply logrel_some.
        iMod (interp_ref_alloc with "Hcell1 Hcell2 Hv") as "#Hcell".
        iApply dwp_value. eauto.
  Qed.

End proof.
