From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import tactics.
From iris_ni.logrel Require Import interp.
From iris_ni.proofmode Require Import dwp_tactics.
From iris.heap_lang Require Import lang proofmode.

Definition rand : val := λ: <>,
  let: "x" := ref #true in
  Fork ("x" <- #false);;
  !"x".

Section proof.
  Context `{!heapDG Σ}.

  Lemma rand_sec ξ :
    DWP rand #() & rand #() : ⟦ tbool Low ⟧ ξ.
  Proof.
    unlock rand.
    dwp_pures. simpl.
    dwp_bind (ref #true)%E (ref #true)%E.
    pose (Φ1 := (λ v, ∃ (l : loc), ⌜v = #l⌝ ∗ l ↦ₗ #true)%I).
    pose (Φ2 := (λ v, ∃ (l : loc), ⌜v = #l⌝ ∗ l ↦ᵣ #true)%I).
    iApply (dwp_atomic_lift_wp Φ1 Φ2%I); try done.
    iModIntro. repeat iSplitR.
    { rewrite /WP1 /Φ1. wp_alloc l1 as "Hl". eauto with iFrame. }
    { rewrite /WP2 /Φ2. wp_alloc l1 as "Hl". eauto with iFrame. }
    iIntros (? ?).
    iDestruct 1 as (l1 ->) "Hl1".
    iDestruct 1 as (l2 ->) "Hl2". clear Φ1 Φ2.
    pose (N := nroot.@"rand").
    iMod (inv_alloc N _
             (∃ (b : bool), l1 ↦ₗ #b ∗ l2 ↦ᵣ #b)%I
            with "[-]") as "#Hinv".
    { eauto with iFrame. }
    iModIntro. iNext. dwp_pures=>/=.
    dwp_bind (Fork _) (Fork _).
    iApply (dwp_wand with "[-]").
    { iApply (logrel_fork ξ).
      pose (Φ1 := (λ v, ⌜v = #()⌝ ∗ l1 ↦ₗ #false)%I).
      pose (Φ2 := (λ v, ⌜v = #()⌝ ∗ l2 ↦ᵣ #false)%I).
      iApply (dwp_atomic_lift_wp Φ1 Φ2%I); try done.
      iInv N as (b) "[Hl1 Hl2]" "Hcl". iModIntro.
      iSplitL "Hl1"; [|iSplitL "Hl2"].
      - rewrite /WP1 /Φ1. wp_store. eauto.
      - rewrite /WP2 /Φ2. wp_store. eauto.
      - iIntros (? ?) "[-> Hl1] [-> Hl2]".
        iMod ("Hcl" with "[-]") as "_".
        + iNext. iExists false. iFrame.
        + iModIntro. iNext. eauto. }
    iIntros (? ?) "[-> ->]". dwp_pures=>/=.
    iApply dwp_atomic; try done.
    iInv N as (b) "[Hl1 Hl2]" "Hcl".
    iModIntro. iApply (dwp_load with "Hl1 Hl2").
    iIntros "Hl1 Hl2". iNext.
    iMod ("Hcl" with "[-]") as "_".
    { iNext. eauto with iFrame. }
    iModIntro. iExists b,b. eauto.
  Qed.
End proof.
