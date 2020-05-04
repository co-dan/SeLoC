From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types interp.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import tactics.
From iris_ni.proofmode Require Import dwp_tactics.
From iris.heap_lang Require Import lang proofmode.
From iris.algebra Require Import excl.

From iris.heap_lang.lib Require Export spin_lock.

Section proof.
  Context `{!heapDG Σ, !lockG Σ}.

  Variable N : namespace.

  Definition lock_inv (γ : gname) (l1 l2 : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l1 ↦ₗ #b ∗ l2 ↦ᵣ #b ∗
       if b then True else own γ (Excl ()) ∗ R)%I.

  Definition is_lock (γ : gname) (lk1 lk2 : val) (R : iProp Σ) : iProp Σ :=
    (∃ l1 l2: loc, ⌜lk1 = #l1⌝ ∧ ⌜lk2 = #l2⌝
        ∧ inv N (lock_inv γ l1 l2 R))%I.

  Definition locked (γ : gname) : iProp Σ := own γ (Excl ()).


  Lemma newlock_spec (R : iProp Σ) Φ :
    R -∗
    (∀ γ lk1 lk2, is_lock γ lk1 lk2 R -∗ Φ lk1 lk2) -∗
    DWP newlock #() & newlock #() : Φ.
  Proof.
    iIntros "R HΦ".
    unlock newlock. dwp_pures=>/=.
    iApply dwp_fupd.
    pose (Ψ1 := (λ v, ∃ l : loc, ⌜v = #l⌝ ∗ l ↦ₗ #false)%I).
    pose (Ψ2 := (λ v, ∃ l : loc, ⌜v = #l⌝ ∗ l ↦ᵣ #false)%I).
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2).
    { rewrite /TWP1. wp_alloc l as "Hl".
      iExists l. eauto with iFrame. }
    { rewrite /TWP2. wp_alloc l as "Hl".
      iExists l. eauto with iFrame. }
    iIntros (? ?). iDestruct 1 as (l1 ->) "Hl1". iDestruct 1 as (l2 ->) "Hl2".
    iNext. iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc N _ (lock_inv γ l1 l2 R) with "[-HΦ]") as "#Hinv".
    { iIntros "!>". iExists false. by iFrame. }
    iModIntro. iApply ("HΦ" $! γ).
    iExists l1,l2. eauto with iFrame.
  Qed.

  Lemma try_acquire_spec γ lk1 lk2 R Φ :
    is_lock γ lk1 lk2 R -∗
    (∀ b : bool, (if b then locked γ ∗ R else True) -∗ Φ #b #b) -∗
    DWP try_acquire lk1 & try_acquire lk2 : Φ.
  Proof.
    iIntros "#Hlk HΦ". iDestruct "Hlk" as (l1 l2 -> ->) "#Hinv".
    unlock try_acquire. dwp_pures=>/=.
    dwp_bind (CmpXchg _ _ _) (CmpXchg _ _ _).
    iApply dwp_atomic.
    iInv N as (b) "(>Hl1 & >Hl2 & HR)" "Hcl". iModIntro.
    pose (Ψ1 := (λ v, ⌜v = (#b, #(negb b))%V⌝ ∗ l1 ↦ₗ #true)%I).
    pose (Ψ2 := (λ v, ⌜v = (#b, #(negb b))%V⌝ ∗ l2 ↦ᵣ #true)%I).
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[Hl1] [Hl2] [-]").
    { rewrite /TWP1 /Ψ1. destruct b.
      by wp_cmpxchg_fail; iFrame.
      by wp_cmpxchg_suc; iFrame. }
    { rewrite /TWP2 /Ψ2. destruct b.
      by wp_cmpxchg_fail; iFrame.
      by wp_cmpxchg_suc; iFrame. }
    iIntros (? ?). iDestruct 1 as (->) "Hl1". iDestruct 1 as (->) "Hl2".
    iNext. iMod ("Hcl" with "[-HR HΦ]") as "_".
    { iNext. iExists true. by iFrame. }
    iModIntro. dwp_pures. iApply dwp_value. iModIntro.
    iApply ("HΦ" $! (negb b)).
    by destruct b.
  Qed.

  Lemma acquire_spec γ lk1 lk2 R Φ :
    is_lock γ lk1 lk2 R -∗
    (locked γ -∗ R -∗ Φ #() #()) -∗
    DWP acquire lk1 & acquire lk2 : Φ.
  Proof.
    iIntros "#Hinv HΦ".
    unlock acquire. dwp_pures=>/=. iLöb as "IH".
    dwp_bind (try_acquire _) (try_acquire _).
    iApply (try_acquire_spec with "Hinv"). iIntros ([]).
    - iIntros "[Hlked HR]". dwp_pures.
      iApply dwp_value. by iApply ("HΦ" with "Hlked HR").
    - iIntros "_". dwp_pures=>/=.
      by iApply "IH".
  Qed.

  Lemma release_spec γ lk1 lk2 R Φ :
    is_lock γ lk1 lk2 R -∗
    locked γ -∗
    R -∗
    Φ #() #() -∗
    DWP release lk1 & release lk2 : Φ.
  Proof.
    iIntros "#Hinv Hlked HR HΦ".
    rewrite/release. dwp_pures=>/=.
    iDestruct "Hinv" as (l1 l2 -> ->) "#Hinv".
    pose (Ψ1 := (λ v, ⌜v = #()⌝ ∗ l1 ↦ₗ #false)%I).
    pose (Ψ2 := (λ v, ⌜v = #()⌝ ∗ l2 ↦ᵣ #false)%I).
    iApply dwp_atomic.
    iInv N as (b) "(>Hl1 & >Hl2 & Hb)" "Hcl".
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[Hl1] [Hl2] [-]").
    { rewrite /TWP1 /Ψ1. wp_store. eauto with iFrame. }
    { rewrite /TWP2 /Ψ2. wp_store. eauto with iFrame. }
    iIntros (? ?). iDestruct 1 as (->) "Hl1". iDestruct 1 as (->) "Hl2".
    iNext. iMod ("Hcl" with "[-HΦ]") as "_".
    { iNext. iExists false. by iFrame. }
    eauto with iFrame.
  Qed.

End proof.

Section semtyping.
  Context `{!heapDG Σ}.

  Lemma newlock_typed ξ :
    ⊢ DWP newlock #() & newlock #() : ⟦ tmutex ⟧ ξ.
  Proof.
    rewrite tmutex_eq.
    unlock newlock. dwp_pures=>/=.
    iApply logrel_alloc. iApply logrel_bool.
  Qed.

  Lemma acquire_typed ξ :
    ⊢ DWP acquire & acquire : ⟦ tarrow tmutex tunit Low ⟧ ξ.
  Proof.
    rewrite tmutex_eq.
    unfold acquire. dwp_pures. iApply dwp_value. iModIntro.
    rewrite interp_eq. iAlways. iIntros (lk1 lk2) "#Hlk".
    dwp_pures. iLöb as "IH".
    rewrite {5 7}/try_acquire. dwp_pures.
    dwp_bind (CmpXchg _ _ _) (CmpXchg _ _ _).
    rewrite /tmutex (interp_eq (tref _)).
    iDestruct "Hlk" as (l1 l2 -> ->) "Hinv".
    iInv (locsN.@(l1, l2)) as (w1 w2) "(>Hl1 & >Hl2 & >Hw)".
    iDestruct "Hw" as (b b' -> ->) "%".
    assert (b = b') as <- by (destruct ξ; eauto).
    destruct b.
    - pose (Φ1 := (λ v, ⌜v = (#true, #false)%V⌝ ∧ l1 ↦ₗ #true)%I).
      pose (Φ2 := (λ v, ⌜v = (#true, #false)%V⌝ ∧ l2 ↦ᵣ #true)%I).
      iApply (dwp_atomic_lift_wp Φ1 Φ2 with "[Hl1] [Hl2] [-]"); unfold TWP1, TWP2.
      { wp_cmpxchg_fail. unfold Φ1. iFrame. eauto. }
      { wp_cmpxchg_fail. unfold Φ2. iFrame. eauto. }
      iIntros (? ?). iDestruct 1 as "[-> Hl1]". iDestruct 1 as "[-> Hl2]".
      iNext. iModIntro. iSplitL "Hl1 Hl2".
      { iNext. iExists _,_. iFrame. rewrite interp_eq.
        iExists _,_. eauto with iFrame. }
      dwp_pures. iApply "IH".
    - pose (Φ1 := (λ v, ⌜v = (#false, #true)%V⌝ ∧ l1 ↦ₗ #true)%I).
      pose (Φ2 := (λ v, ⌜v = (#false, #true)%V⌝ ∧ l2 ↦ᵣ #true)%I).
      iApply (dwp_atomic_lift_wp Φ1 Φ2 with "[Hl1] [Hl2] [-]"); unfold TWP1, TWP2.
      { wp_cmpxchg_suc. unfold Φ1. iFrame. eauto. }
      { wp_cmpxchg_suc. unfold Φ2. iFrame. eauto. }
      iIntros (? ?). iDestruct 1 as "[-> Hl1]". iDestruct 1 as "[-> Hl2]".
      iNext. iModIntro. iSplitL "Hl1 Hl2".
      { iNext. iExists _,_. iFrame. rewrite interp_eq.
        iExists _,_. eauto with iFrame. }
      dwp_pures. iApply logrel_unit.
  Qed.

  Lemma release_typed ξ :
    ⊢ DWP release & release : ⟦ tarrow tmutex tunit Low ⟧ ξ.
  Proof.
    rewrite tmutex_eq.
    unfold release. dwp_pures. iApply dwp_value. iModIntro.
    rewrite interp_eq. iAlways. iIntros (lk1 lk2) "#Hlk".
    dwp_pures. iApply logrel_store; eauto.
    - rewrite /tmutex. iApply dwp_value. iApply "Hlk".
    - iApply logrel_bool.
  Qed.

End semtyping.
