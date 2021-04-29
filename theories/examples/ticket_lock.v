From iris.base_logic Require Import invariants.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import excl auth gset.
From iris_ni.proofmode Require Import dwp_tactics.
From iris.heap_lang.lib Require Export ticket_lock.


Section proof.
  Context `{!heapDG Σ, !tlockG Σ}.

  Variable N : namespace.

  Definition lock_inv (γ : gname) (lo1 ln1 lo2 ln2 : loc) (R : iProp Σ) : iProp Σ :=
    (∃ o n : nat,
      lo1 ↦ₗ #o ∗ ln1 ↦ₗ #n ∗
      lo2 ↦ᵣ #o ∗ ln2 ↦ᵣ #n ∗
      own γ (● (Excl' o, GSet (set_seq 0 n))) ∗
      ((own γ (◯ (Excl' o, GSet ∅)) ∗ R) ∨ own γ (◯ (ε, GSet {[ o ]}))))%I.


  Definition is_lock (γ : gname) (lk1 lk2 : val) (R : iProp Σ) : iProp Σ :=
    (∃ lo1 ln1 lo2 ln2: loc, ⌜lk1 = (#lo1, #ln1)%V⌝ ∧ ⌜lk2 = (#lo2, #ln2)%V⌝
        ∧ inv N (lock_inv γ lo1 ln1 lo2 ln2 R))%I.

  Definition issued (γ : gname) (x : nat) : iProp Σ :=
    own γ (◯ (ε, GSet {[ x ]}))%I.

  Definition locked (γ : gname) : iProp Σ := (∃ o, own γ (◯ (Excl' o, GSet ∅)))%I.

  Lemma locked_exclusive (γ : gname) : locked γ -∗ locked γ -∗ False.
  Proof.
    iDestruct 1 as (o1) "H1". iDestruct 1 as (o2) "H2".
    iDestruct (own_valid_2 with "H1 H2") as %[[] _]%auth_frag_op_valid_1.
  Qed.

  Lemma newlock_spec (R : iProp Σ) Φ :
    R -∗
    (∀ γ lk1 lk2, is_lock γ lk1 lk2 R -∗ Φ lk1 lk2) -∗
    DWP newlock #() & newlock #() : Φ.
  Proof.
    iIntros "R HΦ".
    unlock newlock. dwp_pures=>/=.
    dwp_bind (ref _)%E (ref _)%E.
    iApply dwp_alloc. iIntros (ln1 ln2) "Hln1 Hln2".
    iNext.

    dwp_bind (ref _)%E (ref _)%E.
    iApply dwp_alloc. iIntros (lo1 lo2) "Hlo1 Hlo2".
    iNext.

    iMod (own_alloc (● (Excl' 0%nat, GSet ∅) ⋅ ◯ (Excl' 0%nat, GSet ∅))) as (γ) "[Hγ Hγ']".
    { by apply auth_both_valid_discrete. }
    iMod (inv_alloc N _ (lock_inv γ lo1 ln1 lo2 ln2 R) with "[-HΦ]") as "Hinv".
    { iNext. rewrite /lock_inv.
      iExists 0%nat, 0%nat. iFrame. iLeft. by iFrame. }
    dwp_pures. iApply dwp_value. iModIntro.
    iApply "HΦ". rewrite /is_lock.
    iExists lo1,ln1,lo2,ln2. eauto.
  Qed.


  Lemma wait_loop_spec γ lk1 lk2 x R Φ :
    is_lock γ lk1 lk2 R -∗
    issued γ x -∗
    (locked γ -∗ R -∗ Φ #() #()) -∗
    DWP wait_loop #x lk1 & wait_loop #x lk2 : Φ.
  Proof.
    iIntros "Hl Ht HΦ".
    iDestruct "Hl" as (lo1 ln1 lo2 ln2 -> ->) "#Hinv".
    iLöb as "IH". dwp_rec. dwp_pures.
    dwp_bind (! _)%E (! _)%E.
    iInv N as (o n) "(>Hlo1 & >Hln1 & >Hlo2 & >Hln2 & Ha)".
    iApply (dwp_load with "Hlo1 Hlo2"). iIntros "Hlo1 Hlo2".
    destruct (decide (x = o)) as [->|Hneq].
    - iDestruct "Ha" as "[Hainv [[Ho HR] | Haown]]".
      + iNext. iModIntro. iSplitL "Hlo1 Hln1 Hlo2 Hln2 Hainv Ht".
        { iNext. iExists o, n. iFrame. }
        dwp_pures.
        case_bool_decide; [|done]. dwp_pures. iApply dwp_value.
        iModIntro.
        iApply ("HΦ" with "[Ho] HR").
        rewrite /locked. eauto.
      + iNext.
        iDestruct (own_valid_2 with "Ht Haown") as % [_ ?%gset_disj_valid_op]%auth_frag_op_valid_1.
        set_solver.
    - iNext. iModIntro. iSplitL "Hlo1 Hln1 Hlo2 Hln2 Ha".
      { iNext. iExists o, n. by iFrame. }
      dwp_pures.
      case_bool_decide; [simplify_eq |]. dwp_pures.
      iApply ("IH" with "Ht HΦ").
  Qed.

  Lemma acquire_spec γ lk1 lk2 R Φ :
    is_lock γ lk1 lk2 R -∗
    (locked γ -∗ R -∗ Φ #() #()) -∗
    DWP acquire lk1 & acquire lk2 : Φ.
  Proof.
    iIntros "Hl HΦ".
    iDestruct "Hl" as (lo1 ln1 lo2 ln2 -> ->) "#Hinv".
    iLöb as "IH". dwp_rec. dwp_pures.
    dwp_bind (! _)%E (! _)%E. simplify_eq/=.
    iInv N as (o n) "(>Hlo1 & >Hln1 & >Hlo2 & >Hln2 & Ha)".
    iApply (dwp_load with "Hln1 Hln2"). iIntros "Hln1 Hln2".
    iNext. iModIntro. iSplitL "Hlo1 Hln1 Hlo2 Hln2 Ha".
    { iNext. iExists o, n. by iFrame. }
    dwp_pures. dwp_bind (CmpXchg _ _ _) (CmpXchg _ _ _).
    iInv N as (o' n') "(>Hlo1 & >Hln1 & >Hlo2 & >Hln2 & >Hauth & Haown)".
    destruct (decide (#n' = #n))%V as [[= ->%Nat2Z.inj] | Hneq].
    - iMod (own_update with "Hauth") as "[Hauth Hofull]".
      { eapply auth_update_alloc, prod_local_update_2.
        eapply (gset_disj_alloc_empty_local_update _ {[ n ]}).
        apply (set_seq_S_end_disjoint 0). }
      rewrite -(set_seq_S_end_union_L 0).
      pose (Ψ1 := (λ v, ⌜v = (#n, #true)%V⌝ ∗ ln1 ↦ₗ #(n+1))%I).
      pose (Ψ2 := (λ v, ⌜v = (#n, #true)%V⌝ ∗ ln2 ↦ᵣ #(n+1))%I).
      iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[Hln1] [Hln2]").
      { rewrite /TWP1 /Ψ1. wp_cmpxchg_suc. eauto with iFrame. }
      { rewrite /TWP2 /Ψ2. wp_cmpxchg_suc. eauto with iFrame. }
      iIntros (? ?) "[-> Hln1] [-> Hln2]". iNext.
      iModIntro. iSplitL "Hlo1 Hln1 Hlo2 Hln2 Haown Hauth".
      { iNext. iExists o', (S n).
        rewrite Nat2Z.inj_succ -Z.add_1_r. by iFrame. }
      dwp_pures.
      iApply (wait_loop_spec γ (#lo1, #ln1) (#lo2, #ln2) with "[] Hofull HΦ").
      iFrame. rewrite /is_lock; eauto 10.
    - pose (Ψ1 := (λ v, ⌜v = (#n', #false)%V⌝ ∗ ln1 ↦ₗ #n')%I).
      pose (Ψ2 := (λ v, ⌜v = (#n', #false)%V⌝ ∗ ln2 ↦ᵣ #n')%I).
      iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[Hln1] [Hln2]").
      { rewrite /TWP1 /Ψ1. wp_cmpxchg_fail. eauto with iFrame. }
      { rewrite /TWP2 /Ψ2. wp_cmpxchg_fail. eauto with iFrame. }
      iIntros (? ?) "[-> Hln1] [-> Hln2]". iNext.
      iModIntro. iSplitL "Hlo1 Hln1 Hlo2 Hln2 Hauth Haown".
      { iNext. iExists o', n'. by iFrame. }
      dwp_pures. by iApply "IH"; auto.
  Qed.

  Lemma release_spec γ lk1 lk2 R Φ :
    is_lock γ lk1 lk2 R -∗
    locked γ -∗
    R -∗
    Φ #() #() -∗
    DWP release lk1 & release lk2 : Φ.
  Proof.
    iIntros "Hl Hγ HR HΦ".
    iDestruct "Hl" as (lo1 ln1 lo2 ln2 -> ->) "#Hinv".
    iDestruct "Hγ" as (o) "Hγo".
    dwp_rec. dwp_pures. dwp_bind (! _)%E (! _)%E.
    iInv N as (o' n) "(>Hlo1 & >Hln1 & >Hlo2 & >Hln2 & >Hauth & Haown)".
    iApply (dwp_load with "Hlo1 Hlo2"). iIntros "Hlo1 Hlo2". iNext.
    iDestruct (own_valid_2 with "Hauth Hγo") as
      %[[<-%Excl_included%leibniz_equiv _]%prod_included _]%auth_both_valid_discrete.
    iModIntro. iSplitL "Hlo1 Hln1 Hlo2 Hln2 Hauth Haown".
    { iNext. iExists o, n. by iFrame. }
    dwp_pures.
    iInv N as (o' n') "(>Hlo1 & >Hln1 & >Hlo2 & >Hln2 & >Hauth & Haown)".
    iApply dwp_fupd. iApply (dwp_store with "Hlo1 Hlo2").
    iIntros "Hlo1 Hlo2". iNext. iModIntro.
    iDestruct (own_valid_2 with "Hauth Hγo") as
      %[[<-%Excl_included%leibniz_equiv _]%prod_included _]%auth_both_valid_discrete.
    iDestruct "Haown" as "[[Hγo' _]|Haown]".
    { iDestruct (own_valid_2 with "Hγo Hγo'") as %[[] ?]%auth_frag_op_valid_1. }
    iMod (own_update_2 with "Hauth Hγo") as "[Hauth Hγo]".
    { apply auth_update, prod_local_update_1.
      by apply option_local_update, (exclusive_local_update _ (Excl (S o))). }
    iModIntro. iSplitR "HΦ"; last by iApply "HΦ". iNext.
    iExists (S o), n'.
    rewrite Nat2Z.inj_succ -Z.add_1_r. iFrame. iLeft. by iFrame.
  Qed.

End proof.
