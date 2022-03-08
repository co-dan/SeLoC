From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import proofmode.
From iris_ni.proofmode Require Import dwp_tactics.
From iris.heap_lang Require Import lang proofmode.
From iris.algebra Require Import excl.

From iris.heap_lang.lib Require Export spawn par.

Section proof.
  Context `{!heapDG Σ, !spawnG Σ}.

  (** * Spawn *)
  Definition spawn_inv (γ : gname) (l1 l2 : loc) (Ψ : val → val → iProp Σ) : iProp Σ :=
    (∃ lv1 lv2, l1 ↦ₗ lv1 ∗ l2 ↦ᵣ lv2 ∗
      ((⌜lv1 = NONEV⌝ ∗ ⌜lv2 = NONEV⌝) ∨
       (∃ w1 w2, ⌜lv1 = SOMEV w1⌝ ∗ ⌜lv2 = SOMEV w2⌝
           ∗ (Ψ w1 w2 ∨ own γ (Excl ())))))%I.

  Definition join_handle N (l1 l2 : loc) (Ψ : val → val → iProp Σ) : iProp Σ :=
    (∃ γ, own γ (Excl ()) ∗ inv N (spawn_inv γ l1 l2 Ψ))%I.

  Lemma spawn_spec N Ψ (f1 f2 : val) Φ :
    (DWP f1 #() & f2 #() : Ψ) -∗
    (∀ l1 l2, join_handle N l1 l2 Ψ -∗ Φ #l1 #l2) -∗
    DWP spawn f1 & spawn f2 : Φ.
  Proof.
    iIntros "Hf HΦ". unlock spawn. dwp_pures=>/=.
    dwp_bind (ref _)%E (ref _)%E.

    pose (Ψ1 := (λ v, ∃ l : loc, ⌜v = #l⌝ ∗ l ↦ₗ NONEV)%I).
    pose (Ψ2 := (λ v, ∃ l : loc, ⌜v = #l⌝ ∗ l ↦ᵣ NONEV)%I).
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2).
    { rewrite /TWP1. wp_alloc l as "Hl".
      iExists l. eauto with iFrame. }
    { rewrite /TWP2. wp_alloc l as "Hl".
      iExists l. eauto with iFrame. }
    iIntros (??). iDestruct 1 as (l1 ->) "Hl1". iDestruct 1 as (l2 ->) "Hl2".
    clear Ψ1 Ψ2. iModIntro. dwp_pures=>/=.

    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc N _ (spawn_inv γ l1 l2 Ψ) with "[Hl1 Hl2]") as "#Hinv".
    { iNext. iExists NONEV, NONEV. iFrame; eauto. }

    dwp_bind (Fork _) (Fork _). iApply (dwp_fork with "[Hf]").
    { iNext. dwp_bind (f1 #()) (f2 #()).
      iApply (dwp_wand with "Hf").
      iIntros (w1 w2) "HΨ". dwp_pures=>/=.

      pose (Ψ1 := (λ v, ⌜v = #()⌝ ∗ l1 ↦ₗ SOMEV w1)%I).
      pose (Ψ2 := (λ v, ⌜v = #()⌝ ∗ l2 ↦ᵣ SOMEV w2)%I).
      iApply dwp_atomic.
      iInv N as (v1 v2) "(>Hl1 & >Hl2 & _)" "Hcl".
      iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[Hl1] [Hl2] [-]").
      { rewrite /TWP1 /Ψ1. wp_store. eauto with iFrame. }
      { rewrite /TWP2 /Ψ2. wp_store. eauto with iFrame. }
      iIntros (??). iDestruct 1 as (->) "Hl1". iDestruct 1 as (->) "Hl2".
      iNext. iApply "Hcl".
      iNext. iExists (SOMEV w1), (SOMEV w2). iFrame.
      iRight. iExists _,_. eauto with iFrame. }
    iNext. dwp_pures=>/=. iApply dwp_value.
    iModIntro. iApply "HΦ". rewrite /join_handle.
    eauto with iFrame.
  Qed.

  Lemma join_spec N (Ψ : val → val → iProp Σ) l1 l2 Φ :
    join_handle N l1 l2 Ψ -∗
    (∀ v1 v2, Ψ v1 v2 -∗ Φ v1 v2) -∗
    DWP join #l1 & join #l2 : Φ.
  Proof.
    iIntros "H HΦ". iDestruct "H" as (γ) "[Hγ #Hinv]".
    iLöb as "IH". rewrite {3 4}/join. dwp_pures=>/=.

    dwp_bind (! _)%E (! _)%E.
    iApply dwp_atomic.
    iInv N as (v1 v2) "(>Hl1 & >Hl2 & H)" "Hcl".
    pose (Ψ1 := (λ v, ⌜v = v1⌝ ∗ l1 ↦ₗ v)%I).
    pose (Ψ2 := (λ v, ⌜v = v2⌝ ∗ l2 ↦ᵣ v)%I).
    iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[Hl1] [Hl2] [-]").
    { rewrite /TWP1 /Ψ1. wp_load. eauto with iFrame. }
    { rewrite /TWP2 /Ψ2. wp_load. eauto with iFrame. }
    iIntros (??). iDestruct 1 as (->) "Hl1". iDestruct 1 as (->) "Hl2".
    iDestruct "H" as "[>[%%]|H]"; simplify_eq/=.
    - iNext. iMod ("Hcl" with "[Hl1 Hl2]").
      { iNext. iExists _,_. eauto with iFrame. }
      iModIntro. do 3 dwp_pure _ _. simpl.
      iApply ("IH" with "Hγ HΦ").
    - iDestruct "H" as (w1 w2) "(>% & >% & [H|H])"; simplify_eq/=.
      + iNext. iMod ("Hcl" with "[Hl1 Hl2 Hγ]").
        { iNext. iExists _,_. iFrame.
          iRight. iExists _,_. eauto with iFrame. }
        iModIntro. dwp_pures=>/=.
        iApply dwp_value. iModIntro.
        by iApply ("HΦ" with "H").
      + iDestruct (own_valid_2 with "H [Hγ]") as ">Hfoo".
        { iNext. done. }
        iDestruct "Hfoo" as %[].
  Qed.

  (** * Par *)
  Definition parN : namespace := nroot .@ "par".

  Lemma par_spec (Ψ1 Ψ2 : val → val → iProp Σ) (f1 f2 g1 g2 : val) (Φ : val → val → iProp Σ) :
    (DWP f1 #() & g1 #() : Ψ1) -∗
    (DWP f2 #() & g2 #() : Ψ2) -∗
    (▷ ∀ v1 w1 v2 w2, Ψ1 v1 w1 -∗ Ψ2 v2 w2 -∗ ▷ Φ (v1,v2)%V (w1,w2)%V) -∗
    DWP par f1 f2 & par g1 g2 : Φ.
  Proof.
    iIntros "Hf Hg HΦ". unlock par.
    dwp_pures=>/=. dwp_bind (spawn _) (spawn _).
    iApply (spawn_spec parN with "Hf").
    iIntros (l1 l2) "Hjoin".
    dwp_pures=>/=. dwp_bind (f2 #()) (g2 #()).
    iApply (dwp_wand with "Hg"). iIntros (w1 w2) "Hw".
    dwp_pures=>/=. dwp_bind (join _) (join _).
    iApply (join_spec with "Hjoin").
    iIntros (v1 v2) "Hv".
    iSpecialize ("HΦ" with "Hv Hw").
    dwp_pures=>/=. iApply dwp_value. done.
  Qed.

  Lemma dwp_par (Ψ1 Ψ2 : val → val → iProp Σ) e1 e2 t1 t2 (Φ : val → val → iProp Σ) :
    (DWP e1 & t1 : Ψ1) -∗
    (DWP e2 & t2 : Ψ2) -∗
    (∀ v1 w1 v2 w2, Ψ1 v1 w1 -∗ Ψ2 v2 w2 -∗ ▷ Φ (v1,v2)%V (w1,w2)%V) -∗
    DWP (e1 ||| e2)%V & (t1 ||| t2)%V : Φ.
  Proof.
    iIntros "H1 H2 H".
    iApply (par_spec with "[H1] [H2] H"); by dwp_pures.
  Qed.

End proof.
