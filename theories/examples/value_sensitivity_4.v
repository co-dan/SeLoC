From iris.base_logic Require Import cancelable_invariants.
From iris_ni.logrel Require Import types.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import lang proofmode.
From iris_ni.proofmode Require Import dwp_tactics.
From iris_ni.logrel Require Import interp.
From iris_ni.examples Require Import par value_dep various (* for oneshot *).

Definition thread1 : val :=
  λ: "out_low" "out_high" "rec",
    if: ~ is_classified "rec"
    then "out_low" <- read_dep "rec"
    else "out_high" <- read_dep "rec".

Definition thread2 : val :=
  λ: "ch" "rec",
    store_dep "rec" (!"ch");;
    declassify "rec" #0.

Definition prog : val := λ: "data" "out_low" "out_high",
  let: "rec" := (ref #true, ref "data") in
  thread1 "out_low" "out_high" "rec" ||| thread2 "out_high" "rec";;
  classify "rec";;
  store_dep "rec" (!"out_high").

Section proof.
  Context `{!heapDG Σ, !cinvG Σ, !valueDepG Σ, !spawnG Σ, !oneshotG Σ}.

  Definition glinv γ γs :=
    (∃ α, classification γ α (1/2) ∗
     ((pending γs ∗ ⌜α = High⌝) ∨ (shot γs ∗ ⌜α = Low⌝)))%I.


  Definition N := nroot.@"blabla".

  (* We verify that the thread that does the "dumping out" in a loop is secure,
    under the monotonicity assumption. *)
  Lemma thread1_spec γi p γ γs out_low1 out_low2 out_high1 out_high2 rec1 rec2 ξ :
    ⟦ tref (tint Low) ⟧ ξ out_low1 out_low2 -∗
    ⟦ tref (tint High) ⟧ ξ out_high1 out_high2 -∗
    value_dependent γ (tint Low) ξ rec1 rec2 -∗
    cinv N γi (glinv γ γs) -∗
    cinv_own γi p -∗
    DWP thread1 out_low1 out_high1 rec1 & thread1 out_low2 out_high2 rec2
        : λ _ _, cinv_own γi p.
  Proof.
    iIntros "#HoutL #HoutH #Hvd #Hinv Hp". dwp_rec. dwp_pures.
    dwp_bind (is_classified _) (is_classified _).
    iApply (is_classified_spec with "Hvd").
    iIntros (α b) "Ha".
    iCinv "Hinv" "Hp" as (β) "[>Hc Hi]" "Hcl".
    iDestruct (classification_auth_agree with "Ha Hc") as %<-.
    iFrame "Ha". iDestruct "Hi" as ">[[Htok %]|[#Htok %]]"; simplify_eq/=.
    - iMod ("Hcl" with "[Htok Hc]") as "_".
      { iNext. iExists _. iFrame. iLeft. eauto with iFrame. }
      iModIntro. iIntros (Hfoo). assert (b = true) as ->.
      { destruct b; naive_solver. }
      iSimpl. dwp_pures. dwp_bind (read_dep _) (read_dep _).
      iApply (read_spec with "Hvd").
      iIntros (α v1 v2) "Ha #Hv".
      iCinv "Hinv" "Hp" as (β) "[>Hc Hi]" "Hcl".
      iFrame "Ha".
      iMod ("Hcl" with "[Hi Hc]") as "_".
      { iNext. iExists _. iFrame. }
      iModIntro. iApply dwp_wand; [iApply logrel_store; first done|].
      + iApply dwp_value; eauto with iFrame.
      + iApply dwp_value. iModIntro.
        destruct α; simpl; last by eauto with iFrame.
        rewrite left_id. iApply (interp_sub_mono with "Hv"). by constructor.
      + iIntros (??) "_". done.
    - iMod ("Hcl" with "[Htok Hc]") as "_".
      { iNext. iExists _. iFrame. iRight. eauto with iFrame. }
      iModIntro. iIntros (Hfoo). destruct b.
      { iSimpl. dwp_pures. dwp_bind (read_dep _) (read_dep _).
      iApply (read_spec with "Hvd").
      iIntros (α v1 v2) "Ha #Hv". iFrame "Ha".
      iModIntro. iApply dwp_wand; [iApply logrel_store; first done|].
        + iApply dwp_value; eauto with iFrame.
        + iApply dwp_value. iModIntro.
          iApply (interp_sub_mono with "Hv"). by constructor.
        + iIntros (??) "_". done.  }
      dwp_pures.
      dwp_bind (read_dep _) (read_dep _).
      iApply (read_spec with "Hvd").
      iIntros (α v1 v2) "Ha #Hv".
      iCinv "Hinv" "Hp" as (β) "[>Hc Hi]" "Hcl".
      iDestruct "Hi" as ">[[Htok2 %]|[_ %]]"; simplify_eq/=.
      { iExFalso. iApply (shot_not_pending with "Htok Htok2"). }
      iDestruct (classification_auth_agree with "Ha Hc") as %->.
      iFrame "Ha".
      iMod ("Hcl" with "[Htok Hc]") as "_".
      { iNext. iExists _. iFrame. iRight. eauto with iFrame. }
      iModIntro.
      iApply dwp_wand; [iApply logrel_store; first done|];
        try iApply dwp_value; eauto with iFrame.
  Qed.

  Lemma thread2_spec γi p γ γs ch1 ch2 rec1 rec2 ξ :
    ⟦ tref (tint High) ⟧ ξ ch1 ch2 -∗
    value_dependent γ (tint Low) ξ rec1 rec2 -∗
    cinv N γi (glinv γ γs) -∗
    cinv_own γi p -∗
    classification γ High (1/2) -∗
    DWP thread2 ch1 rec1 & thread2 ch2 rec2 :
      λ _ _, cinv_own γi p ∗ classification γ Low (1/2).
  Proof.
    iIntros "#Hch #Hvd #Hinv Hp Hc2".
    dwp_rec. dwp_pures. dwp_bind (! _)%E (! _)%E.
    iApply dwp_wand.
    { iApply (logrel_deref with "[Hch]"). by iApply dwp_value. }
    iIntros (v1 v2) "#Hv". dwp_bind (store_dep _ _) (store_dep _ _).
    iApply (store_spec with "Hvd"). iIntros (α) "Ha".
    iDestruct (classification_auth_agree with "Ha Hc2") as %->.
    iFrame "Ha". iModIntro. iSimpl. rewrite left_id. iFrame "Hv".
    dwp_pures.
    iApply (declassify_spec with "Hvd [] Hc2").
    { rewrite !interp_eq. iExists 0,0. by eauto. }
    iSimpl. iIntros "Ha Hc2".
    iCinv "Hinv" "Hp" as (α') "[>Hc1 >Hi]" "Hcl".
    iDestruct (classification_auth_agree with "Ha Hc1") as %<-.
    iCombine "Hc1 Hc2" as "Hc".
    iMod (classification_update Low with "Ha Hc") as "[$ [Hc1 Hc2]]".
    iDestruct "Hi" as "[[Htok %]|[Htok %]]"; simplify_eq/=.
    iMod (shoot with "Htok") as "#Htok".
    iMod ("Hcl" with "[-Hc2 Hp]") as "_".
    { iNext. iExists _. iFrame. eauto with iFrame. }
    iModIntro. iFrame "Hc2". eauto with iFrame.
  Qed.

  Lemma proof out_low1 out_low2 out_high1 out_high2 dat1 dat2 ξ :
    ⟦ tref (tint Low) ⟧ ξ out_low1 out_low2 -∗
    ⟦ tref (tint High) ⟧ ξ out_high1 out_high2 -∗
    ⟦ tint High ⟧ ξ dat1 dat2 -∗
    DWP (prog dat1 out_low1 out_high1) &
        (prog dat2 out_low2 out_high2) : ⟦ tunit ⟧ ξ.
  Proof.
    iIntros "#HoutL #HoutH #Hdat".
    dwp_rec. dwp_pures.

    dwp_bind (ref _)%E (ref _)%E.
    iApply dwp_alloc. iIntros (rd1 rd2) "Hrd1 Hrd2". iNext.

    dwp_bind (ref _)%E (ref _)%E.
    iApply dwp_alloc. iIntros (is_classified1 is_classified2) "Hc1 Hc2". iNext.

    iMod (make_value_dependent (tint Low) with "Hrd1 Hrd2 Hc1 Hc2 []")
      as (γ) "[#Hvd Hc]".
    { simpl. rewrite left_id. iExact "Hdat". }
    iClear "Hdat". iDestruct "Hc" as "[Hc1 Hc2]".
    dwp_pures.
    iMod new_pending as (γs) "Hpend".

    iMod (cinv_alloc _ N (glinv γ γs) with "[-Hc2]") as (γi) "[#Hinv [Hp1 Hp2]]".
    { iNext. iExists _. iFrame. iLeft. eauto with iFrame. }
    dwp_bind (par _ _) (par _ _).
    iApply (dwp_par _ _ with "[Hp1] [Hc2 Hp2]").
    - (* Thread 1 *) iApply (thread1_spec with "HoutL HoutH Hvd Hinv Hp1").
    - (* Thread 2 *) iApply (thread2_spec with "HoutH Hvd Hinv Hp2 Hc2").
    - (* Finally *)
      iIntros (z1 z2 r1 r2) "Hp1 [Hp2 Hc2]". iCombine "Hp1 Hp2" as "Hp".
      iNext. dwp_pures. clear z1 z2 r1 r2.
      iMod (cinv_cancel with "Hinv Hp") as (β) "[>Hc1 >Hi]"; first done.
      iDestruct "Hi" as "[[Htok2 %]|[_ %]]"; simplify_eq/=.
      { iExFalso. by iDestruct (classification_agree with "Hc1 Hc2") as %?. }
      iCombine "Hc1 Hc2" as "Hc".
      dwp_bind (classify _) (classify _).
      iApply (classify_spec with "Hvd Hc").
      iIntros "Hauth Hc".
      iMod (classification_update High with "Hauth Hc") as "[$ Hc]".
      iModIntro. dwp_pures.
      dwp_bind (! _)%E (! _)%E. iApply dwp_wand; [iApply logrel_deref|].
      { iApply dwp_value. eauto. }
      iIntros (v1 v2) "Hv".
      iApply (store_spec with "Hvd"). iIntros (α) "Hauth".
      iDestruct (classification_auth_agree with "Hauth Hc") as %->.
      iModIntro. eauto with iFrame.
  Qed.

End proof.
