From stdpp Require Import namespaces.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation lifting proofmode. (* for the example *)
From iris_ni.program_logic Require Export dwp lifting heap_lang_lifting.
Import uPred.

(** Now we define a simulation from a DWP *)
Class heapPreDG Σ := HeapPreDG {
  heapPreDG_proph_mapG1 :> proph_mapPreG proph_id (val*val) Σ;
  heapPreDG_proph_mapG2 :> proph_mapPreG proph_id (val*val) Σ;
  heapPreDG_gen_heapG1 :> gen_heapPreG loc val Σ;
  heapPreDG_gen_heapG2 :> gen_heapPreG loc val Σ
}.

(** First the mega future modality *)
Definition mega_future `{!invG Σ} (P : iProp Σ) :=
  (|={⊤,∅}=> |={∅,∅}=> ▷ |={∅,∅}=> ▷ |={∅,⊤}=> P)%I.
Instance: Params (@mega_future) 3.

Instance mega_future_proper `{invG Σ} : Proper ((⊢) ==> (⊢)) mega_future.
Proof. by rewrite /mega_future=> P Q ->. Qed.

Section mega_future_props.
  Context `{!invG Σ}.

  Lemma except_0_later'  (P : iProp Σ) :
    ◇ ▷ P -∗
    ▷ ◇ P.
  Proof.
    rewrite bi.except_0_later. apply later_mono, except_0_intro.
  Qed.

  Lemma mega_future_mono (P Q : iProp Σ) :
    (P -∗ Q) →
    (mega_future P -∗ mega_future Q).
  Proof. intros HPQ. by rewrite /mega_future HPQ. Qed.

  Lemma mega_futureN_mono n (P Q : iProp Σ) :
    (P -∗ Q) →
    (Nat.iter n mega_future P -∗ Nat.iter n mega_future Q).
  Proof.
    intros HPQ. induction n as [|n IH]=> //=.
    rewrite /mega_future IH //.
  Qed.

  Lemma mega_future_wand (P Q : iProp Σ) :
    mega_future P -∗
    (P -∗ Q) -∗
    mega_future Q.
  Proof.
    iIntros "HP HPQ".
    rewrite /mega_future.
    iMod "HP". iModIntro.
    iMod "HP". iModIntro. iNext.
    iApply (step_fupd_wand with "HP HPQ").
  Qed.

  Lemma mega_futureN_wand n (P Q : iProp Σ) :
    Nat.iter n mega_future P -∗
    (P -∗ Q) -∗
    Nat.iter n mega_future Q.
  Proof.
    iIntros "HP HPQ".
    iInduction n as [|n] "IH".
    - simpl. by iApply "HPQ".
    - rewrite !Nat_iter_S.
      iApply (mega_future_wand with "HP").
      iIntros "H".
      iApply ("IH" with "H HPQ").
  Qed.

  Lemma mega_future_fupd (P : iProp Σ) :
    mega_future P ⊣⊢ mega_future (|={⊤}=> P).
  Proof.
    apply (anti_symm (⊢)).
    - by rewrite /mega_future -(fupd_intro ⊤ P).
    - rewrite /mega_future.
      iIntros "H". iMod "H". iModIntro.
      iMod "H". iModIntro. iNext.
      iMod "H". iModIntro. iNext.
      by rewrite fupd_trans.
  Qed.

  Lemma mega_futureN_S_fupd n (P : iProp Σ) :
    Nat.iter (S n) mega_future P ⊣⊢ Nat.iter (S n) mega_future (|={⊤}=> P).
  Proof.
    apply (anti_symm (⊢)); rewrite !Nat_iter_S_r; apply mega_futureN_mono.
    - rewrite mega_future_fupd //.
    - rewrite -mega_future_fupd //.
  Qed.

  Lemma mega_futureN_add n1 n2 (P : iProp Σ) :
    Nat.iter (n1 + n2) mega_future P ⊣⊢
             Nat.iter n1 mega_future (Nat.iter n2 mega_future P).
  Proof. by rewrite Nat_iter_add. Qed.

  Lemma mega_future_plain P `{!Plain P} :
    mega_future P -∗ |={⊤}=> ▷ ◇ ▷ ◇ P.
  Proof.
    rewrite /mega_future.
    rewrite -(fupd_plain_mask _ ∅ (▷ ◇ ▷ ◇ P)%I).
    iIntros "H". iMod "H".
    iMod "H".
    rewrite -(fupd_plain_later _ (▷ ◇ P)%I). iNext.
    iMod "H".
    by rewrite fupd_plain_mask -fupd_plain_later.
  Qed.

  Lemma mega_futureN_plain n P `{!Plain P} :
    Nat.iter n mega_future P -∗ |={⊤}=> Nat.iter n (λ x, ▷ ◇ ▷ ◇ x) P.
  Proof.
    induction n as [|n IH].
    - simpl. by rewrite -fupd_intro.
    - rewrite !Nat_iter_S.
      rewrite IH. rewrite -mega_future_fupd.
      apply mega_future_plain. clear IH.
      induction n=>/= //. apply _.
  Qed.

End mega_future_props.

Lemma mega_future_soundness `{!invPreG Σ} φ :
  (∀ `{Hinv: !invG Σ}, (mega_future (|={⊤}=> ⌜ φ ⌝ : iProp Σ))%I) →
  φ.
Proof.
  intros Hprf.
  apply (soundness (M:=iResUR Σ) _  (S (S 2))); simpl.
  apply (fupd_plain_soundness ⊤ ⊤); first by apply _.
  intros Hinv.
  iPoseProof (Hprf Hinv) as "H". clear Hprf.
  rewrite -mega_future_fupd.
  iMod (mega_future_plain with "H") as "Hφ".
  iModIntro. iNext. iMod "Hφ" as "Hφ".
  iNext. iMod "Hφ" as "Hφ". by iNext.
Qed.

Lemma mega_futureN_soundness `{!invPreG Σ} n φ :
  (∀ `{Hinv: !invG Σ}, (Nat.iter n mega_future (|={⊤}=> ⌜ φ ⌝ : iProp Σ))%I) →
  φ.
Proof.
  intros Hprf.
  apply (soundness (M:=iResUR Σ) _  (S (S (n * 2)))); simpl.
  apply (fupd_plain_soundness ⊤ ⊤); first by apply _. intros Hinv.
  iPoseProof (Hprf Hinv) as "H". clear Hprf.
  destruct n as [|n].
  - simpl. iMod "H" as "H". done.
  - rewrite -mega_futureN_S_fupd.
    iMod (mega_futureN_plain with "H") as "Hφ".
    iModIntro. iClear "H".
    iInduction n as [|n] "IH"; simpl.
    + iNext. iMod "Hφ" as "Hφ".
      iNext. iMod "Hφ" as "Hφ". by iNext.
    + iNext. iMod "Hφ" as "Hφ".
      iNext. iMod "Hφ" as "Hφ".
      by iApply "IH".
Qed.

(** Now the relation *)
Definition dwp_rel Σ `{!invPreG Σ, !heapPreDG Σ}
  (es ss : list expr)
  (σ1 σ2 : state) (Φ : val → val → iProp Σ) :=
  ∃ n, ∀ `{Hinv : !invG Σ},
      (Nat.iter n mega_future
         (|={⊤}=> ∃ (h1 h2 : gen_heapG loc val Σ)
                   (p1 p2 : proph_mapG proph_id (val*val) Σ),
            let _ := HeapDG _ _ p1 p2 h1 h2 in
            state_rel σ1 σ2 [] [] ∗
            [∗ list] e;s ∈ es;ss, dwp ⊤ e s Φ))%I.

Definition I {Σ} (v1 v2 : val) : iProp Σ := ⌜v1 = v2⌝%I.


(** Example program that satisfies the relation *)
Definition e_test := (let: "x" := ref #0 in !"x")%E.
Lemma dwp_e_test `{heapDG Σ} :
  dwp ⊤ e_test e_test I.
Proof.
  iApply (dwp_bind (fill [AppRCtx _]) (fill [AppRCtx _])). simpl.
  pose (Ψ1 := (λ v, ∃ (l : loc), ⌜v = #l⌝ ∧ l ↦ₗ #0)%I).
  pose (Ψ2 := (λ v, ∃ (l : loc), ⌜v = #l⌝ ∧ l ↦ᵣ #0)%I).
  iApply (dwp_atomic_lift_wp Ψ1 Ψ2); try done.
  iModIntro. repeat iSplitL.
  { unfold WP1, Ψ1. wp_alloc l as "Hl". eauto with iFrame. }
  { unfold WP2, Ψ2. wp_alloc l as "Hl". eauto with iFrame. }
  iIntros (? ?) "H1 H2".
  iDestruct "H1" as (l1 ->) "Hl1".
  iDestruct "H2" as (l2 ->) "Hl2".
  iModIntro. iNext.

  iApply dwp_pure_step_later.
  { eapply (pure_exec_ctx (fill [AppLCtx _])). apply _. }
  { eapply (pure_exec_ctx (fill [AppLCtx _])). apply _. }
  done. done. iNext.
  iApply dwp_pure_step_later=>// /=. iNext.

  iApply (dwp_load with "Hl1 Hl2"). iNext. eauto.
Qed.
Lemma dwp_rel_e_test σ1 σ2 Σ `{!invPreG Σ, !heapPreDG Σ} :
  dwp_rel Σ [e_test] [e_test] σ1 σ2 I.
Proof.
  exists 0%nat. intros Hinv. simpl.
  iMod (gen_heap_init σ1.(heap)) as (hg1) "Hh1".
  iMod (gen_heap_init σ2.(heap)) as (hg2) "Hh2".
  iMod (proph_map_init [] σ1.(used_proph_id)) as (pg1) "Hp1".
  iMod (proph_map_init [] σ2.(used_proph_id)) as (pg2) "Hp2".
  iModIntro. iExists hg1,hg2,pg1,pg2. iFrame.
  pose (Hdheap := (HeapDG Σ Hinv pg1 pg2 hg1 hg2)).
  iSplit; last done.
  iApply dwp_e_test.
Qed.

(** The relation has good properties *)
Lemma dwp_rel_val Σ `{!invPreG Σ, !heapPreDG Σ} (v1 v2 : val) e s σ1 σ2 :
  dwp_rel Σ (of_val v1::e) (of_val v2::s) σ1 σ2 I →
  v1 = v2.
Proof.
  intros [n HR].
  eapply (mega_futureN_soundness n)=>Hinv.
  iPoseProof (HR Hinv) as "HR".
  iApply (mega_futureN_mono with "HR").
  iIntros "HR".
  iMod "HR" as (h1 h2 p1 p2) "[HSR H]".
  rewrite big_sepL2_cons. iDestruct "H" as "[H _]".
  rewrite dwp_value_inv'. done.
Qed.

Lemma dwp_rel_reducible_no_obs Σ `{!invPreG Σ, !heapPreDG Σ} es ss e s i σ1 σ2 Φ :
  es !! i = Some e →
  ss !! i = Some s →
  language.to_val e = None →
  dwp_rel Σ es ss σ1 σ2 Φ →
  reducible_no_obs e σ1 ∧ reducible_no_obs s σ2.
Proof.
  intros Hes Hss He [n HR].
  eapply (mega_futureN_soundness n)=>Hinv.
  iPoseProof (HR Hinv) as "HR".
  iApply (mega_futureN_mono with "HR").
  iIntros "HR". iApply fupd_plain_mask_empty.
  iMod "HR" as (h1 h2 p1 p2) "[HSR H]".
  rewrite (big_sepL2_lookup _ _ _ i)=>//.
  iEval (rewrite dwp_unfold /dwp_pre He) in "H".
  iMod ("H" $! _ _ [] [] [] [] with "HSR") as (Hred1 Hred2) "H".
  iModIntro. done.
Qed.

Lemma dwp_rel_efs_length Σ `{!invPreG Σ, !heapPreDG Σ} es ss i e s σ1 σ2 e' σ1' efs1 s' σ2' efs2 Φ :
  es !! i = Some e →
  ss !! i = Some s →
  dwp_rel Σ es ss σ1 σ2 Φ →
  (prim_step e σ1 [] e' σ1' efs1) →
  (prim_step s σ2 [] s' σ2' efs2) →
  length efs1 = length efs2.
Proof.
  intros Hes Hss [n HR1] Hstep1 Hstep2.
  eapply (mega_futureN_soundness (S n))=>Hinv.
  iPoseProof (HR1 Hinv) as "HR".
  rewrite Nat_iter_S_r.
  iApply (mega_futureN_mono with "HR").
  iIntros "HR".
  iMod "HR" as (h1 h2 p1 p2) "[HSR H]".
  rewrite (big_sepL2_lookup _ _ _ i)=>//.
  iEval (rewrite dwp_unfold /dwp_pre) in "H".
  assert (@language.to_val heap_lang e = None) as ->.
  (* TODO: why do I have to be explicit here? *)
  { eapply val_stuck; eauto. }
  iMod ("H" $! _ _ [] [] [] [] with "HSR") as (Hred1 Hred2) "H".
  iSpecialize ("H" with "[//]").
  iSpecialize ("H" with "[//]"). iMod "H".
  iModIntro. iModIntro. iNext. iMod "H" as "H".
  iModIntro. iNext. iMod "H" as "[_ [_ Hefs]]".
  iModIntro. iModIntro. iApply (big_sepL2_length with "Hefs").
Qed.

(* TODO: move to iris *)
Section help.
  Context {A : Type} {Σ : gFunctors}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : nat → A → A → iProp Σ.

  Lemma big_sepL2_app_inv Φ l1 l2 l1' l2' :
    length l1 = length l1' →
    ([∗ list] k↦y1;y2 ∈ l1 ++ l2; l1' ++ l2', Φ k y1 y2) -∗
    ([∗ list] k↦y1;y2 ∈ l1; l1', Φ k y1 y2) ∗
    ([∗ list] k↦y1;y2 ∈ l2; l2', Φ (length l1 + k)%nat y1 y2).
  Proof.
    intros Hlen. rewrite !big_sepL2_alt.
    iIntros "[Hfoo H]". iDestruct "Hfoo" as %Hfoo.
    rewrite zip_with_app=>//.
    rewrite big_sepL_app. iDestruct "H" as "[H1 H2]".
    rewrite zip_with_length.
    assert ((length l1 `min` length l1')%nat = length l1) as ->.
    { lia. }
    iFrame. iSplit; iPureIntro; eauto.
    revert Hfoo. rewrite !app_length. lia.
  Qed.
End help.

Lemma dwp_rel_step Σ `{!invPreG Σ, !heapPreDG Σ} es ss es' ss' e s σ1 σ2 e' s' σ1' σ2' Φ :
  length es = length ss →
  dwp_rel Σ (es ++ e::es') (ss ++ s::ss') σ1 σ2 Φ →
  (prim_step e σ1 [] e' σ1' []) →
  (prim_step s σ2 [] s' σ2' []) →
  dwp_rel Σ (es ++ e'::es') (ss ++ s'::ss') σ1' σ2' Φ.
Proof.
  intros Hlen [n HR] Hstep1 Hstep2.
  rewrite /dwp_rel. exists (S n). move=>Hinv.
  rewrite Nat_iter_S_r.
  iPoseProof HR as "H".
  iApply (mega_futureN_mono with "H").
  rewrite /mega_future /=.
  iIntros "H". iMod "H" as (h1 h2 p1 p2) "[HI HWP]".
  iExists h1,h2,p1,p2.

  rewrite big_sepL2_app_inv=>//. rewrite big_sepL2_cons.
  iDestruct "HWP" as "[H1 [HWP H2]]".
  iEval (rewrite dwp_unfold /dwp_pre) in "HWP".
  assert (language.to_val e = None) as ->.
  { eapply val_stuck. eauto. }
  iSpecialize ("HWP" $! _ _ [] [] [] [] with "HI").
  iMod "HWP" as (_ _) "HWP". iModIntro.
  iSpecialize ("HWP" with "[//]").
  iSpecialize ("HWP" with "[//]").
  iMod "HWP" as "HWP". iModIntro. iNext.
  iMod "HWP" as "HWP". iModIntro. iNext.
  iMod "HWP" as "(HI & HWP & _)". iModIntro. iModIntro. iFrame.
Qed.

(** XXX TODO: the steps should produce forked off threads! *)
Lemma dwp_rel_simul Σ `{!invPreG Σ, !heapPreDG Σ} es ss es' ss' e s σ1 σ2 e' σ1' Φ :
  length es = length ss →
  dwp_rel Σ (es++e::es') (ss++s::ss') σ1 σ2 Φ →
  (prim_step e σ1 [] e' σ1' []) →
  ∃ s' σ2' κ2,
    prim_step s σ2 κ2 s' σ2' [] ∧
    dwp_rel Σ (es++e'::es') (ss++s'::ss') σ1' σ2' Φ.
Proof.
  intros Hlen HR Hstep1.
  assert (to_val e = None) as Hnon. { by eapply val_stuck. }
  assert ((es++e::es') !! length es = Some e) as Hi1.
  { by apply list_lookup_middle. }
  assert ((ss++s::ss') !! length es = Some s) as Hi2.
  { by apply list_lookup_middle. }
  destruct (dwp_rel_reducible_no_obs Σ _ _ e s _ σ1 σ2 Φ Hi1 Hi2 Hnon HR) as [Hred1 Hred2].
  destruct Hred2 as (s'&σ2'&efs2&Hstep2).
  assert (efs2 = []) as ->.
  { apply nil_length_inv. change 0%nat with (length (@nil expr)).
    symmetry.
    eapply (dwp_rel_efs_length Σ _ _ (length es) e s)=>//. }
  destruct HR as [n HR].
  exists s', σ2', []. split; auto.
  rewrite /dwp_rel. exists (S n). move=>Hinv.
  rewrite Nat_iter_S_r.
  iPoseProof HR as "H".
  iApply (mega_futureN_mono with "H").
  rewrite /mega_future /=.
  iIntros "H". iMod "H" as (h1 h2 p1 p2) "[HI HWP]".
  iExists h1,h2,p1,p2.

  rewrite big_sepL2_app_inv=>//. rewrite big_sepL2_cons.
  iDestruct "HWP" as "[H1 [HWP H2]]".
  rewrite (dwp_unfold _ e s) /dwp_pre.
  assert (language.to_val e = None) as ->.
  { by simpl. }
  iSpecialize ("HWP" $! _ _ [] [] [] [] with "HI").
  iMod "HWP" as (_ _) "HWP". iModIntro.
  iSpecialize ("HWP" with "[//]").
  iSpecialize ("HWP" with "[//]").
  iMod "HWP" as "HWP". iModIntro. iNext.
  iMod "HWP" as "HWP". iModIntro. iNext.
  iMod "HWP" as "(HI & HWP & _)". iModIntro. iModIntro. iFrame.
Qed.
