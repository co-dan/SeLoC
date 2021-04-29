From iris.base_logic.lib Require Export fancy_updates.
From iris.program_logic Require Export language weakestpre.
From iris.proofmode Require Import base tactics classes.
Set Default Proof Using "Type".
Import uPred.

(* We define irisDG only for languages for which we already have
weakest precondition calculus. This makes our lives easier in some
places because we don't need to care about two different instances of
`invG` whenever we have _both_ irisG and irisDG. *)
Class irisDG' (Λstate Λobs : Type) (Σ : gFunctors) := IrisDG {
  state_rel : Λstate → Λstate → list Λobs → list Λobs → iProp Σ;
}.
Notation irisDG Λ Σ := (irisDG' (state Λ) (observation Λ) Σ).

Definition dwp_pre `{invG Σ, irisDG Λ Σ}
    (dwp : coPset -d> expr Λ -d> expr Λ -d> (val Λ -d> val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> expr Λ -d> (val Λ -d> val Λ -d> iPropO Σ) -d> iPropO Σ := λ E1 e1 e2 Φ,
 (match to_val e1,to_val e2 with
  | Some v1, Some v2 => |={E1}=> Φ v1 v2
  | Some _, None => |={E1}=> False
  | None, Some _ => |={E1}=> False
  | _,_ => ∀ σ1 σ2 κ1 κs1 κ2 κs2,
     state_rel σ1 σ2 (κ1 ++ κs1) (κ2 ++ κs2) -∗
     |={E1,∅}=> ⌜reducible_no_obs e1 σ1⌝ ∗ ⌜reducible_no_obs e2 σ2⌝ ∗
     ∀ e1' σ1' efs1 e2' σ2' efs2, ⌜prim_step e1 σ1 [] e1' σ1' efs1⌝ -∗
                                   ⌜prim_step e2 σ2 [] e2' σ2' efs2⌝ -∗
       |={∅}=> ▷ |={∅,E1}=>
         state_rel σ1' σ2' (κ1++κs1) (κ2++κs2) ∗ dwp E1 e1' e2' Φ ∗
         [∗ list] ef ; ef' ∈ efs1 ; efs2, dwp ⊤ ef ef' (λ _ _, True)
  end)%I.

Local Instance dwp_pre_contractive `{invG Σ, irisDG Λ Σ} : Contractive dwp_pre.
Proof.
  rewrite /dwp_pre=> n dwp dwp' Hwp E1 e1 e2 Φ.
  repeat case_match; [ reflexivity.. | ].
  apply bi.forall_ne. intros σ1.
  apply bi.forall_ne. intros σ2.
  apply bi.forall_ne=>κ1.
  apply bi.forall_ne=>κs1.
  apply bi.forall_ne=>κ2.
  apply bi.forall_ne=>κs2.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Definition dwp_def `{irisDG Λ Σ, invG Σ} :
  coPset → expr Λ → expr Λ → (val Λ → val Λ → iProp Σ) → iProp Σ :=
  fixpoint dwp_pre.
Definition dwp_aux `{invG Σ, irisDG Λ Σ} : seal (@dwp_def Λ Σ _ _). by eexists. Qed.
Definition dwp `{irisDG Λ Σ, invG Σ} := dwp_aux.(unseal).
Definition dwp_eq `{irisDG Λ Σ, invG Σ} : dwp = @dwp_def Λ Σ _ _ := dwp_aux.(seal_eq).

Section dwp.
Context `{irisDG Λ Σ, invG Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Lemma dwp_unfold E1 e1 e2 Φ :
  dwp E1 e1 e2 Φ ⊣⊢ dwp_pre dwp E1 e1 e2 Φ.
Proof. rewrite dwp_eq. apply (fixpoint_unfold dwp_pre). Qed.

Global Instance dwp_ne E1 e1 e2 n :
  Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==> dist n) (dwp E1 e1 e2).
Proof.
  revert e1 e2. induction (lt_wf n) as [n _ IH]=> e1 e2 Φ Ψ HΦ.
  rewrite !dwp_unfold /dwp_pre.
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  do 37 (f_contractive || f_equiv).
  apply IH; first lia.
  intros ??. eapply (dist_le (S n)); eauto with lia.
  apply HΦ.
Qed.

Global Instance dwp_proper E1 e1 e2 :
  Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (≡)) (dwp E1 e1 e2).
Proof.
  by intros Φ Φ' HΦ; apply equiv_dist=>n; apply dwp_ne=>v v'; apply equiv_dist, HΦ.
Qed.

Lemma dwp_value' E1 Φ v v' :
  (|={E1}=> Φ v v') ⊢ dwp E1 (of_val v) (of_val v') Φ.
Proof.
  iIntros "HΦ". rewrite dwp_unfold /dwp_pre !to_of_val.
  eauto with iFrame.
Qed.

Lemma dwp_value_inv' E1 Φ v v' :
  dwp E1 (of_val v) (of_val v') Φ ={E1}=∗ Φ v v'.
Proof.
  rewrite dwp_unfold /dwp_pre !to_of_val. done.
Qed.

Lemma dwp_strong_mono E1 E1' e1 e2 Φ Ψ :
  E1 ⊆ E1' →
  dwp E1 e1 e2 Φ -∗
  (∀ v1 v2, Φ v1 v2 ={E1'}=∗ Ψ v1 v2) -∗
  dwp E1' e1 e2 Ψ.
Proof.
  iIntros (HE) "H HΦ". iLöb as "IH" forall (e1 e2 E1 HE Φ Ψ).
  rewrite !dwp_unfold /dwp_pre.
  repeat case_match; try by (rewrite (fupd_mask_mono E1 E1'); last assumption).
  { rewrite (fupd_mask_mono E1 E1'); last assumption.
    iMod "H". by iApply "HΦ". }
  iIntros (σ1 σ2 κ1 κs1 κ2 κs2) "Hσ".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "Hσ") as "[% [% H]]".
  iModIntro. iSplit; [by eauto|]. iSplit; [by eauto|].
  iIntros (e1' σ1' efs1 e2' σ2' efs2 Hstep1 Hstep2).
  do 2 iSpecialize ("H" with "[//]"). iMod "H" as "H". iIntros "!>!>".
  iMod "H" as "H". iMod "Hclose" as "_". iModIntro.
  iDestruct "H" as "(Hσ & H & Hefs)". iFrame.
  iApply ("IH" with "[//] H HΦ").
Qed.

Lemma fupd_dwp E1 e1 e2 Φ :
  (|={E1}=> dwp E1 e1 e2 Φ) ⊢ dwp E1 e1 e2 Φ.
Proof.
  rewrite dwp_unfold /dwp_pre. iIntros "H".
  repeat case_match; by iMod "H".
Qed.

Lemma dwp_fupd E1 e1 e2 Φ :
  dwp E1 e1 e2 (λ v1 v2, |={E1}=> Φ v1 v2) ⊢
  dwp E1 e1 e2 Φ.
Proof.
  iIntros "H".
  iApply (dwp_strong_mono E1 with "H"); auto.
Qed.

Lemma dwp_bind K1 K2 `{!LanguageCtx K1, !LanguageCtx K2} E1 e1 e2 Φ :
  dwp E1 e1 e2 (λ v1 v2,
      dwp E1 (K1 (of_val v1)) (K2 (of_val v2)) Φ) -∗
  dwp E1 (K1 e1) (K2 e2) Φ.
Proof.
  iIntros "H". iLöb as "IH" forall (E1 e1 e2 Φ).
  rewrite dwp_unfold /dwp_pre.
  destruct (to_val e1) as [v1|] eqn:He1;
    destruct (to_val e2) as [v2|] eqn:He2;
    try by (iApply fupd_dwp; iMod "H").
  { iApply fupd_dwp. rewrite (of_to_val e1) // (of_to_val e2) //. }
  rewrite dwp_unfold /dwp_pre.
  rewrite (fill_not_val e1) //.
  rewrite (fill_not_val e2); last done. (* rewrite .. // hangs coq *)
  iIntros (σ1 σ2 κ1 κs1 κ2 κs2) "Hσ".
  iMod ("H" with "Hσ") as "[Hstep1 [Hstep2 H]]".
  iDestruct "Hstep1" as %Hstep1.
  iDestruct "Hstep2" as %Hstep2.
  iModIntro. iSplit.
  { iPureIntro.
    unfold reducible in *.
    destruct Hstep1 as (e' & σ' & efs & Hstep1).
    apply (fill_step (K:=K1)) in Hstep1. eexists. eauto. }
  iSplit.
  { iPureIntro.
    unfold reducible in *.
    destruct Hstep2 as (e' & σ' & efs & Hstep2).
    apply (fill_step (K:=K2)) in Hstep2. eexists. eauto. }
  clear Hstep1 Hstep2.
  iIntros (e1' σ1' efs1 e2' σ2' efs2 Hstep1 Hstep2).
  destruct (fill_step_inv e1 σ1 [] e1' σ1' efs1 He1 Hstep1) as (e1''&->&?) .
  destruct (fill_step_inv e2 σ2 [] e2' σ2' efs2 He2 Hstep2) as (e2''&->&?).
  iSpecialize ("H" with "[//]").
  iSpecialize ("H" with "[//]").
  iMod "H" as "H". iIntros "!>!>".
  iMod "H" as "H". iModIntro.
  iDestruct "H" as "(Hσ & H & Hefs)".
  apply fill_step in Hstep2. iFrame.
  by iApply "IH".
Qed.

(** NB: The other bind rule does not hold.
Counterexample K1 = [] + 1; K2 = []

dwp (1+1) (1+1) Φ
-----------------------------------------
dwp 1 (1+1) { v1 v2. dwp (v1+1) (1+1) Φ }

Maybe it only works with K1 = K2?
*)
Lemma dwp_bind_inv K1 K2 `{!LanguageCtx K1, !LanguageCtx K2} E1 e1 e2 Φ :
  dwp E1 (K1 e1) (K2 e2) Φ -∗
  dwp E1 e1 e2 (λ v1 v2,
  dwp E1 (K1 (of_val v1)) (K2 (of_val v2)) Φ).
Proof. Abort.

Lemma dwp_step_fupd E1 E1' e1 e2 P Φ :
  to_val e1 = None →
  to_val e2 = None →
  E1' ⊆ E1 →
  (|={E1}[E1']▷=> P) -∗
  dwp E1' e1 e2 (λ v1 v2, P ={E1}=∗ Φ v1 v2) -∗
  dwp E1 e1 e2 Φ.
Proof.
  rewrite !dwp_unfold /dwp_pre. iIntros (-> -> ?) "HR H".
  iIntros (σ1 σ2 ? ? ? ?) "Hσ". iMod "HR".
  iMod ("H" with "Hσ") as "[$ [$ H]]".
  iIntros "!>" (e1' σ1' efs Hstep1 e2' σ2' efs2 Hstep2).
  iSpecialize ("H" with "[//]").
  iSpecialize ("H" with "[//]").
  iMod "H" as "H".
  iModIntro. iNext.
  iMod "H" as "H".
  iMod "HR" as "HR". iModIntro.
  iDestruct "H" as "(Hσ & H & Hefs)". iFrame.
  iApply (dwp_strong_mono with "H"); first done.
  iIntros (v1 v2) "H". by iApply "H".
Qed.

(** * Derived rules *)
Lemma dwp_value E Φ e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  (|={E}=> Φ v1 v2)%I ⊢ dwp E e1 e2 Φ.
Proof. intros <- <-. by apply dwp_value'. Qed.

Lemma dwp_mono E1 e1 e2 Φ Ψ :
  (∀ v1 v2, Φ v1 v2 ⊢ Ψ v1 v2) →
  dwp E1 e1 e2 Φ ⊢ dwp E1 e1 e2 Ψ.
Proof.
  iIntros (HΦ) "H". iApply (dwp_strong_mono with "H"); auto.
  iIntros (??) "?". by iApply HΦ.
Qed.

Lemma dwp_mask_mono E1 E1' e1 e2 Φ :
  E1 ⊆ E1' →
  dwp E1 e1 e2 Φ ⊢ dwp E1' e1 e2 Φ.
Proof. iIntros (?) "H"; iApply (dwp_strong_mono with "H"); auto. Qed.

Global Instance dwp_mono' E1 e1 e2 :
  Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (⊢))
         (dwp E1 e1 e2).
Proof. by intros Φ Φ' ?; apply dwp_mono. Qed.

Lemma dwp_frame_l E1 e1 e2 Φ R :
  R ∗ dwp E1 e1 e2 Φ ⊢ dwp E1 e1 e2 (λ v1 v2, R ∗ Φ v1 v2).
Proof. iIntros "[? H]". iApply (dwp_strong_mono with "H"); auto with iFrame. Qed.
Lemma dwp_frame_r E1 e1 e2 Φ R :
  dwp E1 e1 e2 Φ ∗ R ⊢ dwp E1 e1 e2 (λ v1 v2, Φ v1 v2 ∗ R).
Proof. iIntros "[H ?]". iApply (dwp_strong_mono with "H"); auto with iFrame. Qed.

Lemma dwp_wand E1 e1 e2 Φ Ψ :
  dwp E1 e1 e2 Φ -∗
  (∀ v1 v2, Φ v1 v2 -∗ Ψ v1 v2) -∗
  dwp E1 e1 e2 Ψ.
Proof.
  iIntros "Hwp H". iApply (dwp_strong_mono with "Hwp"); auto.
  iIntros (??) "?". by iApply "H".
Qed.

Lemma dwp_atomic E1 E2 e1 e2 Φ
  `{!Atomic StronglyAtomic e1}
  `{!Atomic StronglyAtomic e2} :
  (|={E1,E2}=> dwp E2 e1 e2 (λ v1 v2, |={E2,E1}=> Φ v1 v2)) -∗
  dwp E1 e1 e2 Φ.
Proof.
  iIntros "H".
  rewrite (dwp_unfold E1) /dwp_pre /=.
  rewrite (dwp_unfold E2) /dwp_pre /=.
  destruct (to_val e1) as [v1|] eqn:He1;
    destruct (to_val e2) as [v2|] eqn:He2;
    try by (iMod "H" as "H"; iMod "H").
  iIntros (σ1 σ2 κ1 κs1 κ2 κs2) "Hσ".
  iMod "H" as "H".
  iSpecialize ("H" $! σ1 σ2 κ1 κs1 κ2 κs2 with "Hσ").
  iMod "H" as  "[$ [$ H]]". iModIntro.
  iIntros (e1' σ1' efs e2' σ2' efs2 Hstep1 Hstep2).
  iSpecialize ("H" $! e1' σ1' efs e2' σ2' efs2 Hstep1 Hstep2).
  iMod "H" as "H". iModIntro. iNext.
  iMod "H" as "[Hst [H $]]".
  destruct (to_val e1') as [v1|] eqn:Hv1; last first.
  { exfalso. destruct (atomic _ _ _ _ _ Hstep1). naive_solver. }
  destruct (to_val e2') as [v2|] eqn:Hv2; last first.
  { exfalso. destruct (atomic _ _ _ _ _ Hstep2). naive_solver. }
  rewrite -(of_to_val _ _ Hv1) -(of_to_val _ _ Hv2).
  rewrite dwp_value_inv' -dwp_value'. iMod "H". iMod "H" as "$".
  iModIntro. iFrame. done.
Qed.

End dwp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{irisDG Λ Σ, invG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → val Λ → iProp Σ.

  Global Instance frame_dwp p E1 e1 e2 R Φ Ψ :
    (∀ v1 v2, Frame p R (Φ v1 v2) (Ψ v1 v2)) →
    Frame p R (dwp E1 e1 e2 Φ) (dwp E1 e1 e2 Ψ).
  Proof. rewrite /Frame=> HR. rewrite dwp_frame_l. apply dwp_mono, HR. Qed.

  Global Instance is_except_0_dwp E1 e1 e2 Φ :
    IsExcept0 (dwp E1 e1 e2 Φ).
  Proof. by rewrite /IsExcept0 -{2}fupd_dwp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_dwp p E1 e1 e2 P Φ :
    ElimModal True p false (|==> P) P
              (dwp E1 e1 e2 Φ) (dwp E1 e1 e2 Φ).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E1) fupd_frame_r wand_elim_r fupd_dwp.
  Qed.

  Global Instance elim_modal_fupd_dwp p E1 e1 e2 P Φ :
    ElimModal True p false (|={E1}=> P) P
              (dwp E1 e1 e2 Φ) (dwp E1 e1 e2 Φ).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_dwp.
  Qed.

  Global Instance elim_modal_fupd_dwp_atomic p E1 E2 e1 e2 P Φ :
    Atomic StronglyAtomic e1 →
    Atomic StronglyAtomic e2 →
    ElimModal True p false (|={E1,E2}=> P) P
            (dwp E1 e1 e2 Φ) (dwp E2 e1 e2 (λ v1 v2, |={E2,E1}=> Φ v1 v2)%I).
  Proof.
    intros. by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r dwp_atomic.
  Qed.

  Global Instance add_modal_fupd_dwp E1 e1 e2 P Φ :
    AddModal (|={E1}=> P) P (dwp E1 e1 e2 Φ).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_dwp. Qed.

  Global Instance elim_acc_wp {X} E1 E2 α β γ e1 e2 Φ :
    Atomic StronglyAtomic e1 →
    Atomic StronglyAtomic e2 →
    ElimAcc True (X:=X) (fupd E1 E2) (fupd E2 E1)
            α β γ (dwp E1 e1 e2 Φ)
            (λ x, dwp E2 e1 e2 (λ v1 v2, |={E2}=> β x ∗ (γ x -∗? Φ v1 v2)))%I.
  Proof.
    intros ???.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (dwp_wand with "[Hinner Hα]"); first by iApply "Hinner".
    iIntros (v1 v2) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

End proofmode_classes.

Notation "'DWP' e1 '&' e2 '@' E ':' A" :=
  (dwp E e1%E e2%E A)
  (at level 100, E at next level, e1, e2 at next level,
   A at level 200,
   format "'[hv' 'DWP'  e1  '/' '&'  '/  ' e2  '@'  E  :  A ']'").
Notation "'DWP' e1 '&' e2 ':' A" :=
  (dwp ⊤ e1%E e2%E A)
  (at level 100, e1, e2 at next level,
   A at level 200,
   format "'[hv' 'DWP'  e1  '/' '&'  '/  ' e2  :  A ']'").
