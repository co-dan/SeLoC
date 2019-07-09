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
  (* irisDG_irisG :> irisG' Λstate Σ; *)
  state_rel : Λstate → Λstate → list Λobs → list Λobs → iProp Σ;
}.
Notation irisDG Λ Σ := (irisDG' (state Λ) (observation Λ) Σ).
(* Global Opaque irisDG_irisG. *)

Definition dwp_pre `{invG Σ, irisDG Λ Σ}
    (dwp : coPset -d> expr Λ -d> expr Λ -d> (val Λ -d> val Λ -d> iProp Σ) -d> iProp Σ) :
    coPset -d> expr Λ -d> expr Λ -d> (val Λ -d> val Λ -d> iProp Σ) -d> iProp Σ := λ E1 e1 e2 Φ,
 (match to_val e1,to_val e2 with
  | Some v1, Some v2 => |={E1}=> Φ v1 v2
  | Some v1, None => |={E1}=> False
  | None,x => ∀ σ1 σ2 κ1 κs1 κ2 κs2,
     state_rel σ1 σ2 (κ1 ++ κs1) (κ2 ++ κs2) -∗
     |={E1,∅}=> ⌜reducible_no_obs e1 σ1⌝ ∗ ⌜reducible_no_obs e2 σ2⌝ ∗
     ∀ e1' σ1' efs1 e2' σ2' efs2, ⌜prim_step e1 σ1 [] e1' σ1' efs1⌝ -∗
                                  ⌜prim_step e2 σ2 [] e2' σ2' efs2⌝ -∗
       |={∅,∅}=> ▷ |={∅,∅}=> ▷ |={∅,E1}=>
         state_rel σ1' σ2' (κ1++κs1) (κ2++κs2) ∗ dwp E1 e1' e2' Φ ∗
         [∗ list] ef ; ef' ∈ efs1 ; efs2, dwp ⊤ ef ef' (λ _ _, True)
  end)%I.

Local Instance dwp_pre_contractive `{invG Σ, irisDG Λ Σ} : Contractive dwp_pre.
Proof.
  rewrite /dwp_pre=> n dwp dwp' Hwp E1 e1 e2 Φ.
  repeat case_match. f_equiv. f_equiv.
  apply bi.forall_ne. intros σ1.
  apply bi.forall_ne. intros σ2.
  apply bi.forall_ne=>κ1.
  apply bi.forall_ne=>κs1.
  apply bi.forall_ne=>κ2.
  apply bi.forall_ne=>κs2.
  repeat (f_contractive || f_equiv); apply dist_S, Hwp.
  (* TODO: this is so slow ugu *)
Qed.

Definition dwp_def `{irisDG Λ Σ, invG Σ} :
  coPset → expr Λ → expr Λ → (val Λ → val Λ → iProp Σ) → iProp Σ :=
  fixpoint dwp_pre.
Definition dwp_aux `{invG Σ, irisDG Λ Σ} : seal (@dwp_def Λ Σ _ _). by eexists. Qed.
Definition dwp `{irisDG Λ Σ, invG Σ} := dwp_aux.(unseal).
Definition dwp_eq `{irisDG Λ Σ, invG Σ} : dwp = @dwp_def Λ Σ _ _ := dwp_aux.(seal_eq).

(* Notation "'DWP' e '&' t @ E {{ Φ } }" := (dwp E e%E t%E Φ) *)
(*   (at level 20, e, t, Φ at level 200, only parsing) : bi_scope. *)
(* Notation "'DWP' e '&' t {{ Φ } }" := (dwp ⊤ e%E t%E Φ) *)
(*   (at level 20, e, t, Φ at level 200, only parsing) : bi_scope. *)
(* Notation "'DWP' e '&' t @ E {{ v1  v2 , Q } }" := (dwp E e%E t%E (λ v1 v2, Q)) *)
(*   (at level 20, e, t, Q at level 200, *)
(*    format "'[' 'DWP'  e  &  t  '/' '[       ' @  E  {{  v1  v2 ,  Q  } } ']' ']'") : bi_scope. *)
(* Notation "'DWP' e '&' t {{ v1 v2 , Q } }" := (dwp ⊤ e%E t%E (λ v1 v2, Q)) *)
(*   (at level 20, e, t, Q at level 200, *)
(*    format "'[' 'DWP'  e  &  t  '/' '[   ' {{  v1  v2 ,  Q  } } ']' ']'") : bi_scope. *)

Section dwp.
Context `{irisDG Λ Σ, invG Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Lemma dwp_unfold E1 e1 e2 Φ :
  dwp E1 e1 e2 Φ ⊣⊢ dwp_pre dwp E1 e1 e2 Φ.
  (* DWP e1 & e2 @ E {{ Φ }} ⊣⊢ dwp_pre dwp E e1 e2 Φ. *)
Proof. rewrite dwp_eq. apply (fixpoint_unfold dwp_pre). Qed.

(* Lemma dwp_atomic E1 E2 E3 e1 e2 Φ `{Atomic _ StronglyAtomic e1} : *)
(*   (|={E1,E2}=> dwp E2 E3 e1 e2 (λ v1 v2, |={E2,E1}=> Φ v1 v2)) ⊢ *)
(*   dwp E1 E3 e1 e2 Φ. *)
(* Proof. *)
(*   iIntros "H". rewrite !dwp_unfold /dwp_pre. *)
(*   destruct (to_val e1) as [v1|] eqn:He1. *)
(*   { destruct (to_val e2) as [v2|] eqn:He2. *)
(*     - repeat rewrite fupd_trans. done. *)
(*     - repeat rewrite fupd_trans. *)
(*       iIntros (σ1 σ2) "Hσ". iMod "H". iSpecialize ("H" with "Hσ"). *)
(*       by iMod "H". } *)
(*   iIntros (σ1 σ2) "Hσ". iMod "H". iMod ("H" with "Hσ") as "[$ H]". *)
(*   iModIntro. iIntros (e1' σ1' efs1 Hstep1). *)
(*   iMod ("H" with "[//]") as "H". iModIntro. iNext. *)
(*   iMod "H" as "H". *)
(*   iDestruct "H" as (e2' σ2' efs2 Hstep2) "(Hσ & H & Hefs)". *)
(*   destruct (atomic _ _ _ _ Hstep1) as [v1 <-%of_to_val]. *)
(*   iExists e2', σ2', efs2. iFrame "Hefs". *)
(*   rewrite dwp_unfold /dwp_pre. rewrite to_of_val. *)
(*   destruct (to_val e2') as [v2|] eqn:He2; simplify_eq/=. *)
(*   - iMod "H". iMod "H". iModIntro. iFrame "Hσ". *)
(*     iSplit; eauto.  rewrite dwp_unfold /dwp_pre. rewrite to_of_val. *)
(*     rewrite He2. done. *)
(*   - iMod ("H" with "Hσ") as "H". done. *)
(* Qed. *)

Global Instance dwp_ne E1 e1 e2 n :
  Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==> dist n) (dwp E1 e1 e2).
Proof.
  revert e1 e2. induction (lt_wf n) as [n _ IH]=> e1 e2 Φ Ψ HΦ.
  rewrite !dwp_unfold /dwp_pre.
  (* FIXME: figure out a way to properly automate this proof *)
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  do 33 (f_contractive || f_equiv).
  do 5 (f_contractive || f_equiv).
  apply IH; first lia.
  intros v v'. eapply (dist_le (S (S n))); eauto with lia.
  apply HΦ.
Qed.

Global Instance dwp_proper E1 e1 e2 :
  Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (≡)) (dwp E1 e1 e2).
Proof.
  by intros Φ Φ' HΦ; apply equiv_dist=>n; apply dwp_ne=>v v'; apply equiv_dist, HΦ.
Qed.

Lemma dwp_value' E1 Φ v v' :
  (|={E1}=> Φ v v')%I ⊢ dwp E1 (of_val v) (of_val v') Φ.
Proof.
  iIntros "HΦ". rewrite dwp_unfold /dwp_pre !to_of_val.
  eauto with iFrame.
Qed.

Lemma dwp_value_inv' E1 Φ v v' :
  dwp E1 (of_val v) (of_val v') Φ
  ={E1}=∗ Φ v v'.
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
  destruct (to_val e1) as [v1|] eqn:?.
  { destruct (to_val e2) as [v2|] eqn:?.
    - rewrite (fupd_mask_mono E1 E1'); last assumption.
      iMod "H" as "H". by iApply ("HΦ" with "[> -]").
    - by rewrite (fupd_mask_mono E1 E1'). }
  iIntros (σ1 σ2 κ1 κs1 κ2 κs2) "Hσ".
  iMod (fupd_intro_mask' E1' E1) as "Hclose"; first done.
  iMod ("H" with "Hσ") as "[% [% H]]".
  iModIntro. iSplit; [by eauto|]. iSplit; [by eauto|].
  iIntros (e1' σ1' efs1 e2' σ2' efs2 Hstep1 Hstep2).
  do 2 iSpecialize ("H" with "[//]"). iMod "H" as "H". iIntros "!>!>".
  iMod "H" as "H". iModIntro. iNext.
  iMod "H" as "H". iMod "Hclose" as "_". iModIntro.
  iDestruct "H" as "(Hσ & H & Hefs)". iFrame.
  iApply ("IH" with "[//] H HΦ").
Qed.

Lemma fupd_dwp E1 e1 e2 Φ :
  (|={E1}=> dwp E1 e1 e2 Φ) ⊢
  dwp E1 e1 e2 Φ.
Proof.
  rewrite dwp_unfold /dwp_pre. iIntros "H".
  destruct (to_val e1) as [v1|] eqn:?.
  { destruct (to_val e2) as [v2|] eqn:?; first rewrite fupd_trans //.
    iMod "H". by iApply "H". }
  iMod "H". iIntros (σ1 σ' ????) "Hσ".
  by iMod ("H" with "Hσ").
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
  destruct (to_val e1) as [v1|] eqn:He1.
  { destruct (to_val e2) as [v2|] eqn:He2.
    - apply of_to_val in He1 as <-.
      apply of_to_val in He2 as <-. by iApply fupd_dwp.
    - rewrite dwp_unfold /dwp_pre (fill_not_val e2) //.
      destruct (to_val (K1 e1)) as [w|] eqn:?; eauto.
      iIntros (??????) "Hσ". by iMod "H". }
  rewrite dwp_unfold /dwp_pre !fill_not_val //.
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
  assert (to_val e2 = None) as He2.
  { eapply reducible_not_val. eexists. eauto. }
  clear Hstep1 Hstep2.
  iIntros (e1' σ1' efs1 e2' σ2' efs2 Hstep1 Hstep2).
  destruct (fill_step_inv e1 σ1 [] e1' σ1' efs1 He1 Hstep1) as (e1''&->&?) .
  destruct (fill_step_inv e2 σ2 [] e2' σ2' efs2 He2 Hstep2) as (e2''&->&?).
  iSpecialize ("H" with "[//]").
  iSpecialize ("H" with "[//]").
  iMod "H" as "H". iIntros "!>!>".
  iMod "H" as "H". iIntros "!>!>".
  iMod "H" as "H".
  iDestruct "H" as "(Hσ & H & Hefs)".
  apply fill_step in Hstep2. iFrame.
  by iApply "IH".
Qed.

(** DF: The other bind rule does not hold.
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
  to_val e1 = None → E1' ⊆ E1 →
  (|={E1,E1'}▷=> P) -∗
  dwp E1' e1 e2 (λ v1 v2, P ={E1}=∗ Φ v1 v2) -∗
  dwp E1 e1 e2 Φ.
Proof.
  rewrite !dwp_unfold /dwp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1 σ2 ? ? ? ?) "Hσ". iMod "HR".
  iMod ("H" with "Hσ") as "[$ [$ H]]".
  iIntros "!>" (e1' σ1' efs Hstep1 e2' σ2' efs2 Hstep2).
  iSpecialize ("H" with "[//]").
  iSpecialize ("H" with "[//]").
  iMod "H" as "H".
  iModIntro. iNext.
  iMod "H" as "H". iModIntro. iNext.
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
(* Global Instance dwp_mono' E1 e1 e2 : *)
(*   Proper (pointwise_relation _ (⊢) ==> (⊢)) (dwp E1 e1 e2). *)
(* Proof. by intros Φ Φ' ?; apply wp_mono. Qed. *)

Lemma dwp_frame_l E1 e1 e2 Φ R :
  R ∗ dwp E1 e1 e2 Φ ⊢ dwp E1 e1 e2 (λ v1 v2, R ∗ Φ v1 v2).
Proof. iIntros "[? H]". iApply (dwp_strong_mono with "H"); auto with iFrame. Qed.
Lemma dwp_frame_r E1 e1 e2 Φ R :
  dwp E1 e1 e2 Φ ∗ R ⊢ dwp E1 e1 e2 (λ v1 v2, Φ v1 v2 ∗ R).
Proof. iIntros "[H ?]". iApply (dwp_strong_mono with "H"); auto with iFrame. Qed.

(* Lemma wp_frame_step_l s E1 E2 e Φ R : *)
(*   to_val e = None → E2 ⊆ E1 → *)
(*   (|={E1,E2}▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}. *)
(* Proof. *)
(*   iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done. *)
(*   iApply (wp_mono with "Hwp"). by iIntros (?) "$$". *)
(* Qed. *)
(* Lemma wp_frame_step_r s E1 E2 e Φ R : *)
(*   to_val e = None → E2 ⊆ E1 → *)
(*   WP e @ s; E2 {{ Φ }} ∗ (|={E1,E2}▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}. *)
(* Proof. *)
(*   rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R). *)
(*   apply wp_frame_step_l. *)
(* Qed. *)
(* Lemma wp_frame_step_l' s E e Φ R : *)
(*   to_val e = None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}. *)
(* Proof. iIntros (?) "[??]". iApply (wp_frame_step_l s E E); try iFrame; eauto. Qed. *)
(* Lemma wp_frame_step_r' s E e Φ R : *)
(*   to_val e = None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}. *)
(* Proof. iIntros (?) "[??]". iApply (wp_frame_step_r s E E); try iFrame; eauto. Qed. *)

Lemma dwp_wand E1 e1 e2 Φ Ψ :
  dwp E1 e1 e2 Φ -∗
  (∀ v1 v2, Φ v1 v2 -∗ Ψ v1 v2) -∗
  dwp E1 e1 e2 Ψ.
Proof.
  iIntros "Hwp H". iApply (dwp_strong_mono with "Hwp"); auto.
  iIntros (??) "?". by iApply "H".
Qed.
End dwp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{irisDG Λ Σ, invG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → val Λ → iProp Σ.

  Global Instance frame_wp p E1 e1 e2 R Φ Ψ :
    (∀ v1 v2, Frame p R (Φ v1 v2) (Ψ v1 v2)) →
    Frame p R (dwp E1 e1 e2 Φ) (dwp E1 e1 e2 Ψ).
  Proof. rewrite /Frame=> HR. rewrite dwp_frame_l. apply dwp_mono, HR. Qed.

  Global Instance is_except_0_wp E1 e1 e2 Φ :
    IsExcept0 (dwp E1 e1 e2 Φ).
  Proof. by rewrite /IsExcept0 -{2}fupd_dwp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p E1 e1 e2 P Φ :
    ElimModal True p false (|==> P) P
              (dwp E1 e1 e2 Φ) (dwp E1 e1 e2 Φ).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E1) fupd_frame_r wand_elim_r fupd_dwp.
  Qed.

  Global Instance elim_modal_fupd_wp p E1 e1 e2 P Φ :
    ElimModal True p false (|={E1}=> P) P
              (dwp E1 e1 e2 Φ) (dwp E1 e1 e2 Φ).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_dwp.
  Qed.

  (* Global Instance elim_modal_fupd_wp_atomic p E1 E2 E3 e1 e2 P Φ : *)
  (*   Atomic StronglyAtomic e1 → *)
  (*   ElimModal True p false (|={E1,E2}=> P) P *)
  (*           (dwp E1 E3 e1 e2 Φ) (dwp E2 E3 e1 e2 (λ v1 v2, |={E2,E1}=> Φ v1 v2)%I). *)
  (* Proof. *)
  (*   intros. by rewrite /ElimModal intuitionistically_if_elim *)
  (*     fupd_frame_r wand_elim_r dwp_atomic. *)
  (* Qed. *)

  Global Instance add_modal_fupd_wp E1 e1 e2 P Φ :
    AddModal (|={E1}=> P) P (dwp E1 e1 e2 Φ).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_dwp. Qed.

  (* Global Instance elim_acc_wp {X} E1 E2 α β γ e s Φ : *)
  (*   Atomic (stuckness_to_atomicity s) e → *)
  (*   ElimAcc (X:=X) (fupd E1 E2) (fupd E2 E1) *)
  (*           α β γ (WP e @ s; E1 {{ Φ }}) *)
  (*           (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I. *)
  (* Proof. *)
  (*   intros ?. rewrite /ElimAcc. *)
  (*   iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]". *)
  (*   iApply (wp_wand with "[Hinner Hα]"); first by iApply "Hinner". *)
  (*   iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose". *)
  (* Qed. *)

  (* Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ : *)
  (*   ElimAcc (X:=X) (fupd E E) (fupd E E) *)
  (*           α β γ (WP e @ s; E {{ Φ }}) *)
  (*           (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I. *)
  (* Proof. *)
  (*   rewrite /ElimAcc. *)
  (*   iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]". *)
  (*   iApply wp_fupd. *)
  (*   iApply (wp_wand with "[Hinner Hα]"); first by iApply "Hinner". *)
  (*   iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose". *)
  (* Qed. *)
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
