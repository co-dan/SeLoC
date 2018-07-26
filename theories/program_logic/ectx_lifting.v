(** Some derived lemmas for ectx-based languages *)
From iris_ni.program_logic Require Export dwp lifting.
From iris.program_logic Require Export ectx_language weakestpre.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section lifting.
Context {Λ : ectxLanguage} `{irisDG Λ Σ, invG Σ} {Hinh : Inhabited (state Λ)}.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → val Λ → iProp Σ.
Hint Resolve head_prim_reducible head_reducible_prim_step.
Hint Resolve (reducible_not_val _ inhabitant).
Hint Resolve head_stuck_stuck.

(* Lemma dwp_lift_head_step_fupd E1 Φ e1 e2 : *)
(*   to_val e1 = None → *)
(*   (∀ σ1 σ2 κ1 κs1 κs2, state_rel σ1 σ2 (κ1 ++ κs1) κs2 ={E1,∅}=∗ *)
(*     ⌜head_reducible e1 σ1⌝ ∗ *)
(*     ∀ e1' σ1' efs, ⌜head_step e1 σ1 κ1 e1' σ1' efs⌝ ={∅,∅,E1}▷=∗ *)
(*       ∃ κ2 κs2' e2' σ2' efs', ⌜κs2 = κ2 ++ κs2'⌝ ∗ *)
(*          ⌜head_step e2 σ2 κ2 e2' σ2' efs'⌝ ∗ *)
(*          state_rel σ1' σ2' κs1 κs2' ∗ dwp E1 e1' e2' Φ ∗ *)
(*          [∗ list] ef ; ef' ∈ efs ; efs', dwp ⊤ ef ef' (λ _ _, True)) *)
(*   ⊢ dwp E1 e1 e2 Φ. *)
(* Proof. *)
(*   iIntros (?) "H". iApply dwp_lift_step_fupd; first done. *)
(*   iIntros (σ1 σ2 κ1 κs1 κs2) "Hσ". *)
(*   iMod ("H" with "Hσ") as "[Hred H]". iModIntro. *)
(*   iDestruct "Hred" as %Hred1. *)
(*   iSplit; first eauto. iIntros (e1' σ1' efs Hstep1). *)
(*   apply (head_reducible_prim_step _ _ _ _ _ _ Hred1) in Hstep1. *)
(*   iSpecialize ("H" $! e1' σ1' efs with "[%]"); first eauto. *)
(*   iMod "H" as "H". iModIntro. iNext. *)
(*   iMod "H" as (κ2 κs2' e2' σ2' efs') "(% & Hred & H)". iModIntro. *)
(*   iDestruct "Hred" as %Hred2. *)
(*   apply head_prim_step in Hred2. *)
(*   iExists _,_,_,_,_. iFrame "H". iSplit; eauto. *)
(* Qed. *)

Lemma dwp_lift_pure_det_head_step {E1 E1' Φ} e1 e1' e2 e2' efs1 efs2 :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ κ1 σ1 e1'' σ1' efs1', head_step e1 σ1 κ1 e1'' σ1' efs1' → κ1 = [] ∧ σ1' = σ1 ∧ e1'' = e1' ∧ efs1' = efs1) →
  (∀ σ2, head_reducible e2 σ2) →
  (∀ κ2 σ2 e2'' σ2' efs2', head_step e2 σ2 κ2 e2'' σ2' efs2' → κ2 = [] ∧ σ2' = σ2 ∧ e2'' = e2' ∧ efs2' = efs2) →
  (|={E1,E1'}▷=> dwp E1 e1' e2' Φ ∗
                 [∗ list] ef1;ef2 ∈ efs1;efs2, dwp ⊤ ef1 ef2 (λ _ _, True ))
  ⊢ dwp E1 e1 e2 Φ.
Proof using Hinh.
  intros. rewrite -(dwp_lift_pure_det_step e1 e1' e2 e2'); eauto.
Qed.

End lifting.
