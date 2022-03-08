(** Some derived lemmas for ectx-based languages *)
From iris_ni.program_logic Require Export dwp lifting.
From iris.program_logic Require Export ectx_language weakestpre.
From iris.proofmode Require Import proofmode.
Set Default Proof Using "Type".

Section lifting.
Context {Λ : ectxLanguage} `{!irisDG Λ Σ, !invGS Σ} {Hinh : Inhabited (state Λ)}.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → val Λ → iProp Σ.
Hint Resolve head_prim_reducible head_reducible_prim_step : core.
Hint Resolve reducible_not_val : core.
Hint Resolve head_stuck_stuck : core.

Lemma dwp_lift_pure_det_head_step {E1 E1' Φ} e1 e1' e2 e2' efs1 efs2 :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ κ1 σ1 e1'' σ1' efs1', head_step e1 σ1 κ1 e1'' σ1' efs1' → κ1 = [] ∧ σ1' = σ1 ∧ e1'' = e1' ∧ efs1' = efs1) →
  (∀ σ2, head_reducible e2 σ2) →
  (∀ κ2 σ2 e2'' σ2' efs2', head_step e2 σ2 κ2 e2'' σ2' efs2' → κ2 = [] ∧ σ2' = σ2 ∧ e2'' = e2' ∧ efs2' = efs2) →
  (|={E1}[E1']▷=> dwp E1 e1' e2' Φ ∗
                 [∗ list] ef1;ef2 ∈ efs1;efs2, dwp ⊤ ef1 ef2 (λ _ _, True ))
  ⊢ dwp E1 e1 e2 Φ.
Proof using Hinh.
  intros. rewrite -(dwp_lift_pure_det_step e1 e1' e2 e2'); eauto.
Qed.

End lifting.
