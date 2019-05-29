From iris.base_logic Require Export gen_heap.
From iris_ni.program_logic Require Export dwp classes ectx_lifting.
From iris.heap_lang Require Export lang lifting notation.
From iris.heap_lang Require Import tactics.
From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
Set Default Proof Using "Type".

Class heapDG Σ := HeapDG {
  heapDG_invG :> invG Σ;
  heapDG_proph_mapG1 :> proph_mapG proph_id val Σ;
  heapDG_proph_mapG2 :> proph_mapG proph_id val Σ;
  heapDG_gen_heapG1 :> gen_heapG loc val Σ;
  heapDG_gen_heapG2 :> gen_heapG loc val Σ
}.

(** irisG instances for both sides *)
Definition irisG1 `{heapDG Σ} : irisG heap_lang Σ :=
  @heapG_irisG Σ {| heapG_invG := heapDG_invG;
                    heapG_gen_heapG := heapDG_gen_heapG1;
                    heapG_proph_mapG := heapDG_proph_mapG1 |}.
Definition irisG2 `{heapDG Σ} : irisG heap_lang Σ :=
  @heapG_irisG Σ {| heapG_invG := heapDG_invG;
                    heapG_gen_heapG := heapDG_gen_heapG2;
                    heapG_proph_mapG := heapDG_proph_mapG2 |}.

Definition WP1 `{heapDG Σ} (e : expr) (E : coPset) (R : val → iProp Σ) :=
  @wp heap_lang (iProp Σ) stuckness
      (@wp' heap_lang Σ irisG1)
      NotStuck E e R.

Definition WP2 `{heapDG Σ} (e : expr) (E : coPset) (R : val → iProp Σ) :=
  @wp heap_lang (iProp Σ) stuckness
      (@wp' heap_lang Σ irisG2)
      NotStuck E e R.

Definition mapsto1 `{heapDG Σ} (l : loc) (q : Qp) (v : val) :=
  @mapsto loc _ _ val Σ heapDG_gen_heapG1 l q v.
Definition mapsto2 `{heapDG Σ} (l : loc) (q : Qp) (v : val) :=
  @mapsto loc _ _ val Σ heapDG_gen_heapG2 l q v.

Notation "l ↦ₗ{ q } v" := (mapsto1 l q v%V)
  (at level 20, q at level 50, format "l  ↦ₗ{ q }  v") : bi_scope.
Notation "l ↦ₗ v" :=
  (mapsto1  l 1 v%V) (at level 20) : bi_scope.
Notation "l ↦ₗ{ q } -" := (∃ v, l ↦ₗ{q} v)%I
  (at level 20, q at level 50, format "l  ↦ₗ{ q }  -") : bi_scope.
Notation "l ↦ₗ -" := (l ↦ₗ{1} -)%I (at level 20) : bi_scope.

Notation "l ↦ᵣ{ q } v" := (mapsto2 l q v%V)
  (at level 20, q at level 50, format "l  ↦ᵣ{ q }  v") : bi_scope.
Notation "l ↦ᵣ v" :=
  (mapsto2 l 1 v%V) (at level 20) : bi_scope.
Notation "l ↦ᵣ{ q } -" := (∃ v, l ↦ᵣ{q} v)%I
  (at level 20, q at level 50, format "l  ↦ᵣ{ q }  -") : bi_scope.
Notation "l ↦ᵣ -" := (l ↦ₗ{1} -)%I (at level 20) : bi_scope.

Instance heapDG_irisDG `{heapDG Σ} : irisDG heap_lang Σ := {
  state_rel := (λ σ1 σ2 κs1 κs2,
      @gen_heap_ctx _ _ _ _ _ heapDG_gen_heapG1 σ1.(heap)
    ∗ @proph_map_ctx _ _ _ _ _ heapDG_proph_mapG1 κs1 σ1.(used_proph_id)
    ∗ @gen_heap_ctx _ _ _ _ _ heapDG_gen_heapG2 σ2.(heap)
    ∗ @proph_map_ctx _ _ _ _ _ heapDG_proph_mapG2 κs2 σ2.(used_proph_id))%I
}.

Section lifting.
Context `{heapDG Σ}.

(* Local Hint Extern 0 (atomic _ _) => solve_atomic. *)
Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl.

Local Hint Constructors head_step.

Lemma dwp_fork E e1 e2 Φ :
  ▷ dwp ⊤ e1 e2 (λ _ _, True)%I -∗
  ▷ Φ #() #() -∗
  dwp E (Fork e1) (Fork e2) Φ.
Proof.
  iIntros "He HΦ".
  iApply dwp_lift_pure_det_head_step; [auto| |auto| |].
  all: try by (intros; inv_head_step; eauto).
  iModIntro. iNext. iModIntro. simpl. iFrame "He".
  by iApply dwp_value.
Qed.

(* TODO:
   - all these `to_val ei = None` and "no forks" conditions
     should be dischargeable automatically
   - |={E1,E2}=> ∃ Ψ1 Ψ2, ...
*)
Lemma dwp_atomic_lift_wp E1 E2 Ψ1 Ψ2 e1 e2 Φ
  `{Atomic _ StronglyAtomic e1}
  `{Atomic _ StronglyAtomic e2}
  {NF1 : NoFork e1}
  {NF2 : NoFork e2}
  {NO1 : NoObs e1}
  {NO2 : NoObs e2} :
  to_val e1 = None →
  to_val e2 = None →
  ((|={E1,E2}=> WP1 e1 E2 Ψ1 ∗ WP2 e2 ∅ (λ v, |={E2}=> Ψ2 v) ∗
     (∀ v1 v2, Ψ1 v1 -∗ Ψ2 v2 ={E2,E1}=∗ ▷ Φ v1 v2)) -∗
  dwp E1 e1 e2 Φ).
Proof.
  intros He1 He2.
  iIntros "H".
  rewrite dwp_unfold /dwp_pre /=.
  rewrite /WP1 /WP2 !wp_unfold /wp_pre /= !He1 !He2.
  iIntros (σ1 σ2 κ1 κs1 κ2 κs2) "Hσ".
  iDestruct "Hσ" as "(Hσ1 & Hκs1 & Hσ2 & Hκs2)".
  iMod "H" as "(HWP1 & HWP2 & H)".
  iSpecialize ("HWP1" $! σ1 [] (κ1++κs1) 0%nat with "[$Hσ1 $Hκs1]").
  iSpecialize ("HWP2" $! σ2 [] (κ2++κs2) 0%nat with "[$Hσ2 $Hκs2]").
  iMod "HWP1" as (Hred1) "HWP1".
  iMod "HWP2" as (Hred2) "HWP2".
  destruct Hred1 as (κ1' & ? & ? & ? & Hred1).
  assert (κ1' = []) as ->.
  { eapply (@noobs e1 _). eauto. }
  destruct Hred2 as (κ2' & ? & ? & ? & Hred2).
  assert (κ2' = []) as ->.
  { eapply (@noobs e2 _). eauto. }
  iModIntro.
  iSplit. { iPureIntro. eexists. eauto. }
  iSplit. { iPureIntro. eexists. eauto. }
  iIntros (e1' σ1' efs e2' σ2' efs2 Hstep1 Hstep2).
  iSpecialize ("HWP1" $! e1' σ1' efs with "[//]").
  iSpecialize ("HWP2" with "[//]").
  iMod "HWP1". iMod "HWP2". iModIntro. iNext.
  iMod "HWP2". iMod "HWP1".
  iDestruct "HWP1" as "([Hh1 Hp1] & HWP1 & _)".
  iDestruct "HWP2" as "([Hh2 Hp2] & HWP2 & _)".
  destruct (to_val e1') as [v1|] eqn:Hv1; last first.
  { exfalso. destruct (atomic _ _ _ _ _ Hstep1). naive_solver. }
  destruct (to_val e2') as [v2|] eqn:Hv2; last first.
  { exfalso. destruct (atomic _ _ _ _ _ Hstep2). naive_solver. }
  rewrite -(of_to_val _ _ Hv1) -(of_to_val _ _ Hv2).
  rewrite !wp_value_inv'. iMod "HWP1".
  rewrite (fupd_mask_mono ∅ E2); last by set_solver.
  iMod "HWP2". iMod "HWP2".
  iMod ("H" with "HWP1 HWP2") as "H".
  iApply step_fupd_intro. set_solver.
  iNext. rewrite -dwp_value. iFrame.
  rewrite (nofork _ _ _ _ _ Hstep1).
  rewrite (nofork _ _ _ _ _ Hstep2).
  simpl. eauto with iFrame.
Qed.

Lemma dwp_load E (l1 l2: loc) v1 v2 Φ :
  ▷l1 ↦ₗ v1 -∗
  ▷l2 ↦ᵣ v2 -∗
  ▷ (l1 ↦ₗ v1 ∗ l2 ↦ᵣ v2 -∗ Φ v1 v2) -∗
  dwp E (! #l1) (! #l2) Φ.
Proof.
  iIntros "Hl1 Hl2 HΦ".
  iApply (dwp_atomic_lift_wp _ _
    (λ v, ⌜v = v1⌝ ∗ l1 ↦ₗ v1)%I
    (λ v, ⌜v = v2⌝ ∗ l2 ↦ᵣ v2)%I)=>//.
  iModIntro. iSplitL "Hl1".
  { iApply (wp_load  _ _ l1 1 v1 with "[Hl1]").
    iNext. iFrame "Hl1". eauto. }
  iSplitL "Hl2".
  { iApply (wp_load  _ _ l2 1 v2 with "[Hl2]").
    iNext. done. eauto. }
  iIntros (? ?) "[% Hl1] [% Hl2]". simplify_eq.
  iModIntro. iNext. iApply "HΦ". iFrame.
Qed.

Lemma dwp_atomic E1 E2 e1 e2 Φ
  `{Atomic _ StronglyAtomic e1}
  `{Atomic _ StronglyAtomic e2} :
  (|={E1,E2}=> dwp E2 e1 e2 (λ v1 v2, |={E2,E1}=> Φ v1 v2)) -∗
  dwp E1 e1 e2 Φ.
Proof.
  iIntros "H".
  rewrite (dwp_unfold E1) /dwp_pre /=.
  destruct (to_val e1) as [v1|] eqn:He1.
  { rewrite dwp_unfold /dwp_pre /= He1.
    destruct (to_val e2) as [v2|] eqn:He2.
    - iMod "H" as "H". by iMod "H" as "H".
    - iMod "H" as "H". by iMod "H". }
  iIntros (σ1 σ2 κ1 κs1 κ2 κs2) "Hσ".
  iDestruct "Hσ" as "(Hσ1 & Hκs1 & Hσ2 & Hκs2)".
  iMod "H" as "H".
  rewrite dwp_unfold /dwp_pre /= He1.
  iSpecialize ("H" $! σ1 σ2 κ1 κs1 κ2 κs2 with "[$Hσ1 $Hκs1 $Hσ2 $Hκs2]").
  iMod "H" as (??) "H". iModIntro.
  do 2 (iSplit; first done).
  iIntros (e1' σ1' efs e2' σ2' efs2 Hstep1 Hstep2).
  iSpecialize ("H" $! e1' σ1' efs e2' σ2' efs2 Hstep1 Hstep2).
  iMod "H" as "H". iModIntro. iNext.
  iMod "H" as "H". iModIntro. iNext.
  iMod "H" as "[Hst [H $]]".
  destruct (to_val e1') as [v1|] eqn:Hv1; last first.
  { exfalso. destruct (atomic _ _ _ _ _ Hstep1). naive_solver. }
  destruct (to_val e2') as [v2|] eqn:Hv2; last first.
  { exfalso. destruct (atomic _ _ _ _ _ Hstep2). naive_solver. }
  rewrite -(of_to_val _ _ Hv1) -(of_to_val _ _ Hv2).
  rewrite dwp_value_inv' -dwp_value. iMod "H". iMod "H" as "$".
  iModIntro. iFrame. done.
Qed.

End lifting.


