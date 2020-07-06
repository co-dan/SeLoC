From iris.base_logic Require Export gen_heap.
From iris_ni.program_logic Require Export dwp classes ectx_lifting.
From iris_ni.program_logic Require Export dwp classes.
From iris.heap_lang Require Export lang notation.
From iris.heap_lang Require Import tactics proofmode.
From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
Set Default Proof Using "Type".

Class heapDG Σ := HeapDG {
  heapDG_invG :> invG Σ;
  heapDG_proph_mapG1 :> proph_mapG proph_id (val*val) Σ;
  heapDG_proph_mapG2 :> proph_mapG proph_id (val*val) Σ;
  heapDG_gen_heapG1 :> gen_heapG loc (option val) Σ;
  heapDG_gen_heapG2 :> gen_heapG loc (option val) Σ;
  heapDG_inv_heapG1 :> inv_heapG loc (option val) Σ;
  heapDG_inv_heapG2 :> inv_heapG loc (option val) Σ;
}.

(** heapG instanecs for both sides *)
Definition heapG1 `{heapDG Σ} : heapG Σ :=
  {| heapG_invG := heapDG_invG;
     heapG_gen_heapG := heapDG_gen_heapG1;
     heapG_inv_heapG := heapDG_inv_heapG1;
     heapG_proph_mapG := heapDG_proph_mapG1 |}.
Definition heapG2 `{heapDG Σ} : heapG Σ :=
  {| heapG_invG := heapDG_invG;
     heapG_gen_heapG := heapDG_gen_heapG2;
     heapG_inv_heapG := heapDG_inv_heapG2;
     heapG_proph_mapG := heapDG_proph_mapG2 |}.

(** irisG instances for both sides *)
Definition irisG1 `{!heapDG Σ} : irisG heap_lang Σ :=
  @heapG_irisG Σ heapG1.
Definition irisG2 `{!heapDG Σ} : irisG heap_lang Σ :=
  @heapG_irisG Σ heapG2.

Definition TWP1 `{!heapDG Σ} (e : expr) (E : coPset) (R : val → iProp Σ) :=
  @twp heap_lang (iProp Σ) stuckness
       (@twp' heap_lang Σ irisG1)
       NotStuck E e R.

Definition TWP2 `{!heapDG Σ} (e : expr) (E : coPset) (R : val → iProp Σ) :=
  @twp heap_lang (iProp Σ) stuckness
       (@twp' heap_lang Σ irisG2)
       NotStuck E e R.

Definition mapsto1 `{!heapDG Σ} (l : loc) (q : Qp) (v : val) :=
  @mapsto loc _ _ _ Σ heapDG_gen_heapG1 l q (Some v%V).
Definition mapsto2 `{!heapDG Σ} (l : loc) (q : Qp) (v : val) :=
  @mapsto loc _ _ _ Σ heapDG_gen_heapG2 l q (Some v%V).

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

Definition array1 `{heapDG Σ} (l : loc) (vs :  list val) :=
  ([∗ list] i ↦ v ∈ vs, (l +ₗ i) ↦ₗ v)%I.
Definition array2 `{heapDG Σ} (l : loc) (vs :  list val) :=
  ([∗ list] i ↦ v ∈ vs, (l +ₗ i) ↦ᵣ v)%I.

Notation "l ↦ₗ∗ vs" := (array1 l vs)
  (at level 20, format "l  ↦ₗ∗  vs") : bi_scope.
Notation "l ↦ᵣ∗ vs" := (array2 l vs)
  (at level 20, format "l  ↦ᵣ∗  vs") : bi_scope.

Definition meta1 `{heapDG Σ} {A} `{EqDecision A, Countable A}
           (l : loc) (N : namespace) (x : A) :=
  @meta loc _ _ _ Σ heapDG_gen_heapG1 A _ _ l N x.
Definition meta2 `{heapDG Σ} {A} `{EqDecision A, Countable A}
           (l : loc) (N : namespace) (x : A) :=
  @meta loc _ _ _ Σ heapDG_gen_heapG2 A _ _ l N x.


Instance heapDG_irisDG `{!heapDG Σ} : irisDG heap_lang Σ := {
  state_rel := (λ σ1 σ2 κs1 κs2,
      @gen_heap_ctx _ _ _ _ _ heapDG_gen_heapG1 σ1.(heap)
    ∗ @proph_map_ctx _ _ _ _ _ heapDG_proph_mapG1 κs1 σ1.(used_proph_id)
    ∗ @gen_heap_ctx _ _ _ _ _ heapDG_gen_heapG2 σ2.(heap)
    ∗ @proph_map_ctx _ _ _ _ _ heapDG_proph_mapG2 κs2 σ2.(used_proph_id))%I
}.

Section array_liftings.
  Context `{!heapDG Σ}.
  Lemma array1_cons l v vs : l ↦ₗ∗ (v :: vs) ⊣⊢ l ↦ₗ v ∗ (l +ₗ 1) ↦ₗ∗ vs.
  Proof.
    rewrite /array1 /mapsto1 big_sepL_cons loc_add_0.
    setoid_rewrite loc_add_assoc.
    setoid_rewrite Nat2Z.inj_succ.
    by setoid_rewrite Z.add_1_l.
  Qed.
  Lemma array2_cons l v vs : l ↦ᵣ∗ (v :: vs) ⊣⊢ l ↦ᵣ v ∗ (l +ₗ 1) ↦ᵣ∗ vs.
  Proof.
    rewrite /array2 /mapsto2 big_sepL_cons loc_add_0.
    setoid_rewrite loc_add_assoc.
    setoid_rewrite Nat2Z.inj_succ.
    by setoid_rewrite Z.add_1_l.
  Qed.
End array_liftings.

Section lifting.
Context `{!heapDG Σ}.

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

Lemma dwp_atomic_lift_wp Ψ1 Ψ2 E2 e1 e2 Φ
  `{!Atomic StronglyAtomic e1}
  `{!Atomic StronglyAtomic e2}
  {NF1 : NoFork e1}
  {NF2 : NoFork e2}
  {NO1 : NoObs e1}
  {NO2 : NoObs e2}
  {He1 : NotVal e1}
  {He2 : NotVal e2}:
  TWP1 e1 E2 Ψ1 -∗
  TWP2 e2 ∅ Ψ2 -∗
  (∀ v1 v2, Ψ1 v1 -∗ Ψ2 v2 -∗ ▷ Φ v1 v2) -∗
  dwp E2 e1 e2 Φ.
Proof.
  iIntros "HTWP1 HTWP2 H".
  rewrite dwp_unfold /dwp_pre /= He1 He2.
  iIntros (σ1 σ2 κ1 κs1 κ2 κs2) "Hσ".
  iDestruct "Hσ" as "(Hσ1 & Hκs1 & Hσ2 & Hκs2)".
  rewrite /TWP1 /TWP2 !twp_unfold /twp_pre /= !He1 !He2.
  iSpecialize ("HTWP1" $! σ1 (κ1++κs1) 0%nat with "[$Hσ1 $Hκs1]").
  iSpecialize ("HTWP2" $! σ2 (κ2++κs2) 0%nat with "[$Hσ2 $Hκs2]").
  iMod "HTWP1" as (Hred1) "HTWP1".
  iMod "HTWP2" as (Hred2) "HTWP2".
  destruct Hred1 as (? & ? & ? & Hred1).
  destruct Hred2 as (? & ? & ? & Hred2).
  iModIntro.
  iSplit. { iPureIntro. eexists. eauto. }
  iSplit. { iPureIntro. eexists. eauto. }
  iIntros (e1' σ1' efs e2' σ2' efs2 Hstep1 Hstep2).
  iSpecialize ("HTWP1" $! [] e1' σ1' efs with "[//]").
  iSpecialize ("HTWP2" with "[//]").
  iMod "HTWP2" as "(_ & [Hh2 Hp2] & HTWP2 & _)".
  iMod "HTWP1" as "(_ & [Hh1 Hp1] & HTWP1 & _)".
  destruct (to_val e1') as [v1|] eqn:Hv1; last first.
  { exfalso. destruct (atomic _ _ _ _ _ Hstep1). naive_solver. }
  destruct (to_val e2') as [v2|] eqn:Hv2; last first.
  { exfalso. destruct (atomic _ _ _ _ _ Hstep2). naive_solver. }
  rewrite -(of_to_val _ _ Hv1) -(of_to_val _ _ Hv2).
  rewrite !twp_value_inv'. iMod "HTWP1".
  rewrite (fupd_mask_mono ∅ E2); last by set_solver.
  iMod "HTWP2". iFrame "Hh1 Hp1 Hh2 Hp2".
  iApply step_fupd_intro; first set_solver.
  iSpecialize ("H" with "HTWP1 HTWP2").
  iNext. rewrite -dwp_value. iFrame.
  rewrite (nofork _ _ _ _ _ Hstep1).
  rewrite (nofork _ _ _ _ _ Hstep2).
  simpl. eauto with iFrame.
Qed.

Lemma dwp_load E (l1 l2: loc) v1 v2 Φ :
  ▷l1 ↦ₗ v1 -∗
  ▷l2 ↦ᵣ v2 -∗
  (l1 ↦ₗ v1 -∗ l2 ↦ᵣ v2 -∗ ▷ Φ v1 v2) -∗
  dwp E (! #l1) (! #l2) Φ.
Proof.
  iIntros ">Hl1 >Hl2 HΦ".
  iApply (dwp_atomic_lift_wp
    (λ v, ⌜v = v1⌝ ∗ l1 ↦ₗ v1)%I
    (λ v, ⌜v = v2⌝ ∗ l2 ↦ᵣ v2)%I
    with "[Hl1] [Hl2] [HΦ]").
  { iApply (twp_load  _ _ l1 1 v1 with "[Hl1]"); eauto. }
  { iApply (twp_load  _ _ l2 1 v2 with "[Hl2]"); eauto. }
  iIntros (? ?) "[% Hl1] [% Hl2]". simplify_eq.
  iApply ("HΦ" with "Hl1 Hl2").
Qed.

Lemma dwp_alloc E (v1 v2 : val) Φ :
  (∀ r1 r2, r1 ↦ₗ v1 -∗ r2 ↦ᵣ v2 -∗ ▷ Φ #r1 #r2) -∗
  DWP ref v1 & ref v2 @ E : Φ.
Proof.
  iIntros "H".
  pose (Ψ1 := (λ v, ∃ r : loc, ⌜v = #r⌝ ∧ r ↦ₗ v1)%I).
  pose (Ψ2 := (λ v, ∃ r : loc, ⌜v = #r⌝ ∧ r ↦ᵣ v2)%I).
  iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[] [] [H]").
  { rewrite /TWP1 /Ψ1. wp_alloc r as "Hr". eauto with iFrame. }
  { rewrite /TWP2 /Ψ2. wp_alloc r as "Hr". eauto with iFrame. }
  iIntros (? ?). iDestruct 1 as (r1 ->) "Hr1". iDestruct 1 as (r2 ->) "Hr2".
  iApply ("H" with "Hr1 Hr2").
Qed.

Lemma dwp_store E (v1 v2 v1' v2' : val) (l1 l2 : loc) Φ :
  ▷l1 ↦ₗ v1 -∗
  ▷l2 ↦ᵣ v2 -∗
  (l1 ↦ₗ v1' -∗ l2 ↦ᵣ v2' -∗ ▷Φ #() #()) -∗
  DWP #l1 <- v1' & #l2 <- v2' @ E : Φ.
Proof.
  iIntros ">Hl1 >Hl2 HΦ".
  pose (Ψ1 := (λ v, ⌜v = #()⌝ ∗ l1 ↦ₗ v1')%I).
  pose (Ψ2 := (λ v, ⌜v = #()⌝ ∗ l2 ↦ᵣ v2')%I).
  iApply (dwp_atomic_lift_wp Ψ1 Ψ2 with "[Hl1] [Hl2] [HΦ]").
  { rewrite /TWP1 /Ψ1. wp_store. eauto with iFrame. }
  { rewrite /TWP2 /Ψ2. wp_store. eauto with iFrame. }
  iIntros (? ?). iDestruct 1 as (->) "Hl1". iDestruct 1 as (->) "Hl2".
  iApply ("HΦ" with "Hl1 Hl2").
Qed.

End lifting.
