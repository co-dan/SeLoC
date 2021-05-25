From stdpp Require Import namespaces.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang primitive_laws.
From iris_ni.program_logic Require Export dwp lifting heap_lang_lifting.
From iris_ni.logrel Require Export types interp.
Import uPred.

Local Open Scope nat.
Implicit Types L : gset loc.
Implicit Types l : loc.

Definition low_equiv L σ1 σ2 :=
  (∀ l, l ∈ L → ∃ n : Z, σ1.(heap) !! l = Some $ Some #n ∧ σ2.(heap) !! l = Some $ Some #n).

Instance low_equiv_transitive L : Transitive (low_equiv L).
Proof.
  intros σ1 σ2 σ3 Hl1 Hl2 l Hl.
  destruct (Hl1 l Hl) as [x [Hx1 Hx2]].
  destruct (Hl2 l Hl) as [y [Hy2 Hy3]].
  simplify_eq/=; eauto.
Qed.

(** In this file we define a bisimulation from DWP *)

Class heapPreDG Σ := HeapPreDG {
  heapPreDG_proph_mapG1 :> proph_mapPreG proph_id (val*val) Σ;
  heapPreDG_proph_mapG2 :> proph_mapPreG proph_id (val*val) Σ;
  heapPreDG_gen_heapG1 :> gen_heapPreG loc (option val) Σ;
  heapPreDG_gen_heapG2 :> gen_heapPreG loc (option val) Σ;
  heapPreDG_inv_heapG1 :> inv_heapPreG loc (option val) Σ;
  heapPreDG_inv_heapG2 :> inv_heapPreG loc (option val) Σ
}.

(* BEGIN helper lemmas *)
Section helper.
Definition extract_fn (σ : gmap loc (option val)) : loc → val := fun x =>
  match σ !!! x with
  | None => inhabitant
  | Some v => v
  end.
Lemma extract_fn_spec (σ : gmap loc (option val)) (l : loc) (v : val) :
  σ !! l = Some (Some v) → extract_fn σ l = v.
Proof.
  intros Hx. rewrite /extract_fn.
  by rewrite (lookup_total_correct _ _ _ Hx).
Qed.
End helper.
Section relation_lemmas.
  Context {A : Type}.
  Implicit Types R : relation A.

  Lemma tc_symmetric R :
    symmetric _ R → symmetric _ (tc R).
  Proof.
    intros HR x y. induction 1 as [x y Hxy|x y z Hxy Hyz IH].
    - by constructor; eauto.
    - eapply tc_r; eauto.
  Qed.

  Lemma transitive_tc_id R `{Transitive _ R} : ∀ x y, tc R x y ↔ R x y.
  Proof.
    intros x y; split; last by constructor.
    induction 1; eauto.
  Qed.

  Notation subrel R1 R2 := (∀ x y, R1 x y → R2 x y).

  Lemma tc_subrel R1 R2 : subrel R1 R2 → subrel (tc R1) (tc R2).
  Proof.
    intros HR x y. induction 1 as [x y Hxy|x y z Hxy Hyz IH].
    - by constructor; eauto.
    - eapply tc_l; eauto.
  Qed.
End relation_lemmas.
(* END helper lemmas *)

Lemma allocator_helper (σ : gmap loc (option val)) L `{!invG Σ, !gen_heapG loc (option val) Σ} :
  (∀ l, l ∈ L → ∃ (n : Z), σ !! l = Some $ Some #n) →
  let σ' := filter ((.∉ L) ∘ fst) σ in
  gen_heap_interp σ' ==∗ gen_heap_interp σ ∗ [∗ set] l ∈ L, l ↦ (extract_fn σ l).
Proof.
  iIntros (HL) "Hσ'".
  iMod (gen_heap_alloc_big with "Hσ'") as "(Hσ & HL)".
  { apply map_disjoint_filter. }
  iDestruct "HL" as "[HL _]".
  rewrite map_union_filter. iFrame "Hσ".
  iAssert ([∗ map] l↦d ∈ (filter (λ x, x.1 ∈ L) σ), l ↦ (extract_fn σ l))%I
      with "[HL]" as "HL".
  { iApply (big_sepM_mono with "HL").
    intros l v. rewrite map_filter_lookup_Some=> [[Hlσ HlL]].
    destruct (HL l HlL) as [n Hl]. simplify_eq/=.
    by rewrite (extract_fn_spec _ _ _ Hlσ). }
  rewrite big_sepM_dom.
  rewrite (dom_filter_L (λ x, x.1 ∈ L) σ L); first done.
  intros i. naive_solver.
Qed.

(* Useful version of [step_fupdN_soundnes'] *)
Lemma step_fupdN_soundness'' `{!invPreG Σ} φ n :
  (∀ `{Hinv: !invG Σ}, ⊢@{iPropI Σ} |={⊤}[∅]▷=>^n |={⊤}=> ⌜ φ ⌝) →
  φ.
Proof.
  iIntros (Hiter). eapply (step_fupdN_soundness' _ (S n))=>Hinv.
  rewrite Nat_iter_S_r.
  iPoseProof (Hiter Hinv) as "H".
  iApply (step_fupdN_mono with "H").
  iIntros "H". iMod "H".
  iApply (fupd_mask_weaken ∅); first set_solver.
  iIntros "H2". iModIntro. iNext. iMod "H2" as "_".
  done.
Qed.
Lemma step_fupdN_soundness''' `{!invPreG Σ} φ n :
  (∀ `{Hinv: !invG Σ}, ⊢@{iPropI Σ} |={⊤}[∅]▷=>^n |={⊤, ∅}=> ⌜ φ ⌝) →
  φ.
Proof.
  iIntros (Hiter).
  eapply (step_fupdN_soundness'' _ n)=>Hinv.
  iPoseProof (Hiter Hinv) as "H".
  iApply (step_fupdN_mono with "H").
  iIntros "H". iApply fupd_plainly_mask_empty.
  iMod "H" as "%Hfoo". done.
Qed.


Definition I_L (L : gset loc) `{!heapDG Σ} :=
  ([∗ set] l ∈ L, ⟦ tref (tint Low) ⟧ Low #(LitLoc l) #l)%I.

(** Now the relation *)
Definition dwp_rel Σ `{!invPreG Σ, !heapPreDG Σ}
  (es ss : list expr)
  (σ1 σ2 : state) (L : gset loc) (Φ : val → val → iProp Σ) :=
  ∃ n, ∀ `{Hinv : !invG Σ},
      ⊢ |={⊤}[∅]▷=>^n
         (|={⊤}=> ∃ (h1 h2 : gen_heapG loc (option val) Σ)
                    (hi1 hi2 : inv_heapG loc (option val) Σ)
                   (p1 p2 : proph_mapG proph_id (val*val) Σ),
            let _ := HeapDG _ _ p1 p2 h1 h2 in
            state_rel σ1 σ2 [] [] ∗
            I_L L ∗
            [∗ list] k↦e;s ∈ es;ss,
                dwp ⊤ e s (if decide (k = O) then Φ else (λ _ _, True))).

Definition I {Σ} (v1 v2 : val) : iProp Σ := ⌜v1 = v2⌝%I.

(** Lifting DWP proofs *)
Lemma dwp_lift_bisim e1 e2 σ1 σ2 L Σ `{!invPreG Σ, !heapPreDG Σ} :
  low_equiv L σ1 σ2 →
  (∀ `{!heapDG Σ}, I_L L -∗ DWP e1 & e2 : I) →
  dwp_rel Σ [e1] [e2] σ1 σ2 L I.
Proof.
  intros Hσ Hdwp.
  exists 0. intros Hinv. simpl.
  pose (σ1' := filter ((.∉ L) ∘ fst) (σ1.(heap))).
  pose (σ2' := filter ((.∉ L) ∘ fst) (σ2.(heap))).
  iMod (gen_heap_init σ1') as (hg1) "[Hh1 _]".
  iMod (allocator_helper _ L with "Hh1") as "[Hh1 HL1]".
  { unfold low_equiv in Hσ; naive_solver. }
  iMod (gen_heap_init σ2') as (hg2) "[Hh2 _]".
  iMod (allocator_helper _ L with "Hh2") as "[Hh2 HL2]".
  { unfold low_equiv in Hσ; naive_solver. }

  iMod (proph_map_init [] σ1.(used_proph_id)) as (pg1) "Hp1".
  iMod (proph_map_init [] σ2.(used_proph_id)) as (pg2) "Hp2".

  iMod (inv_heap_init loc (option val) ⊤) as (ih1) "Hih1".
  iMod (inv_heap_init loc (option val) ⊤) as (ih2) "Hih2".

  pose (Hdheap := (HeapDG Σ Hinv pg1 pg2 hg1 hg2 ih1 ih2)).
  iAssert (|={⊤}=> ([∗ set] l ∈ L, ⟦ tref (tint Low) ⟧ Low #(LitLoc l) #(LitLoc l)))%I
          with "[HL1 HL2]" as "HI".
  { iApply big_sepS_fupd.
    iCombine "HL1 HL2" as "HL".
    rewrite -big_sepS_sep.
    iApply (big_sepS_mono with "HL").
    iIntros (x Hx) "[Hx1 Hx2]".
    destruct (Hσ x Hx) as (n&Hn1&Hn2).
    rewrite (extract_fn_spec _ _ _ Hn1).
    rewrite (extract_fn_spec _ _ _ Hn2).
    iApply (interp_ref_alloc Low x x #n #n (tint Low) with "[$Hx1] [$Hx2] []").
    rewrite interp_eq. iExists n,n; eauto. }
  iMod "HI" as "#HI".
  iModIntro. iExists hg1,hg2,ih1,ih2,pg1,pg2.
  iFrame "Hh1 Hh2 Hp1 Hp2 HI".
  iSplit; last done.
  iApply (Hdwp with "HI").
Qed.

Lemma dwp_lift_bisim_singleton e1 e2 σ1 σ2 (out : loc) (n : Z) Σ `{!invPreG Σ, !heapPreDG Σ} :
  σ1.(heap) !! out = Some (Some #n) →
  σ2.(heap) !! out = Some (Some #n) →
  (∀ `{!heapDG Σ}, ⟦ tref (tint Low) ⟧ Low #out #out -∗ DWP e1 & e2 : I) →
  dwp_rel Σ [e1] [e2] σ1 σ2 {[out]} I.
Proof.
  intros Hσ1 Hσ2 He1e2. apply dwp_lift_bisim.
  - intros l. rewrite elem_of_singleton. naive_solver.
  - intros ?. rewrite /I_L big_sepS_singleton. done.
Qed.

(** The relation has good properties *)
Lemma dwp_rel_sym `{!invPreG Σ, !heapPreDG Σ} es ss σ1 σ2 L Φ :
  (∀ v1 v2, Φ v1 v2 ⊢ Φ v2 v1) →
  dwp_rel Σ es ss σ1 σ2 L Φ →
  dwp_rel Σ ss es σ2 σ1 L Φ.
Proof.
  intros HΦ [n HR].
  exists n. intros Hinv.
  iPoseProof (HR Hinv) as "H".
  iApply (step_fupdN_mono with "H").
  iIntros "H". iMod "H". iModIntro.
  iDestruct "H" as (h1 h2 ih1 ih2 p1 p2) "[Hσ [Hout HDWP]]".
  iExists h2, h1, ih2, ih1, p2, p1.
  rewrite /state_rel /=.
  iDestruct "Hσ" as "($&$&$&$)". clear HR.
  (* first we prove that we can get the symmetric version of the invariant *)
  iSplitL "Hout".
  { rewrite /I_L. iApply (big_sepS_mono with "Hout").
    intros x Hx. rewrite !interp_eq /=.
    iDestruct 1 as (l1 l2 Hl1 Hl2) "H". simplify_eq/=.
    iExists l1, l1. repeat iSplit; eauto.
    iApply (invariants.inv_iff with "H").
    iNext. iModIntro. iSplit.
    - iDestruct 1 as (v1 v2) "(Hl1 & Hl2 & Hv)".
      iExists v2, v1. iFrame. iDestruct "Hv" as (i1 i2 -> ->) "%".
      iExists i2, i1. repeat iSplit; eauto with iFrame.
      iPureIntro. naive_solver.
    - iDestruct 1 as (v1 v2) "(Hl1 & Hl2 & Hv)".
      iExists v2, v1. iFrame. iDestruct "Hv" as (i1 i2 -> ->) "%".
      iExists i2, i1. repeat iSplit; eauto with iFrame.
      iPureIntro. naive_solver. }
  rewrite big_sepL2_flip.
  iApply (big_sepL2_impl with "HDWP []").
  iModIntro. iIntros (k s e Hs He) "HDWP".
  (* now we do Löb induction *)
  (* ugly context manipulations incoming *)
  iAssert (□ ∀ v1 v2 : val, Φ v1 v2 -∗ Φ v2 v1)%I as "#HΦ".
  { iModIntro. iIntros (v1 v2). by iApply HΦ. }
  clear HΦ. iRevert "HΦ". clear Hs He.
  iLöb as "IH" forall (e s k Φ). iIntros "#HΦ".
  rewrite !dwp_unfold /dwp_pre /=.
  destruct (to_val e) as [ev|] eqn:Hev;
    destruct (to_val s) as [sv|] eqn:Hsv; [|done..|].
  { iMod "HDWP" as "H". iModIntro.
    case_match; eauto; by iApply "HΦ". }
  clear σ1 σ2. iIntros (σ1 σ2 κ1 κs1 κ2 κs2) "(Hσ1 & Hp1 & Hσ2 & Hp2)".
  iMod ("HDWP" with "[$Hσ1 $Hp1 $Hσ2 $Hp2]") as "($ & $ & HDWP)".
  iModIntro. iIntros (s' σ1' efs1 e' σ2' efs2 Hst_s Hst_e).
  iMod ("HDWP" with "[//] [//]") as "HDWP". iModIntro. iNext.
  iMod "HDWP" as "(($ & $ & $ & $) & Hdwp & Hefs)". iModIntro.
  iSplitL "Hdwp".
  - by iApply ("IH" with "Hdwp HΦ").
  - rewrite big_sepL2_flip.
    iApply (big_sepL2_impl with "Hefs").
    iModIntro. iIntros (m e1 e2 ??) "Hdwp".
    iApply ("IH" $! _ _ 1 Φ with "Hdwp HΦ").
Qed.
(* Transitivity is still infeasible! *)

Lemma dwp_rel_hd_to_val Σ `{!invPreG Σ, !heapPreDG Σ} e s es ss σ1 σ2 L :
  dwp_rel Σ (e::es) (s::ss) σ1 σ2 L I →
  to_val e = to_val s.
Proof.
  intros [n HR].
  eapply (step_fupdN_soundness'' _ n)=>Hinv.
  iPoseProof (HR Hinv) as "HR".
  iApply (step_fupdN_mono with "HR").
  iIntros "HR".
  iMod "HR" as (h1 h2 ih1 ih2 p1 p2) "[HSR H]".
  rewrite big_sepL2_cons. iDestruct "H" as "(_ & H & _)".
  rewrite decide_True_pi.
  destruct (to_val e) as [v1|] eqn:He, (to_val s) as [v2|] eqn:Hs; try done.
  - rewrite -(of_to_val e v1)// -(of_to_val s v2)//.
    rewrite dwp_value_inv'. iMod "H" as %?. simplify_eq/=.
    done.
  - rewrite !dwp_unfold /dwp_pre /= ?He ?Hs.
    by iMod "H".
  - rewrite !dwp_unfold /dwp_pre /= ?He ?Hs.
    by iMod "H".
Qed.

Lemma dwp_rel_val Σ `{!invPreG Σ, !heapPreDG Σ} (v1 v2 : val) e s σ1 σ2 L :
  dwp_rel Σ (of_val v1::e) (of_val v2::s) σ1 σ2 L I →
  v1 = v2.
Proof.
  intros HR%dwp_rel_hd_to_val. by simplify_eq/=.
Qed.

Lemma dwp_rel_progress Σ `{!invPreG Σ, !heapPreDG Σ} e s σ1 σ2 L :
  dwp_rel Σ e s σ1 σ2 L I →
  low_equiv L σ1 σ2.
Proof.
  intros [n HR] l Hl.
  eapply (step_fupdN_soundness'' _ n)=>Hinv.
  iPoseProof (HR Hinv) as "HR".
  iApply (step_fupdN_mono with "HR").
  iIntros "HR".
  iMod "HR" as (h1 h2 ih1 ih2 p1 p2) "[HSR [Hinv _]]".
  iDestruct "HSR" as "(Hσ1 & _ & Hσ2 & _)".
  rewrite /I_L. rewrite (big_sepS_elem_of _ _ l) //.
  rewrite interp_eq. iDestruct "Hinv" as (o1 o2 ? ?) "#Hinv".
  simplify_eq/=.

  iInv (locsN.@(o1, o1)) as (v1 v2) "(>Ho1 & >Ho2 & >Hv)" "Hcl".

  iDestruct "Hv" as (i1 i2 -> ->) "%".
  assert (i1 = i2) as -> by eauto.
  iDestruct (gen_heap_valid with "Hσ1 Ho1") as %->.
  iDestruct (gen_heap_valid with "Hσ2 Ho2") as %->.

  iMod ("Hcl" with "[-]") as "_".
  { iNext. iExists _,_. iFrame "Ho1 Ho2".
    iExists _,_. eauto with iFrame. }
  iModIntro. iPureIntro. eauto.
Qed.

Lemma dwp_rel_reducible_no_obs Σ `{!invPreG Σ, !heapPreDG Σ} es ss e s i σ1 σ2 L Φ :
  es !! i = Some e →
  ss !! i = Some s →
  language.to_val e = None →
  dwp_rel Σ es ss σ1 σ2 L Φ →
  reducible_no_obs e σ1 ∧ reducible_no_obs s σ2.
Proof.
  intros Hes Hss He [n HR].
  eapply (step_fupdN_soundness''' _ n)=>Hinv.
  iPoseProof (HR Hinv) as "HR".
  iApply (step_fupdN_mono with "HR").
  iIntros "HR".
  iMod "HR" as (h1 h2 ih1 ih2 p1 p2) "[HSR [Hinv H]]".
  rewrite (big_sepL2_lookup _ _ _ i)=>//.
  iEval (rewrite dwp_unfold /dwp_pre He) in "H".
  simpl. destruct (to_val s) as [vs|] eqn:Hs.
  { by iMod "H". }
  iMod ("H" $! _ _ [] [] [] [] with "HSR") as (Hred1 Hred2) "H".
  iModIntro. done.
Qed.

Lemma dwp_rel_tp_length Σ `{!invPreG Σ, !heapPreDG Σ} es ss σ1 σ2 L Φ :
  dwp_rel Σ es ss σ1 σ2 L Φ →
  length es = length ss.
Proof.
  intros [n HR].
  eapply (step_fupdN_soundness'' _ n)=>Hinv.
  iPoseProof (HR Hinv) as "HR".
  iApply (step_fupdN_mono with "HR").
  iIntros "HR".
  iMod "HR" as (h1 h2 ih1 ih2 p1 p2) "[HSR [Hinv H]]".
  rewrite big_sepL2_length. done.
Qed.

Lemma dwp_rel_efs_length Σ `{!invPreG Σ, !heapPreDG Σ} es ss i e s σ1 σ2 e' σ1' efs1 s' σ2' efs2 L Φ :
  es !! i = Some e →
  ss !! i = Some s →
  dwp_rel Σ es ss σ1 σ2 L Φ →
  (prim_step e σ1 [] e' σ1' efs1) →
  (prim_step s σ2 [] s' σ2' efs2) →
  length efs1 = length efs2.
Proof.
  intros Hes Hss [n HR1] Hstep1 Hstep2.
  eapply (step_fupdN_soundness' _ (S n))=>Hinv.
  rewrite Nat_iter_S_r.
  iPoseProof (HR1 Hinv) as "HR".
  iApply (step_fupdN_mono with "HR").
  iIntros "HR".
  iMod "HR" as (h1 h2 ih1 ih2 p1 p2) "[HSR [Hinv H]]".
  rewrite (big_sepL2_lookup _ _ _ i)=>//.
  iEval (rewrite dwp_unfold /dwp_pre) in "H".
  simpl.
  assert (to_val e = None) as ->.
  { eapply val_stuck; eauto. }
  assert (to_val s = None) as ->.
  { eapply val_stuck; eauto. }
  iMod ("H" $! _ _ [] [] [] [] with "HSR") as (Hred1 Hred2) "H".
  iSpecialize ("H" with "[//]").
  iSpecialize ("H" with "[//]"). iMod "H".
  iModIntro. iNext. iMod "H" as "[_ [_ Hefs]]".
  iModIntro.
  iApply (big_sepL2_length with "Hefs").
Qed.

Lemma dwp_rel_step Σ `{!invPreG Σ, !heapPreDG Σ} es ss es' ss' e s σ1 σ2 e' s' σ1' σ2' L Φ :
  length es = length ss →
  dwp_rel Σ (es ++ e::es') (ss ++ s::ss') σ1 σ2 L Φ →
  (prim_step e σ1 [] e' σ1' []) →
  (prim_step s σ2 [] s' σ2' []) →
  dwp_rel Σ (es ++ e'::es') (ss ++ s'::ss') σ1' σ2' L Φ.
Proof.
  intros Hlen [n HR] Hstep1 Hstep2.
  rewrite /dwp_rel. exists (S n). move=>Hinv.
  rewrite Nat_iter_S_r.
  iPoseProof HR as "H".
  iApply (step_fupdN_mono with "H").
  iIntros "H". iMod "H" as (h1 h2 ih1 ih2 p1 p2) "[HI [Hinv HWP]]".
  iExists h1,h2,ih1,ih2,p1,p2.

  rewrite big_sepL2_app_inv; last first.
  { naive_solver. }
  rewrite big_sepL2_cons.
  iDestruct "HWP" as "[H1 [HWP H2]]".
  iEval (rewrite dwp_unfold /dwp_pre) in "HWP".
  assert (language.to_val e = None) as ->.
  { eapply val_stuck. eauto. }
  assert (language.to_val s = None) as ->.
  { eapply val_stuck. eauto. }
  iSpecialize ("HWP" $! _ _ [] [] [] [] with "HI").
  iMod "HWP" as (_ _) "HWP".
  iSpecialize ("HWP" with "[//]").
  iSpecialize ("HWP" with "[//]").
  iMod "HWP" as "HWP". iModIntro. iNext.
  iMod "HWP" as "(HI & HWP & _)". iModIntro. iModIntro. by iFrame.
Qed.

Lemma dwp_rel_simul Σ `{!invPreG Σ, !heapPreDG Σ} es ss es' ss' e s σ1 σ2 e' σ1' efs L Φ :
  length es = length ss →
  dwp_rel Σ (es++e::es') (ss++s::ss') σ1 σ2 L Φ →
  (prim_step e σ1 [] e' σ1' efs) →
  ∃ s' σ2' sfs,
    prim_step s σ2 [] s' σ2' sfs ∧
    dwp_rel Σ (es++(e'::es')++efs) (ss++(s'::ss')++sfs) σ1' σ2' L Φ.
Proof.
  intros Hlen HR Hstep1.
  assert (to_val e = None) as Hnon. { by eapply val_stuck. }
  assert ((es++e::es') !! length es = Some e) as Hi1.
  { by apply list_lookup_middle. }
  assert ((ss++s::ss') !! length es = Some s) as Hi2.
  { by apply list_lookup_middle. }
  destruct (dwp_rel_reducible_no_obs Σ _ _ e s _ σ1 σ2 _ Φ Hi1 Hi2 Hnon HR) as [Hred1 Hred2].
  destruct Hred2 as (s'&σ2'&efs2&Hstep2).
  destruct HR as [n HR].
  exists s', σ2', efs2. split; auto.
  rewrite /dwp_rel. exists (S n). move=>Hinv.
  rewrite Nat_iter_S_r.
  iPoseProof HR as "H".
  iApply (step_fupdN_mono with "H").
  iIntros "H". iMod "H" as (h1 h2 ih1 ih2 p1 p2) "[HI [Hinv HWP]]".
  iExists h1,h2,ih1,ih2,p1,p2.

  rewrite big_sepL2_app_inv; last naive_solver.
  rewrite big_sepL2_cons.
  iDestruct "HWP" as "[H1 [HWP H2]]".
  rewrite (dwp_unfold _ e s) /dwp_pre.
  assert (language.to_val e = None) as ->.
  { by simpl. }
  destruct (language.to_val s) as [sv|] eqn:Hsv.
  { by iMod "HWP". }
  iSpecialize ("HWP" $! _ _ [] [] [] [] with "HI").
  iMod "HWP" as (_ _) "HWP".
  iSpecialize ("HWP" with "[//]").
  iSpecialize ("HWP" with "[//]").
  iMod "HWP" as "HWP". iModIntro. iNext.
  iMod "HWP" as "(HI & HWP & Hefs)". iModIntro. iModIntro.
  iFrame "Hinv HI".
  iApply (big_sepL2_app with "H1").
  iApply (big_sepL2_app with "[HWP H2] [Hefs]").
  - iFrame "HWP".
    iApply (big_sepL2_mono with "H2").
    intros; simpl. apply dwp_mono=> v1 v2.
    rewrite -plus_n_Sm. naive_solver.
  - iApply (big_sepL2_mono with "Hefs").
    intros; simpl. apply dwp_mono=> v1 v2.
    rewrite - !plus_n_Sm. naive_solver.
Qed.

(* A helper lemma.
   TODO: Move it out to a different module *)
Lemma list_decompose {A:Type} (es1 : list A) e (es2 : list A) (ss : list A) :
  length (es1++e::es2) = length ss →
  ∃ ss1 s ss2, length es1 = length ss1 ∧ ss = ss1 ++ s::ss2.
Proof.
  intros Hlen.
  assert (length es1 < length ss) as Hlen2.
  { revert Hlen. rewrite app_length /=. lia. }
  destruct (@nth_split _ (length es1) ss e Hlen2) as (ss1 & ss2 & -> & Hlen3).
  exists ss1, (nth (length es1) ss e), ss2. eauto.
Qed.

(* A slightly different version of [dwp_rel_simul] *)
Lemma dwp_rel_simul' Σ `{!invPreG Σ, !heapPreDG Σ} es1 (e : expr) es2 ss σ1 σ2 L Φ :
  dwp_rel Σ (es1++e::es2) ss σ1 σ2 L Φ →
  ∃ ss1 s ss2, length es1 = length ss1 ∧ ss = ss1++s::ss2 ∧
    ∀ e' σ1' es',
      (prim_step e σ1 [] e' σ1' es') →
      ∃ s' σ2' ss',
      prim_step s σ2 [] s' σ2' ss' ∧
      dwp_rel Σ (es1++(e'::es2)++es') (ss1++(s'::ss2)++ss') σ1' σ2' L Φ.
Proof.
  intros HR.
  assert (length (es1 ++ e :: es2) = length ss) as Htmplen.
  { eapply dwp_rel_tp_length, HR. }
  destruct (list_decompose es1 e es2 ss Htmplen) as (ss1&s&ss2&Hlen1&->).
  do 3 eexists. repeat (split ; first done).
  intros e' σ1' efs Hstep. eapply dwp_rel_simul; eauto.
Qed.


(** Putting everything together *)

Definition R_pre Σ `{!invPreG Σ, !heapPreDG Σ} L x1 x2 : Prop :=
  match x1,x2 with
  | (es, σ1), (ss, σ2) => dwp_rel Σ es ss σ1 σ2 L I
  end.

Definition R Σ `{!invPreG Σ, !heapPreDG Σ} L : relation (list expr*state)
  := tc (R_pre Σ L).

(** A strong low-bisimulation *)
Definition strong_bisim (L : gset loc)
  (R : (list expr*state) → (list expr*state) → Prop) : Prop :=
  (** - is a PER *)
  transitive _ R ∧ symmetric _ R ∧
  (** - on the threadpools of equal size *)
  (∀ es σ1 ss σ2, R (es, σ1) (ss, σ2) → length es = length ss) ∧
  (** - final values are observable *)
  (∀ v1 v2 es σ1 ss σ2, R (of_val v1::es, σ1) (of_val v2::ss, σ2) → v1 = v2) ∧
  (** - untrusted sinks are observable *)
  (∀ es σ1 ss σ2, R (es, σ1) (ss, σ2) → low_equiv L σ1 σ2) ∧
  (** - the bisimulation condition *)
  (∀ es1 e es2 σ1 ss1 s ss2 σ2,
      length es1 = length ss1 →
      R (es1++e::es2, σ1) (ss1++s::ss2, σ2) →
      ∀ e' σ1' es', prim_step e σ1 [] e' σ1' es' →
        ∃ s' ss' σ2', prim_step s σ2 [] s' σ2' ss' ∧
        R (es1++(e'::es2)++es', σ1') (ss1++(s'::ss2)++ss', σ2')).


Theorem R_strong_bisim Σ L `{!invPreG Σ, !heapPreDG Σ} : strong_bisim L (R Σ L).
Proof.
  unfold R. repeat split.
  - unfold transitive. apply tc_transitive.
  - apply tc_symmetric. intros [es σ1] [ss σ2].
    unfold R_pre. apply dwp_rel_sym. eauto.
  - intros es σ1 ss σ2 Htc.
    (* We generalize the goal slightly so that the induction works out.
     We use the same trick in all the cases below. *)
    pose (f := λ (x y : list expr*state), length x.1 = length y.1).
    enough (f (es, σ1) (ss, σ2)); first by eauto.
    enough (tc f (es, σ1) (ss, σ2)).
    { apply transitive_tc_id; eauto.
      intros [x ?] [y ?] [z ?]; unfold f=>/= -> -> //. }
    eapply (tc_subrel (R_pre Σ L)); last done.
    clear. rewrite /f /R_pre=> [[es σ1] [ss σ2]] /=.
    (* Just lifting the property *)
    apply dwp_rel_tp_length.
  - intros v1 v2 es σ1 ss σ2 Htc.
    pose (f := λ (x y : list expr*state),
               to_val <$> hd_error x.1 = to_val <$> hd_error y.1).
    cut (f (of_val v1 :: es, σ1) (of_val v2 :: ss, σ2)).
    { rewrite /f /=; naive_solver.  }
    enough (tc f (of_val v1 :: es, σ1) (of_val v2 :: ss, σ2)).
    { apply transitive_tc_id; eauto.
      intros [x ?] [y ?] [z ?]; unfold f=>/= -> -> //. }
    eapply (tc_subrel (R_pre Σ L)); last done.
    clear. rewrite /f /R_pre=> [[es σ1] [ss σ2]] /=.
    (* Just lifting the property *)
    destruct es as [|e es], ss as [|s ss];
      first [ intros ?%dwp_rel_tp_length; naive_solver
            | simpl; eauto ].
    by intros ->%dwp_rel_hd_to_val.
  - intros es σ1 ss σ2 Htc.
    pose (f := λ (x y : list expr*state), low_equiv L x.2 y.2).
    enough (f (es, σ1) (ss, σ2)); first done.
    enough (tc f (es, σ1) (ss, σ2)).
    { apply transitive_tc_id; eauto.
      intros [? x] [? y] [? z]; apply low_equiv_transitive. }
    eapply (tc_subrel (R_pre Σ L)); last done.
    clear. rewrite /f /R_pre=> [[es σ1] [ss σ2]] /=.
    (* Just lifting the property *)
    apply dwp_rel_progress.
  - intros es1 e es2 σ1 ss1 s ss2 σ2 Hlen Htc.
    (* Here we need a stronger statement to get the IH right. *)
    pose (f :=  λ (x y : list expr*state),
            let '(es, σ1) := x in
            let '(ss, σ2) := y in
            ∀ es1 e es2, es = es1 ++ e::es2 →
            ∃ ss1 s ss2, length es1 = length ss1 ∧ ss = ss1 ++ s::ss2 ∧
            ∀ e' σ1' es', prim_step e σ1 [] e' σ1' es' →
              ∃ s' ss' σ2', prim_step s σ2 [] s' σ2' ss' ∧
              tc (R_pre Σ L) (es1 ++ (e' :: es2) ++ es', σ1') (ss1 ++ (s' :: ss2) ++ ss', σ2')).
    enough (f (es1 ++ e :: es2, σ1) (ss1 ++ s :: ss2, σ2)) as Hf.
    { specialize (Hf es1 e es2 eq_refl).
      destruct Hf as (ss1' & s' & ss2' & Hlen2 & Heqss & Hf).
      simplify_list_eq. apply Hf. }
    revert Htc.
    generalize (es1 ++ e :: es2, σ1) as x.
    generalize (ss1 ++ s :: ss2, σ2) as y.
    intros x y. clear Hlen σ1 σ2 es1 es2 e ss1 s ss2.
    (* Here we do the induction directly, as it is perhaps easier *)
    induction 1 as [x y H|x y z H1 H2 IH]; destruct x as [es σ1], y as [ss σ2].
    + unfold f. unfold R_pre in H.
      intros es1 e es2 ->.
      destruct (dwp_rel_simul' _ es1 e es2 ss σ1 σ2 L _ H)
               as (ss1 & s & ss2 & Hlen & -> & HR).
      do 3 eexists. repeat (split; first done).
      intros e' σ1' es' Hstep1.
      destruct (HR e' σ1' es' Hstep1) as (s' & σ2' & sfs & Hstep2 & HR').
      do 3 eexists. split; first done. econstructor; eauto.
    + destruct z as (ts, σ3).
      intros es1 e es2 ->.
      destruct (dwp_rel_simul' _ es1 e es2 ss σ1 σ2 L _ H1)
               as (ss1 & s & ss2 & Hlen & -> & HR).
      specialize (IH ss1 s ss2 eq_refl).
      destruct IH as (ts1 & t & ts2 & Hlen2 & -> & IH).
      exists ts1,t,ts2. repeat split; eauto.
      { by rewrite Hlen. }
      intros e' σ1' es' Hstep1.
      destruct (HR e' σ1' es' Hstep1) as (s' & σ2' & ss' & Hstep2 & HR2).
      destruct (IH s' σ2' ss' Hstep2) as (t' & σ3' & ts' & Hstep3 & IH3).
      exists t', σ3', ts'. split; eauto.
      rewrite /R_pre. eapply tc_l; eauto; simpl; eauto.
Qed.
