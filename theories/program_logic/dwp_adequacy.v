From stdpp Require Import namespaces.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation lifting proofmode. (* for the example *)
From iris_ni.program_logic Require Export dwp lifting heap_lang_lifting.
From iris_ni.logrel Require Export types interp.
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

(* TODO: move to iris *)

Local Open Scope nat.

Implicit Types L : gset loc.
Implicit Types l : loc.

Definition I_L (L : gset loc) `{!heapDG Σ} :=
  ([∗ set] l ∈ L, ⟦ tref (tint Low) ⟧ Low #(LitLoc l) #l)%I.

(** Now the relation *)
Definition dwp_rel Σ `{!invPreG Σ, !heapPreDG Σ}
  (es ss : list expr)
  (σ1 σ2 : state) (L : gset loc) (Φ : val → val → iProp Σ) :=
  ∃ n, ∀ `{Hinv : !invG Σ},
      (Nat.iter n mega_future
         (|={⊤}=> ∃ (h1 h2 : gen_heapG loc val Σ)
                   (p1 p2 : proph_mapG proph_id (val*val) Σ),
            let _ := HeapDG _ _ p1 p2 h1 h2 in
            state_rel σ1 σ2 [] [] ∗
            I_L L ∗
            [∗ list] k↦e;s ∈ es;ss,
                dwp ⊤ e s (if decide (k = O) then Φ else (λ _ _, True))))%I.

Definition I {Σ} (v1 v2 : val) : iProp Σ := ⌜v1 = v2⌝%I.

Lemma allocator_helper σ L `{!invG Σ, !gen_heapG loc val Σ} :
  (∀ l, l ∈ L → σ !! l = Some #0) →
  let σ' := filter ((∉ L) ∘ fst) σ in
  gen_heap_ctx σ' ==∗ gen_heap_ctx σ ∗ [∗ set] l ∈ L, l ↦ #0.
Proof.
  iIntros (HL) "Hσ'".
  iMod (gen_heap_alloc_gen with "Hσ'") as "(Hσ & HL)".
  { apply map_disjoint_filter. }
  iDestruct "HL" as "[HL _]".
  rewrite map_union_filter. iFrame "Hσ".
  iAssert ([∗ map] l↦_ ∈ (filter (λ x, x.1 ∈ L) σ), l ↦ #0)%I with "[HL]" as "HL".
  { iApply (big_sepM_mono with "HL").
    intros l v. rewrite map_filter_lookup_Some=> [[Hlσ HlL]].
    assert (v = #0) as -> by naive_solver. eauto. }
  rewrite big_sepM_dom.
  rewrite (dom_map_filter_L (λ x, x.1 ∈ L) σ L); first done.
  intros i. naive_solver.
Qed.

(** Lifting DWP proofs *)
Lemma dwp_lift_bisim e1 e2 σ1 σ2 L Σ `{!invPreG Σ, !heapPreDG Σ} :
  (∀ l, l ∈ L → σ1.(heap) !! l = Some #0 ∧ σ2.(heap) !! l = Some #0) →
  (∀ `{!heapDG Σ}, I_L L -∗ DWP e1 & e2 : I) →
  dwp_rel Σ [e1] [e2] σ1 σ2 L I.
Proof.
  intros Hσ Hdwp.
  exists 0. intros Hinv. simpl.
  pose (σ1' := filter ((∉ L) ∘ fst) (σ1.(heap))).
  pose (σ2' := filter ((∉ L) ∘ fst) (σ2.(heap))).
  iMod (gen_heap_init σ1') as (hg1) "Hh1".
  iMod (allocator_helper σ1.(heap) L with "Hh1") as "[Hh1 HL1]".
  { naive_solver. }
  iMod (gen_heap_init σ2') as (hg2) "Hh2".
  iMod (allocator_helper σ2.(heap) L with "Hh2") as "[Hh2 HL2]".
  { naive_solver. }

  iMod (proph_map_init [] σ1.(used_proph_id)) as (pg1) "Hp1".
  iMod (proph_map_init [] σ2.(used_proph_id)) as (pg2) "Hp2".

  pose (Hdheap := (HeapDG Σ Hinv pg1 pg2 hg1 hg2)).

  iAssert (|={⊤}=> ([∗ set] l ∈ L, ⟦ tref (tint Low) ⟧ Low #(LitLoc l) #l))%I
          with "[HL1 HL2]" as "HI".
  { iApply big_sepS_fupd.
    iCombine "HL1 HL2" as "HL".
    rewrite -big_sepS_sep.
    iApply (big_sepS_mono with "HL").
    iIntros (x Hx) "[Hx1 Hx2]".
    iApply (interp_ref_alloc Low x x #0 #0 (tint Low) with "Hx1 Hx2 []").
    rewrite interp_eq. iExists 0,0; eauto. }
  iMod "HI" as "#HI".
  iModIntro. iExists hg1,hg2,pg1,pg2.
  iFrame "Hh1 Hh2 Hp1 Hp2 HI".
  iSplit; last done.
  iApply (Hdwp with "HI").
Qed.

Lemma dwp_lift_bisim_singleton e1 e2 σ1 σ2 (out : loc) Σ `{!invPreG Σ, !heapPreDG Σ} :
  σ1.(heap) !! out = Some #0 →
  σ2.(heap) !! out = Some #0 →
  (∀ `{!heapDG Σ}, ⟦ tref (tint Low) ⟧ Low #out #out -∗ DWP e1 & e2 : I) →
  dwp_rel Σ [e1] [e2] σ1 σ2 {[out]} I.
Proof.
  intros Hσ1 Hσ2 He1e2. apply dwp_lift_bisim.
  - intros l. rewrite elem_of_singleton. naive_solver.
  - intros ?. rewrite /I_L big_sepS_singleton. done.
Qed.

(** The relation has good properties *)
(* NB: the out channel has to be the same location! *)
Lemma dwp_rel_sym `{!invPreG Σ, !heapPreDG Σ} es ss σ1 σ2 L Φ :
  (∀ v1 v2, Φ v1 v2 ⊢ Φ v2 v1) →
  dwp_rel Σ es ss σ1 σ2 L Φ →
  dwp_rel Σ ss es σ2 σ1 L Φ.
Proof.
  intros HΦ [n HR].
  exists n. intros Hinv.
  iPoseProof (HR Hinv) as "H".
  iApply (mega_futureN_mono with "H").
  iIntros "H". iMod "H". iModIntro.
  iDestruct "H" as (h1 h2 p1 p2) "[Hσ [Hout HDWP]]".
  iExists h2, h1, p2, p1.
  rewrite /state_rel /=.
  iDestruct "Hσ" as "($&$&$&$)". clear HR.
  (* first we prove that we can get the symmetric version of the invariant *)
  iSplitL "Hout".
  { rewrite /I_L. iApply (big_sepS_mono with "Hout").
    intros x Hx. rewrite !interp_eq /=.
    iDestruct 1 as (l1 l2 Hl1 Hl2) "H". simplify_eq/=.
    iExists l1, l1. repeat iSplit; eauto.
    iApply (invariants.inv_iff with "[] H").
    iNext. iAlways. iSplit.
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
  iAlways. iIntros (k s e Hs He) "HDWP".
  (* now we do Löb induction *)
  (* ugly context manipulations incoming *)
  iAssert (□ ∀ v1 v2 : val, Φ v1 v2 -∗ Φ v2 v1)%I as "#HΦ".
  { iAlways. iIntros (v1 v2). by iApply HΦ. }
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
  iMod "HDWP" as "HDWP". iModIntro. iNext.
  iMod "HDWP" as "(($ & $ & $ & $) & Hdwp & Hefs)". iModIntro.
  iSplitL "Hdwp".
  - by iApply ("IH" with "Hdwp HΦ").
  - rewrite big_sepL2_flip.
    iApply (big_sepL2_impl with "Hefs").
    iAlways. iIntros (m e1 e2 ??) "Hdwp".
    iApply ("IH" $! _ _ 1 Φ with "Hdwp HΦ").
Qed.

(* Transitivity is still infeasible! *)

Lemma dwp_rel_val Σ `{!invPreG Σ, !heapPreDG Σ} (v1 v2 : val) e s σ1 σ2 L :
  dwp_rel Σ (of_val v1::e) (of_val v2::s) σ1 σ2 L I →
  v1 = v2.
Proof.
  intros [n HR].
  eapply (mega_futureN_soundness n)=>Hinv.
  iPoseProof (HR Hinv) as "HR".
  iApply (mega_futureN_mono with "HR").
  iIntros "HR".
  iMod "HR" as (h1 h2 p1 p2) "[HSR H]".
  rewrite big_sepL2_cons. iDestruct "H" as "(_ & H & _)".
  rewrite dwp_value_inv'. done.
Qed.

Lemma dwp_rel_progress Σ `{!invPreG Σ, !heapPreDG Σ} e s σ1 σ2 L :
  dwp_rel Σ e s σ1 σ2 L I →
  ∀ l, l ∈ L → σ1.(heap) !! l = σ2.(heap) !! l.
Proof.
  intros [n HR] l Hl.
  eapply (mega_futureN_soundness n)=>Hinv.
  iPoseProof (HR Hinv) as "HR".
  iApply (mega_futureN_mono with "HR").
  iIntros "HR".
  iMod "HR" as (h1 h2 p1 p2) "[HSR [Hinv _]]".
  iDestruct "HSR" as "(Hσ1 & _ & Hσ2 & _)".
  rewrite /I_L. rewrite (big_sepS_elem_of _ _ l) //.
  rewrite interp_eq. iDestruct "Hinv" as (o1 o2 ? ?) "#Hinv".
  simplify_eq/=.
  iApply fupd_plain_mask.
  iInv (locsN.@(o1, o1)) as (v1 v2) "(>Ho1 & >Ho2 & >Hv)" "_".
  iModIntro.
  iDestruct "Hv" as (i1 i2 -> ->) "%".
  assert (i1 = i2) as -> by eauto.
  iDestruct (gen_heap_valid with "Hσ1 Ho1") as %->.
  iDestruct (gen_heap_valid with "Hσ2 Ho2") as %->.
  done.
Qed.

Lemma dwp_rel_reducible_no_obs Σ `{!invPreG Σ, !heapPreDG Σ} es ss e s i σ1 σ2 L Φ :
  es !! i = Some e →
  ss !! i = Some s →
  language.to_val e = None →
  dwp_rel Σ es ss σ1 σ2 L Φ →
  reducible_no_obs e σ1 ∧ reducible_no_obs s σ2.
Proof.
  intros Hes Hss He [n HR].
  eapply (mega_futureN_soundness n)=>Hinv.
  iPoseProof (HR Hinv) as "HR".
  iApply (mega_futureN_mono with "HR").
  iIntros "HR". iApply fupd_plain_mask_empty.
  iMod "HR" as (h1 h2 p1 p2) "[HSR [Hinv H]]".
  rewrite (big_sepL2_lookup _ _ _ i)=>//.
  iEval (rewrite dwp_unfold /dwp_pre He) in "H".
  simpl. destruct (to_val s) as [vs|] eqn:Hs.
  { by iMod "H". }
  iMod ("H" $! _ _ [] [] [] [] with "HSR") as (Hred1 Hred2) "H".
  iModIntro. done.
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
  eapply (mega_futureN_soundness (S n))=>Hinv.
  iPoseProof (HR1 Hinv) as "HR".
  rewrite Nat_iter_S_r.
  iApply (mega_futureN_mono with "HR").
  iIntros "HR".
  iMod "HR" as (h1 h2 p1 p2) "[HSR [Hinv H]]".
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
  iModIntro. iModIntro. iNext. iMod "H" as "H".
  iModIntro. iNext. iMod "H" as "[_ [_ Hefs]]".
  iModIntro. iModIntro. iApply (big_sepL2_length with "Hefs").
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
  iApply (mega_futureN_mono with "H").
  rewrite /mega_future /=.
  iIntros "H". iMod "H" as (h1 h2 p1 p2) "[HI [Hinv HWP]]".
  iExists h1,h2,p1,p2.

  rewrite big_sepL2_app_inv=>//. rewrite big_sepL2_cons.
  iDestruct "HWP" as "[H1 [HWP H2]]".
  iEval (rewrite dwp_unfold /dwp_pre) in "HWP".
  assert (language.to_val e = None) as ->.
  { eapply val_stuck. eauto. }
  assert (language.to_val s = None) as ->.
  { eapply val_stuck. eauto. }
  iSpecialize ("HWP" $! _ _ [] [] [] [] with "HI").
  iMod "HWP" as (_ _) "HWP". iModIntro.
  iSpecialize ("HWP" with "[//]").
  iSpecialize ("HWP" with "[//]").
  iMod "HWP" as "HWP". iModIntro. iNext.
  iMod "HWP" as "HWP". iModIntro. iNext.
  iMod "HWP" as "(HI & HWP & _)". iModIntro. iModIntro. by iFrame.
Qed.

Lemma dwp_rel_simul Σ `{!invPreG Σ, !heapPreDG Σ} es ss es' ss' e s σ1 σ2 e' σ1' efs L Φ :
  length es = length ss →
  dwp_rel Σ (es++e::es') (ss++s::ss') σ1 σ2 L Φ →
  (prim_step e σ1 [] e' σ1' efs) →
  ∃ s' σ2' κ2 sfs,
    prim_step s σ2 κ2 s' σ2' sfs ∧
    dwp_rel Σ (es++(e'::efs)++es') (ss++(s'::sfs)++ss') σ1' σ2' L Φ.
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
  exists s', σ2', [], efs2. split; auto.
  rewrite /dwp_rel. exists (S n). move=>Hinv.
  rewrite Nat_iter_S_r.
  iPoseProof HR as "H".
  iApply (mega_futureN_mono with "H").
  rewrite /mega_future /=.
  iIntros "H". iMod "H" as (h1 h2 p1 p2) "[HI [Hinv HWP]]".
  iExists h1,h2,p1,p2.

  rewrite big_sepL2_app_inv=>//. rewrite big_sepL2_cons.
  iDestruct "HWP" as "[H1 [HWP H2]]".
  rewrite (dwp_unfold _ e s) /dwp_pre.
  assert (language.to_val e = None) as ->.
  { by simpl. }
  destruct (language.to_val s) as [sv|] eqn:Hsv.
  { by iMod "HWP". }
  iSpecialize ("HWP" $! _ _ [] [] [] [] with "HI").
  iMod "HWP" as (_ _) "HWP". iModIntro.
  iSpecialize ("HWP" with "[//]").
  iSpecialize ("HWP" with "[//]").
  iMod "HWP" as "HWP". iModIntro. iNext.
  iMod "HWP" as "HWP". iModIntro. iNext.
  iMod "HWP" as "(HI & HWP & Hefs)". iModIntro. iModIntro. iFrame.
  iApply (big_sepL2_app with "[Hefs] [H2]").
  - iApply (big_sepL2_mono with "Hefs").
    intros; simpl. apply dwp_mono=> v1 v2.
    rewrite -plus_n_Sm. naive_solver.
  - iApply (big_sepL2_mono with "H2").
    intros; simpl. apply dwp_mono=> v1 v2.
    rewrite - !plus_n_Sm. naive_solver.
Qed.
