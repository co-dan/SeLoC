From stdpp Require Import namespaces.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation lifting proofmode. (* for the example *)
(* From iris_ni.program_logic Require Import lifting heap_lang_lifting. *)
Import uPred.

From iris.heap_lang Require Import adequacy.

(** Warmup : from WP to a relation that is closed under steps *)
Definition wp_r Σ `{!heapPreG Σ}
  (e : expr) (σ : state) (Φ : val → iProp Σ) : Prop :=
  (∃ (n: nat), ∀ `{invG Σ},
   (|={⊤,∅}▷=>^n |={⊤}=> ∃ (hg : gen_heapG loc val Σ)
        (pg : proph_mapG proph_id val Σ),
        let _ := HeapG Σ _ hg pg in
        state_interp σ [] 0%nat ∗
        WP e {{ Φ }})%I).

Lemma test Σ `{!heapPreG Σ} σ :
  wp_r Σ (let: "x" := ref #0 in !"x")%E σ (λ v, ⌜v = #0⌝)%I.
Proof.
  exists 0%nat. intros Hinv. simpl.
  iMod (gen_heap_init σ.(heap)) as (hg) "Hh".
  iMod (proph_map_init [] σ.(used_proph_id)) as (pg) "Hp".
  iModIntro. iExists hg,pg. iFrame.
  wp_alloc l as "Hl". wp_pures. wp_load. done.
Qed.

Lemma step_fupdN_soundness'' `{!invPreG Σ} φ n :
  (∀ `{Hinv: !invG Σ}, (|={⊤,∅}▷=>^n |={⊤}=> ⌜ φ ⌝ : iProp Σ)%I) →
  φ.
Proof.
  intros Hiter.
  apply (soundness (M:=iResUR Σ) _  (S (S n))); simpl.
  apply (fupd_plain_soundness ⊤ _)=> Hinv.
  iPoseProof (Hiter Hinv) as "H". clear Hiter.
  destruct n as [|n].
  - iMod "H" as %?; auto.
  - rewrite -step_fupdN_S_fupd.
    iMod (step_fupdN_plain with "H") as "Hφ". iModIntro. iNext.
    rewrite -later_laterN laterN_later.
    iNext. by iMod "Hφ".
Qed.


Lemma wp_r_value Σ `{!heapPreG Σ} (v : val) σ Φ (φ : val → Prop) :
  wp_r Σ (of_val v) σ Φ →
  (∀ v, Φ v -∗ ⌜φ v⌝) →
  φ v.
Proof.
  intros [n HR] Hφ.
  apply (step_fupdN_soundness'' _ n)=>Hinv.
  iPoseProof (HR Hinv) as "H".
  iApply (step_fupdN_mono with "H").
  iIntros "H". iMod "H" as (hg pg) "[HI HWP]".
  by rewrite wp_value_inv Hφ.
Qed.

Lemma wp_r_step Σ `{!heapPreG Σ} e e' σ σ' Φ :
  wp_r Σ e σ Φ →
  (prim_step e σ [] e' σ' []) →
  wp_r Σ e' σ' Φ.
Proof.
  intros [n HR] Hstep1.
  rewrite /wp_r. exists (S n). move=>Hinv.
  rewrite Nat_iter_S_r.
  iPoseProof HR as "H".
  iApply (step_fupdN_mono with "H").
  iIntros "H". iMod "H" as (hg pg) "[HI HWP]".
  iExists hg,pg. rewrite (wp_unfold _ _ e) /wp_pre.
  assert (language.to_val e = None) as ->.
  { eapply val_stuck; eassumption. }
  iSpecialize ("HWP" $! σ [] [] 0%nat with "HI").
  iMod "HWP" as (?) "HWP".
  iSpecialize ("HWP" $! e' σ' [] with "[//]").
  rewrite big_sepL_nil. cbn[length plus].
  iMod "HWP" as "HWP". iModIntro. iNext.
  iMod "HWP" as "[$ [$ _]]". do 2 iModIntro. done.
Qed.

Lemma wp_r_reducible Σ `{!heapPreG Σ} e σ Φ :
  to_val e = None →
  wp_r Σ e σ Φ →
  reducible e σ.
Proof.
  intros He [n HR].
  eapply (step_fupdN_soundness _ n)=>Hinv.
  iPoseProof (HR Hinv) as "HR".
  iApply (step_fupdN_mono with "HR").
  iIntros "H". iMod "H" as (? ?) "[HI H]".
  rewrite wp_unfold /wp_pre /= He.
  iSpecialize ("H" $! σ [] [] 0%nat with "HI").
  iMod "H" as (Hred) "H". by iModIntro.
Qed.

(** Now we define a simulation from a DWP *)
Class heapPreDG Σ := HeapPreDG {
  heapPreDG_proph_mapG1 :> proph_mapPreG proph_id val Σ;
  heapPreDG_proph_mapG2 :> proph_mapPreG proph_id val Σ;
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
  apply (fupd_plain_soundness ⊤ _)=> Hinv.
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
  apply (fupd_plain_soundness ⊤ _)=> Hinv.
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
  (e1 e2 : expr)
  (σ1 σ2 : state) (Φ : val → val → iProp Σ) :=
  ∃ n, ∀ `{Hinv : !invG Σ},
      (Nat.iter n mega_future
         (|={⊤}=> ∃ (h1 h2 : gen_heapG loc val Σ)
                   (p1 p2 : proph_mapG proph_id val Σ),
            let _ := HeapDG _ _ p1 p2 h1 h2 in
            state_rel σ1 σ2 [] [] ∗
            dwp ⊤ e1 e2 Φ))%I.

Definition I {Σ} (v1 v2 : val) : iProp Σ := ⌜v1 = v2⌝%I.


(** Example program that satisfies the relation *)
Definition e_test := (let: "x" := ref #0 in !"x")%E.
Lemma dwp_e_test `{heapDG Σ} :
  dwp ⊤ e_test e_test I.
Proof.
  iApply (dwp_bind (fill [AppRCtx _]) (fill [AppRCtx _])). simpl.
  iApply dwp_atomic_lift_wp; try done.
  iModIntro.
  iApply wp_alloc=>//.
  iNext. iIntros (x1) "Hx1".
  iApply wp_alloc=>//.
  iNext. iIntros (x2) "Hx2".
  iModIntro.
  iApply dwp_pure_step_later.
  { eapply (pure_exec_ctx (fill [AppLCtx _])). apply _. }
  { eapply (pure_exec_ctx (fill [AppLCtx _])). apply _. }
  done. done. iNext.
  iApply dwp_pure_step_later=>// /=. iNext.
  iApply (dwp_load with "Hx1 Hx2"). iNext. eauto.
Qed.
Lemma dwp_rel_e_test σ1 σ2 Σ `{!invPreG Σ, !heapPreDG Σ} :
  dwp_rel Σ e_test e_test σ1 σ2 I.
Proof.
  exists 0%nat. intros Hinv. simpl.
  iMod (gen_heap_init σ1.(heap)) as (hg1) "Hh1".
  iMod (gen_heap_init σ2.(heap)) as (hg2) "Hh2".
  iMod (proph_map_init [] σ1.(used_proph_id)) as (pg1) "Hp1".
  iMod (proph_map_init [] σ2.(used_proph_id)) as (pg2) "Hp2".
  iModIntro. iExists hg1,hg2,pg1,pg2. iFrame.
  pose (Hdheap := (HeapDG Σ Hinv pg1 pg2 hg1 hg2)).
  iApply dwp_e_test.
Qed.

(** The relation has good properties *)
Lemma dwp_brel_val Σ `{!invPreG Σ, !heapPreDG Σ} (v1 v2 : val) σ1 σ2 :
  dwp_rel Σ (of_val v1) (of_val v2) σ1 σ2 I →
  v1 = v2.
Proof.
  intros [n HR].
  eapply (mega_futureN_soundness n)=>Hinv.
  iPoseProof (HR Hinv) as "HR".
  iApply (mega_futureN_mono with "HR").
  iIntros "HR".
  iMod "HR" as (h1 h2 p1 p2) "[HSR H]".
  rewrite dwp_value_inv'. done.
Qed.

Lemma dwp_rel_step Σ `{!invPreG Σ, !heapPreDG Σ} e s σ1 σ2 e' σ1' Φ :
  dwp_rel Σ e s σ1 σ2 Φ →
  (prim_step e σ1 [] e' σ1' []) →
  ∃ s' σ2',
    prim_step s σ2 [] s' σ2' [] ∧
    dwp_rel Σ e' s' σ1' σ2' Φ.
Proof.
  intros [n HR] Hstep1.
  apply (mega_futureN_soundness (S n))=>Hinv.
  rewrite Nat_iter_S_r.
  iPoseProof (HR Hinv) as "H".
  iApply (mega_futureN_mono with "H").
  iIntros "H". iMod "H" as (h1 h2 p1 p2) "[HI H]".
  rewrite dwp_unfold /dwp_pre.
  rewrite (val_stuck _ _ _ _ _ _ Hstep1) /=.
  iSpecialize ("H" $! σ1 σ2 [] [] [] with "HI").
  iMod "H" as (Hred) "H".
  iSpecialize ("H" $! e' σ1' [] with "[//]").
  iMod "H" as "H". iModIntro. iModIntro. iNext.
  iMod "H" as "H". iModIntro. iNext.
  iMod "H" as "H". iModIntro.
  iDestruct "H" as (κ2 κs2' s' σ2' efs' Hκs Hstep2) "[HSR [Hdwp Hefs]]".
  iExists 

  cut (∀ (Hinv : invG Σ),
   (Nat.iter (S n) mega_future True)%I).
  cut (True ⊢ ∀ (Hinv : invG Σ),

    (|={⊤,∅}=> |={∅,∅}=> ▷ |={∅,∅}=> ▷ |={∅,⊤}=>
     |={⊤,∅}=> |={∅,∅}=> ▷ |={∅,∅}=> ▷ |={∅,⊤}=>
   ∃ s' σ2',
    ⌜prim_step s σ2 [] s' σ2' []⌝ ∧
    ∃ (h1 h2 : gen_heapG loc val Σ)
      (p1 p2 : proph_mapG proph_id val Σ),
         let _ := HeapDG _ _ p1 p2 h1 h2 in
         state_rel σ1' σ2' [] [] ∗
         dwp ⊤ e' s' I))%I.
  - intros HP1.
    admit.
  - iIntros "_". iIntros (Hinv).
    iPoseProof (HR1 $! Hinv) as "H".
    iMod "H" as "H". iModIntro.
    iMod "H" as "H". iModIntro. iNext.
    iMod "H" as "H". iModIntro. iNext.
    iMod "H" as (h1 h2 p1 p2) "[HSR H]". iModIntro.
    rewrite dwp_unfold /dwp_pre.
    assert (language.to_val e = None) as ->. admit.
    simpl. iSpecialize ("H" $! σ1 σ2 [] [] [] with "HSR").
    iMod "H" as (Hred) "H".
    iSpecialize ("H" $! e' σ1' [] with "[//]").
    iMod "H" as "H". iModIntro. iModIntro. iNext.
    iMod "H" as "H". iModIntro. iNext.
    iMod "H" as "H". iModIntro.
    iDestruct "H" as (κ2 κs2' s' σ2' efs' Hκs Hstep2) "[HSR [Hdwp Hefs]]".
    iAssert (⌜efs' = []⌝%I) with "[Hefs]" as %->. { destruct efs'; eauto. }
    symmetry in Hκs. apply app_eq_nil in Hκs. destruct  Hκs as [-> ->].
    iExists s', σ2'. iSplitR; first done.
    iExists h1,h2,p1,p2. iFrame.
Admitted.

Lemma dwp_brel_aa Σ `{!invPreG Σ, !heapPreDG Σ} e s t σ1 σ2 σ3 e' σ1' :
  dwp_brel Σ e s σ1 σ2 →
  dwp_brel Σ s t σ2 σ3 →
  (prim_step e σ1 [] e' σ1' []) →
  ∃ s' σ2' t' σ3',
    prim_step s σ2 [] s' σ2' [] ∧
    prim_step t σ3 [] t' σ3' [] ∧
    dwp_brel Σ e' s' σ1' σ2.
Abort.

Lemma dwp_brel_trans Σ `{!invPreG Σ, !heapPreDG Σ} e1 e2 e3 σ1 σ2 σ3 :
  dwp_brel Σ e1 e2 σ1 σ2 -∗
  dwp_brel Σ e2 e3 σ2 σ3 -∗
  dwp_brel Σ e1 e3 σ1 σ3.
Proof.
  iIntros "H1 H2".
  rewrite /dwp_brel /=. iIntros (Hinv).
  iSpecialize ("H1" $! Hinv).
  iSpecialize ("H2" $! Hinv).
  iMod "H1" as (h1 h2 p1 p2) "((Hh1 & Hp1 & Hh2 & Hp2) & H1)".
  iMod "H2" as (h2' h3 p2' p3) "((Hh2' & Hp2' & Hh3 & Hp3) & H2)".
  (* iMod (gen_heap_init σ1.(heap)) as (h1) "Hh1". *)
  (* iMod (proph_map_init [] σ1.(used_proph_id)) as (p1) "Hp1". *)
  (* iMod (gen_heap_init σ3.(heap)) as (h3) "Hh3". *)
  (* iMod (proph_map_init [] σ3.(used_proph_id)) as (p3) "Hp3". *)
  iExists h1, h3, p1, p3.
  iLöb as "IH" forall (e1 e2 e3 σ1 σ2 σ3).
  rewrite !dwp_unfold /dwp_pre.
  repeat case_match.
  - iFrame. eauto.
  - iFrame. eauto.
  - iFrame. iModIntro. iModIntro. done.
  - iFrame. iModIntro. done.
  - admit.
  - admit.
  - iFrame "Hh1 Hp1 Hh3 Hp3".
    iModIntro. clear σ1 σ3. iIntros (σ1 σ3 κ1 κs1 κs3) "(Hh1 & Hp1 & Hh3 & Hp3)".
    iSpecialize ("H1" $! σ1 σ2 κ1 κs1 with "[Hh1 Hh2 Hp1 Hp2]"); first iFrame.
    iMod "H1" as "[% H1]". iModIntro. iSplit; first done.
    iIntros (e1' σ1' efs Hstep1). iSpecialize ("H1" $! e1' σ1' efs with "[//]").
    iMod "H1" as "H1". iModIntro. iNext. iMod "H1" as "H1".
  simpl. iFrame.
  iIntros (κs1 κs2).
  rewrite plainly_forall.
  iSpecialize ("H1" $! κs1).
  rewrite plainly_forall.

Abort.
*)
