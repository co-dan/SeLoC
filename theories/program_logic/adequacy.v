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
