From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang proofmode.
From iris_ni.proofmode Require Import dwp_tactics.
From iris_ni.logrel Require Import interp.
From iris_ni.examples Require Import lock.

Section calendar.
  Context `{!heapDG Σ}.

  Fixpoint is_list (hd1 : val) (hd2 : val) (xs1 xs2 : list val) : iProp Σ :=
    match xs1,xs2 with
    | [],[] => ⌜hd1 = NONEV⌝ ∗ ⌜hd2 = NONEV⌝
    | x1 :: xs1, x2 :: xs2 => ∃ (l1:loc) (l2 :loc) hd1' hd2',
         ⌜hd1 = SOMEV #l1⌝ ∗ ⌜hd2 = SOMEV #l2⌝ ∗ l1 ↦ₗ (x1,hd1') ∗ l2 ↦ᵣ (x2,hd2')
         ∗ is_list hd1' hd2' xs1 xs2
    | _, _ => False
    end%I.

  Definition iter : val := rec: "loop" "hd" "f" :=
      match: "hd" with
        NONE => #()
      | SOME "l" =>
         let: "tmp1" := Fst !"l" in
         let: "tmp2" := Snd !"l" in
         "f" "tmp1";;
         "loop" "tmp2" "f"
      end.

  Lemma iter_spec P (f1 f2 :val) hd1 hd2 xs1 xs2 ξ :
    Forall2 P xs1 xs2 →
    is_list hd1 hd2 xs1 xs2 -∗
    □(∀ x1 x2, ⌜P x1 x2⌝ → DWP (App f1 x1) & (App f2 x2) : ⟦ tunit ⟧ ξ) -∗
    DWP iter hd1 f1 & iter hd2 f2 : ⟦ tunit ⟧ ξ.  (* TODO: return is_list *)
  Proof.
    iIntros (Hxs) "Hlst #Hf". iRevert (Hxs).
    iLöb as "IH" forall (hd1 hd2 xs1 xs2). iIntros (Hxs).
    dwp_rec. dwp_pures.
    destruct xs1 as [|x1 xs1], xs2 as [|x2 xs2]; iSimpl in "Hlst"; try by iExFalso.
    - iDestruct "Hlst" as "[-> ->]". dwp_pures. iApply logrel_unit.
    - iDestruct "Hlst" as (l1 l2 hd1' hd2' -> ->) "(Hl1 & Hl2 & Hlst)".
      apply Forall2_cons_inv in Hxs.
      dwp_pures. dwp_bind (! _)%E (! _)%E. iApply (dwp_load with "Hl1 Hl2"). iIntros "Hl1 Hl2". iNext.
      dwp_pures. dwp_bind (! _)%E (! _)%E. iApply (dwp_load with "Hl1 Hl2"). iIntros "Hl1 Hl2". iNext.
      dwp_pures. dwp_bind (f1 x1) (f2 x2). iApply (dwp_wand with "[Hf]").
      { iApply "Hf". iPureIntro. naive_solver. }
      iIntros (??) "_". dwp_pures. iApply ("IH" with "Hlst"). naive_solver.
  Qed.
End calendar.
