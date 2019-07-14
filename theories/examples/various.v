(** Small examples *)
From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang proofmode.
From iris_ni.proofmode Require Import dwp_tactics.
From iris_ni.logrel Require Import interp.
From iris_ni.examples Require Import par.

(** Examples from Huisman-Worah-Sunesen CSFW-06 *)

Definition loop : val := rec: "loop" <> := "loop" #().
Definition t4 : val := λ: "l", ("l" <- #7) ||| (loop #()).

Section t4_proof.
  Context `{!heapDG Σ, !spawnG Σ}.

  (** According to Huisman's definition of observational determinism
  this program is *not* secure. Because there is a trace that assigns
  7 to the low location `l`, and there is another trace in which the
  right side of the parallel composition starves the lhs, and the
  assignment is not executed. Those traces are *not* equivalent up to
  stuttering. *)
  Lemma t4_safe (l1 l2 : val) ξ :
    ⟦ tref (tint Low) ⟧ ξ l1 l2 -∗
    DWP (t4 l1) & (t4 l2) : ⟦ tprod tunit tunit ⟧ ξ.
  Proof.
    iIntros "#Hl". dwp_rec. dwp_pures.
    iApply (dwp_par (⟦tunit⟧ ξ) (⟦tunit⟧ ξ)).
    - iApply (logrel_store with "[Hl]").
      + by iApply dwp_value.
      + iApply dwp_value. iModIntro. iExists _,_. eauto with iFrame.
    - iLöb as "IH". dwp_rec.
      iApply "IH".
    - iIntros (????) "??". rewrite (interp_eq (tprod _ _)).
      iNext. iExists _,_,_,_. eauto with iFrame.
  Qed.

End t4_proof.

(** Awkward exmples *)

(* awk : tint^low → (tunit → τ) → tint^low *)
Definition awk : val :=
  λ: "v", let: "x" := ref "v" in
          λ: "f", "x" <- #1;; "f" #();; !"x".

Section awk_proof.
  Context `{!heapDG Σ}.

  Definition f_ty τ l : type := tarrow tunit τ l.

  Lemma awk_typing τ l ξ :
    DWP awk & awk : ⟦ tarrow (tint Low)
                       (tarrow (f_ty τ l) (tint Low) Low) Low ⟧ ξ.
  Proof.
    iApply logrel_lam. iAlways. iIntros (i1 i2) "#Hi". iSimpl.
    dwp_bind (ref _)%E (ref _)%E. iApply dwp_wand.
    { iApply logrel_alloc. iApply (dwp_value with "Hi"). }
    iIntros (r1 r2) "#Hr". dwp_pures.
    iApply logrel_lam. iAlways.
    rewrite /f_ty (interp_eq (tarrow _ _ _)). iIntros (f1 f2) "#Hf". iSimpl.
    dwp_bind (_ <- _)%E (_ <- _)%E. iApply dwp_wand.
    { iApply logrel_store; first by iApply dwp_value.
      iApply logrel_int. }
    iIntros (? ?) "H". iApply (logrel_seq with "[H]").
    { by iApply dwp_value. }
    iApply logrel_seq.
    { iApply "Hf". rewrite (interp_eq tunit). eauto with iFrame. }
    iApply logrel_deref. rewrite !left_id.
    iApply (dwp_value with "Hr").
  Qed.
End awk_proof.
