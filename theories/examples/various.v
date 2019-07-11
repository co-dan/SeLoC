(** Examples from Huisman-Worah-Sunesen CSFW-06 *)
From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang proofmode.
From iris_ni.proofmode Require Import dwp_tactics.
From iris_ni.logrel Require Import typemap interp.
From iris_ni.examples Require Import par.


Definition loop : val := rec: "loop" <> := "loop" #().
Definition t4 : val := λ: "l", ("l" <- #7) ||| (loop #()).

Section proof.
  Context `{!heapDG Σ, !typemapG (loc*loc) Σ, !spawnG Σ}.

  (** According to Huisman's definition of observational determinism
  this program is *not* secure. Because there is a trace that assigns
  7 to the low location `l`, and there is another trace in which the
  right side of the parallel composition starves the lhs, and the
  assignment is not executed. Those traces are *not* equivalent up to
  stuttering. *)
  Lemma t4_safe (l1 l2 : val) ξ :
    locationsI ξ -∗
    ⟦ tref (tint Low) ⟧ ξ l1 l2 -∗
    DWP (t4 l1) & (t4 l2) : ⟦ tprod tunit tunit ⟧ ξ.
  Proof.
    iIntros "#Hinv #Hl". dwp_rec. dwp_pures.
    iApply (dwp_par (⟦tunit⟧ ξ) (⟦tunit⟧ ξ)).
    - iApply (interp.dwp_store with "Hinv [Hl]").
      + by iApply dwp_value.
      + iApply dwp_value. iModIntro. iExists _,_. eauto with iFrame.
    - iLöb as "IH". dwp_rec.
      iApply "IH".
    - iIntros (????) "??".
      iNext. iExists _,_,_,_. eauto with iFrame.
  Qed.

End proof.
