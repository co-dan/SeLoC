(** Small examples *)
From iris.algebra Require Import csum agree excl.
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
    - iApply (logrel_store with "[Hl]"); first solve_ndisj.
      + by iApply dwp_value.
      + iApply dwp_value. iModIntro. iExists _,_. eauto with iFrame.
    - iLöb as "IH". dwp_rec.
      iApply "IH".
    - iIntros (????) "??". rewrite (interp_eq (tprod _ _)).
      iNext. iExists _,_,_,_. eauto with iFrame.
  Qed.

End t4_proof.

(** Awkward examples *)

(* awk : tint^h → (tunit → τ) → tint^Low *)
Definition awk : val :=
  λ: "v", let: "x" := ref "v" in
          λ: "f", "x" <- #1;; "f" #();; !"x".

Section awk_proof.
  Context `{!heapDG Σ}.

  Definition f_ty τ l : type := tarrow tunit τ l.

  Lemma awk_typing1 τ l2 ξ :
    DWP awk & awk : ⟦ tarrow (tint Low)
                       (tarrow (f_ty τ l2) (tint Low) Low) Low ⟧ ξ.
  Proof.
    iApply logrel_lam. iAlways. iIntros (i1 i2) "#Hi". iSimpl.
    dwp_bind (ref _)%E (ref _)%E. iApply dwp_wand.
    { iApply logrel_alloc. iApply (dwp_value with "Hi"). }
    iIntros (r1 r2) "#Hr". dwp_pures.
    iApply logrel_lam. iAlways.
    rewrite /f_ty (interp_eq (tarrow _ _ _)). iIntros (f1 f2) "#Hf". iSimpl.
    dwp_bind (_ <- _)%E (_ <- _)%E. iApply dwp_wand.
    { iApply logrel_store; first solve_ndisj.
      + by iApply dwp_value.
      + iApply logrel_int. }
    iIntros (? ?) "H". iApply (logrel_seq with "[H]").
    { by iApply dwp_value. }
    iApply logrel_seq.
    { iApply "Hf". rewrite (interp_eq tunit). eauto with iFrame. }
    iApply logrel_deref. rewrite !left_id.
    iApply (dwp_value with "Hr").
  Qed.

  Definition oneshotR := csumR (exclR unitR) (agreeR unitR).
  Class oneshotG Σ := { oneshot_inG :> inG Σ oneshotR }.
  Definition oneshotΣ : gFunctors := #[GFunctor oneshotR].
  Instance subG_oneshotΣ {Σ} : subG oneshotΣ Σ → oneshotG Σ.
  Proof. solve_inG. Qed.

  Definition pending γ `{oneshotG Σ} := own γ (Cinl (Excl ())).
  Definition shot γ `{oneshotG Σ} := own γ (Cinr (to_agree ())).
  Lemma new_pending `{oneshotG Σ} : (|==> ∃ γ, pending γ)%I.
  Proof. by apply own_alloc. Qed.
  Lemma shoot γ `{oneshotG Σ} : pending γ ==∗ shot γ.
  Proof.
    apply own_update.
    intros n [f |]; simpl; eauto.
    destruct f; simpl; try by inversion 1.
  Qed.
  Definition shootN := nroot .@ "shootN".
  Lemma shot_not_pending γ `{oneshotG Σ} :
    shot γ -∗ pending γ -∗ False.
  Proof.
    iIntros "Hs Hp".
    iPoseProof (own_valid_2 with "Hs Hp") as "H".
    iDestruct "H" as %[].
  Qed.

  Lemma awk_typing2 l τ l2 ξ `{oneshotG Σ} :
    DWP awk & awk : ⟦ tarrow (tint l)
                       (tarrow (f_ty τ l2) (tint Low) Low) Low ⟧ ξ.
  Proof.
    iApply logrel_lam. iAlways. iIntros (i1 i2) "#Hi". iSimpl.
    dwp_bind (ref _)%E (ref _)%E. iApply dwp_alloc.
    iIntros (r1 r2) "Hr1 Hr2". iNext. dwp_pures.
    iMod new_pending as (γ) "Hγ".
    pose (N := nroot.@"hewwo").
    iMod (inv_alloc N _ ((∃ v1 v2, pending γ ∗ r1 ↦ₗ v1 ∗ r2 ↦ᵣ v2)
                           ∨ (shot γ ∗ r1 ↦ₗ #1 ∗ r2 ↦ᵣ #1))%I
            with "[Hr1 Hr2 Hγ]") as "#Hinv".
    { iNext. iLeft. iExists _,_. by iFrame. }
    iApply logrel_lam. iAlways.
    rewrite /f_ty (interp_eq (tarrow _ _ _)). iIntros (f1 f2) "#Hf". iSimpl.
    dwp_bind (_ <- _)%E (_ <- _)%E.
    iApply (dwp_wand _ _ _ (λ v1 v2, ⟦ tunit ⟧ ξ v1 v2 ∗ shot γ)%I).
    { iApply dwp_atomic. iInv N as "HN" "Hcl". iModIntro.
      iDestruct "HN" as "[HN|[#Hγ [>Hr1 >Hr2]]]";
        first iDestruct "HN" as (v1 v2) "[>Hγ [>Hr1 >Hr2]]".
      - iApply (dwp_store with "Hr1 Hr2"). iIntros "Hr1 Hr2".
        iNext. iMod (shoot with "Hγ") as "#Hγ".
        iMod ("Hcl" with "[-]") as "_".
        + iNext. iRight. by iFrame.
        + iModIntro. rewrite (interp_eq tunit). eauto with iFrame.
      - iApply (dwp_store with "Hr1 Hr2"). iIntros "Hr1 Hr2".
        iNext. iMod ("Hcl" with "[-]") as "_".
        + iNext. iRight. by iFrame.
        + iModIntro. rewrite (interp_eq tunit). eauto with iFrame. }
    iIntros (? ?) "[H #Hγ]". iApply (logrel_seq with "[H]").
    { by iApply dwp_value. }
    iApply logrel_seq.
    { iApply "Hf". rewrite (interp_eq tunit). eauto with iFrame. }
    iApply dwp_atomic. iInv N as "HN" "Hcl". iModIntro.
      iDestruct "HN" as "[HN|[_ [>Hr1 >Hr2]]]";
        first iDestruct "HN" as (v1 v2) "[>Hγ' _]".
    { iExFalso. iApply (shot_not_pending with "Hγ Hγ'"). }
    iApply (dwp_load with "Hr1 Hr2").
    iIntros "Hr1 Hr2". iNext. iMod ("Hcl" with "[-]") as "_".
    { iNext. iRight. by iFrame. }
    iModIntro. rewrite !left_id (interp_eq (tint Low)).
    iExists 1,1. by eauto.
  Qed.
End awk_proof.

(* awk : tint^h → (tunit → τ) → (tref tint^Low) *)
Definition awk2 : val :=
  λ: "v", let: "x" := ref "v" in
          λ: "f", "x" <- #1;; "f" #();; "x".

(* What would be a good way of verifying this?
If we make an invariant

    ((∃ v1 v2, pending γ ∗ r1 ↦ₗ v1 ∗ r2 ↦ᵣ v2)
        ∨ (shot γ ∗ ⟦tref (tint Low)⟧ ξ #r1 #r2))

Then we wouldn't be able to use the `shot` case: after
opening the invariant we will get `▷ ⟦tref (tint Low)⟧ ξ #r1 #r2`.
 *)
