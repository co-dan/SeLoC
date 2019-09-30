(** Example from Ernst-Murray CAV 2019, done without locks, using
value-dependent classifications libary. *)
From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang proofmode.
From iris_ni.proofmode Require Import dwp_tactics.
From iris_ni.logrel Require Import interp value_dep.
From iris_ni.examples Require Import par various (* for oneshot *).

Definition thread1 : val :=
  rec: "loop" "out" "rec" :=
    (if: ~ is_classified "rec"
     then "out" <- read_dep "rec"
     else #());;
    "loop" "out" "rec".

Definition thread2 : val :=
  λ: "rec", declassify "rec" #0.

Definition prog : val := λ: "data" "out",
  let: "rec" := (ref #true, ref "data") in
  thread1 "out" "rec" ||| thread2 "rec".

Section proof.
  Context `{!heapDG Σ, !valueDepG Σ, !spawnG Σ, !oneshotG Σ}.

  (* The invariant guarantees the monotonicity of the declassification. *)
  Definition glinv γ γs :=
    (∃ α, classification γ α (1/2) ∗
     ((pending γs ∗ ⌜α = High⌝) ∨ (shot γs ∗ ⌜α = Low⌝)))%I.

  Definition N := nroot.@"blabla".

  (* We verify that the thread that does the "dumping out" in a loop is secure,
    under the monotonicity assumption. *)
  Lemma thread1_spec γ γs out1 rec1 out2 rec2 ξ :
    ⟦ tref (tint Low) ⟧ ξ out1 out2 -∗
    value_dependent γ (tint Low) ξ rec1 rec2 -∗
    inv N (glinv γ γs) -∗
    DWP thread1 out1 rec1 & thread1 out2 rec2 : ⟦ tunit ⟧ ξ.
  Proof.
    iIntros "#Hout #Hvd #Hinv".
    iLöb as "IH". dwp_rec. dwp_pures.
    dwp_bind (is_classified _) (is_classified _).
    iApply (is_classified_spec with "Hvd").
    iIntros (α b) "Ha".
    iInv N as (β) "[>Hc Hi]" "Hcl".
    iDestruct (classification_auth_agree with "Ha Hc") as %<-.
    iFrame "Ha". iDestruct "Hi" as ">[[Htok %]|[#Htok %]]"; simplify_eq/=.
    - iMod ("Hcl" with "[Htok Hc]") as "_".
      { iNext. iExists _. iFrame. iLeft. eauto with iFrame. }
      iModIntro. iIntros (Hfoo). assert (b = true) as ->.
      { destruct b; naive_solver. }
      iSimpl. dwp_pures. iApply "IH".
    - iMod ("Hcl" with "[Htok Hc]") as "_".
      { iNext. iExists _. iFrame. iRight. eauto with iFrame. }
      iModIntro. iIntros (Hfoo). destruct b.
      { iSimpl. dwp_pures. iApply "IH". }
      dwp_pures. iApply (logrel_seq with "[-IH] IH").
      dwp_bind (read_dep _) (read_dep _).
      iApply (read_spec with "Hvd").
      iIntros (α v1 v2) "Ha #Hv".
      iInv N as (β) "[>Hc Hi]" "Hcl".
      iDestruct "Hi" as ">[[Htok2 %]|[_ %]]"; simplify_eq/=.
      { iExFalso. iApply (shot_not_pending with "Htok Htok2"). }
      iDestruct (classification_auth_agree with "Ha Hc") as %->.
      iFrame "Ha".
      iMod ("Hcl" with "[Htok Hc]") as "_".
      { iNext. iExists _. iFrame. iRight. eauto with iFrame. }
      iModIntro.
      iApply logrel_store; first (by solve_ndisj); iApply dwp_value; eauto with iFrame.
  Qed.

  Lemma thread2_spec γ γs rec1 rec2 ξ :
    value_dependent γ (tint Low) ξ rec1 rec2 -∗
    inv N (glinv γ γs) -∗
    classification γ High (1/2) -∗
    DWP thread2 rec1 & thread2 rec2 : ⟦ tunit ⟧ ξ.
  Proof.
    iIntros "#Hvd #Hinv Hc2".
    dwp_rec.
    iApply (declassify_spec with "Hvd [] Hc2").
    { rewrite !interp_eq. iExists 0,0. by eauto. }
    iSimpl. iIntros "Ha Hc2".
    iInv N as (α') "[>Hc1 >Hi]" "Hcl".
    iDestruct (classification_auth_agree with "Ha Hc1") as %<-.
    iCombine "Hc1 Hc2" as "Hc".
    iMod (classification_update Low with "Ha Hc") as "[$ [Hc1 Hc2]]".
    iDestruct "Hi" as "[[Htok %]|[Htok %]]"; simplify_eq/=.
    iMod (shoot with "Htok") as "Htok".
    iMod ("Hcl" with "[-Hc2]") as "_".
    { iNext. iExists _. iFrame. eauto with iFrame. }
    iModIntro. iFrame "Hc2". iIntros "Hc2". eauto.
  Qed.

  Lemma proof out1 out2 dat1 dat2 ξ :
    ⟦ tref (tint Low) ⟧ ξ out1 out2 -∗
    ⟦ tint High ⟧ ξ dat1 dat2 -∗
    DWP (prog dat1 out1) & (prog dat2 out2) : ⟦ tprod tunit tunit ⟧ ξ.
  Proof.
    iIntros "#Hout #Hdat".
    dwp_rec. dwp_pures.

    dwp_bind (ref _)%E (ref _)%E.
    iApply dwp_alloc. iIntros (rd1 rd2) "Hrd1 Hrd2". iNext.

    dwp_bind (ref _)%E (ref _)%E.
    iApply dwp_alloc. iIntros (is_classified1 is_classified2) "Hc1 Hc2". iNext.

    iMod (make_value_dependent (tint Low) with "Hrd1 Hrd2 Hc1 Hc2 []")
      as (γ) "[#Hvd Hc]".
    { simpl. rewrite left_id. iExact "Hdat". }
    iClear "Hdat". iDestruct "Hc" as "[Hc1 Hc2]".
    dwp_pures.
    iMod new_pending as (γs) "Hpend".

    iMod (inv_alloc N _ (glinv γ γs) with "[-Hc2]") as "#Hinv".
    { iNext. iExists _. iFrame. iLeft. eauto with iFrame. }

    iApply (dwp_par (⟦ tunit ⟧ ξ) (⟦ tunit ⟧ ξ) with "[] [Hc2]").
    - (* Thread 1 *) iApply (thread1_spec with "Hout Hvd Hinv").
    - (* Thread 2 *) iApply (thread2_spec with "Hvd Hinv Hc2").
    - (* Finally *)
      iIntros (???? [-> ->] [-> ->]).
      iNext. iExists _,_,_,_; eauto with iFrame.
  Qed.

End proof.
