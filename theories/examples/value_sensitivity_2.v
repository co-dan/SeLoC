(** Example from Ernst-Murray CAV 2019, done without locks, using
value-dependent classifications libary. *)
From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang proofmode.
From iris_ni.proofmode Require Import dwp_tactics.
From iris_ni.logrel Require Import interp value_dep.
From iris_ni.examples Require Import lock par various (* for oneshot *).

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
    ((pending γs ∗ classification γ High (1/4))
   ∨ (shot γs ∗ classification γ Low (1/4)))%I.

  Definition N := nroot.@"blabla".

  (* We verify that the thread that does the "dumping out" in a loop is secure,
    under the monotonicity assumption. *)
  Lemma thread1_spec γ γst γs out1 rec1 out2 rec2 ξ :
    ⟦ tref (tint Low) ⟧ ξ out1 out2 -∗
    value_dependent γ γst (tint Low) ξ rec1 rec2 -∗
    inv N (glinv γ γs) -∗
    DWP thread1 out1 rec1 & thread1 out2 rec2 : ⟦ tunit ⟧ ξ.
  Proof.
    iIntros "#Hout #Hvd #Hinv".
    iLöb as "IH". dwp_rec. dwp_pures.
    dwp_bind (is_classified _) (is_classified _).
    iApply (is_classified_spec with "Hvd").
    iIntros (α) "Ha".
    iInv N as "[[Htok >Hc]|[#Htok >Hc]]" "Hcl";
      iDestruct (classification_auth_agree with "Ha Hc") as %->;
      iFrame "Ha".
    + iMod ("Hcl" with "[Htok Hc]") as "_".
      { iNext. iLeft. iFrame. }
      iModIntro. iSimpl. dwp_pures. iApply "IH".
    + iMod ("Hcl" with "[Htok Hc]") as "_".
      { iNext. iRight. by iFrame. }
      iModIntro. iSimpl. dwp_pures.
      iApply (logrel_seq with "[-IH] IH").
      dwp_bind (read_dep _) (read_dep _).
      iApply (read_spec with "Hvd").
      iIntros (α v1 v2) "Ha #Hv".
      iInv N as "[[>Htok2 >Hc]|[_ >Hc]]" "Hcl".
      { iExFalso. iApply (shot_not_pending with "Htok Htok2"). }
      iDestruct (classification_auth_agree with "Ha Hc") as %->.
      iFrame "Ha".
      iMod ("Hcl" with "[Htok Hc]") as "_".
      { iNext. iRight. by iFrame. }
      iModIntro.
      iApply logrel_store; first (by solve_ndisj); iApply dwp_value; eauto with iFrame.
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
      as (γ γst) "[#Hvd Hc]".
    { simpl. rewrite left_id. iExact "Hdat". }
    iClear "Hdat".
    dwp_pures.
    iMod new_pending as (γs) "Hpend".

    rewrite classification_quarter.
    iDestruct "Hc" as "[Hc1 Hc]".

    iMod (inv_alloc N _ (glinv γ γs) with "[-Hc]") as "#Hinv".
    { iNext. iLeft. by iFrame. }

    iApply (dwp_par (⟦ tunit ⟧ ξ) (⟦ tunit ⟧ ξ) with "[] [Hc]").
    - (* Thread 1 *) iApply (thread1_spec with "Hout Hvd Hinv").
    - (* Thread 2 *)
      dwp_rec.
      iApply (declassify_spec with "Hvd [] Hc").
      { rewrite !interp_eq. iExists 0,0. by eauto. }
      iIntros (α) "Ha Hf".
      assert (Heq : ((3/4)%Qp + (1/4)%Qp)%Qp = 1%Qp).
      { by apply (bool_decide_unpack _). }
      iInv N as "[[>Htok >Hc]|[#Htok >Hc]]" "Hcl";
        iDestruct (classification_auth_agree with "Ha Hc") as %->;
        iCombine "Hf Hc" as "Hc"; rewrite Heq;
        iMod (classification_update Low with "Ha Hc") as "[$ Hc]";
        rewrite classification_quarter;
        iDestruct "Hc" as "[Hc1 Hc]".
      + iMod (shoot with "Htok") as "Htok".
        iMod ("Hcl" with "[Htok Hc1]") as "_".
        { iNext. iRight. by iFrame. }
        iModIntro. eauto.
      + iMod ("Hcl" with "[Htok Hc1]") as "_".
        { iNext. iRight. by iFrame. }
        iModIntro. eauto.
    - (* Finally *)
      iIntros (???? [-> ->] [-> ->]).
      iNext. iExists _,_,_,_; eauto with iFrame.
  Qed.

End proof.
