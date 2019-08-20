(** Example from Ernst-Murray CAV 2019, done without locks, proven directly. *)
From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang proofmode.
From iris_ni.proofmode Require Import dwp_tactics.
From iris_ni.logrel Require Import interp.
From iris_ni.examples Require Import lock par various (* for oneshot *).
From iris.algebra Require Import auth agree csum frac excl cmra.
From iris.base_logic Require Import auth.

(** * The example program.
Note that a record

   { is_classified: ref bool;
     data : ref τ }

is modeled by a tuple

   (is_classified, data)
**)
Definition thread1 : val :=
  rec: "loop" "out" "rec" :=
    let: "is_classified" := Fst "rec" in
    let: "data" := Snd "rec" in
    (if: ~ !"is_classified"
     then "out" <- !"data"
     else #());;
    "loop" "out" "rec".

Definition thread2 : val :=
  λ: "rec", let: "is_classified" := Fst "rec" in
            let: "data" := Snd "rec" in
            "data" <- #0;;
            "is_classified" <- #false.


Definition prog : val := λ: "out" "secret",
  let: "rec" := (ref #true, ref "secret") in
  thread1 "out" "rec" ||| thread2 "rec".


(** * Ghost state *)
Definition rec : Type := loc * loc.
Inductive state :=
| Classified
| Intermediate
| Declassified.

Canonical Structure stateO := leibnizO state.
Instance state_inhabited : Inhabited state := populate Declassified.

Class stateG Σ := StateG {
   state_stateG :> authG Σ (optionUR (exclR stateO));
}.

Definition classified := Excl' Classified.
Definition intermediate := Excl' Intermediate.
Definition declassified := Excl' Declassified.

Section ghost_state.
  Context `{!stateG Σ}.

  (* TODO: move *)
  Lemma Some_None_not_included {A : cmraT} (x : A) :
    ¬ Some x ≼ None.
  Proof.
    rewrite option_included. intros [?|Hfoo]; simplify_eq/=.
    destruct Hfoo as [a [b [? [? ?]]]]. simplify_eq/=.
  Qed.

  Lemma current_state γ s1 s2 :
    own γ (◯ Some s2) -∗ own γ (● Some s1) -∗ ⌜s1 = s2⌝.
  Proof.
    iIntros "Hf Ha".
    iPoseProof (own_valid_2 with "Ha Hf") as "H".
    iDestruct "H" as %[Hfoo Hh]%auth_both_valid. iPureIntro.
    revert Hfoo. rewrite Some_included.
    intros [Hfoo|Hfoo]; eauto.
    + by unfold_leibniz.
    + exfalso. eapply (exclusive_included _ _ Hfoo). done.
  Qed.

  Lemma change_state s2 s1 γ :
    own γ (● Excl' s1) -∗ own γ (◯ Excl' s1) ==∗ own γ (● Excl' s2) ∗ own γ (◯ Excl' s2).
  Proof.
    apply bi.wand_intro_r. rewrite - !own_op.
    apply own_update. apply auth_update.
    apply option_local_update.
    apply exclusive_local_update. done.
  Qed.

End ghost_state.

Section proof.
  Context `{!heapDG Σ, !spawnG Σ, !stateG Σ, !oneshotG Σ}.

  (* The invariant guarantees the monotonicity of the declassification. *)
  Definition inv_body (r1 r2 : rec) γ γs ξ :=
    (* in the state CLASSIFIED *)
    ((∃ v1 v2, own γ (● classified) ∗ pending γs ∗ r1.1 ↦ₗ #true ∗ r2.1 ↦ᵣ #true
                   ∗ r1.2 ↦ₗ v1 ∗ r2.2 ↦ᵣ v2 ∗ ⟦ tint High ⟧ ξ v1 v2)
   ∨ (* in the state INTERMEDIATE *)
     (∃ v, own γ (● intermediate) ∗ pending γs ∗ r1.1 ↦ₗ #true ∗ r2.1 ↦ #true
               ∗ r1.2 ↦ₗ v ∗ r2.2 ↦ᵣ v ∗ ⟦ tint Low ⟧ ξ v v)
   ∨ (* in the state DECLASSIFIED *)
     (∃ v, own γ (● declassified) ∗ shot γs ∗ r1.1 ↦ₗ #false ∗ r2.1 ↦ #false
               ∗ r1.2 ↦ₗ v ∗ r2.2 ↦ᵣ v ∗ ⟦ tint Low ⟧ ξ v v))%I.

  Definition N := nroot.@"example".

  Definition I (rec1 rec2 : val) γ ξ :=
    (∃ (i1 i2 d1 d2 : loc), ⌜rec1 = (#i1, #d1)%V⌝ ∗ ⌜rec2 = (#i2, #d2)%V⌝ ∗
        inv N (inv_body (i1,d1) (i2,d2) γ.1 γ.2 ξ))%I.

  Lemma thread1_spec γ out1 rec1 out2 rec2 ξ :
    ⟦ tref (tint Low) ⟧ ξ out1 out2 -∗
    I rec1 rec2 γ ξ -∗
    DWP thread1 out1 rec1 & thread1 out2 rec2 : ⟦ tunit ⟧ ξ.
  Proof.
    iIntros "#Hout".
    iDestruct 1 as (ri1 ri2 rd1 rd2 -> ->) "#Hinv".
    iLöb as "IH". dwp_rec. dwp_pures.
    dwp_bind (!_)%E (!_)%E.
    iApply dwp_atomic.
    iInv N as "[Hst|[Hst|Hst]]" "Hcl"; iModIntro.
    - (* We are still in the CLASSIFIED state *)
      iDestruct "Hst" as (v1 v2) "(Hstate & Htok & Hi1 & Hi2 & Hd1 & Hd2 & Hv)".
      iApply (dwp_load with "Hi1 Hi2"). iIntros "Hi1 Hi2". iNext.
      iMod ("Hcl" with "[-]") as "_".
      { iNext. iLeft. eauto with iFrame. }
      iModIntro. dwp_pures. by iApply "IH".
    - (* We are in the INTERMEDIATE state *)
      iDestruct "Hst" as (v) "(Hstate & Htok & Hi1 & Hi2 & Hd1 & Hd2 & Hv)".
      iApply (dwp_load with "Hi1 Hi2"). iIntros "Hi1 Hi2". iNext.
      iMod ("Hcl" with "[-]") as "_".
      { iNext. iRight. iLeft. eauto with iFrame. }
      iModIntro. dwp_pures. by iApply "IH".
    - (* We are in the DECLASSIFIED state *)
      iDestruct "Hst" as (v) "(Hstate & #Hdecl & Hi1 & Hi2 & Hd1 & Hd2 & Hv)".
      iApply (dwp_load with "Hi1 Hi2"). iIntros "Hi1 Hi2". iNext.
      iMod ("Hcl" with "[-]") as "_".
      { iNext. iRight. iRight. eauto with iFrame. }
      iModIntro. dwp_pures. clear v.
      dwp_bind (_ <- _)%E (_ <- _)%E.
      iApply (dwp_wand _ _ _ (⟦ tunit ⟧ ξ)); last first.
      { iIntros (??) "_". dwp_pures.
        by iApply "IH". }
      dwp_bind (! _)%E (! _)%E.
      iApply dwp_atomic.
      iInv N as "[Hst|[Hst|Hst]]" "Hcl"; iModIntro.
      + (* We *cannot* be in the CLASSIFIED state *)
        iDestruct "Hst" as (v1 v2) "(Hstate & >Htok & Hi1 & Hi2 & Hd1 & Hd2 & Hv)".
        iExFalso. iApply (shot_not_pending with "Hdecl Htok").
      + (* We also cannot be in the INTERMEDIATE state, but we do not
           really care about that here. *)
        iDestruct "Hst" as (v) "(Hstate & Htok & Hi1 & Hi2 & Hd1 & Hd2 & #Hv)".
        iApply (dwp_load with "Hd1 Hd2"). iIntros "Hd1 Hd2". iNext.
        iMod ("Hcl" with "[-]") as "_".
        { iNext. iRight. iLeft. eauto with iFrame. }
        iModIntro. iApply logrel_store; first solve_ndisj; by iApply dwp_value.
      + (* Still in the DECLASSIFIED state *)
        iDestruct "Hst" as (v) "(Hstate & Hfrag & Hi1 & Hi2 & Hd1 & Hd2 & #Hv)".
        iApply (dwp_load with "Hd1 Hd2"). iIntros "Hd1 Hd2". iNext.
        iMod ("Hcl" with "[-]") as "_".
        { iNext. iRight. iRight. eauto with iFrame. }
        iModIntro. iApply logrel_store; first solve_ndisj; by iApply dwp_value.
  Qed.

  Lemma thread2_spec γ rec1 rec2 ξ :
    I rec1 rec2 γ ξ -∗
    own γ.1 (◯ classified) -∗
    DWP thread2 rec1 & thread2 rec2 : ⟦ tunit ⟧ ξ.
  Proof.
    iDestruct 1 as (ri1 ri2 rd1 rd2 -> ->) "#Hinv".
    iIntros "Hstt".
    dwp_rec. dwp_pures.
    dwp_bind (_ <- _)%E (_ <- _)%E.
    iApply dwp_atomic.
    iInv N as "[Hst|[Hst|Hst]]" "Hcl"; iModIntro.
    - (* We are still in the CLASSIFIED state *)
      iDestruct "Hst" as (v1 v2) "(Hstate & Htok & Hi1 & Hi2 & Hd1 & Hd2 & Hv)".
      iApply (dwp_store with "Hd1 Hd2"). iIntros "Hd1 Hd2". iNext.
      iMod (change_state Intermediate with "Hstate Hstt") as "[Hstate Hstt]".
      iMod ("Hcl" with "[-Hstt]") as "_".
      { iNext. iRight. iLeft. iExists #0. iFrame.
        rewrite interp_eq. iExists 0,0. eauto with iFrame. } clear v1 v2.
      iModIntro. dwp_pures. iApply dwp_atomic.
      iInv N as "[Hst|[Hst|Hst]]" "Hcl"; iModIntro.
      + (* CLASSIFIED state --> impossible *)
        iDestruct "Hst" as (v1 v2) "(>Hstate & Htok & Hi1 & Hi2 & Hd1 & Hd2 & Hv)".
        iDestruct (current_state with "Hstt Hstate") as %Hfoo.
        simplify_eq/=.
      + (* INTERMEDIATE state *)
        iDestruct "Hst" as (v) "(Hstate & Htok & Hi1 & Hi2 & Hd1 & Hd2 & Hv)".
        iApply (dwp_store with "Hi1 Hi2"). iIntros "Hi1 Hi2". iNext.
        iMod (change_state Declassified with "Hstate Hstt") as "[Hstate Hstt]".
        iMod (shoot with "Htok") as "Htok".
        iMod ("Hcl" with "[-Hstt]") as "_".
        { iNext. iRight. iRight. eauto with iFrame.  }
        iModIntro. eauto with iFrame.
      + (* DECLASSIFIED state --> impossible *)
        iDestruct "Hst" as (v) "(>Hstate & Htok & Hi1 & Hi2 & Hd1 & Hd2 & Hv)".
        iDestruct (current_state with "Hstt Hstate") as %Hfoo.
        simplify_eq/=.
    - (* INTERMEDIATE state --> impossible *)
      iDestruct "Hst" as (v) "(>Hstate & Htok & Hi1 & Hi2 & Hd1 & Hd2 & Hv)".
      iDestruct (current_state with "Hstt Hstate") as %Hfoo. simplify_eq/=.
    - (* DECLASSIFIED state --> impossible *)
      iDestruct "Hst" as (v) "(>Hstate & Htok & Hi1 & Hi2 & Hd1 & Hd2 & Hv)".
      iDestruct (current_state with "Hstt Hstate") as %Hfoo. simplify_eq/=.
  Qed.


  Lemma proof out1 out2 dat1 dat2 ξ :
    ⟦ tref (tint Low) ⟧ ξ out1 out2 -∗
    ⟦ tint High ⟧ ξ dat1 dat2 -∗
    DWP (prog out1 dat1) & (prog out2 dat2) : ⟦ tprod tunit tunit ⟧ ξ.
  Proof.
    iIntros "#Hout #Hdat".
    dwp_rec. dwp_pures.

    dwp_bind (ref _)%E (ref _)%E.
    iApply dwp_alloc. iIntros (rd1 rd2) "Hrd1 Hrd2". iNext.

    dwp_bind (ref _)%E (ref _)%E.
    iApply dwp_alloc. iIntros (is_classified1 is_classified2) "Hc1 Hc2". iNext.

    iMod new_pending as (γs) "Hstt".
    iMod (own_alloc (● classified ⋅ ◯ classified)) as (γ) "[Hstate Htoken]".
    { by apply auth_both_valid_2. }
    iMod (inv_alloc N _
           (inv_body (is_classified1,rd1) (is_classified2,rd2) γ γs ξ) with "[-Htoken]")
      as "#Hinv".
    { iNext. iLeft. iExists _,_. eauto with iFrame. }
    dwp_pures.
    iApply (dwp_par (⟦ tunit ⟧ ξ) (⟦ tunit ⟧ ξ) with "[] [Htoken]").
    - (* Thread 1 *) iApply (thread1_spec (γ,γs) with "Hout []").
      iExists _,_,_,_. repeat iSplit; eauto.
    - (* Thread 2 *) iApply (thread2_spec (γ,γs) with "[] Htoken").
      iExists _,_,_,_. repeat iSplit; eauto.
    - (* Finally *)
      iIntros (???? [-> ->] [-> ->]).
      iNext. iExists _,_,_,_; eauto with iFrame.
  Qed.

End proof.
