(** Example from Ernst-Murray CAV 2019 *)
From iris.base_logic Require Import invariants.
From iris_ni.logrel Require Import types.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang proofmode.
From iris_ni.proofmode Require Import dwp_tactics.
From iris_ni.logrel Require Import interp.
From iris_ni.examples Require Import lock par.

Definition thread1 : val :=
  rec: "loop" "lk" "out" "rec" :=
    acquire "lk";;
    let: "is_classified" := Fst "rec" in
    let: "data" := Snd "rec" in
    (if: ~ !"is_classified"
     then "out" <- !"data"
     else #());;
    release "lk";;
    "loop" "lk" "out" "rec".

Definition thread2 : val :=
  λ: "lk" "rec",
  acquire "lk";;
  let: "is_classified" := Fst "rec" in
  let: "data" := Snd "rec" in
  "is_classified" <- #false;;
  "data" <- #0;;
  release "lk".

Definition prog : val := λ: "data" "out",
  let: "rec" := (ref #true, ref "data") in
  let: "lk" := newlock #() in
  thread1 "lk" "out" "rec" ||| thread2 "lk" "rec".

Section proof.
  Context `{!heapDG Σ, !lockG Σ, !spawnG Σ}.
  Definition lockN := nroot.@"lock".

  Definition rec_inv is_classified1 is_classified2 rd1 rd2 ξ :=
    (∃ (b : bool) d1 d2,
        is_classified1 ↦ₗ #b ∗ is_classified2 ↦ᵣ #b
        ∗ rd1 ↦ₗ d1 ∗ rd2 ↦ᵣ d2
        ∗ ⟦ tint (if b then High else Low) ⟧ ξ d1 d2)%I.

  Definition N := nroot.@"rec_is_classified".

  Lemma proof out1 out2 dat1 dat2 ξ :
    ⟦ tref (tint Low) ⟧ ξ out1 out2 -∗
    ⟦ tint High ⟧ ξ dat1 dat2 -∗
    DWP (prog dat1 out1) & (prog dat2 out2) : ⟦ tprod tunit tunit ⟧ ξ.
  Proof.
    iIntros "#Hout #Hdat".
    dwp_rec. dwp_pures.

    dwp_bind (ref _)%E (ref _)%E.
    iApply heap_lang_lifting.dwp_alloc. iIntros (rd1 rd2) "Hrd1 Hrd2". iNext.

    dwp_bind (ref _)%E (ref _)%E.
    iApply heap_lang_lifting.dwp_alloc. iIntros (is_classified1 is_classified2) "Hc1 Hc2". iNext.

    dwp_pures.
    dwp_bind (newlock #()) (newlock #()).
    iApply (newlock_spec lockN
             (rec_inv is_classified1 is_classified2 rd1 rd2 ξ)
             with "[-]").
    { iExists true, dat1, dat2. by iFrame. }
    iIntros (γlk lk1 lk2) "#Hlk".

    dwp_pures.
    iApply (dwp_par (⟦ tunit ⟧ ξ) (⟦ tunit ⟧ ξ)).
    - (* Thread 1 *)
      iLöb as "IH". dwp_rec. dwp_pures.
      dwp_bind (acquire _) (acquire _).
      iApply (acquire_spec with "Hlk").
      iIntros "Hlkd H". dwp_pures.
      iDestruct "H" as (b d1 d2) "(Hc1 & Hc2 & Hd1 & Hd2 & #H)".
      dwp_bind (! _)%E (! _)%E. iApply (dwp_load with "Hc1 Hc2").
      iIntros "Hc1 Hc2". iNext. destruct b; dwp_pures.
      + dwp_bind (release _) (release _).
        iApply (release_spec with "Hlk Hlkd [-]").
        { iExists _,_,_. by iFrame. }
        dwp_pures.
        iApply "IH".
      + dwp_bind (!_)%E (!_)%E.
        iApply (dwp_load with "Hd1 Hd2").
        iIntros "Hd1 Hd2". iNext.

        dwp_bind (_ <- _)%E (_ <- _)%E.
        iApply dwp_wand.
        { iApply logrel_store; first by solve_ndisj.
          - by iApply dwp_value.
          - by iApply dwp_value. }
        iIntros (? ?) "Hunit".
        dwp_pures.

        dwp_bind (release _) (release _).
        iApply (release_spec with "Hlk Hlkd [-]").
        { iExists _,_,_. by iFrame. }
        dwp_pures.
        iApply "IH".
    - (* Thread 2 *)
      dwp_rec. dwp_pures.
      dwp_bind (acquire _) (acquire _).
      iApply (acquire_spec with "Hlk").
      iIntros "Hlkd H". dwp_pures.

      iDestruct "H" as (b d1 d2) "(Hc1 & Hc2 & Hd1 & Hd2 & #H)".
      dwp_bind (_ <- _)%E (_ <- _)%E.
      iApply (heap_lang_lifting.dwp_store with "Hc1 Hc2").
      iIntros "Hc1 Hc2". iNext. dwp_pures.

      dwp_bind (_ <- _)%E (_ <- _)%E.
      iApply (heap_lang_lifting.dwp_store with "Hd1 Hd2").
      iIntros "Hd1 Hd2". iNext. dwp_pures.

      iApply (release_spec with "Hlk Hlkd [-]").
      { iExists _, _,_. iFrame.
        iExists _,_. eauto with iFrame. }
      eauto with iFrame.
    - (* Finally *)
      iIntros (???? [-> ->] [-> ->]).
      iNext. iExists _,_,_,_; eauto with iFrame.
  Qed.

End proof.
