(** * Value-dependent classifications.

This implements value-dependent classification for locations with the
following protocol:

- Multiple threads can do reads, and look at the classification
  levels, permitting arbitrary interference. (No additional resources
  are required beyond a view shift). Althought you do need a token if
  you want to verify that what you read is indeed low-security.
  Similarly for write: you can always write stuff, but you need a
  token if you want to store high-security data.

- Only one thread can perform declassification or classification, but
  it can it do concurrently with reads or writes.

- As per the first point, if you do declassification concurrently with
  writes, then writes have to provide low security data. Similarly, if
  you do classification concurrently with reads, you can only assume
  that the read operation returns high-security data.

- The [is_classified] operation returns an *upper bound* on the
security level. That is, if it returns [false], then you know that the
data is surely declassified. But if it returns [true] you cannot be
certain. *)

From iris.base_logic Require Import invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang proofmode.
From iris.algebra Require Export auth frac excl.
From iris.bi.lib Require Export fractional.
From iris_ni.logrel Require Import types.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris_ni.proofmode Require Import dwp_tactics.
From iris_ni.logrel Require Import interp.

(** ** Implementation

We model value-dependent classified variables as records:

   { is_classified: ref bool;
     data : ref τ }

  (well, we actually model it using a tuple..)

  The security level of `data` is actually determined by the value
  of `is_classified`.
*)
Definition classify : val := λ: "rec",
  Fst "rec" <- #true.

Definition declassify : val := λ: "rec" "dv",
  let: "is_classified" := Fst "rec" in
  let: "data" := Snd "rec" in
  "data" <- "dv";;
  "is_classified" <- #false.

Definition read_dep : val := λ: "rec", ! (Snd "rec").

Definition store_dep : val := λ: "rec" "v", Snd "rec" <- "v".

Definition is_classified : val := λ: "rec", ! (Fst "rec").


(** ** The invariant guarding the records:

There are always the following propositions together with the current
state of the reference:

- is_classified ↦ (b : bool)
- data is related at ⟦ τ ⊔ α ⟧


There are three possible states:


                                +--------------+
                                |              |
          +-------------------->| Intermediate +-----------------+
          |                     |              |                 v
   +------+-------+             +--------------+          +--------------+
   |              |             | b = false    |          |              |
   |  Classified  |             | α = Low      |          | Declassified |
   |              |             |              |          |              |
   +--------------+             +--------------+          +--------------+
   |  b = false   |                                       | b = true     |
   |  α = High    |                                       | α = Low      |
   +--------------+                                       +------+-------+
          ^                                                      |
          |                                                      |
          +------------------------------------------------------+
*)

Class valueDepG Σ := ValueDepG {
   value_dep_slelveG :> inG Σ (authR $ optionUR (prodR fracR (agreeR slevelO)));
}.

Section value_dep.
  Implicit Types α β : slevel.
  Implicit Types q : frac.
  Implicit Types γ : gname.
  Implicit Types τ : type.
  Implicit Types b : bool.
  Context `{!heapDG Σ, !valueDepG Σ}.

  (* XXX *)
  Hint Rewrite interp_eq.

  (** ** Definitions and properties of tokens *)
  Definition classification γ (α : slevel) (q : frac) : iProp Σ :=
    (own γ (◯ (Some (q, to_agree α)) : authR (optionUR (prodR fracR (agreeR slevelO)))))%I.

  Definition classification_auth γ (α : slevel) : iProp Σ :=
    (own γ (● (Some (1%Qp, to_agree α)) : authR (optionUR (prodR fracR (agreeR slevelO)))))%I.

  Global Instance classification_fractional γ α :
    Fractional (classification γ α).
  Proof. rewrite /classification.
    intros p q. rewrite /classification. iSplit.
    - by iDestruct 1 as "[$ $]".
    - iDestruct 1 as "[H1 H2]". by iCombine "H1 H2" as "H".
  Qed.

  Global Instance classification_as_fractional γ α q :
    AsFractional (classification γ α q) (classification γ α) q.
  Proof. split. done. apply _. Qed.

  Global Instance classification_timeless γ α q :
    Timeless (classification γ α q).
  Proof. apply _. Qed.

  Global Instance classification_auth_timeless γ α :
    Timeless (classification_auth γ α).
  Proof. apply _. Qed.

  Lemma classification_new α :
    ⊢ |==> ∃ γ, classification_auth γ α ∗ classification γ α 1.
  Proof.
    (* Why all the type annotations? *)
    rewrite /classification_auth /classification.
    iMod (own_alloc ((● (Some (1%Qp, to_agree α)) ⋅
                        ◯ (Some (1%Qp, to_agree α)))
                     : authR (optionUR (prodR fracR (agreeR slevelO))) )) as (γ) "H".
    { apply auth_both_valid_discrete. split; done. }
    iModIntro. iExists γ. by rewrite -own_op.
  Qed.

  Lemma classification_update μ γ α β :
    classification_auth γ α -∗ classification γ β 1
    ==∗
    classification_auth γ μ ∗ classification γ μ 1.
  Proof.
    apply bi.wand_intro_r.
    rewrite /classification /classification_auth - !own_op.
    apply own_update. apply auth_update, option_local_update.
    by apply exclusive_local_update.
  Qed.

  Lemma classification_auth_agree γ α β q :
    classification_auth γ α -∗ classification γ β q -∗ ⌜α = β⌝.
  Proof.
    apply bi.wand_intro_r. rewrite /classification /classification_auth - !own_op.
    iIntros "H". iDestruct (own_valid with "H") as %Hfoo.
    iPureIntro; revert Hfoo.
    rewrite auth_both_valid_discrete.
    intros [[_ foo%to_agree_included]%Some_pair_included_total_2 _].
    by unfold_leibniz.
  Qed.

  Lemma classification_agree γ β β' q q' :
    classification γ β q -∗
    classification γ β' q' -∗ ⌜β = β'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hfoo.
    iPureIntro. revert Hfoo.
    rewrite auth_frag_op_valid Some_valid.
    by intros [_ foo%to_agree_op_inv_L]%pair_valid.
  Qed.

  Lemma classification_1_exclusive γ β β' q :
    classification γ β 1 -∗
    classification γ β' q -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hfoo.
    iPureIntro. revert Hfoo.
    rewrite -auth_frag_op auth_frag_valid -Some_op Some_valid.
    apply exclusive_l. apply _.
  Qed.

  (** Functions converting between security levels, states, and booleans *)
  Definition lvl_of_bool (b : bool) :=
    match b with
    | true => High
    | false => Low
    end.

  (** ** The invariant and transitions *)
  Definition cl_state_inv b α τ w1 w2 ξ :=
    (* classified *)
   ((⌜b = true⌝ ∗ ⌜α = High⌝ ∗ ⟦ stamp τ High ⟧ ξ w1 w2) ∨
    (* intermediate *)
    (⌜b = true⌝ ∗ ⌜α = Low⌝ ∗ ⟦ τ ⟧ ξ w1 w2)   ∨
    (* declassified *)
    (⌜b = false⌝ ∗ ⌜α = Low⌝ ∗ ⟦ τ ⟧ ξ w1 w2))%I.

  (** The Boolean flag always determines the "visible" classification
  level of the reference. Whereas the actual data can be related at a
  lower reference. This basically enables concurrent/non-blocking
  declassification. *)
  Definition value_dependent_inv γ τ (cl1 cl2 r1 r2 : loc) ξ :=
    (∃ (w1 w2 : val) (b : bool) (α : slevel),
       r1 ↦ₗ w1 ∗ r2 ↦ᵣ w2 ∗ cl1 ↦ₗ #b ∗ cl2 ↦ᵣ #b ∗
       classification_auth γ α ∗
       cl_state_inv b α τ w1 w2 ξ)%I.


  Definition value_dependent γ τ : lrel Σ := LRel (λ ξ v1 v2,
    ∃ (cl1 cl2 r1 r2: loc),
      ⌜v1 = (#cl1, #r1)%V⌝ ∗ ⌜v2 = (#cl2, #r2)%V⌝ ∗
      inv (nroot.@"vdep".@(v1,v2))
        (value_dependent_inv γ τ cl1 cl2 r1 r2 ξ))%I.

  (** ** A "constructor" *)
  Lemma make_value_dependent τ (cl1 cl2 r1 r2 : loc) w1 w2 b E ξ :
    r1 ↦ₗ w1 -∗
    r2 ↦ᵣ w2 -∗
    cl1 ↦ₗ #b -∗
    cl2 ↦ᵣ #b -∗
    ⟦ stamp τ (lvl_of_bool b) ⟧ ξ w1 w2 ={E}=∗
    ∃ γ, value_dependent γ τ ξ (#cl1, #r1)%V (#cl2, #r2)%V ∗
      classification γ (lvl_of_bool b) 1.
  Proof.
    iIntros "Hr1 Hr2 Hcl1 Hcl2 #Hw".
    iMod (classification_new (lvl_of_bool b)) as (γ) "[Ha Hf]".
    iMod (inv_alloc (nroot.@"vdep".@((#cl1,#r1)%V,(#cl2,#r2)%V)) _
       (value_dependent_inv γ τ cl1 cl2 r1 r2 ξ) with "[-Hf]") as "#Hinv".
    { iNext. rewrite /value_dependent_inv. iExists _,_,_,(lvl_of_bool b).
      iFrame. destruct b; simpl; rewrite ?stamp_low.
      - iLeft. eauto with iFrame.
      - iRight. iRight. eauto with iFrame. }
    iModIntro. iExists γ. iFrame.
    iExists _,_,_,_. by eauto.
  Qed.

  (** ** Specifications for the functions *)

  Lemma is_classified_spec γ τ rec1 rec2 ξ Q :
    value_dependent γ τ ξ  rec1 rec2 -∗
    (∀ α b, classification_auth γ α
          ={⊤∖↑nroot.@"vdep".@(rec1,rec2)}=∗
      classification_auth γ α ∗
        (⌜b = false → α = Low⌝ -∗ Q #b #b)) -∗
    DWP is_classified rec1 & is_classified rec2 : Q.
  Proof.
    iIntros "Hdep Hvs".
    iDestruct "Hdep" as (cl1 cl2 r1 r2 -> ->) "#Hinv".
    dwp_rec. dwp_pures.
    iApply dwp_atomic.
    iInv (nroot.@"vdep".@((#cl1, #r1)%V, (#cl2, #r2)%V)) as (w1 w2 b α)
        "(Hr1 & Hr2 & >Hcl1 & >Hcl2 & Ha & Hi)" "Hcl".
    iModIntro. iApply (dwp_load with "Hcl1 Hcl2"). iIntros "Hcl1 Hcl2". iNext.

    iMod ("Hvs" with "Ha") as "[Ha HQ]".
    iAssert (⌜b = false → α = Low⌝)%I as %Hfoo.
    { rewrite /cl_state_inv. destruct b; first by eauto.
      iDestruct "Hi" as "[(% & _)|[(% & _) | (% & % & _)]]"; by simplify_eq/=. }
    iMod ("Hcl" with "[- HQ]") as "_".
    { iNext. iExists _,_,_,_. by iFrame. }
    iModIntro. iFrame. by iApply "HQ".
  Qed.

  Lemma declassify_spec γ τ q α rec1 rec2 v1 v2 ξ Q :
    value_dependent γ τ ξ rec1 rec2 -∗
    ⟦ τ ⟧ ξ v1 v2 -∗
    classification γ α q -∗
    (classification_auth γ α -∗ classification γ α q
          ={⊤∖↑nroot.@"vdep".@(rec1,rec2)}=∗
      classification_auth γ Low ∗ classification γ Low q
      ∗ (classification γ Low q -∗ Q #() #())) -∗
    DWP declassify rec1 v1 & declassify rec2 v2 : Q.
  Proof.
    iIntros "Hdep #Hv Hf Hvs".
    iDestruct "Hdep" as (cl1 cl2 r1 r2 -> ->) "#Hinv".
    dwp_rec. dwp_pures. dwp_bind (#r1 <- _)%E (#r2 <- _)%E.

    (** First we store the values and change the state to intermediate *)
    iApply dwp_atomic.
    iInv (nroot.@"vdep".@((#cl1, #r1)%V, (#cl2, #r2)%V)) as (w1 w2 b α')
                   "(>Hr1 & >Hr2 & Hcl1 & Hcl2 & Ha & Hi)" "Hcl".
    iModIntro. iApply (dwp_store with "Hr1 Hr2"). iIntros "Hr1 Hr2". iNext.

    (** Notice that we know the exact classification of the values *)
    iDestruct (classification_auth_agree with "Ha Hf") as %->.

    (* Case analysis on the slevel bound *)
    destruct α.
    - rewrite /cl_state_inv.
      iMod ("Hcl" with "[-Hf Hvs]") as "_".
      { iNext. iExists _,_,_,_. iFrame "Hcl1 Hcl2 Ha Hr1 Hr2".
        iDestruct "Hi" as "[  (% & % & #Hw)
                           |[ (% & % & #Hw)
                            | (% & % & #Hw) ]]"; simplify_eq/=.
        - iRight. iLeft. eauto with iFrame.
        - iRight. iRight. eauto with iFrame. }
      clear b. iModIntro. dwp_pures.
      iApply dwp_atomic.
      iInv (nroot.@"vdep".@((#cl1, #r1)%V, (#cl2, #r2)%V)) as (w1' w2' b α)
                   "(Hr1 & Hr2 & >Hcl1 & >Hcl2 & Ha & Hi)" "Hcl".
      iModIntro. iApply (dwp_store with "Hcl1 Hcl2"). iIntros "Hcl1 Hcl2". iNext.
      (* classification is still the same *)
      iDestruct (classification_auth_agree with "Ha Hf") as %->.
      iMod ("Hvs" with "Ha Hf") as "[Ha [Hf HQ]]".
      iDestruct ("HQ" with "Hf") as "$".
      iApply "Hcl". iNext. iExists _,_,_,_. iFrame "Hr1 Hr2 Hcl1 Hcl2 Ha".
      iRight. iRight. repeat iSplit; eauto.
      iDestruct "Hi" as "[  (% & % & #Hw')
                         |[ (% & % & #Hw')
                          | (% & % & #Hw') ]]"; by simplify_eq/=.
    - (* it is in the classified state *)
      iDestruct "Hi" as "[  (% & % & #Hw')
                         |[ (% & % & #Hw')
                          | (% & % & #Hw') ]]"; simplify_eq/=.
      iMod ("Hvs" with "Ha Hf") as "[Ha [Hf HQ]]".
      iMod ("Hcl" with "[-Hf HQ]") as "_".
      { iNext. iExists _,_,_,_. iFrame "Hcl1 Hcl2 Ha Hr1 Hr2".
        iRight. iLeft. eauto with iFrame. }
      iModIntro. dwp_pures.
      iApply dwp_atomic.
      iInv (nroot.@"vdep".@((#cl1, #r1)%V, (#cl2, #r2)%V)) as (w1' w2' b α)
                   "(Hr1 & Hr2 & >Hcl1 & >Hcl2 & Ha & Hi)" "Hcl".
      iModIntro. iApply (dwp_store with "Hcl1 Hcl2"). iIntros "Hcl1 Hcl2". iNext.
      (* classification is still the same *)
      iDestruct (classification_auth_agree with "Ha Hf") as %->.
      iMod ("Hcl" with "[-Hf HQ]") as "_".
      { iNext. iExists _,_,_,_. iFrame "Hcl1 Hcl2 Ha Hr1 Hr2".
        iRight. iRight. repeat iSplit; eauto.
        iDestruct "Hi" as "[  (% & % & #Hw)
                           |[ (% & % & #Hw)
                            | (% & % & #Hw) ]]"; by simplify_eq/=. }
      iModIntro. by iApply "HQ".
  Qed.

  Lemma read_spec γ τ rec1 rec2 ξ Q :
    value_dependent γ τ ξ rec1 rec2 -∗
    (∀ α v1 v2, classification_auth γ α -∗ ⟦ stamp τ α ⟧ ξ v1 v2
          ={⊤∖↑nroot.@"vdep".@(rec1,rec2)}=∗
      classification_auth γ α ∗ Q v1 v2) -∗
    DWP read_dep rec1 & read_dep rec2 : Q.
  Proof.
    iIntros "Hdep Hvs".
    iDestruct "Hdep" as (cl1 cl2 r1 r2 -> ->) "#Hinv".
    dwp_rec. dwp_pures.
    iApply dwp_atomic.
    iInv (nroot.@"vdep".@((#cl1, #r1)%V, (#cl2, #r2)%V)) as (w1 w2 b α)
                   "(>Hr1 & >Hr2 & Hcl1 & Hcl2 & Ha & Hi)" "Hcl".
    iModIntro. iApply (dwp_load with "Hr1 Hr2"). iIntros "Hr1 Hr2". iNext.
    iDestruct "Hi" as "[  (% & % & #Hw)
                       |[ (% & % & #Hw)
                        | (% & % & #Hw) ]]"; simplify_eq/=.
    - iMod ("Hvs" with "Ha [//]") as "[Ha $]".
      iApply "Hcl". iNext. iExists _,_,_,_. iFrame "Hcl1 Hcl2 Hr1 Hr2 Ha".
      iLeft. eauto with iFrame.
    - iMod ("Hvs" with "Ha []") as "[Ha $]".
      { by rewrite stamp_low. }
      iApply "Hcl". iNext. iExists _,_,_,_. iFrame "Hcl1 Hcl2 Hr1 Hr2 Ha".
      iRight. iLeft. eauto with iFrame.
    - iMod ("Hvs" with "Ha []") as "[Ha $]".
      { by rewrite stamp_low. }
      iApply "Hcl". iNext. iExists _,_,_,_. iFrame "Hcl1 Hcl2 Hr1 Hr2 Ha".
      iRight. iRight. eauto with iFrame.
  Qed.

  Lemma classify_spec γ τ α q rec1 rec2 ξ Q :
    value_dependent γ τ ξ rec1 rec2 -∗
    classification γ α q -∗
    (classification_auth γ α -∗ classification γ α q
          ={⊤∖↑nroot.@"vdep".@(rec1,rec2)}=∗
      classification_auth γ High ∗ Q #() #()) -∗
    DWP classify rec1 & classify rec2 : Q.
  Proof.
    iIntros "Hdep Hf Hvs".
    iDestruct "Hdep" as (cl1 cl2 r1 r2 -> ->) "#Hinv".
    dwp_rec. dwp_pures.
    iApply dwp_atomic.
    iInv (nroot.@"vdep".@((#cl1, #r1)%V, (#cl2, #r2)%V)) as (w1 w2 b α')
                   "(Hr1 & Hr2 & >Hcl1 & >Hcl2 & Ha & Hi)" "Hcl".
    iModIntro. iApply (dwp_store with "Hcl1 Hcl2"). iIntros "Hcl1 Hcl2". iNext.

    iDestruct (classification_auth_agree with "Ha Hf") as %->.
    iMod ("Hvs" with "Ha Hf") as "[Ha $]".

    iApply ("Hcl" with "[-]").
    iNext. iExists _,_,_,_. iFrame "Hcl1 Hcl2 Hr1 Hr2 Ha".
    iDestruct "Hi" as "[  (% & % & #Hw)
                       |[ (% & % & #Hw)
                        | (% & % & #Hw) ]]"; simplify_eq/=.
    - iLeft. eauto with iFrame.
    - iLeft. repeat iSplit; eauto.
      iApply (interp_sub_mono with "Hw"). apply stamp_sub.
    - iLeft. repeat iSplit; eauto.
      iApply (interp_sub_mono with "Hw"). apply stamp_sub.
  Qed.

  Lemma store_spec γ τ rec1 rec2 v1 v2 ξ Q :
    value_dependent γ τ ξ rec1 rec2 -∗
    (∀ α, classification_auth γ α
          ={⊤∖↑nroot.@"vdep".@(rec1,rec2)}=∗
      classification_auth γ α ∗ ⟦ stamp τ α ⟧ ξ v1 v2 ∗ Q #() #()) -∗
    DWP store_dep rec1 v1 & store_dep rec2 v2 : Q.
  Proof.
    iIntros "Hdep Hvs".
    iDestruct "Hdep" as (cl1 cl2 r1 r2 -> ->) "#Hinv".
    dwp_rec. dwp_pures.
    iApply dwp_atomic.
    iInv (nroot.@"vdep".@((#cl1, #r1)%V, (#cl2, #r2)%V)) as (w1 w2 b α)
                   "(>Hr1 & >Hr2 & Hcl1 & Hcl2 & Ha & Hi)" "Hcl".
    iModIntro. iApply (dwp_store with "Hr1 Hr2"). iIntros "Hr1 Hr2". iNext.

    iMod ("Hvs" with "Ha") as "[Ha [#Hvs $]]".

    iApply ("Hcl" with "[-]").
    iNext. iExists _,_,_,_. iFrame "Hcl1 Hcl2 Hr1 Hr2 Ha".
    iDestruct "Hi" as "[  (% & % & #Hw)
                       |[ (% & % & #Hw)
                        | (% & % & #Hw) ]]"; simplify_eq/=.
    - iLeft. eauto with iFrame.
    - iRight. iLeft. rewrite stamp_low. eauto with iFrame.
    - iRight. iRight. rewrite stamp_low. eauto with iFrame.
  Qed.

End value_dep.

Typeclasses Opaque classification classification_auth.
