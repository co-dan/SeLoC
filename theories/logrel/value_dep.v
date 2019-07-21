(** Value-dependent classifications.

This implements value-dependent classification for locations with the
following protocol:

- Multiple threads can do reads, and look at the classification
  levels, permitting arbitrary interference. (No additional resources
  are required beyond a view shift).

- Only one thread can perform declassification, but it can it do
  concurrently with reads. Cannot be done concurrently with writes.
  (Requires a token [classification γ (3/4)])

- The same condition holds for writes. (Requires a token
  [classification γ (3/4)])

- Only a single thread can perform classification. No interference
  from any other operations is permitted. (Requires a full token
  [classification γ 1]).

The restriction that only one thread can perform declassification is
artificial, it should be completely safe to do that. But it is more
annoying to prove.

There are other variations that can be implemented:

- Classification can be done concurrently with writes, but no
  interference from reads is allowed.

- Both reads and writes can be performed completely concurrently, but
  no interference from declassification and classification is allowed.
  Thus only one thread can declassify/classify and no other thread can
  access the resource.

What is the "best" the most general specification? It's hard to tell,
because those resource with value-dependent classification are
basically like references, and references are invariant in their type.
This imposes a severe restriction on what kind of interference each
operation can tolerate, and a lot of combinations just do not make
sense.

I choose this particular protocol, because it allowed me to verify the
non-blocking declassification example in
examples/value_sensitivity_2.v

** TODO:

- use meta-tokens

- saner (curried) lemmas

*)
From iris.base_logic Require Import invariants lib.auth.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang proofmode.
From iris.algebra Require Export auth frac excl.
From iris.bi.lib Require Export fractional.
From iris_ni.logrel Require Import types.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris_ni.proofmode Require Import dwp_tactics.
From iris_ni.logrel Require Import interp.

(** We model value-dependent classified variables as records:

   { is_classified: ref bool;
     data : ref τ }

  (well, we actually model it using a tuple..)

  The security level of `data` is actually determined by the value
  of `is_classified`.
*)
Definition classify : val := λ: "rec",
  Fst "rec" <- #true.

Definition declassify : val := rec: "declassify" "rec" "dv" :=
  let: "is_classified" := Fst "rec" in
  let: "data" := Snd "rec" in
  "data" <- "dv";;
  "is_classified" <- #false.

Definition read_dep : val := λ: "rec", ! (Snd "rec").

Definition store_dep : val := λ: "rec" "v", Snd "rec" <- "v".

Definition is_classified : val := λ: "rec", ! (Fst "rec").


Inductive cl_state :=
| Classified
| Declassified
| Intermediate.

Canonical Structure cl_stateO := leibnizO cl_state.
Instance cl_state_inhabited : Inhabited cl_state := populate Declassified.

Class valueDepG Σ := ValueDepG {
   value_dep_stateG :> authG Σ (optionUR (exclR cl_stateO));
   value_dep_slelveG :> authG Σ (optionUR (prodR fracR (agreeR slevelO)));
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

  Definition classification γ (α : slevel) (q : frac) : iProp Σ :=
    (own γ (◯ (Some (q, to_agree α))))%I.

  Definition classification_auth γ (α : slevel) : iProp Σ :=
    (own γ (● (Some (1%Qp, to_agree α))))%I.

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

  Lemma classification_quarter γ α :
    classification γ α 1 ⊣⊢ classification γ α (1/4) ∗ classification γ α (3/4).
  Proof.
    assert (1%Qp = (1/4)%Qp + (3/4)%Qp)%Qp as Heq.
    { by apply (bool_decide_unpack _). }
    rewrite {1}Heq.
    apply fractional.
  Qed.

  Global Instance classification_timeless γ α q :
    Timeless (classification γ α q).
  Proof. apply _. Qed.

  Global Instance classification_auth_timeless γ α :
    Timeless (classification_auth γ α).
  Proof. apply _. Qed.

  Lemma classification_new α :
    (|==> ∃ γ, classification_auth γ α ∗ classification γ α 1)%I.
  Proof.
    (* Why all the type annotations? *)
    rewrite /classification_auth /classification.
    iMod (own_alloc (● (Some (1%Qp, to_agree α))⋅
            ◯ (Some (1%Qp, to_agree α)))) as (γ) "H".
    { apply auth_both_valid. split; done. }
    iModIntro. iExists γ. by rewrite -own_op.
  Qed.

  Lemma classification_update μ γ α β :
    classification_auth γ α ∗ classification γ β 1
    ==∗
    classification_auth γ μ ∗ classification γ μ 1.
  Proof.
    rewrite /classification /classification_auth - !own_op. apply own_update.
    apply auth_update.
    apply option_local_update.
    by apply exclusive_local_update.
  Qed.

  Lemma classification_auth_agree γ α β q :
    classification_auth γ α ∗ classification γ β q -∗ ⌜α = β⌝.
  Proof.
    rewrite /classification /classification_auth - !own_op.
    iIntros "H". iDestruct (own_valid with "H") as %Hfoo.
    iPureIntro; revert Hfoo.
    rewrite auth_both_valid.
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
    rewrite -auth_frag_op -Some_op pair_op.
    rewrite auth_frag_valid Some_valid.
    by intros [_ foo%agree_op_invL']%pair_valid.
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

  Lemma cl_state_update (new_st : cl_state) γst (st : cl_state) :
    own γst (● Excl' st) ∗ own γst (◯ Excl' st)
    ==∗
    own γst (● Excl' new_st) ∗ own γst (◯ Excl' new_st).
  Proof.
    rewrite - !own_op. apply own_update.
    apply auth_update.
    apply option_local_update.
    by apply exclusive_local_update.
  Qed.

  Lemma cl_state_agree γst (st st' : cl_state) :
    own γst (● Excl' st) ∗ own γst (◯ Excl' st') -∗ ⌜st = st'⌝.
  Proof.
    rewrite -own_op.
    iIntros "H". iDestruct (own_valid with "H") as %Hfoo.
    iPureIntro; revert Hfoo.
    rewrite auth_both_valid. intros [foo _].
    apply Some_included_exclusive in foo; try (simplify_eq; done).
    apply _.
  Qed.

  Definition lvl_of_bool (b : bool) :=
    match b with
    | true => High
    | false => Low
    end.

  Definition state_of_bool (b : bool) :=
    match b with
    | true => Classified
    | false => Declassified
    end.

  Definition bool_of_state (st : cl_state) :=
    match st with
    | Classified => true
    | Intermediate => true
    | Declassified => false
    end.

  Definition bool_of_lvl (sl : slevel) :=
    match sl with
    | High => true
    | Low => false
    end.

  Definition lvl_of_state (st : cl_state) := lvl_of_bool (bool_of_state st).

  Definition cl_state_inv γ γst st b τ w1 w2 ξ :=
    match st with
    | Classified =>
      ⌜b = true⌝ ∗ ⟦ stamp τ High ⟧ ξ w1 w2 ∗ own γst (◯ Excl' Classified)
    | Declassified =>
      ⌜b = false⌝ ∗ ⟦ τ ⟧ ξ w1 w2 ∗ own γst (◯ Excl' Declassified)
    | Intermediate =>
      ⟦ τ ⟧ ξ w1 w2 ∗ classification γ (lvl_of_bool b) (3/4)
    end%I.

  Lemma cl_state_not_intermediate γ γst st b τ w1 w2 β ξ :
    cl_state_inv γ γst st b τ w1 w2 ξ -∗
    classification γ β 1 -∗ ⌜st ≠ Intermediate⌝.
  Proof.
    iIntros "Hst Hc". rewrite /cl_state_inv.
    destruct st; eauto.
    iDestruct "Hst" as "(_ & Hc2)".
    iExFalso. iApply (classification_1_exclusive with "Hc Hc2").
  Qed.

  Lemma cl_state_not_intermediate_2 γ γst st b τ w1 w2 β ξ :
    cl_state_inv γ γst st b τ w1 w2 ξ -∗
    classification γ β (3/4) -∗ ⌜st ≠ Intermediate⌝.
  Proof.
    iIntros "Hst Hc". rewrite /cl_state_inv.
    destruct st; eauto.
    iDestruct "Hst" as "(_ & Hc2)".
    iExFalso. iDestruct (own_valid_2 with "Hc Hc2") as %Hfoo.
    iPureIntro. revert Hfoo.
    rewrite -auth_frag_op auth_frag_valid -Some_op Some_valid.
    rewrite pair_op frac_op'. Admitted.

  (* We can change the values unless we are in the intermediate step *)
  Lemma cl_state_change_values γ γst st b τ w1 w2 v1 v2 ξ :
    st ≠ Intermediate →
    cl_state_inv γ γst st b τ w1 w2 ξ -∗
    ⟦ stamp τ (lvl_of_bool b) ⟧ ξ v1 v2 -∗
    cl_state_inv γ γst st b τ v1 v2 ξ.
  Proof.
    iIntros (?) "Hst #Hv". rewrite /cl_state_inv.
    destruct st; simplify_eq/=; iDestruct "Hst" as "(-> & Hw & $)";
      compute[lvl_of_state]; simplify_eq/=;
      rewrite ?stamp_low; eauto with iFrame.
  Qed.

  Lemma cl_state_classify γ γst st b τ w1 w2 ξ :
    st ≠ Intermediate → (* cannot go from intermediate to declassified *)
    own γst (● Excl' st) -∗
    cl_state_inv γ γst st b τ w1 w2 ξ ==∗
    own γst (● Excl' Classified) ∗ cl_state_inv γ γst Classified true τ w1 w2 ξ.
  Proof.
    iIntros (?) "Hst Hw". rewrite /cl_state_inv.
    destruct st; try by iFrame; simplify_eq/=.
    - iDestruct "Hw" as "(-> & Hw & Hstf)". eauto with iFrame.
    - iDestruct "Hw" as "(-> & Hw & Hstf)".
      iMod (cl_state_update Classified with "[$Hst $Hstf]") as "[$ $]".
      iModIntro. iSplit; eauto.
      iApply (interp_sub_mono with "Hw"). by apply stamp_sub.
  Qed.

  Lemma cl_state_make_intermediate γ γst st b τ w1 w2 v1 v2 ξ :
    st ≠ Intermediate →
    ⟦ τ ⟧ ξ v1 v2 -∗
    classification γ (lvl_of_bool b) (3/4) -∗
    own γst (● Excl' st) -∗
    cl_state_inv γ γst st b τ w1 w2 ξ ==∗
    own γst (● Excl' Intermediate) ∗
    own γst (◯ Excl' Intermediate) ∗ (* you also get a token *)
    cl_state_inv γ γst Intermediate b τ v1 v2 ξ.
  Proof.
    iIntros (?) "#Hv Hcl Hst Hw". rewrite /cl_state_inv.
    destruct st; try by iFrame; simplify_eq/=.
    - iDestruct "Hw" as "(-> & Hw & Hstf)".
      iMod (cl_state_update Intermediate with "[$Hst $Hstf]") as "[$ $]".
      by iFrame.
    - iDestruct "Hw" as "(-> & Hw & Hstf)".
      iMod (cl_state_update Intermediate with "[$Hst $Hstf]") as "[$ $]".
      by iFrame.
  Qed.

  Lemma cl_state_values γ γst st b τ w1 w2 ξ :
    cl_state_inv γ γst st b τ w1 w2 ξ -∗
    ⟦ stamp τ (lvl_of_bool b) ⟧ ξ w1 w2.
  Proof.
    iIntros "Hw". rewrite /cl_state_inv.
    destruct st.
    - iDestruct "Hw" as "(-> & Hw & Hstf)". simpl. by iFrame.
    - iDestruct "Hw" as "(-> & Hw & Hstf)". simpl.
      rewrite stamp_low. by iFrame.
    - iDestruct "Hw" as "(Hw & Hstf)".
      iApply (interp_sub_mono with "Hw"). apply stamp_sub.
  Qed.

  Definition value_dependent_inv γ γst τ (cl1 cl2 r1 r2 : loc) ξ :=
    (∃ (w1 w2 : val) (b : bool) (st : cl_state),
       r1 ↦ₗ w1 ∗ r2 ↦ᵣ w2 ∗ cl1 ↦ₗ #b ∗ cl2 ↦ᵣ #b ∗
       own γst (● Excl' st) ∗
       classification_auth γ (lvl_of_bool b) ∗
       cl_state_inv γ γst st b τ w1 w2 ξ)%I.

  Definition value_dependent γ γst τ : lrel Σ := LRel (λ ξ v1 v2,
    ∃ (cl1 cl2 r1 r2: loc),
      ⌜v1 = (#cl1, #r1)%V⌝ ∗ ⌜v2 = (#cl2, #r2)%V⌝ ∗
      inv (nroot.@"vdep".@(v1,v2))
        (value_dependent_inv γ γst τ cl1 cl2 r1 r2 ξ))%I.

  (** ** A "constructor" *)
  Lemma make_value_dependent τ (cl1 cl2 r1 r2 : loc) w1 w2 b E ξ :
    r1 ↦ₗ w1 -∗
    r2 ↦ᵣ w2 -∗
    cl1 ↦ₗ #b -∗
    cl2 ↦ᵣ #b -∗
    ⟦ stamp τ (lvl_of_bool b) ⟧ ξ w1 w2 ={E}=∗
    ∃ γ γst, value_dependent γ γst τ ξ (#cl1, #r1)%V (#cl2, #r2)%V ∗
      classification γ (lvl_of_bool b) 1.
  Proof.
    iIntros "Hr1 Hr2 Hcl1 Hcl2 #Hw".
    iMod (classification_new (lvl_of_bool b)) as (γ) "[Ha Hf]".
    iMod (own_alloc (● Excl' (state_of_bool b) ⋅ ◯ Excl' (state_of_bool b)))
      as (γst) "[Hst Hstf]".
    { apply auth_both_valid. split; done. }
    iMod (inv_alloc (nroot.@"vdep".@((#cl1,#r1)%V,(#cl2,#r2)%V)) _
       (value_dependent_inv γ γst τ cl1 cl2 r1 r2 ξ) with "[-Hf]") as "#Hinv".
    { iNext. rewrite /value_dependent_inv. iExists _,_,_,(state_of_bool b).
      iFrame. destruct b; simpl; rewrite ?stamp_low; by eauto with iFrame. }
    iModIntro. iExists γ,γst. iFrame.
    iExists _,_,_,_. by eauto.
  Qed.

  (** ** Specifications for the functions *)

  Lemma is_classified_spec γ γst τ rec1 rec2 ξ Q :
    value_dependent γ γst τ ξ  rec1 rec2 -∗
    (∀ α, classification_auth γ α
          ={⊤∖↑nroot.@"vdep".@(rec1,rec2)}=∗
      classification_auth γ α ∗ Q #(bool_of_lvl α) #(bool_of_lvl α)) -∗
    DWP is_classified rec1 & is_classified rec2 : Q.
  Proof.
    iIntros "Hdep Hvs".
    iDestruct "Hdep" as (cl1 cl2 r1 r2 -> ->) "#Hinv".
    dwp_rec. dwp_pures.
    iApply dwp_atomic.
    iInv (nroot.@"vdep".@((#cl1, #r1)%V, (#cl2, #r2)%V)) as (w1 w2 b st)
                   "(Hr1 & Hr2 & Hcl1 & Hcl2 & Hst & Ha & Hw)" "Hcl".
    iModIntro. iApply (dwp_load with "Hcl1 Hcl2"). iIntros "Hcl1 Hcl2". iNext.

    iMod ("Hvs" with "Ha") as "[Ha HQ]".

    iMod ("Hcl" with "[- HQ]") as "_".
    { iNext. iExists _,_,_,_. by iFrame. }
    iModIntro. iFrame. by destruct b; eauto.
  Qed.

  Lemma declassify_spec γ γst τ β rec1 rec2 v1 v2 ξ Q :
    value_dependent γ γst τ ξ rec1 rec2 -∗
    ⟦ τ ⟧ ξ v1 v2 -∗
    classification γ β (3/4) -∗
    (∀ α, classification_auth γ α -∗ classification γ α (3/4)
          ={⊤∖↑nroot.@"vdep".@(rec1,rec2)}=∗
      classification_auth γ Low ∗ Q #() #()) -∗
    DWP declassify rec1 v1 & declassify rec2 v2 : Q.
  Proof.
    iIntros "Hdep #Hv Hf Hvs".
    iDestruct "Hdep" as (cl1 cl2 r1 r2 -> ->) "#Hinv".
    dwp_rec. dwp_pures. dwp_bind (#r1 <- _)%E (#r2 <- _)%E.

    (** First we store the values and change the state to intermediate *)
    iApply dwp_atomic.
    iInv (nroot.@"vdep".@((#cl1, #r1)%V, (#cl2, #r2)%V)) as (w1 w2 b st)
                   "(Hr1 & Hr2 & Hcl1 & Hcl2 & Hst & Ha & Hw)" "Hcl".
    iModIntro. iApply (dwp_store with "Hr1 Hr2"). iIntros "Hr1 Hr2". iNext.

    (** Notice that we cannot already be in the intermediate step *)
    iDestruct (cl_state_not_intermediate_2 with "Hw Hf") as %?.

    (** Notice that we know the exact classification of the values *)
    iDestruct (classification_auth_agree with "[$Ha $Hf]") as %<-.

    (** Actually update the state.. *)
    iMod (cl_state_make_intermediate with "Hv Hf Hst Hw") as "(Hst&Htok&Hw)";
      first fast_done.

    iMod ("Hcl" with "[-Htok Hvs]") as "_".
    { iNext. iExists _,_,_,Intermediate. by iFrame. }

    (** Now we finish up by physically declassifying the location and
    updating the state to Declassified *)
    iModIntro. dwp_pures.

    iApply dwp_atomic.
    iInv (nroot.@"vdep".@((#cl1, #r1)%V, (#cl2, #r2)%V)) as (w1' w2' b' st')
                   "(Hr1 & Hr2 & Hcl1 & Hcl2 & Hst & Ha & Hw)" "Hcl".
    iModIntro. iApply (dwp_store with "Hcl1 Hcl2"). iIntros "Hcl1 Hcl2". iNext.

    (** Notice that we are still in the intermediate step *)
    iDestruct (cl_state_agree with "[$Hst $Htok]") as %->.
    iSimpl in "Hw". iDestruct "Hw" as "[#Hw Hc]".

    iMod ("Hvs" with "Ha Hc") as "[Ha HQ]".

    (** Update the ghost state *)
    iMod (cl_state_update Declassified with "[$Hst $Htok]") as "[Hst Hstf]".

    iMod ("Hcl" with "[-HQ]") as "_".
    { iNext. iExists _,_,false,Declassified.
      iFrame. iSplit; by eauto. }

    by eauto.
  Qed.

  Lemma read_spec γ γst τ rec1 rec2 ξ Q :
    value_dependent γ γst τ ξ rec1 rec2 -∗
    (∀ α v1 v2, classification_auth γ α -∗ ⟦ stamp τ α ⟧ ξ v1 v2
          ={⊤∖↑nroot.@"vdep".@(rec1,rec2)}=∗
      classification_auth γ α ∗ Q v1 v2) -∗
    DWP read_dep rec1 & read_dep rec2 : Q.
  Proof.
    iIntros "Hdep Hvs".
    iDestruct "Hdep" as (cl1 cl2 r1 r2 -> ->) "#Hinv".
    dwp_rec. dwp_pures.
    iApply dwp_atomic.
    iInv (nroot.@"vdep".@((#cl1, #r1)%V, (#cl2, #r2)%V)) as (w1 w2 b st)
                   "(Hr1 & Hr2 & Hcl1 & Hcl2 & Hst & Ha & Hw)" "Hcl".
    iModIntro. iApply (dwp_load with "Hr1 Hr2"). iIntros "Hr1 Hr2". iNext.

    (** The values have to be related at the "actual" state
    irregardless of the ghost state *)
    iDestruct (cl_state_values with "Hw") as "#Hws".

    iMod ("Hvs" with "Ha Hws") as "[Ha $]".

    iApply ("Hcl" with "[-]").
    iNext. iExists _,_,_,_. by iFrame.
  Qed.

  Lemma classify_spec γ γst τ β rec1 rec2 ξ Q :
    value_dependent γ γst τ ξ rec1 rec2 -∗
    classification γ β 1 -∗
    (∀ α, classification_auth γ α -∗ classification γ α 1
          ={⊤∖↑nroot.@"vdep".@(rec1,rec2)}=∗
      classification_auth γ High ∗ Q #() #()) -∗
    DWP classify rec1 & classify rec2 : Q.
  Proof.
    iIntros "Hdep Hf Hvs".
    iDestruct "Hdep" as (cl1 cl2 r1 r2 -> ->) "#Hinv".
    dwp_rec. dwp_pures.
    iApply dwp_atomic.
    iInv (nroot.@"vdep".@((#cl1, #r1)%V, (#cl2, #r2)%V)) as (w1 w2 b st)
                   "(Hr1 & Hr2 & Hcl1 & Hcl2 & Hst & Ha & Hw)" "Hcl".
    iModIntro. iApply (dwp_store with "Hcl1 Hcl2"). iIntros "Hcl1 Hcl2". iNext.

    iDestruct (classification_auth_agree with "[$Ha $Hf]") as %<-.
    (** Notice that we cannot be in the intermediate state *)
    iDestruct (cl_state_not_intermediate with "Hw Hf") as %?.

    (** Change the state *)
    iMod (cl_state_classify with "Hst Hw") as "[Hst Hw]"; try done.

    iMod ("Hvs" with "Ha Hf") as "[Ha $]".

    iApply ("Hcl" with "[-]").
    iNext. iExists _,_,_,Classified. by iFrame.
  Qed.

  Lemma store_spec γ γst τ β rec1 rec2 v1 v2 ξ Q :
    value_dependent γ γst τ ξ rec1 rec2 -∗
    ⟦ stamp τ β ⟧ ξ v1 v2 -∗
    classification γ β (3/4) -∗
    (∀ α, classification_auth γ α -∗ classification γ α (3/4)
          ={⊤∖↑nroot.@"vdep".@(rec1,rec2)}=∗
      classification_auth γ α ∗ Q #() #()) -∗
    DWP store_dep rec1 v1 & store_dep rec2 v2 : Q.
  Proof.
    iIntros "Hdep #Hv Hf Hvs".
    iDestruct "Hdep" as (cl1 cl2 r1 r2 -> ->) "#Hinv".
    dwp_rec. dwp_pures.
    iApply dwp_atomic.
    iInv (nroot.@"vdep".@((#cl1, #r1)%V, (#cl2, #r2)%V)) as (w1 w2 b st)
                   "(Hr1 & Hr2 & Hcl1 & Hcl2 & Hst & Ha & Hw)" "Hcl".
    iModIntro. iApply (dwp_store with "Hr1 Hr2"). iIntros "Hr1 Hr2". iNext.

    iDestruct (classification_auth_agree with "[$Ha $Hf]") as %<-.

    (** Notice that we cannot be in the intermediate state *)
    iDestruct (cl_state_not_intermediate_2 with "Hw Hf") as %?.

    (** Then we can change the values *)
    iDestruct (cl_state_change_values with "Hw Hv") as "Hw"; first done.

    iMod ("Hvs" with "Ha Hf") as "[Ha $]".

    iApply ("Hcl" with "[-]").
    iNext. iExists _,_,_,_. by iFrame.
  Qed.

End value_dep.

Typeclasses Opaque classification classification_auth.
