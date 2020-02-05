From stdpp Require Export stringmap gmap.
From iris.heap_lang Require Import lang notation metatheory proofmode.
From iris_ni.logrel Require Export types interp.
From iris_ni.proofmode Require Import dwp_tactics.
From iris_ni.examples Require Export lock.

Section typing.
Variable 𝔏 : gset loc.
Variable ξ : slevel.

Instance insert_binder (A : Type): Insert binder A (stringmap A) :=
  binder_insert.

Inductive has_type (Γ : stringmap type) :
  expr → type → Prop :=
(* structural *)
| Sub_typed e τ τ' :
    has_type Γ e τ →
    τ <: τ' →
    has_type Γ e τ'
| Var_typed x τ :
    Γ !! x = Some τ →
    has_type Γ (Var x) τ
| Low_loc_typed (l : loc) :
    l ∈ 𝔏 →
    has_type Γ #l (tref (tint Low))
(* constructors *)
| Int_typed (n : Z) χ :
    has_type Γ #n (tint χ)
| Bool_typed (b : bool) χ :
    has_type Γ #b (tbool χ)
| Unit_typed :
    has_type Γ #() tunit
| None_typed τ :
    has_type Γ NONE (toption τ)
| Some_typed τ e :
    has_type Γ e τ →
    has_type Γ (SOME e) (toption τ)
| Rec_typed f x e τ τ' χ :
    has_type (<[f:=tarrow τ τ' χ]>(<[x:=τ]>Γ)) e (stamp τ' χ) →
    has_type Γ (rec: f x := e) (tarrow τ τ' χ)
(* destructors *)
| If_typed e e1 e2 χ τ :
    has_type Γ e (tbool χ) →
    χ ⊑ ξ →
    has_type Γ e1 τ →
    has_type Γ e2 τ →
    has_type Γ (if: e then e1 else e2) τ
| If_typed_flat e (v1 v2 : val) τ :
    flat_type τ →
    ξ ≠ High →
    has_type Γ e (tbool High) →
    has_type Γ v1 τ →
    has_type Γ v2 τ →
    has_type Γ (if: e then v1 else v2) τ
| Match_typed e e1 x e2 τ τ' :
    has_type Γ e (toption τ) →
    has_type Γ e1 τ' →
    has_type (<[x:=τ]>Γ) e2 τ' →
    has_type Γ (match: e with NONE => e1 | SOME x => e2 end) τ'
(* effects *)
| Fork_typed e τ :
    has_type Γ e τ →
    has_type Γ (Fork e) tunit
| Deref_typed e τ :
    has_type Γ e (tref τ) →
    has_type Γ (!e) τ
| Alloc_typed e τ :
    has_type Γ e τ →
    has_type Γ (ref e) (tref τ)
| Store_typed e1 e2 τ :
    has_type Γ e1 (tref τ) →
    has_type Γ e2 τ →
    has_type Γ (e1 <- e2) tunit
| FAA_typed e1 e2 χ :
    has_type Γ e1 (tref (tint χ)) →
    has_type Γ e2 (tint χ) →
    has_type Γ (FAA e1 e2) (tint χ)
| Newlock_typed :
    has_type Γ (newlock #()) tmutex
| Acquire_typed lk :
    has_type Γ lk tmutex →
    has_type Γ (acquire lk) tunit
| Release_typed lk :
    has_type Γ lk tmutex →
    has_type Γ (release lk) tunit
.


Section fundamental.
  Context `{!heapDG Σ}.

  Definition subst_valid Γ (γ : gmap string (val*val)) : iProp Σ :=
    ([∗ map] i ↦ τ;vv ∈ Γ;γ, ⟦ τ ⟧ ξ vv.1 vv.2)%I.

  Notation "⟦ Γ ⟧*" := (subst_valid Γ).

  Lemma subst_valid_insert Γ γ x τ v1 v2 :
    ⟦ τ ⟧ ξ v1 v2 -∗ ⟦ Γ ⟧* γ -∗
    ⟦ <[x:=τ]>Γ ⟧* (<[x:=(v1,v2)]>γ).
  Proof.
    destruct x as [|x]=> /=; first by auto.
    rewrite /subst_map. iIntros "Hτ HΓ".
    (* XXX: We cannot pass Hτ directly to the lemma below, because Coq
    cannot unify the arguments correctly. Apparently Coq tries to
    unify arguments left-to-right, and fails to unify the function
    (reasonably so). At the point where we do `iExact` all the
    existentials are already instantiated. *)
    (* TODO: iApply (big_sepM2_insert_2 (λ (_ : string) (y1 : type) (y2 : val * val), ⟦ y1 ⟧ ξ y2.1 y2.2) with "Hτ HΓ"). iExact "Hτ". *)
    iApply (big_sepM2_insert_2 _ with "[Hτ] [$HΓ]"). simpl. iExact "Hτ".
  Qed.

  Definition sem_typed Γ e τ :=
    ∀ γ, ⟦ Γ ⟧* γ -∗ ([∗ set] l ∈ 𝔏, ⟦ tref (tint Low) ⟧ ξ #(LitLoc l) #l) -∗
         DWP (subst_map (fmap fst γ) e) & (subst_map (fmap snd γ) e) : ⟦ τ ⟧ ξ.

  Notation "Γ '⊧' e ':' τ" := (sem_typed Γ e τ)
  (at level 100, e at next level, τ at level 200).

  Lemma fundamental Γ e τ : has_type Γ e τ → Γ ⊧ e : τ.
  Proof.
    induction 1; iIntros (γ) "#HΓ #HI"; iSimpl.
    - iApply logrel_sub=>//. by iApply IHhas_type.
    - rewrite !lookup_fmap /subst_valid.
      rewrite big_sepM2_lookup_1//. iDestruct "HΓ" as ([v1 v2] ->) "Hv".
      iSimpl. by iApply dwp_value.
    - iApply dwp_value. iModIntro.
      iApply (big_sepS_elem_of _ 𝔏 l with "HI")=>//.
    - iApply logrel_int.
    - iApply logrel_bool.
    - iApply logrel_unit.
    - dwp_pures. iApply logrel_none.
    - dwp_bind (subst_map _ e) (subst_map _ e).
      iApply dwp_wand.
      { by iApply IHhas_type. }
      iIntros (v1 v2) "#Hv". dwp_pures. iApply logrel_some.
      by iApply dwp_value.
    - dwp_pures. iApply logrel_rec. iAlways. rewrite (interp_eq (tarrow _ _ _)).
      iIntros (f1 f2 v1 v2) "#Hf #Hv".
      pose (γ' := <[f:=(f1,f2)]>(<[x:=(v1,v2)]>γ)).
      iDestruct (IHhas_type γ' with "[-] HI") as "H".
      { iApply (subst_valid_insert with "[Hf]").
        { by rewrite (interp_eq (tarrow _ _ _)). }
        iApply (subst_valid_insert with "Hv HΓ"). }
      rewrite /γ'. rewrite /insert /insert_binder.
      rewrite !binder_insert_fmap.
      destruct x as [|x], f as [|f];
        simpl; rewrite ?subst_map_insert; try iApply "H".
      destruct (decide (x = f)) as [->|]; iSimpl in "H".
      + rewrite !delete_insert_delete !subst_subst !delete_idemp.
        iApply "H".
      + rewrite !delete_insert_ne // subst_map_insert.
        rewrite !(subst_subst_ne _ x f) // subst_map_insert.
        iApply "H".
    - iApply logrel_if_low=>//.
      + by iApply IHhas_type1.
      + by iApply IHhas_type2.
      + by iApply IHhas_type3.
    - iApply logrel_if_flat=>//.
      + by iApply IHhas_type1.
      + by iApply IHhas_type2.
      + by iApply IHhas_type3.
    - iApply logrel_match.
      + by iApply IHhas_type1.
      + by iApply IHhas_type2.
      + iIntros (v1 v2) "#Hv".
        pose (γ' := (<[x:=(v1,v2)]>γ)).
        iDestruct (IHhas_type3 γ' with "[-] HI") as "H".
        { iApply (subst_valid_insert with "Hv HΓ"). }
        rewrite /γ'. rewrite /insert /insert_binder.
        rewrite !binder_insert_fmap.
        destruct x as [|x];
          simpl; rewrite ?subst_map_insert; try iApply "H".
    - iApply dwp_fork; last by eauto.
      iNext. iApply dwp_wand.
      + iApply (IHhas_type with "HΓ HI").
      + eauto with iFrame.
    - iApply logrel_deref.
      iApply (IHhas_type with "HΓ HI").
    - iApply logrel_alloc.
      iApply (IHhas_type with "HΓ HI").
    - iApply logrel_store; first done.
      + iApply (IHhas_type1 with "HΓ HI").
      + iApply (IHhas_type2 with "HΓ HI").
    - iApply logrel_faa; first done.
      + iApply (IHhas_type1 with "HΓ HI").
      + iApply (IHhas_type2 with "HΓ HI").
    - iApply newlock_typed.
    - change tunit with (stamp tunit Low).
      iApply logrel_app.
      + iApply acquire_typed.
      + iApply IHhas_type; eauto.
    - change tunit with (stamp tunit Low).
      iApply logrel_app.
      + iApply release_typed.
      + iApply IHhas_type; eauto.
  Qed.
End fundamental.
End typing.
