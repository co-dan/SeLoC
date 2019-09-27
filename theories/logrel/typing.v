From stdpp Require Export stringmap gmap.
From iris.heap_lang Require Import lang notation metatheory proofmode.
From iris_ni.logrel Require Export types interp.
From iris_ni.proofmode Require Import dwp_tactics.

Section typing.
Variable 𝔏 : gset loc.
Variable ξ : slevel.

Instance insert_binder (A : Type): Insert binder A (stringmap A) :=
  binder_insert.

Inductive has_type (Γ : stringmap type) :
  expr → type → Prop :=
| Sub_typed e τ τ' :
    has_type Γ e τ →
    τ <: τ' →
    has_type Γ e τ'
| Var_typed x τ :
    Γ !! x = Some τ →
    has_type Γ (Var x) τ
| Int_typed (n : Z) χ :
    has_type Γ #n (tint χ)
| Bool_typed (b : bool) χ :
    has_type Γ #b (tbool χ)
| Unit_typed :
    has_type Γ #() tunit
| If_typed e e1 e2 χ τ :
    has_type Γ e (tbool χ) →
    χ ⊑ ξ →
    has_type Γ e1 τ →
    has_type Γ e2 τ →
    has_type Γ (if: e then e1 else e2) τ
| Rec_typed f x e τ τ' χ :
    has_type (<[f:=tarrow τ τ' χ]>(<[x:=τ]>Γ)) e (stamp τ' χ) →
    has_type Γ (rec: f x := e) (tarrow τ τ' χ)
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
| Low_loc_typed (l : loc) :
    l ∈ 𝔏 →
    has_type Γ #l (tref (tint Low)).

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
    (* TODO: whyyyy *)
    iApply (big_sepM2_insert_2 with "[Hτ] HΓ"). iExact "Hτ".
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
    - iApply logrel_int.
    - iApply logrel_bool.
    - iApply logrel_unit.
    - iApply logrel_if_low=>//.
      + by iApply IHhas_type1.
      + by iApply IHhas_type2.
      + by iApply IHhas_type3.
    - dwp_pures. iApply logrel_rec. iAlways. rewrite (interp_eq (tarrow _ _ _)).
      iIntros (f1 f2 v1 v2) "#Hf #Hv".
      pose (γ' := <[f:=(f1,f2)]>(<[x:=(v1,v2)]>γ)).
      iDestruct (IHhas_type γ' with "[-] HI") as "H".
      { iApply (subst_valid_insert with "[Hf]").
        { by rewrite (interp_eq (tarrow _ _ _)). }
        iApply (subst_valid_insert with "Hv HΓ"). }
      rewrite /γ'.
      admit.
      (* TODO :(
      destruct x as [|x], f as [|f]; simpl; try iApply "H".
      compute[insert_binder]. *)
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
    - iApply dwp_value. iModIntro.
      iApply (big_sepS_elem_of _ 𝔏 l with "HI")=>//.
  Abort.
End typing.
