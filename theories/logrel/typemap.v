(** (Monotone) finite maps {A → typeS}.
    The main idea is to have the proposition [has_type x τ] be persistent
    while allowing weakening.
*)
From iris.algebra Require Import auth agree gmap.
From iris.base_logic Require Export auth invariants.
From iris.proofmode Require Import tactics.
From iris_ni.logrel Require Import types.
From iris.heap_lang Require Import lang.
Import uPred.

Canonical Structure typeC := leibnizC type.

Definition typemapUR A `{!EqDecision A, !Countable A} :=
  gmapUR A (prodR (agreeR typeC) slevelR).

Class typemapPreG A `{!EqDecision A, !Countable A} Σ := TypemapPreG
{ typemaPreG_inG :> authG Σ (typemapUR A) }.
Class typemapG A `{!EqDecision A, !Countable A} Σ := TypemapG
{ typemaG_inG :> authG Σ (typemapUR A);
  typemap_name : gname }.

Arguments typemap_name {_ _ _ _} _ : assert.

Definition typemapΣ A `{!EqDecision A, !Countable A} : gFunctors :=
  #[ authΣ (typemapUR A) ].
Global Instance subG_typemapΣ {A Σ} `{!EqDecision A, !Countable A} :
  subG (typemapΣ A) Σ → typemapPreG A Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context {A : Type} `{!EqDecision A, !Countable A}.
  Context `{hG : !typemapG A Σ}.

  Definition to_typemap (f : gmap A (type*slevel)) : typemapUR A :=
    fmap (λ ts, (to_agree ts.1, ts.2)) f.

  Definition typemap_ctx (f : gmap A (type*slevel)) : iProp Σ :=
    own (typemap_name hG) (● to_typemap f).

  Definition has_type (x : A) (τ : type) (l : slevel) : iProp Σ :=
    (own (typemap_name hG) (◯ {[ x := (to_agree τ, l) ]}))%I.

  Lemma to_typemap_valid f : ✓ to_typemap f.
  Proof. intros l. rewrite lookup_fmap. by case (f !! l). Qed.

End definitions.


Lemma typemap_init `{!EqDecision A, !Countable A, !typemapPreG A Σ} f :
  (|==> ∃ _ : typemapG A Σ, typemap_ctx f)%I.
Proof.
  iMod (own_alloc (● to_typemap f)) as (γ) "H".
  { apply auth_auth_valid, to_typemap_valid. }
  iModIntro. iExists (TypemapG _ _ _ _ _ γ). done.
Qed.

Lemma gmap_singleton_mono {A} `{!EqDecision A, !Countable A}
  {B : cmraT}
  (x : A) (y z : B) :
  y ≼ z → {[ x := y ]} ≼ ({[ x := z ]} : gmapUR A B).
Proof.
  intros Hyz.
  apply (singleton_included ({[ x := z ]} : gmapUR A B) x y).
  exists z. rewrite lookup_singleton.
  split; first done. apply (Some_included y z). eauto.
Qed.

Section logic.
  Context {A : Type} `{!EqDecision A, !Countable A}.
  Context `{!typemapG A Σ}.

  Implicit Types τ : type.
  Implicit Types l : slevel.
  Implicit Types x : A.

  Global Instance has_type_persistent x τ l :
    Persistent (has_type x τ l).
  Proof. apply _. Qed.

  Lemma has_type_weaken x τ l l' :
    l ⊑ l' →
    has_type x τ l -∗ has_type x τ l'.
  Proof.
    intros Hinc%slevelR_included. rewrite /has_type.
    apply own_mono, auth_frag_mono.
    pose (y := (to_agree τ, l') : prodR (agreeR typeC) slevelR).
    apply (gmap_singleton_mono x y (to_agree τ, l)).
    apply (prod_included y (to_agree τ, l)). split; eauto.
  Qed.

  Lemma typemap_lookup f x τ l :
    typemap_ctx f -∗
    has_type x τ l -∗
    ⌜∃ l', f !! x = Some (τ,l') ∧ l' ⊑ l⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as
        %[foo _]%auth_valid_discrete_2.
        (* %[[τ' [Hf Hτ'%Some_included]]%singleton_included _] *)
        (*  %auth_valid_discrete_2. *)
    apply (singleton_included (to_typemap f)) in foo.
    destruct foo as [[τ' l'] [Hf Hτ']].
    pose (y := (to_agree τ, l) : prodR (agreeR typeC) slevelR).
    apply (Some_included y) in Hτ'. subst y.
    iPureIntro. exists l'.
    admit.
  (*   fold_leibniz. unfold to_typemap in *. *)
  (*   destruct Hτ'; first by subst. *)
  (*   by rewrite -slevelS_included. *)
  (* Qed. *)
  Admitted.

  Lemma typemap_alloc f x τ l :
    f !! x = None →
    typemap_ctx f ==∗
    (typemap_ctx (<[x:=(τ,l)]>f) ∗ has_type x τ l).
  Proof.
    rewrite /typemap_ctx /to_typemap /has_type.
    iIntros (Hl) "H".
    rewrite -own_op. iApply (own_update with "H").
    apply auth_update_alloc.
    rewrite fmap_insert /=.
    eapply (alloc_singleton_local_update (to_typemap f : typemapUR A) x).
    { rewrite /to_typemap lookup_fmap Hl //. }
    done.
  Qed.

End logic.
