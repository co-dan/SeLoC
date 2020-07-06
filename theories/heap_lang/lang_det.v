(* heap_lang with deterministic allocation *)
From stdpp Require Import base gmap.
From iris.proofmode Require Import base tactics classes.
From iris.heap_lang Require Import lang primitive_laws.
From iris_ni.program_logic Require Import dwp heap_lang_lifting.

(** A simple allocator only knows about the state.
    In the future we can also make it aware of the threadpool.
*)
Module Type Allocator.
Parameter oracle : state -> Z -> loc.
Axiom oracle_fresh : ∀ σ n (i : Z), (0 ≤ i)%Z → (i < n)%Z → (heap σ) !! (oracle σ n +ₗ i) = None.
End Allocator.

Module SimpleAllocator : Allocator.
  Definition oracle σ (n : Z) := fresh_locs (dom (gset loc) σ.(heap)).
  Lemma oracle_fresh : ∀ σ n (i : Z), (0 ≤ i)%Z → (i < n)%Z → (heap σ) !! (oracle σ n +ₗ i) = None.
  Proof.
    intros σ n i Hi Hn. eapply (not_elem_of_dom (D:=gset loc)).
    by apply fresh_locs_fresh.
  Qed.
End SimpleAllocator.

Module heap_lang_det (A : Allocator).

Inductive head_step : expr → state → list observation → expr → state → list expr → Prop :=
  | RecS f x e σ :
     head_step (Rec f x e) σ [] (Val $ RecV f x e) σ []
  | PairS v1 v2 σ :
     head_step (Pair (Val v1) (Val v2)) σ [] (Val $ PairV v1 v2) σ []
  | InjLS v σ :
     head_step (InjL $ Val v) σ [] (Val $ InjLV v) σ []
  | InjRS v σ :
     head_step (InjR $ Val v) σ [] (Val $ InjRV v) σ []
  | BetaS f x e1 v2 e' σ :
     e' = subst' x v2 (subst' f (RecV f x e1) e1) →
     head_step (App (Val $ RecV f x e1) (Val v2)) σ [] e' σ []
  | UnOpS op v v' σ :
     un_op_eval op v = Some v' →
     head_step (UnOp op (Val v)) σ [] (Val v') σ []
  | BinOpS op v1 v2 v' σ :
     bin_op_eval op v1 v2 = Some v' →
     head_step (BinOp op (Val v1) (Val v2)) σ [] (Val v') σ []
  | IfTrueS e1 e2 σ :
     head_step (If (Val $ LitV $ LitBool true) e1 e2) σ [] e1 σ []
  | IfFalseS e1 e2 σ :
     head_step (If (Val $ LitV $ LitBool false) e1 e2) σ [] e2 σ []
  | FstS v1 v2 σ :
     head_step (Fst (Val $ PairV v1 v2)) σ [] (Val v1) σ []
  | SndS v1 v2 σ :
     head_step (Snd (Val $ PairV v1 v2)) σ [] (Val v2) σ []
  | CaseLS v e1 e2 σ :
     head_step (Case (Val $ InjLV v) e1 e2) σ [] (App e1 (Val v)) σ []
  | CaseRS v e1 e2 σ :
     head_step (Case (Val $ InjRV v) e1 e2) σ [] (App e2 (Val v)) σ []
  | ForkS e σ:
     head_step (Fork e) σ [] (Val $ LitV LitUnit) σ [e]
  | AllocNS n v σ :
      let l := A.oracle σ n in
     (0 < n)%Z →
     (∀ i, (0 ≤ i)%Z → (i < n)%Z → σ.(heap) !! (l +ₗ i) = None) →
     head_step (AllocN (Val $ LitV $ LitInt n) (Val v)) σ
               []
               (Val $ LitV $ LitLoc l) (state_init_heap l n v σ)
               []
  | FreeS l v σ :
     σ.(heap) !! l = Some $ Some v →
     head_step (Free (Val $ LitV $ LitLoc l)) σ
               []
               (Val $ LitV LitUnit) (state_upd_heap <[l:=None]> σ)
               []
  | LoadS l v σ :
     σ.(heap) !! l = Some $ Some v →
     head_step (Load (Val $ LitV $ LitLoc l)) σ [] (of_val v) σ []
  | StoreS l v0 v σ :
     σ.(heap) !! l = Some $ Some v0 →
     head_step (Store (Val $ LitV $ LitLoc l) (Val v)) σ
               []
               (Val $ LitV LitUnit) (state_upd_heap <[l:=Some v]> σ)
               []
  | CmpXchgS l v1 v2 vl σ b :
     σ.(heap) !! l = Some $ Some vl →
     (* Crucially, this compares the same way as [EqOp]! *)
     vals_compare_safe vl v1 →
     b = bool_decide (vl = v1) →
     head_step (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) σ
               []
               (Val $ PairV vl (LitV $ LitBool b)) (if b then state_upd_heap <[l:=Some v2]> σ else σ)
               []
  | FaaS l i1 i2 σ :
     σ.(heap) !! l = Some $ Some (LitV (LitInt i1)) →
     head_step (FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2)) σ
               []
               (Val $ LitV $ LitInt i1) (state_upd_heap <[l:=Some $ LitV (LitInt (i1 + i2))]>σ)
               []
  | NewProphS σ :
     let p := fresh σ.(used_proph_id) in
     head_step NewProph σ
               []
               (Val $ LitV $ LitProphecy p) (state_upd_used_proph_id ({[ p ]} ∪.) σ)
               []
  | ResolveS p v e σ w σ' κs ts :
     head_step e σ κs (Val v) σ' ts →
     head_step (Resolve e (Val $ LitV $ LitProphecy p) (Val w)) σ
               (κs ++ [(p, (v, w))]) (Val v) σ' ts.

Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ _ |- _ =>
     inversion H; subst; clear H
  end.

Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Extern 0 (head_reducible_no_obs _ _) => eexists _, _, _; simpl : core.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Local Hint Extern 1 (head_step _ _ _ _ _ _) => econstructor : core.
Local Hint Extern 0 (head_step (CmpXchg _ _ _) _ _ _ _ _) => eapply CmpXchgS : core.
Local Hint Extern 0 (head_step (AllocN _ _) _ _ _ _ _) => apply alloc_fresh : core.
Local Hint Extern 0 (head_step NewProph _ _ _ _ _) => apply new_proph_id_fresh : core.
Local Hint Resolve to_of_val : core.

(** The op sem is actually deterministic. *)
Theorem head_step_det e σ e'1 σ'1 obs1 efs1 e'2 σ'2 obs2 efs2 :
  head_step e σ obs1 e'1 σ'1 efs1 →
  head_step e σ obs2 e'2 σ'2 efs2 →
  obs1 = obs2 ∧ e'1 = e'2 ∧ σ'1 = σ'2 ∧ efs1 = efs2.
Proof.
  intros Hst1. revert obs2 e'2 σ'2 efs2.
  induction Hst1; intros obs2 e'2 σ'2 efs2;
    inversion 1; repeat simplify_map_eq/=; eauto.
  specialize (IHHst1 κs0 (Val v0) σ'2 efs2).
  assert (v = v0) as <-.
  { enough (Val v = Val v0); first by simplify_eq/=.
    by apply IHHst1. }
  repeat split; try f_equiv; eauto; by apply IHHst1.
Qed.

(** Basic properties *)
Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.

Lemma val_head_stuck e1 σ1 κ e2 σ2 efs : head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 efs :
  head_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
Proof. revert κ e2. induction Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof. revert Ki1. induction Ki2, Ki1; naive_solver eauto with f_equal. Qed.


Lemma heap_lang_det_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
Qed.

Canonical Structure heap_ectxi_lang_det := EctxiLanguage heap_lang_det_mixin.
Canonical Structure heap_ectx_lang_det := EctxLanguageOfEctxi heap_ectxi_lang_det.
Canonical Structure heap_lang_det := LanguageOfEctx heap_ectx_lang_det.


(** Different relations between the deterministic and non-deterministic semantics *)

Lemma head_step_det_nondet e σ e' σ' κs efs :
  head_step e σ κs e' σ' efs →
  heap_lang.head_step e σ κs e' σ' efs.
Proof.
  induction 1; try econstructor; eauto.
  - unfold p. apply is_fresh.
Qed.

Lemma prim_step_det_nondet e σ e' σ' κs efs :
  prim_step (Λ := heap_ectx_lang_det) e σ κs e' σ' efs →
  prim_step (Λ := heap_ectx_lang) e σ κs e' σ' efs.
Proof.
  inversion 1. subst. econstructor; try done. by apply head_step_det_nondet.
Qed.

Lemma head_step_nondet_det_val e v σ σ' κs efs e2 σ'2 κs2 efs2 :
  heap_lang.head_step e σ κs (Val v) σ' efs →
  head_step e σ κs2 e2 σ'2 efs2 →
  is_Some (to_val e2).
Proof.
  intros Hst_nondet Hst_det.
  inversion Hst_nondet; inversion Hst_det; simplify_eq/=; eauto.
  exists v. rewrite -H. eauto.
Qed.

Lemma head_reducible_nondet_det e σ :
  head_reducible (Λ := heap_ectx_lang) e σ →
  head_reducible (Λ := heap_ectx_lang_det) e σ.
Proof.
  destruct 1 as (κs&e2&σ2&efs&H).
  induction H; try by (do 4 eexists; econstructor; eauto).
  - repeat econstructor; eauto=> i Hi Hn.
    by apply A.oracle_fresh.
  - destruct IHhead_step as (κs2&e2&σ2&efs2&Hst_det). simpl in *.
    assert (is_Some (to_val e2)) as [v2 Hv2].
    { by eapply head_step_nondet_det_val. }
    repeat econstructor.
    rewrite -(of_to_val _ _ Hv2) in Hst_det. done.
Qed.

Lemma reducible_det_nondet e σ :
  reducible (Λ := heap_lang_det) e σ →
  reducible (Λ := heap_lang) e σ.
Proof.
  destruct 1 as (κs & e' & σ' & efs & H).
  inversion H. simpl in *. subst e e'.
  do 4 eexists. econstructor; try naive_solver.
  by apply head_step_det_nondet.
Qed.

Lemma reducible_nondet_det e σ :
  reducible (Λ := heap_lang) e σ →
  reducible (Λ := heap_lang_det) e σ.
Proof.
  destruct 1 as (κs & e' & σ' & efs & H).
  inversion H. simpl in *. subst e e'.
  apply (@head_prim_fill_reducible heap_ectxi_lang_det).
  apply head_reducible_nondet_det.
  by repeat eexists.
Qed.

Lemma head_step_nondet_det_obs e1 σ1 e2 σ2 efs e2' σ2' efs' κ :
  heap_lang.head_step e1 σ1 [] e2 σ2 efs →
  head_step e1 σ1 κ e2' σ2' efs' →
  κ = [].
Proof.
  intros Hst1 Hst2.
  inversion Hst2; try by eauto.
  simpl in * ; subst.
  inversion Hst1. exfalso.
  by eapply app_cons_not_nil.
Qed.

Lemma head_reducible_no_obs_nondet_det e σ :
  head_reducible_no_obs (Λ := heap_ectx_lang) e σ →
  head_reducible_no_obs (Λ := heap_ectx_lang_det) e σ.
Proof.
  destruct 1 as (e'&σ'&efs&Hst).
  assert (head_reducible (Λ := heap_ectx_lang_det) e σ) as Hred2.
  { apply head_reducible_nondet_det. eauto. }
  destruct Hred2 as (κ&e''&σ''&efs''&Hst2).
  assert (κ = []) as ->.
  { eapply head_step_nondet_det_obs; eauto. }
  eauto.
Qed.

Lemma reducible_no_obs_nondet_det e σ :
  reducible_no_obs (Λ := heap_lang) e σ →
  reducible_no_obs (Λ := heap_lang_det) e σ.
Proof.
  destruct 1 as (e' & σ' & efs & H).
  inversion H. simpl in *. subst e e'.
  apply (@head_prim_fill_reducible_no_obs heap_ectxi_lang_det).
  apply head_reducible_no_obs_nondet_det.
  by repeat eexists.
Qed.

Section lifting.

Instance heapG_irisG_det `{!heapG Σ} : irisG heap_lang_det Σ := {
  iris_invG := heapG_invG;
  state_interp σ κs _ :=
    (gen_heap_ctx σ.(heap) ∗ proph_map_ctx κs σ.(used_proph_id))%I;
  fork_post _ := True%I;
}.


Context `{!heapG Σ}.
Implicit Types Φ Ψ : val → iProp Σ.

Lemma wp_simul e E Φ :
  (wp (Λ := heap_lang) NotStuck E e Φ) -∗
  (wp (Λ := heap_lang_det) NotStuck E e Φ).
Proof.
  iLöb as "IH" forall (e E Φ).
  rewrite !wp_unfold /wp_pre /=.
  destruct (to_val e) as [v|]; first by eauto.
  iIntros "H". iIntros (σ1 κ κs n) "[Hσ Hp]".
  iMod ("H" $! σ1 κ κs n with "[$Hσ $Hp]") as "[% H]".
  iModIntro. iSplitR.
  { iPureIntro. by apply reducible_nondet_det. }
  iIntros (e2 σ2 efs Hst_det).
  iSpecialize ("H" $! e2 σ2 efs with "[%]").
  { by apply prim_step_det_nondet. }
  iMod "H" as "H". iModIntro. iNext.
  iMod "H" as "($&HWP&Hefs)". iModIntro.
  iSplitL "HWP".
  - by iApply "IH".
  - iApply (big_sepL_impl with "Hefs []").
    iAlways. iIntros (???). iApply "IH".
Qed.
End lifting.

Section dwp_lifting.

Instance heapDG_irisDG_det `{heapDG Σ} : irisDG heap_lang_det Σ := {
  state_rel := (λ σ1 σ2 κs1 κs2,
      @gen_heap_ctx _ _ _ _ _ heapDG_gen_heapG1 σ1.(heap)
    ∗ @proph_map_ctx _ _ _ _ _ heapDG_proph_mapG1 κs1 σ1.(used_proph_id)
    ∗ @gen_heap_ctx _ _ _ _ _ heapDG_gen_heapG2 σ2.(heap)
    ∗ @proph_map_ctx _ _ _ _ _ heapDG_proph_mapG2 κs2 σ2.(used_proph_id))%I
}.

Context `{!heapDG Σ}.

Lemma dwp_simul e1 e2 E Φ :
  (dwp (Λ := heap_lang) E e1 e2 Φ) -∗
  (dwp (Λ := heap_lang_det) E e1 e2 Φ).
Proof.
  iLöb as "IH" forall (e1 e2 E Φ).
  rewrite !dwp_unfold /dwp_pre /=.
  repeat case_match; [by eauto with iFrame..|].
  iIntros "H". iIntros (σ1 σ2 κ1 κs1 κ2 κs2) "(Hσ1 & Hp1 & Hσ2 & Hp2)".
  iMod ("H" with "[$Hσ1 $Hp1 $Hσ2 $Hp2]") as "[% [% H]]".
  iModIntro. iSplitR.
  { iPureIntro. by apply reducible_no_obs_nondet_det. }
  iSplitR.
  { iPureIntro. by apply reducible_no_obs_nondet_det. }
  iIntros (e1' σ1' efs1 e2' σ2' efs2 Hst_det1 Hst_det2).
  iSpecialize ("H" $! e1' σ1' efs1 e2' σ2' efs2 with "[%] [%]").
  { by apply prim_step_det_nondet. }
  { by apply prim_step_det_nondet. }
  iMod "H" as "H". iModIntro.
  iNext. iMod "H" as "H". iModIntro.
  iDestruct "H" as "($&HWP&Hefs)".
  iSplitL "HWP".
  - by iApply "IH".
  - iApply (big_sepL2_impl with "Hefs []").
    iAlways. iIntros (?????). iApply "IH".
Qed.

End dwp_lifting.


End heap_lang_det.

