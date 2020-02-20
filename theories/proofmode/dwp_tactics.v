From iris_ni.program_logic Require Import dwp heap_lang_lifting.
From iris.proofmode Require Import
     environments coq_tactics tactics intro_patterns.
From iris.base_logic Require Import cancelable_invariants.
From iris.heap_lang Require Import tactics proofmode.

Lemma tac_dwp_bind `{!heapDG Σ} K1 K2 Δ E Φ e1 e2 f1 f2 :
  f1 = (λ e, fill K1 e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  f2 = (λ e, fill K2 e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (dwp E e1 e2 (λ v1 v2, dwp E (f1 (Val v1)) (f2 (Val v2)) Φ))%I →
  envs_entails Δ (dwp E (fill K1 e1) (fill K2 e2) Φ).

Proof. rewrite envs_entails_eq=> -> -> ->. by apply: dwp_bind. Qed.

Lemma tac_dwp_pure `{!heapDG Σ} Δ Δ' E e1 e2 e1' e2' φ1 φ2 n Φ :
  PureExec φ1 n e1 e1' →
  PureExec φ2 n e2 e2' →
  φ1 →
  φ2 →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (dwp E e1' e2' Φ) →
  envs_entails Δ (dwp E e1 e2 Φ).
Proof.
  rewrite envs_entails_eq=> ????? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ' -dwp_pure_step_later //.
Qed.

Ltac dwp_finish :=
  reduction.pm_prettify.

Ltac dwp_bind_core K1 K2 :=
  match eval hnf in K1 with
  | [] => lazymatch eval hnf in K2 with
          | [] => idtac
          | _ => fail
          end
  | _ => eapply (tac_dwp_bind K1 K2); [simpl; reflexivity|simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "dwp_bind" open_constr(efoc1) open_constr(efoc2) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (dwp ?E ?e1 ?e2 ?Q) =>
    reshape_expr e1 ltac:(fun K1 e1' =>
      unify e1' efoc1;
      reshape_expr e2 ltac:(fun K2 e2' =>
        unify e2' efoc2;
        dwp_bind_core K1 K2))
    || fail "dwp_bind: cannot find" efoc1 efoc2
  | _ => fail "dwp_bind: not a 'dwp'"
  end.

Tactic Notation "dwp_pure" open_constr(efoc1) open_constr(efoc2) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (dwp ?E ?e1 ?e2 ?Q) =>
    let e1 := eval simpl in e1 in
    let e2 := eval simpl in e2 in
    reshape_expr e1 ltac:(fun K1 e1' =>
      unify e1' efoc1;
      reshape_expr e2 ltac:(fun K2 e2' =>
        unify e2' efoc2;
        eapply (tac_dwp_pure _ _ _ (fill K1 e1') (fill K2 e2'));
        [iSolveTC                       (* PureExec *)
        |iSolveTC                       (* PureExec *)
        |try solve_vals_compare_safe    (* The pure condition for PureExec *)
        |try solve_vals_compare_safe    (* The pure condition for PureExec *)
        |iSolveTC                       (* IntoLaters *)
        |dwp_finish
        ]))
    || fail "dwp_pure: cannot find" efoc1 efoc2 "or they are not redexes"
  end.

Tactic Notation "dwp_rec" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  dwp_pure (App _ _) (App _ _); iSimpl;
  clear H.

Ltac dwp_pures :=
  iStartProof;
  repeat (dwp_pure _ _; [iSimpl]).
(* The `;[]` makes sure that no side-condition
   magically spawns. *)


(* iCinv tactic *)
Definition fmt_triple (P : ident) (b c : string) : intro_pat :=
  IList [[IIdent P; IList [[IIdent (INamed b); IIdent (INamed c)]]]].

Definition fmt_cinv_names (a b : string) : string := a ++ " " ++ b.

Tactic Notation "iCinv" constr(cinv1) constr(cinv2) "as"
       "(" simple_intropattern(x1) ")"
       constr(pat) constr(Hclose) :=
  let P := iFresh in
  let tmppat1 := eval vm_compute in (fmt_cinv_names cinv1 cinv2) in
  let tmppat2 := eval vm_compute in (fmt_triple P cinv2 Hclose) in
  iMod (cinv_acc with tmppat1) as tmppat2; first try solve_ndisj;
    last iDestruct P as (x1) pat.
