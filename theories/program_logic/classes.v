From iris.program_logic Require Import language ectx_language.
From iris.heap_lang Require Export lang lifting notation.

(* DF: Basically, this file contains /a lot/ of boilerplate.
   For some DWP lemmas we want to easily discharge the side conditions:
   - An expression does not fork off any threads.
   - An expression does not produce observations/traces in op. sem.

For instance, `App v1 v2` satisfies such side conditions.
To show this we need to establish that if you evaluating `App v1 v2` in a thread
pool does not increase the number of threads. Due to the way the reduction relation
is defined we need to show the auxiliary lemma: `App v1 v2` has only one possible
evaluation context that can trigger the reduction.
*)

Class NotVal (e : expr) :=
  not_val : to_val e = None.

Hint Extern 1 (NotVal _) => fast_done : typeclass_instances.

Class NoFork (e1 : expr) :=
  nofork : (∀ σ1 κ σ1' e1' efs, prim_step e1 σ1 κ e1' σ1' efs → efs = []).

Class NoObs (e1 : expr) :=
  noobs : (∀ σ1 κ σ1' e1' efs, prim_step e1 σ1 κ e1' σ1' efs → κ = []).

(* We use this to prove lemmas like app_fill:

    App v1 v2 = fill K e →
    is_Some (to_val e) ∨ K = [].
*)
Ltac solve_fill e K fill_item_lemma :=
  let IHK := fresh "IHK" in
  revert e; induction K as [|Ki K IHK]=>e; simpl; first eauto;
  intros Hvv; left;
  destruct (IHK _ Hvv) as [Heval | ->];
  [ eapply fill_item_val; eauto
  | eapply fill_item_lemma; eauto ].

(* `fill_lemma` is a lemma a-la `app_fill` below, which is solved
using the `solve_fill` tactic *)
Ltac solve_nofork fill_lemma :=
  repeat (intros <-);   (* introduce the IntoVals *)
  intros σ1 κ σ1' e1' efs Hstep;
  destruct Hstep as [K e1i e2i Hfill Hfill2 Headstep]; simplify_eq/=;
  let Hw := fresh "Hw" in
  match (type of fill_lemma) with
  | forall K _, _ -> _ =>
    destruct (fill_lemma K _ Hfill) as [[w Hw] | ->]
  | forall K _ _, _ -> _ =>
    destruct (fill_lemma K _ _ Hfill) as [[w Hw] | ->]
  | forall K _ _ _, _ -> _ =>
    destruct (fill_lemma K _ _ _ Hfill) as [[w Hw] | ->]
  | forall K _ _ _ _, _ -> _ =>
    destruct (fill_lemma K _ _ _ _ Hfill) as [[w Hw] | ->]
  end;
  [ (* the case when K ≠ [] but the contents of the hole is a value *)
    exfalso;
    apply of_to_val in Hw; simplify_eq;
    apply val_head_stuck in Headstep; naive_solver
  | (* the case when K = [] *)
    simplify_eq/=; inversion Headstep; eauto ].

Lemma app_fill_item Ki (v1 v2 : val) e :
  App v1 v2 = fill_item Ki e →
  is_Some (to_val e).
Proof. destruct Ki; simpl; inversion 1; eauto. Qed.

Lemma app_fill K (v1 v2 : val) e :
  App v1 v2 = fill K e →
  is_Some (to_val e) ∨ K = [].
Proof. solve_fill e K app_fill_item. Qed.

Instance app_nofork e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  NoFork (App e1 e2).
Proof. solve_nofork app_fill. Qed.

Lemma unop_fill_item Ki op (v : val) e :
  UnOp op v = fill_item Ki e →
  is_Some (to_val e).
Proof. destruct Ki; simpl; inversion 1; eauto. Qed.

Lemma unop_fill K op (v : val) e :
  UnOp op v = fill K e →
  is_Some (to_val e) ∨ K = [].
Proof. solve_fill e K unop_fill_item. Qed.

Instance unop_nofork op e v :
  IntoVal e v →
  NoFork (UnOp op e).
Proof. solve_nofork unop_fill. Qed.

Lemma binop_fill_item Ki op (v1 v2 : val) e :
  BinOp op v1 v2 = fill_item Ki e →
  is_Some (to_val e).
Proof. destruct Ki; simpl; inversion 1; eauto. Qed.

Lemma binop_fill K op (v1 v2 : val) e :
  BinOp op v1 v2 = fill K e →
  is_Some (to_val e) ∨ K = [].
Proof. solve_fill e K binop_fill_item. Qed.

Instance binop_nofork op e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  NoFork (BinOp op e1 e2).
Proof. solve_nofork binop_fill. Qed.

Lemma if_fill_item Ki e1 e2 (v : val) e :
  If v e1 e2 = fill_item Ki e →
  is_Some (to_val e).
Proof. destruct Ki; simpl; inversion 1; eauto. Qed.

Lemma if_fill K e1 e2 (v : val) e :
  If v e1 e2 = fill K e →
  is_Some (to_val e) ∨ K = [].
Proof. solve_fill e K if_fill_item. Qed.

Instance if_nofork e v e1 e2 :
  IntoVal e v →
  NoFork (If e e1 e2).
Proof. solve_nofork if_fill. Qed.

Lemma fst_fill_item Ki (v : val) e :
  Fst v = fill_item Ki e →
  is_Some (to_val e).
Proof. destruct Ki; simpl; inversion 1; eauto. Qed.

Lemma fst_fill K (v : val) e :
  Fst v = fill K e →
  is_Some (to_val e) ∨ K = [].
Proof. solve_fill e K fst_fill_item. Qed.

Instance fst_nofork e v :
  IntoVal e v →
  NoFork (Fst e).
Proof. solve_nofork fst_fill. Qed.

Lemma snd_fill_item Ki (v : val) e :
  Snd v = fill_item Ki e →
  is_Some (to_val e).
Proof. destruct Ki; simpl; inversion 1; eauto. Qed.

Lemma snd_fill K (v : val) e :
  Snd v = fill K e →
  is_Some (to_val e) ∨ K = [].
Proof. solve_fill e K snd_fill_item. Qed.

Instance snd_nofork e v :
  IntoVal e v →
  NoFork (Snd e).
Proof. solve_nofork snd_fill. Qed.

Lemma case_fill_item Ki e1 e2 (v : val) e :
  Case v e1 e2 = fill_item Ki e →
  is_Some (to_val e).
Proof. destruct Ki; simpl; inversion 1; eauto. Qed.

Lemma case_fill K e1 e2 (v : val) e :
  Case v e1 e2 = fill K e →
  is_Some (to_val e) ∨ K = [].
Proof. solve_fill e K case_fill_item. Qed.

Instance case_nofork e v e1 e2 :
  IntoVal e v →
  NoFork (Case e e1 e2).
Proof. solve_nofork case_fill. Qed.

Lemma alloc_fill_item Ki (v : val) e :
  Alloc v = fill_item Ki e →
  is_Some (to_val e).
Proof. destruct Ki; simpl; inversion 1; eauto. Qed.

Lemma alloc_fill K (v : val) e :
  Alloc v = fill K e →
  is_Some (to_val e) ∨ K = [].
Proof. solve_fill e K alloc_fill_item. Qed.

Instance alloc_nofork e v :
  IntoVal e v →
  NoFork (ref e).
Proof. solve_nofork alloc_fill. Qed.

Lemma allocn_fill_item Ki (v1 v2 : val) e :
  AllocN v1 v2 = fill_item Ki e →
  is_Some (to_val e).
Proof. destruct Ki; simpl; inversion 1; eauto. Qed.

Lemma allocn_fill K (v1 v2 : val) e :
  AllocN v1 v2 = fill K e →
  is_Some (to_val e) ∨ K = [].
Proof. solve_fill e K allocn_fill_item. Qed.

Instance allocn_nofork e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  NoFork (AllocN e1 e2).
Proof. solve_nofork allocn_fill. Qed.

Lemma load_fill_item Ki (v : val) e :
  Load v = fill_item Ki e →
  is_Some (to_val e).
Proof. destruct Ki; simpl; inversion 1; eauto. Qed.

Lemma load_fill K (v : val) e :
  Load v = fill K e →
  is_Some (to_val e) ∨ K = [].
Proof. solve_fill e K load_fill_item. Qed.

Instance load_nofork e v :
  IntoVal e v →
  NoFork (! e).
Proof. solve_nofork load_fill. Qed.

Lemma store_fill_item Ki (v1 v2 : val) e :
  Store v1 v2 = fill_item Ki e →
  is_Some (to_val e).
Proof. destruct Ki; simpl; inversion 1; eauto. Qed.

Lemma store_fill K (v1 v2 : val) e :
  Store v1 v2 = fill K e →
  is_Some (to_val e) ∨ K = [].
Proof. solve_fill e K store_fill_item. Qed.

Instance store_nofork e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  NoFork (e1 <- e2).
Proof. solve_nofork store_fill. Qed.

Lemma cmpxchg_fill_item Ki (v1 v2 v3 : val) e :
  CmpXchg v1 v2 v3 = fill_item Ki e →
  is_Some (to_val e).
Proof. destruct Ki; simpl; inversion 1; eauto. Qed.

Lemma cmpxchg_fill K (v1 v2 v3 : val) e :
  CmpXchg v1 v2 v3 = fill K e →
  is_Some (to_val e) ∨ K = [].
Proof. solve_fill e K cmpxchg_fill_item. Qed.

Instance cmpxchg_nofork e1 e2 e3 v1 v2 v3 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  IntoVal e3 v3 →
  NoFork (CmpXchg e1 e2 e3).
Proof. solve_nofork cmpxchg_fill. Qed.

Lemma faa_fill_item Ki (v1 v2 : val) e :
  FAA v1 v2 = fill_item Ki e →
  is_Some (to_val e).
Proof. destruct Ki; simpl; inversion 1; eauto. Qed.

Lemma faa_fill K (v1 v2 : val) e :
  FAA v1 v2 = fill K e →
  is_Some (to_val e) ∨ K = [].
Proof. solve_fill e K faa_fill_item. Qed.

Instance faa_nofork e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  NoFork (FAA e1 e2).
Proof. solve_nofork faa_fill. Qed.

(* no obs *)
Instance app_noobs e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  NoObs (App e1 e2).
Proof. solve_nofork app_fill. Qed.

Instance unop_noobs op e v :
  IntoVal e v →
  NoObs (UnOp op e).
Proof. solve_nofork unop_fill. Qed.

Instance binop_noobs op e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  NoObs (BinOp op e1 e2).
Proof. solve_nofork binop_fill. Qed.

Instance if_noobs e v e1 e2 :
  IntoVal e v →
  NoObs (If e e1 e2).
Proof. solve_nofork if_fill. Qed.

Instance fst_noobs e v :
  IntoVal e v →
  NoObs (Fst e).
Proof. solve_nofork fst_fill. Qed.

Instance snd_noobs e v :
  IntoVal e v →
  NoObs (Snd e).
Proof. solve_nofork snd_fill. Qed.

Instance case_noobs e v e1 e2 :
  IntoVal e v →
  NoObs (Case e e1 e2).
Proof. solve_nofork case_fill. Qed.

Instance alloc_noobs e v :
  IntoVal e v →
  NoObs (ref e).
Proof. solve_nofork alloc_fill. Qed.

Instance allocn_noobs e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  NoObs (AllocN e1 e2).
Proof. solve_nofork allocn_fill. Qed.

Instance load_noobs e v :
  IntoVal e v →
  NoObs (! e).
Proof. solve_nofork load_fill. Qed.

Instance store_noobs e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  NoObs (e1 <- e2).
Proof. solve_nofork store_fill. Qed.

Instance cmpxchg_noobs e1 e2 e3 v1 v2 v3 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  IntoVal e3 v3 →
  NoObs (CmpXchg e1 e2 e3).
Proof. solve_nofork cmpxchg_fill. Qed.

Instance faa_noobs e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  NoObs (FAA e1 e2).
Proof. solve_nofork faa_fill. Qed.


