From iris.program_logic Require Import language ectx_language.
From iris.heap_lang Require Export lang lifting notation.

Class NoFork (e1 : expr) :=
  nofork : (∀ σ1 κ σ1' e1' efs, prim_step e1 σ1 κ e1' σ1' efs → efs = []).

Class NoObs (e1 : expr) :=
  noobs : (∀ σ1 κ σ1' e1' efs, prim_step e1 σ1 κ e1' σ1' efs → κ = []).

Instance app_nofork e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  NoFork (App e1 e2).
Proof. Admitted.

Instance unop_nofork op e v :
  IntoVal e v →
  NoFork (UnOp op e).
Proof. Admitted.

Instance binop_nofork op e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  NoFork (BinOp op e1 e2).
Proof. Admitted.

Instance if_nofork e v e1 e2 :
  IntoVal e v →
  NoFork (If e e1 e2).
Proof. Admitted.

Instance fst_nofork e v :
  IntoVal e v →
  NoFork (Fst e).
Proof. Admitted.

Instance snd_nofork e v :
  IntoVal e v →
  NoFork (Fst e).
Proof. Admitted.

Instance case_nofork e v e1 e2 :
  IntoVal e v →
  NoFork (Case e e1 e2).
Proof. Admitted.

Instance alloc_nofork e v :
  IntoVal e v →
  NoFork (ref e).
Proof. Admitted.

Instance load_nofork e v :
  IntoVal e v →
  NoFork (! e).
Proof.
  intros <-. rewrite /NoFork.
Admitted.

Instance store_nofork e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  NoFork (e1 <- e2).
Proof.
  intros <- <-. rewrite /NoFork.
Admitted.

Instance cmpxchg_nofork e1 e2 e3 v1 v2 v3 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  IntoVal e3 v3 →
  NoFork (CmpXchg e1 e2 e3).
Proof. Admitted.

Instance faa_nofork e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  NoFork (FAA e1 e2).
Proof. Admitted.

(* no obs *)
Instance app_noobs e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  NoObs (App e1 e2).
Proof. Admitted.

Instance unop_noobs op e v :
  IntoVal e v →
  NoObs (UnOp op e).
Proof. Admitted.

Instance binop_noobs op e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  NoObs (BinOp op e1 e2).
Proof. Admitted.

Instance if_noobs e v e1 e2 :
  IntoVal e v →
  NoObs (If e e1 e2).
Proof. Admitted.

Instance fst_noobs e v :
  IntoVal e v →
  NoObs (Fst e).
Proof. Admitted.

Instance snd_noobs e v :
  IntoVal e v →
  NoObs (Fst e).
Proof. Admitted.

Instance case_noobs e v e1 e2 :
  IntoVal e v →
  NoObs (Case e e1 e2).
Proof. Admitted.

Instance alloc_noobs e v :
  IntoVal e v →
  NoObs (ref e).
Proof. Admitted.

Instance load_noobs e v :
  IntoVal e v →
  NoObs (! e).
Proof.
  intros <-. rewrite /NoObs.
Admitted.

Instance store_noobs e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  NoObs (e1 <- e2).
Proof.
  intros <- <-. rewrite /NoObs.
Admitted.

Instance cmpxchg_noobs e1 e2 e3 v1 v2 v3 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  IntoVal e3 v3 →
  NoObs (CmpXchg e1 e2 e3).
Proof. Admitted.

Instance faa_noobs e1 e2 v1 v2 :
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  NoObs (FAA e1 e2).
Proof. Admitted.

