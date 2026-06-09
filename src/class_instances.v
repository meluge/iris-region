From stdpp Require Import fin_maps.
From iris.program_logic Require Import ectx_language ectxi_language language.
From iris_simp_lang Require Import tactics.   (* inv_base_step *)
From iris_simp_lang Require Import lang.
From iris.prelude Require Import options.

(*|
These instances prove that various expressions are atomic or pure.

`Atomic e` is defined generically for languages by saying `e` reduces to a value
(recall: this is defined by `to_val e = Some _`) in a single step.

`PureExec φ n e1 e2` shows that if φ holds (a pure Coq proposition), `e1`
executes to `e2` in `n` steps. This is eventually needed to define a tactic
`wp_pure _` that finds and reasons about pure reductions (this subsumes
`wp_let`, `wp_seq`, `wp_app` and the like, which are just restrictions of
`wp_pure`).
|*)

Global Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
Global Instance as_val_val v : AsVal (Val v).
Proof. by eexists. Qed.

Section atomic.
  Local Ltac solve_atomic :=
    apply strongly_atomic_atomic, ectx_language_atomic;
      [inversion 1; naive_solver
      |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

  Global Instance rec_atomic s f x e : Atomic s (Rec f x e).
  Proof. solve_atomic. Qed.
  Global Instance beta_atomic s f x v1 v2 :
    Atomic s (App (Val (RecV f x (Val v1))) (Val v2)).
  Proof. destruct f, x; solve_atomic. Qed.

  Global Instance pair_atomic s v1 v2 : Atomic s (Pair (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance fst_atomic s v : Atomic s (Fst (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance snd_atomic s v : Atomic s (Snd (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance injl_atomic s v : Atomic s (InjL (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance injr_atomic s v : Atomic s (InjR (Val v)).
  Proof. solve_atomic. Qed.


  Global Instance alloc_atomic s ρ v : Atomic s (Alloc (RName ρ) (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance load_atomic s v : Atomic s (Load (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance store_atomic s v1 v2 : Atomic s (Store (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance endregion_atomic s ρ v : Atomic s (EndRegion ρ (Val v)).
  Proof. solve_atomic. Qed.
End atomic.

(** * Instances of the [PureExec] class *)
(** The behavior of the various [wp_] tactics with regard to lambda differs in
the following way:

- [wp_pures] does *not* reduce lambdas/recs that are hidden behind a definition.
- [wp_rec] and [wp_lam] reduce lambdas/recs that are hidden behind a definition.

To realize this behavior, we define the class [AsRecV v f x erec], which takes a
value [v] as its input, and turns it into a [RecV f x erec] via the instance
[AsRecV_recv : AsRecV (RecV f x e) f x e]. We register this instance via
[Hint Extern] so that it is only used if [v] is syntactically a lambda/rec, and
not if [v] contains a lambda/rec that is hidden behind a definition.

To make sure that [wp_rec] and [wp_lam] do reduce lambdas/recs that are hidden
behind a definition, we activate [AsRecV_recv] by hand in these tactics. *)

Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Global Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Global Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Section pure_exec.
  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_base_step.
  Local Ltac solve_pure_exec :=
    subst; intros ?; apply nsteps_once, pure_base_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].

  Global Instance pure_recc f x (erec : expr) :
    PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
    PureExec True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
  Proof. unfold AsRecV in *. solve_pure_exec. Qed.

  Global Instance pure_pair (v1 v2 : val) :
    PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_fst (v1 v2 : val) :
    PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_snd (v1 v2 : val) :
    PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_injl (v : val) :
    PureExec True 1 (InjL (Val v)) (Val $ InjLV v).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_injr (v : val) :
    PureExec True 1 (InjR (Val v)) (Val $ InjRV v).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inl (v : val) x1 e1 x2 e2 :
    PureExec True 1 (Case (Val $ InjLV v) x1 e1 x2 e2) (subst' x1 v e1).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_case_inr (v : val) x1 e1 x2 e2 :
    PureExec True 1 (Case (Val $ InjRV v) x1 e1 x2 e2) (subst' x2 v e2).
  Proof. solve_pure_exec. Qed.
End pure_exec.
