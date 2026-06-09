From stdpp Require Import fin_maps.
From iris_simp_lang Require Import lang.
From iris.prelude Require Import options.

(*|
This file implements some low-level tactics used to implement simp_lang.
`reshape_expr` is used to implement the proofmode support (especially tactics
like `wp_bind` and `wp_pure`) while `inv_base_step` is convenient automation for
proving typeclass instances that describe simp_lang's reduction rules.
|*)

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  let rec go K e :=
    match e with
    | _                          => tac K e
    | App ?e (Val ?v)            => add_item (AppLCtx v) K e
    | App ?e1 ?e2                => add_item (AppRCtx e1) K e2
    | Pair ?e (Val ?v)           => add_item (PairLCtx v) K e
    | Pair ?e1 ?e2               => add_item (PairRCtx e1) K e2
    | Fst ?e                     => add_item FstCtx K e
    | Snd ?e                     => add_item SndCtx K e
    | InjL ?e                    => add_item InjLCtx K e
    | InjR ?e                    => add_item InjRCtx K e
    | Case ?e ?x1 ?e1 ?x2 ?e2    => add_item (CaseCtx x1 e1 x2 e2) K e
    | Alloc ?r ?e                => add_item (AllocCtx r) K e
    | Load ?e                    => add_item LoadCtx K e
    | Store ?e (Val ?v)          => add_item (StoreLCtx v) K e
    | Store ?e1 ?e2              => add_item (StoreRCtx e1) K e2
    | EndRegion ?ρ ?e            => add_item (EndRegionCtx ρ) K e
    end
  with add_item Ki K e := go (Ki :: K) e
  in go (@nil ectx_item) e.
  
(** The tactic [inv_base_step] performs inversion on hypotheses of the shape
[base_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_base_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/=
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : base_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1);
     inversion H; subst; clear H
  end.
