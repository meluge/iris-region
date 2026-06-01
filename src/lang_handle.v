From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.prelude Require Import options.
Open Scope Z.

(*|
=====================================
reghandle_lang
=====================================

This is the **handle** model of RegLang, kept alongside the primary annotation
model [lang.v] for comparison: regions are first-class *values* [RegionV ρ],
`region` binds an ordinary term variable that is substituted with such a handle,
and `alloc er e` takes the region as an evaluated operand. The corresponding type
system is [typing_handle.v]. 

===========
Syntax
===========

We will be careful to minimize the recursive structure of `expr` to make some
administrative stuff later on simpler. For example we group plus, equals, and
pair into a single `expr` constructor that takes two expressions.
|*)

Definition loc := Z.
Definition region := Z.

(*|
Expressions are defined mutually recursively with values. As explained above, an
expression is a value iff it uses the Val constructor, which makes defining
reduction and substitution much simpler, but requires duplicating `Rec` and
`Pair` to `val` as `RecV` and `PairV`.
|*)

Inductive expr :=
  (* Values *)
  | Val (v : val)
  (* Base lambda calculus *)
  | Var (x : string)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (x1 : binder) (e1 : expr) (x2 : binder) (e2 : expr)
  (* Regions and references *)
  | Alloc (e1 : expr) (e2 : expr)     (* alloc INTO region [e1] the value [e2] *)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
  | Region (x : binder) (e : expr)    (* region: x in e *)
  | EndRegion (ρ : region) (e : expr) (* runtime only: deallocates [ρ] when [e] is a value *)
with val :=
  | UnitV
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
  | RecV (f x : binder) (e : expr)
  | RegionV (ρ : region)              (* a region handle *)
  | RefV (ρ : region) (l : loc)       (* a reference (ρ, ℓ) *)
.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

(*|
These define part of ectxi_language: we need a type for expressions, a type for
values, and a way to go back and forth (where to_val is partial because only
some expressions are values). Here the use of Val to identify all values makes
this easy and non-recursive.
|*)

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

(*|
We will now do a bunch of boring work to prove that expressions have decidable
equality and are countable for technical reasons.
|*)

Lemma expr_eq_dec (e1 e2 : expr) : Decision (e1 = e2)
with val_eq_dec (v1 v2 : val) : Decision (v1 = v2).
Proof.
  { refine
      (match e1, e2 with
       | Val v, Val v' => cast_if (decide (v = v'))
       | Var x, Var x' => cast_if (decide (x = x'))
       | Rec f x e, Rec f' x' e' =>
         cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
       | App e1 e2, App e1' e2' =>
         cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
       | Pair e1 e2, Pair e1' e2' =>
         cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
       | Fst e, Fst e' => cast_if (decide (e = e'))
       | Snd e, Snd e' => cast_if (decide (e = e'))
       | InjL e, InjL e' => cast_if (decide (e = e'))
       | InjR e, InjR e' => cast_if (decide (e = e'))
       | Case e0 x1 e1 x2 e2, Case e0' x1' e1' x2' e2' =>
         cast_if_and5 (decide (e0 = e0')) (decide (x1 = x1')) (decide (e1 = e1'))
                      (decide (x2 = x2')) (decide (e2 = e2'))
       | Alloc e1 e2, Alloc e1' e2' =>
         cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
       | Load e, Load e' => cast_if (decide (e = e'))
       | Store e1 e2, Store e1' e2' =>
         cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
       | Region x e, Region x' e' =>
         cast_if_and (decide (x = x')) (decide (e = e'))
       | EndRegion ρ e, EndRegion ρ' e' =>
         cast_if_and (decide (ρ = ρ')) (decide (e = e'))
       | _, _ => right _
       end); solve [ abstract intuition congruence ]. }
  { refine
      (match v1, v2 with
       | UnitV, UnitV => left _
       | PairV v1 v2, PairV v1' v2' =>
         cast_if_and (decide (v1 = v1')) (decide (v2 = v2'))
       | InjLV v, InjLV v' => cast_if (decide (v = v'))
       | InjRV v, InjRV v' => cast_if (decide (v = v'))
       | RecV f x e, RecV f' x' e' =>
         cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
       | RegionV ρ, RegionV ρ' => cast_if (decide (ρ = ρ'))
       | RefV ρ l, RefV ρ' l' =>
         cast_if_and (decide (ρ = ρ')) (decide (l = l'))
       | _, _ => right _
       end); try solve [ abstract intuition congruence ]. }
Defined.
Global Instance expr_eq_dec' : EqDecision expr := expr_eq_dec.
Global Instance val_eq_dec' : EqDecision val := val_eq_dec.

Global Instance expr_countable : Countable expr.
Proof.
 set (enc :=
   fix go e :=
     match e with
     | Val v => GenNode 0 [gov v]
     | Var x => GenLeaf (inl (inl x))
     | Rec f x e => GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
     | App e1 e2 => GenNode 2 [go e1; go e2]
     | Pair e1 e2 => GenNode 3 [go e1; go e2]
     | Fst e => GenNode 4 [go e]
     | Snd e => GenNode 5 [go e]
     | InjL e => GenNode 6 [go e]
     | InjR e => GenNode 7 [go e]
     | Case e0 x1 e1 x2 e2 =>
        GenNode 8 [go e0; GenLeaf (inl (inr x1)); go e1; GenLeaf (inl (inr x2)); go e2]
     | Alloc e1 e2 => GenNode 9 [go e1; go e2]
     | Load e => GenNode 10 [go e]
     | Store e1 e2 => GenNode 11 [go e1; go e2]
     | Region x e => GenNode 12 [GenLeaf (inl (inr x)); go e]
     | EndRegion ρ e => GenNode 13 [GenLeaf (inr (inl ρ)); go e]
     end
   with gov v :=
     match v with
     | UnitV => GenNode 0 []
     | PairV v1 v2 => GenNode 1 [gov v1; gov v2]
     | InjLV v => GenNode 2 [gov v]
     | InjRV v => GenNode 3 [gov v]
     | RecV f x e =>
        GenNode 4 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
     | RegionV ρ => GenNode 5 [GenLeaf (inr (inl ρ))]
     | RefV ρ l => GenNode 6 [GenLeaf (inr (inl ρ)); GenLeaf (inr (inr l))]
     end
   for go).
 set (dec :=
   fix go e :=
     match e with
     | GenNode 0 [v] => Val (gov v)
     | GenLeaf (inl (inl x)) => Var x
     | GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => Rec f x (go e)
     | GenNode 2 [e1; e2] => App (go e1) (go e2)
     | GenNode 3 [e1; e2] => Pair (go e1) (go e2)
     | GenNode 4 [e] => Fst (go e)
     | GenNode 5 [e] => Snd (go e)
     | GenNode 6 [e] => InjL (go e)
     | GenNode 7 [e] => InjR (go e)
     | GenNode 8 [e0; GenLeaf (inl (inr x1)); e1; GenLeaf (inl (inr x2)); e2] =>
        Case (go e0) x1 (go e1) x2 (go e2)
     | GenNode 9 [e1; e2] => Alloc (go e1) (go e2)
     | GenNode 10 [e] => Load (go e)
     | GenNode 11 [e1; e2] => Store (go e1) (go e2)
     | GenNode 12 [GenLeaf (inl (inr x)); e] => Region x (go e)
     | GenNode 13 [GenLeaf (inr (inl ρ)); e] => EndRegion ρ (go e)
     | _ => Val UnitV (* dummy *)
     end
   with gov v :=
     match v with
     | GenNode 0 [] => UnitV
     | GenNode 1 [v1; v2] => PairV (gov v1) (gov v2)
     | GenNode 2 [v] => InjLV (gov v)
     | GenNode 3 [v] => InjRV (gov v)
     | GenNode 4 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => RecV f x (go e)
     | GenNode 5 [GenLeaf (inr (inl ρ))] => RegionV ρ
     | GenNode 6 [GenLeaf (inr (inl ρ)); GenLeaf (inr (inr l))] => RefV ρ l
     | _ => UnitV (* dummy *)
     end
   for go).
 refine (inj_countable' enc dec _).
 refine (fix go (e : expr) {struct e} := _ with gov (v : val) {struct v} := _ for go).
 - destruct e as [v | | | | | | | | | | | | | |]; simpl; f_equal;
     [exact (gov v)|done..].
 - destruct v; by f_equal.
Qed.
Global Instance val_countable : Countable val.
Proof. refine (inj_countable of_val to_val _); auto using to_of_val. Qed.

(** the language interface needs values and expressions to be inhabited *)
Global Instance val_inhabited : Inhabited val := populate UnitV.
Global Instance expr_inhabited : Inhabited expr := populate (Val UnitV).



(** Evaluation contexts *)
Inductive ectx_item :=
  | AppLCtx (v2 : val)
  | AppRCtx (e1 : expr)
  | PairLCtx (v2 : val)
  | PairRCtx (e1 : expr)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (x1 : binder) (e1 : expr) (x2 : binder) (e2 : expr)
  | AllocLCtx (v2 : val)
  | AllocRCtx (e1 : expr)
  | LoadCtx
  | StoreLCtx (v2 : val)
  | StoreRCtx (e1 : expr)
  | EndRegionCtx (ρ : region)
.

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx v2 => App e (of_val v2)
  | AppRCtx e1 => App e1 e
  | PairLCtx v2 => Pair e (of_val v2)
  | PairRCtx e1 => Pair e1 e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | CaseCtx x1 e1 x2 e2 => Case e x1 e1 x2 e2
  | AllocLCtx v2 => Alloc e (of_val v2)
  | AllocRCtx e1 => Alloc e1 e
  | LoadCtx => Load e
  | StoreLCtx v2 => Store e (of_val v2)
  | StoreRCtx e1 => Store e1 e
  | EndRegionCtx ρ => EndRegion ρ e
  end.


(*|
We have to prove a few properties that show `fill_item` and `base_step` is
reasonable for `ectxi_language`.
|*)

Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof. destruct Ki1, Ki2; naive_solver eauto with f_equal. Qed.



(** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr) : expr :=
  match e with
  | Val _ => e
  | Var y => if decide (x = y) then Val v else Var y
  | Rec f y e =>
    Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
  | Fst e => Fst (subst x v e)
  | Snd e => Snd (subst x v e)
  | InjL e => InjL (subst x v e)
  | InjR e => InjR (subst x v e)
  | Case e0 x1 e1 x2 e2 =>
    Case (subst x v e0)
         x1 (if decide (BNamed x ≠ x1) then subst x v e1 else e1)
         x2 (if decide (BNamed x ≠ x2) then subst x v e2 else e2)
  | Alloc e1 e2 => Alloc (subst x v e1) (subst x v e2)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | Region y e =>
    Region y $ if decide (BNamed x ≠ y) then subst x v e else e
  | EndRegion ρ e => EndRegion ρ (subst x v e)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => id end.

(*|
===========
Semantics
===========

State
-----

|*)

Record state : Type := {
  heap : gmap (region * loc) val;
  alive : gmap region bool;
}.

Global Instance state_inhabited : Inhabited state :=
  populate {| heap := inhabitant; alive := inhabitant |}.

Definition state_upd_heap (f : gmap (region * loc) val → gmap (region * loc) val)
    (σ : state) : state :=
  {| heap := f σ.(heap); alive := σ.(alive) |}.
Global Arguments state_upd_heap _ !_ /.

Definition state_upd_alive (f : gmap region bool → gmap region bool)
    (σ : state) : state :=
  {| heap := σ.(heap); alive := f σ.(alive) |}.
Global Arguments state_upd_alive _ !_ /.



Inductive observation :=.
Lemma observations_empty (κs : list observation) : κs = [].
Proof. by destruct κs as [ | [] ]. Qed.


Inductive base_step :
    expr → state → list observation → expr → state → list expr → Prop :=
  | RecS f x e σ :
    base_step (Rec f x e) σ [] (Val $ RecV f x e) σ []
  | BetaS f x e1 v2 e' σ :
    e' = subst' x v2 (subst' f (RecV f x e1) e1) →
    base_step (App (Val $ RecV f x e1) (Val v2)) σ [] e' σ []
  | PairS v1 v2 σ :
    base_step (Pair (Val v1) (Val v2)) σ [] (Val $ PairV v1 v2) σ []
  | FstS v1 v2 σ :
    base_step (Fst (Val $ PairV v1 v2)) σ [] (Val v1) σ []
  | SndS v1 v2 σ :
    base_step (Snd (Val $ PairV v1 v2)) σ [] (Val v2) σ []
  | InjLS v σ :
    base_step (InjL (Val v)) σ [] (Val $ InjLV v) σ []
  | InjRS v σ :
    base_step (InjR (Val v)) σ [] (Val $ InjRV v) σ []
  | CaseLS v x1 e1 x2 e2 σ :
    base_step (Case (Val $ InjLV v) x1 e1 x2 e2) σ [] (subst' x1 v e1) σ []
  | CaseRS v x1 e1 x2 e2 σ :
    base_step (Case (Val $ InjRV v) x1 e1 x2 e2) σ [] (subst' x2 v e2) σ []
  | RegionS x e ρ σ :
    σ.(alive) !! ρ = None →
    base_step (Region x e) σ
              []
              (EndRegion ρ (subst' x (RegionV ρ) e))
              (state_upd_alive <[ρ := true]> σ)
              []
  | EndRegionS ρ v σ :
    σ.(alive) !! ρ = Some true →
    base_step (EndRegion ρ (Val v)) σ
              []
              (Val v) (state_upd_alive <[ρ := false]> σ)
              []
  | AllocS ρ l v σ :
    σ.(alive) !! ρ = Some true →
    σ.(heap) !! (ρ, l) = None →
    base_step (Alloc (Val $ RegionV ρ) (Val v)) σ
              []
              (Val $ RefV ρ l) (state_upd_heap <[(ρ, l) := v]> σ)
              []
  | LoadS ρ l v σ :
    σ.(alive) !! ρ = Some true →
    σ.(heap) !! (ρ, l) = Some v →
    base_step (Load (Val $ RefV ρ l)) σ
              []
              (Val v) σ
              []
  | StoreS ρ l v w σ :
    σ.(alive) !! ρ = Some true →
    σ.(heap) !! (ρ, l) = Some v →
    base_step (Store (Val $ RefV ρ l) (Val w)) σ
              []
              (Val UnitV) (state_upd_heap <[(ρ, l) := w]> σ)
              []
  .


Lemma val_base_stuck e1 σ1 κ e2 σ2 efs : base_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma base_ctx_step_val Ki e σ1 κ e2 σ2 efs :
  base_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.



Lemma region_fresh σ : σ.(alive) !! fresh (dom σ.(alive)) = None.
Proof. apply not_elem_of_dom, is_fresh. Qed.

Lemma region_step_fresh x e σ :
  let ρ := fresh (dom σ.(alive)) in
  base_step (Region x e) σ []
            (EndRegion ρ (subst' x (RegionV ρ) e))
            (state_upd_alive <[ρ := true]> σ) [].
Proof. apply RegionS, region_fresh. Qed.

Definition heap_locs (h : gmap (region * loc) val) : gset loc :=
  set_map snd (dom h).

Lemma heap_loc_fresh ρ h : h !! (ρ, fresh (heap_locs h)) = None.
Proof.
  apply not_elem_of_dom. intros Hin.
  apply (is_fresh (heap_locs h)).
  apply (elem_of_map_2 (D:=gset loc) snd (dom h) (ρ, fresh (heap_locs h)) Hin).
Qed.

Lemma alloc_fresh ρ v σ :
  let l := fresh (heap_locs σ.(heap)) in
  σ.(alive) !! ρ = Some true →
  base_step (Alloc (Val $ RegionV ρ) (Val v)) σ []
            (Val $ RefV ρ l) (state_upd_heap <[(ρ, l) := v]> σ) [].
Proof. intros l Halive. apply AllocS; [done|]. apply heap_loc_fresh. Qed.


Lemma reghandle_lang_mixin : EctxiLanguageMixin of_val to_val fill_item base_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_base_stuck,
    fill_item_val, fill_item_no_val_inj, base_ctx_step_val.
Qed.

Canonical Structure reghandle_ectxi_lang := EctxiLanguage reghandle_lang_mixin.
Canonical Structure reghandle_ectx_lang := EctxLanguageOfEctxi reghandle_ectxi_lang.
Canonical Structure reghandle_lang := LanguageOfEctx reghandle_ectx_lang.


Check (@step reghandle_lang).
Eval compute in cfg reghandle_lang.
