From iris_simp_lang Require Import lang.
From stdpp Require Import binders gmap.


Inductive ty :=
  | TUnit
  | TProd (A B : ty)
  | TSum (A B : ty)
  | TArrow (A : ty) (σ : gset string) (B : ty)   
  | TRef (x : string) (A : ty)                   
.

Notation tctx := (gmap string ty).
Notation eff  := (gset string).   

(** Free region variables of a type. *)
Fixpoint frv (A : ty) : gset string :=
  match A with
  | TUnit => ∅
  | TProd A B => frv A ∪ frv B
  | TSum A B => frv A ∪ frv B
  | TArrow A σ B => frv A ∪ σ ∪ frv B
  | TRef x A => {[ x ]} ∪ frv A
  end.

(** Free region variables of a term context. *)
Definition frv_ctx (Γ : tctx) : gset string :=
  map_fold (λ _ A s, frv A ∪ s) ∅ Γ.

Lemma frv_ctx_empty : frv_ctx ∅ = ∅.
Proof. apply map_fold_empty. Qed.

Open Scope string_scope.


Inductive typed : eff → tctx → expr → ty → eff → Prop :=
  | T_Var Δ Γ x A :                                   (* RegTVar *)
    Γ !! x = Some A →
    typed Δ Γ (Var x) A ∅
  | T_Unit Δ Γ :                                      (* RegTUnit *)
    typed Δ Γ (Val UnitV) TUnit ∅
  | T_Pair Δ Γ e1 e2 A B σ1 σ2 σ :                    (* RegTPair *)
    typed Δ Γ e1 A σ1 →
    typed Δ Γ e2 B σ2 →
    σ = σ1 ∪ σ2 →
    typed Δ Γ (Pair e1 e2) (TProd A B) σ
  | T_Fst Δ Γ e A B σ :                               (* RegTProj (i = 1) *)
    typed Δ Γ e (TProd A B) σ →
    typed Δ Γ (Fst e) A σ
  | T_Snd Δ Γ e A B σ :                               (* RegTProj (i = 2) *)
    typed Δ Γ e (TProd A B) σ →
    typed Δ Γ (Snd e) B σ
  | T_InjL Δ Γ e A B σ :                              (* RegTInj (i = 1) *)
    typed Δ Γ e A σ →
    typed Δ Γ (InjL e) (TSum A B) σ
  | T_InjR Δ Γ e A B σ :                              (* RegTInj (i = 2) *)
    typed Δ Γ e B σ →
    typed Δ Γ (InjR e) (TSum A B) σ
  | T_Case Δ Γ e0 x1 e1 x2 e2 A B C σ0 σ1 σ2 σ :      (* RegTCase *)
    typed Δ Γ e0 (TSum A B) σ0 →
    typed Δ (binder_insert x1 A Γ) e1 C σ1 →
    typed Δ (binder_insert x2 B Γ) e2 C σ2 →
    σ = σ0 ∪ σ1 ∪ σ2 →
    typed Δ Γ (Case e0 x1 e1 x2 e2) C σ
  | T_Rec Δ Γ f x e A B σf :                          (* RegTRec *)
    typed Δ (binder_insert f (TArrow A σf B) (binder_insert x A Γ)) e B σf →
    typed Δ Γ (Rec f x e) (TArrow A σf B) ∅
  | T_App Δ Γ e1 e2 A B σf σ1 σ2 σ :                  (* RegTApp *)
    typed Δ Γ e1 (TArrow A σf B) σ1 →
    typed Δ Γ e2 A σ2 →
    σ = σ1 ∪ σ2 ∪ σf →
    typed Δ Γ (App e1 e2) B σ
  | T_Alloc Δ Γ x ev A σv σ :                         (* RegTNew *)
    typed Δ Γ ev A σv →
    x ∈ Δ →
    σ = σv ∪ {[ x ]} →
    typed Δ Γ (Alloc (RVar x) ev) (TRef x A) σ
  | T_Load Δ Γ e A x σe σ :                           (* RegTDeref *)
    typed Δ Γ e (TRef x A) σe →
    σ = σe ∪ {[ x ]} →
    typed Δ Γ (Load e) A σ
  | T_Store Δ Γ e1 e2 A x σ1 σ2 σ :                   (* RegTAssign *)
    typed Δ Γ e1 (TRef x A) σ1 →
    typed Δ Γ e2 A σ2 →
    σ = σ1 ∪ σ2 ∪ {[ x ]} →
    typed Δ Γ (Store e1 e2) TUnit σ
  | T_Region Δ Γ x e A σ σ' :                         (* RegTMask  *)
    typed ({[ x ]} ∪ Δ) Γ e A σ →
    x ∉ Δ →
    x ∉ frv_ctx Γ →
    x ∉ frv A →
    σ' = σ ∖ {[ x ]} →
    typed Δ Γ (LetRegion (BNamed x) e) A σ'
  | T_Sub Δ Γ e A σ σ' :                              (* RegTSub   *)
    typed Δ Γ e A σ →
    σ ⊆ σ' →
    typed Δ Γ e A σ'
.

(** [(λ y. y) () : unit @ ∅]. *)
Example app_id_typed :
  typed ∅ ∅ (App (Rec BAnon "y" (Var "y")) (Val UnitV)) TUnit ∅.
Proof.
  eapply T_App.
  - apply T_Rec. apply T_Var. rewrite /binder_insert /=. apply lookup_insert_eq.
  - apply T_Unit.
  - set_solver.
Qed.

(** [letregion r in (! (alloc_r ())) : unit @ ∅] *)
Example region_alloc_load_typed :
  typed ∅ ∅ (LetRegion (BNamed "r") (Load (Alloc (RVar "r") (Val UnitV)))) TUnit ∅.
Proof.
  eapply T_Region.
  - eapply T_Load.
    + eapply T_Alloc.
      * apply T_Unit.
      * set_solver.
      * reflexivity.
    + reflexivity.
  - set_solver.
  - rewrite frv_ctx_empty. set_solver.
  - set_solver.
  - set_solver.
Qed.

(** Note (region escape): [letregion r in (alloc_r ())] is NOT typeable at any
   type, because the body's only type is [ref_r unit], whose [frv] is {r} — so the
   side condition [r ∉ frv A] of [T_Region] fails. This is precisely how the
   masking rule confines references to their region (Tofte–Talpin's rule 27 side
   condition [ρ ∉ frv(τ)]); the handle model achieves the same effect through the
   fixed-result-type [∀ρ] of its [T_Region]. *)
