From iris_simp_lang Require Import lang_handle.
From stdpp Require Import binders gmap.


Inductive ty :=
  | TUnit
  | TProd (A B : ty)
  | TSum (A B : ty)
  | TArrow (A : ty) (σ : gset region) (B : ty)  
  | TRef (ρ : region) (A : ty)                
  | TRgn (ρ : region)                             (* region handle for ρ *)
.

Notation tctx := (gmap string ty).
Notation eff  := (gset region).  


Inductive typed : tctx → expr → ty → eff → Prop :=
  | T_Var Γ x A :                                     (* RegTVar *)
    Γ !! x = Some A →
    typed Γ (Var x) A ∅
  | T_Unit Γ :                                        (* RegTUnit *)
    typed Γ (Val UnitV) TUnit ∅
  | T_Pair Γ e1 e2 A B σ1 σ2 σ :                      (* RegTPair *)
    typed Γ e1 A σ1 →
    typed Γ e2 B σ2 →
    σ = σ1 ∪ σ2 →
    typed Γ (Pair e1 e2) (TProd A B) σ
  | T_Fst Γ e A B σ :                                 (* RegTProj (i = 1) *)
    typed Γ e (TProd A B) σ →
    typed Γ (Fst e) A σ
  | T_Snd Γ e A B σ :                                 (* RegTProj (i = 2) *)
    typed Γ e (TProd A B) σ →
    typed Γ (Snd e) B σ
  | T_InjL Γ e A B σ :                                (* RegTInj (i = 1) *)
    typed Γ e A σ →
    typed Γ (InjL e) (TSum A B) σ
  | T_InjR Γ e A B σ :                                (* RegTInj (i = 2) *)
    typed Γ e B σ →
    typed Γ (InjR e) (TSum A B) σ
  | T_Case Γ e0 x1 e1 x2 e2 A B C σ0 σ1 σ2 σ :        (* RegTCase *)
    typed Γ e0 (TSum A B) σ0 →
    typed (binder_insert x1 A Γ) e1 C σ1 →
    typed (binder_insert x2 B Γ) e2 C σ2 →
    σ = σ0 ∪ σ1 ∪ σ2 →
    typed Γ (Case e0 x1 e1 x2 e2) C σ
  | T_Rec Γ f x e A B σf :                            (* RegTRec *)
    typed (binder_insert f (TArrow A σf B) (binder_insert x A Γ)) e B σf →
    typed Γ (Rec f x e) (TArrow A σf B) ∅
  | T_App Γ e1 e2 A B σf σ1 σ2 σ :                    (* RegTApp *)
    typed Γ e1 (TArrow A σf B) σ1 →
    typed Γ e2 A σ2 →
    σ = σ1 ∪ σ2 ∪ σf →
    typed Γ (App e1 e2) B σ
  | T_Alloc Γ er ev A ρ σr σv σ :                     (* RegTNew  *)
    typed Γ er (TRgn ρ) σr →
    typed Γ ev A σv →
    σ = σr ∪ σv ∪ {[ρ]} →
    typed Γ (Alloc er ev) (TRef ρ A) σ
  | T_Load Γ e A ρ σe σ :                             (* RegTDeref *)
    typed Γ e (TRef ρ A) σe →
    σ = σe ∪ {[ρ]} →
    typed Γ (Load e) A σ
  | T_Store Γ e1 e2 A ρ σ1 σ2 σ :                     (* RegTAssign *)
    typed Γ e1 (TRef ρ A) σ1 →
    typed Γ e2 A σ2 →
    σ = σ1 ∪ σ2 ∪ {[ρ]} →
    typed Γ (Store e1 e2) TUnit σ
  | T_Region Γ x e A σ :                              (* RegTMask  *)
    (∀ ρ, typed (binder_insert x (TRgn ρ) Γ) e A (σ ∪ {[ρ]})) →
    typed Γ (Region x e) A σ
  | T_Sub Γ e A σ σ' :                                (* RegTSub *)
    typed Γ e A σ →
    σ ⊆ σ' →
    typed Γ e A σ'
.

Open Scope string_scope.

(** [(λ y. y) () : unit @ ∅]. *)
Example app_id_typed :
  typed ∅ (App (Rec BAnon "y" (Var "y")) (Val UnitV)) TUnit ∅.
Proof.
  eapply T_App.
  - apply T_Rec. apply T_Var. rewrite /binder_insert /=. apply lookup_insert_eq.
  - apply T_Unit.
  - set_solver.
Qed.

(** [letregion r in (! (alloc_r ())) : unit @ ∅] *)
Example region_alloc_load_typed :
  typed ∅ (Region "x" (Load (Alloc (Var "x") (Val UnitV)))) TUnit ∅.
Proof.
  apply T_Region. intros ρ.
  eapply T_Sub.
  - eapply T_Load.
    + eapply T_Alloc.
      * apply T_Var. rewrite /binder_insert /=. apply lookup_insert_eq.
      * apply T_Unit.
      * reflexivity.
    + reflexivity.
  - set_solver.
Qed.

