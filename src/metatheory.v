From stdpp Require Import gmap stringmap.
From iris_simp_lang Require Export lang.
From iris.prelude Require Import options.


Local Definition set_binder_insert (x : binder) (X : stringset) : stringset :=
  match x with
  | BAnon => X
  | BNamed f => {[f]} ∪ X
  end.

Local Instance set_unfold_elem_of_insert_binder x y X Q :
  SetUnfoldElemOf y X Q →
  SetUnfoldElemOf y (set_binder_insert x X) (Q ∨ BNamed y = x).
Proof. destruct 1; constructor; destruct x; set_solver. Qed.

(* Check if expression [e] is closed w.r.t. the set [X] of variable names,
   and that all the values in [e] are closed *)
Fixpoint is_closed_expr (X : stringset) (e : expr) : bool :=
  match e with
  | Val v => is_closed_val v
  | Var x => bool_decide (x ∈ X)
  | Rec f x e => is_closed_expr (set_binder_insert f (set_binder_insert x X)) e
  | App e1 e2 => is_closed_expr X e1 && is_closed_expr X e2
  | Pair e1 e2 => is_closed_expr X e1 && is_closed_expr X e2
  | Fst e => is_closed_expr X e
  | Snd e => is_closed_expr X e
  | InjL e => is_closed_expr X e
  | InjR e => is_closed_expr X e
  | Case e0 x1 e1 x2 e2 =>
     is_closed_expr X e0 &&
     is_closed_expr (set_binder_insert x1 X) e1 &&
     is_closed_expr (set_binder_insert x2 X) e2
  | Alloc _ e => is_closed_expr X e
  | Load e => is_closed_expr X e
  | Store e1 e2 => is_closed_expr X e1 && is_closed_expr X e2
  | LetRegion _ e => is_closed_expr X e
  | EndRegion _ e => is_closed_expr X e
  end
with is_closed_val (v : val) : bool :=
  match v with
  | UnitV => true
  | PairV v1 v2 => is_closed_val v1 && is_closed_val v2
  | InjLV v => is_closed_val v
  | InjRV v => is_closed_val v
  | RecV f x e => is_closed_expr (set_binder_insert f (set_binder_insert x ∅)) e
  | RefV _ _ => true
  end.

(* Parallel substitution *)
Fixpoint subst_map (vs : gmap string val) (e : expr) : expr :=
  match e with
  | Val _ => e
  | Var y => if vs !! y is Some v then Val v else Var y
  | Rec f y e => Rec f y (subst_map (binder_delete y (binder_delete f vs)) e)
  | App e1 e2 => App (subst_map vs e1) (subst_map vs e2)
  | Pair e1 e2 => Pair (subst_map vs e1) (subst_map vs e2)
  | Fst e => Fst (subst_map vs e)
  | Snd e => Snd (subst_map vs e)
  | InjL e => InjL (subst_map vs e)
  | InjR e => InjR (subst_map vs e)
  | Case e0 x1 e1 x2 e2 =>
     Case (subst_map vs e0)
          x1 (subst_map (binder_delete x1 vs) e1)
          x2 (subst_map (binder_delete x2 vs) e2)
  | Alloc r e => Alloc r (subst_map vs e)
  | Load e => Load (subst_map vs e)
  | Store e1 e2 => Store (subst_map vs e1) (subst_map vs e2)
  | LetRegion y e => LetRegion y (subst_map vs e)
  | EndRegion ρ e => EndRegion ρ (subst_map vs e)
  end.

(* Properties *)
Lemma is_closed_weaken X Y e : is_closed_expr X e → X ⊆ Y → is_closed_expr Y e.
Proof. revert X Y; induction e; naive_solver (eauto; set_solver). Qed.

Lemma is_closed_weaken_empty X e : is_closed_expr ∅ e → is_closed_expr X e.
Proof. intros. by apply is_closed_weaken with ∅, empty_subseteq. Qed.

Lemma is_closed_subst X e y v :
  is_closed_val v →
  is_closed_expr ({[y]} ∪ X) e →
  is_closed_expr X (subst y v e).
Proof.
  intros Hv. revert X.
  induction e=> X /= ?; destruct_and?; split_and?; simplify_option_eq;
    try match goal with
    | H : ¬(_ ∧ _) |- _ => apply not_and_l in H as [?%dec_stable|?%dec_stable]
    end; eauto using is_closed_weaken with set_solver.
Qed.
Lemma is_closed_subst' X e x v :
  is_closed_val v →
  is_closed_expr (set_binder_insert x X) e →
  is_closed_expr X (subst' x v e).
Proof. destruct x; eauto using is_closed_subst. Qed.

Lemma subst_is_closed X e x es : is_closed_expr X e → x ∉ X → subst x es e = e.
Proof.
  revert X. induction e=> X /=;
   rewrite ?bool_decide_spec ?andb_True=> ??;
   repeat case_decide; simplify_eq/=; f_equal; intuition eauto with set_solver.
Qed.

Lemma subst_is_closed_empty e x v : is_closed_expr ∅ e → subst x v e = e.
Proof. intros. apply subst_is_closed with (∅:stringset); set_solver. Qed.

Lemma subst_subst e x v v' :
  subst x v (subst x v' e) = subst x v' e.
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    repeat (case_decide; simplify_eq/=);
    auto using subst_is_closed_empty with f_equal.
Qed.
Lemma subst_subst' e x v v' :
  subst' x v (subst' x v' e) = subst' x v' e.
Proof. destruct x; simpl; auto using subst_subst. Qed.

Lemma subst_subst_ne e x y v v' :
  x ≠ y → subst x v (subst y v' e) = subst y v' (subst x v e).
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    repeat (case_decide; simplify_eq/=);
    auto using eq_sym, subst_is_closed_empty with f_equal.
Qed.
Lemma subst_subst_ne' e x y v v' :
  x ≠ y → subst' x v (subst' y v' e) = subst' y v' (subst' x v e).
Proof. destruct x, y; simpl; auto using subst_subst_ne with congruence. Qed.

Lemma subst_map_empty e : subst_map ∅ e = e.
Proof.
  assert (∀ x, binder_delete x (∅:gmap string val) = ∅) as Hdel.
  { intros [|x]; by rewrite /= ?delete_empty. }
  induction e; simplify_map_eq; rewrite ?Hdel; auto with f_equal.
Qed.

Lemma subst_map_insert x v vs e :
  subst_map (<[x:=v]>vs) e = subst x v (subst_map (delete x vs) e).
Proof.
  revert vs. induction e=> vs; simplify_map_eq; auto with f_equal.
  - match goal with
    | |- context [ <[?x:=_]> _ !! ?y ] =>
       destruct (decide (x = y)); simplify_map_eq=> //
    end. by case (vs !! _); simplify_option_eq.
  - destruct (decide _) as [[??]|[<-%dec_stable|[<-%dec_stable ?]]%not_and_l_alt].
    + rewrite !binder_delete_insert // !binder_delete_delete; eauto with f_equal.
    + by rewrite /= delete_insert_eq delete_delete_eq.
    + by rewrite /= binder_delete_insert // delete_insert_eq
        !binder_delete_delete delete_delete_eq.
  - f_equal; [by auto| |].
    + case_decide as Hd.
      * destruct x1 as [|y]; simpl.
        -- apply IHe2.
        -- rewrite delete_insert_ne; last naive_solver.
           rewrite IHe2 delete_delete //.
      * assert (x1 = BNamed x) as -> by (destruct x1; naive_solver).
        by rewrite /= delete_insert_eq delete_delete_eq.
    + case_decide as Hd.
      * destruct x2 as [|y]; simpl.
        -- apply IHe3.
        -- rewrite delete_insert_ne; last naive_solver.
           rewrite IHe3 delete_delete //.
      * assert (x2 = BNamed x) as -> by (destruct x2; naive_solver).
        by rewrite /= delete_insert_eq delete_delete_eq.
Qed.

Lemma subst_map_singleton x v e :
  subst_map {[x:=v]} e = subst x v e.
Proof. by rewrite subst_map_insert delete_empty subst_map_empty. Qed.

Lemma subst_map_binder_insert b v vs e :
  subst_map (binder_insert b v vs) e =
  subst' b v (subst_map (binder_delete b vs) e).
Proof. destruct b; rewrite ?subst_map_insert //. Qed.
Lemma subst_map_binder_insert_empty b v e :
  subst_map (binder_insert b v ∅) e = subst' b v e.
Proof. by rewrite subst_map_binder_insert binder_delete_empty subst_map_empty. Qed.

Lemma subst_map_binder_insert_2 b1 v1 b2 v2 vs e :
  subst_map (binder_insert b1 v1 (binder_insert b2 v2 vs)) e =
  subst' b2 v2 (subst' b1 v1 (subst_map (binder_delete b2 (binder_delete b1 vs)) e)) .
Proof.
  destruct b1 as [|s1], b2 as [|s2]=> /=; auto using subst_map_insert.
  rewrite subst_map_insert. destruct (decide (s1 = s2)) as [->|].
  - by rewrite delete_delete_eq subst_subst delete_insert_eq.
  - by rewrite delete_insert_ne // subst_map_insert subst_subst_ne.
Qed.
Lemma subst_map_binder_insert_2_empty b1 v1 b2 v2 e :
  subst_map (binder_insert b1 v1 (binder_insert b2 v2 ∅)) e =
  subst' b2 v2 (subst' b1 v1 e).
Proof.
  by rewrite subst_map_binder_insert_2 !binder_delete_empty subst_map_empty.
Qed.

Lemma subst_region_subst_map x ρ vs e :
  subst_region x ρ (subst_map vs e) = subst_map vs (subst_region x ρ e).
Proof.
  revert vs. induction e=> vs /=; try (f_equal; eauto; done).
  - by destruct (vs !! _).
  - case_decide; simpl; f_equal; eauto.
Qed.
Lemma subst_region'_subst_map b ρ vs e :
  subst_region' b ρ (subst_map vs e) = subst_map vs (subst_region' b ρ e).
Proof. destruct b; simpl; auto using subst_region_subst_map. Qed.
