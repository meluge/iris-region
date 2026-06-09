From iris.proofmode Require Import proofmode coq_tactics reduction.
From iris.base_logic.lib Require Import invariants ghost_map.
From iris_simp_lang Require Import class_instances primitive_laws proofmode typing metatheory.
From iris_simp_lang Require Import lang.
From iris.prelude Require Import options.

Definition regN : namespace := nroot .@ "reglang".

Section logrel.
  Context `{!regGS Σ}.

  (* The logical relation. *)

  Definition live (σ : eff) : iProp Σ :=
    ([∗ set] ρ ∈ σ, is_alive ρ)%I.

  Fixpoint interp (A : ty) (v : val) : iProp Σ :=
    match A with
    | TUnit => ⌜v = UnitV⌝
    | TProd A B => ∃ v1 v2, ⌜v = PairV v1 v2⌝ ∗ interp A v1 ∗ interp B v2
    | TSum A B =>
        (∃ u, ⌜v = InjLV u⌝ ∗ interp A u) ∨ (∃ u, ⌜v = InjRV u⌝ ∗ interp B u)
    | TRef ρ A =>
        ∃ l, ⌜v = RefV ρ l⌝ ∗ inv regN (∃ u, (ρ, l) ↦ u ∗ interp A u)
    | TArrow A σ B =>
        □ (∀ u, interp A u -∗
             ∀ rs, ⌜σ ⊆ rs⌝ -∗ live rs -∗
               WP App (Val v) (Val u) {{ w, live rs ∗ interp B w }})
    end%I.

  Notation 𝒱 := interp.

  Definition interp_env (Γ : tctx) (vs : gmap string val) : iProp Σ :=
    ([∗ map] A;v ∈ Γ;vs, 𝒱 A v)%I.
  Notation 𝒢 := interp_env.

  Global Instance interp_persistent A v : Persistent (𝒱 A v).
  Proof. revert v; induction A => v; simpl; apply _. Qed.

  Global Instance interp_env_persistent Γ vs : Persistent (𝒢 Γ vs).
  Proof. apply _. Qed.

  Notation ℰ σ A e :=
    (∀ rs, ⌜σ ⊆ rs⌝ -∗ live rs -∗ WP e {{ w, live rs ∗ 𝒱 A w }})%I.

  Definition sem_typed (Γ : tctx) (e : expr) (A : ty) (σ : eff) : iProp Σ :=
    (□ ∀ vs, 𝒢 Γ vs -∗ ℰ σ A (subst_map vs e))%I.

  Global Instance sem_typed_persistent Γ e A σ : Persistent (sem_typed Γ e A σ).
  Proof. apply _. Qed.

  Lemma interp_arrow_unfold A σ B v :
    𝒱 (TArrow A σ B) v ⊣⊢
      □ (∀ u, 𝒱 A u -∗ ℰ σ B (App (Val v) (Val u))).
  Proof. done. Qed.
  Notation "Γ ⊨ e : A @ σ" := (sem_typed Γ e A σ)
    (at level 74, e, A, σ at next level) : bi_scope.

  Implicit Types Γ : tctx.
  Implicit Types A B : ty.
  Implicit Types σ : eff.

  (** * Structural lemmas for [ℰ] and [𝒢]: effect monotonicity, value inclusion,
  semantic-typing coercion, bind, and environment manipulation. *)

  Lemma expr_interp_mono σ σ' A e :
    σ ⊆ σ' → ℰ σ A e -∗ ℰ σ' A e.
  Proof.
    iIntros (Hsub) "He". iIntros (σ2 Hsub2) "Hlive".
    iApply ("He" $! σ2 with "[%] Hlive"). set_solver.
  Qed.

  Lemma expr_interp_val σ A v :
    𝒱 A v -∗ ℰ σ A (Val v).
  Proof. iIntros "#Hv". iIntros (σ' ?) "Hlive". iApply wp_value. by iFrame. Qed.

  Lemma sem_typed_expr Γ e A σ σ' vs :
    σ ⊆ σ' → (Γ ⊨ e : A @ σ) -∗ 𝒢 Γ vs -∗
    ℰ σ' A (subst_map vs e).
  Proof.
    iIntros (Hsub) "#H #Henv". iApply expr_interp_mono; [done|]. by iApply "H".
  Qed.

  Lemma expr_bind K σ A B e :
    ℰ σ A e -∗
    (∀ v, 𝒱 A v -∗ ℰ σ B (fill K (Val v))) -∗
    ℰ σ B (fill K e).
  Proof.
    iIntros "He HK". iIntros (σ' Hσ) "Hlive".
    iApply wp_bind. iApply (wp_wand with "[He Hlive]").
    - iApply ("He" $! σ' with "[%//] Hlive").
    - iIntros (v) "[Hlive HA]". iApply ("HK" $! v with "HA [%//] Hlive").
  Qed.

  Lemma interp_env_binder_insert b A v Γ vs :
    𝒱 A v -∗ 𝒢 Γ vs -∗
    𝒢 (binder_insert b A Γ) (binder_insert b v vs).
  Proof.
    iIntros "#HA Henv". destruct b as [|x]; simpl; first by iFrame "Henv".
    rewrite /interp_env. by iApply (big_sepM2_insert_2 with "[HA] Henv").
  Qed.

  Lemma interp_env_empty : ⊢ 𝒢 ∅ ∅.
  Proof. rewrite /interp_env. apply: big_sepM2_empty'. Qed.

  Lemma is_alive_exclusive ρ : is_alive ρ -∗ is_alive ρ -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    by rewrite dfrac_valid_own in Hv.
  Qed.

  Lemma live_empty : ⊢ live ∅.
  Proof. rewrite /live. apply: big_sepS_empty'. Qed.

(** * Proof-mode tactics for [ℰ]: the [rel_*] analogues of the [wp_*] tactics,
built on [expr_bind] / [expr_interp_val] / [expr_interp_mono]. *)

Ltac rel_bind_ctx K :=
  lazymatch eval hnf in K with
  | [] => idtac                 (* nothing to bind *)
  | _ => iApply (expr_bind K)
  end.

Tactic Notation "rel_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (ℰ ?σ ?A ?e) =>
      let e := eval simpl in e in
      first
        [ reshape_expr e ltac:(fun K e' => unify e' efoc; rel_bind_ctx K)
        | fail 1 "rel_bind: cannot find" efoc "in" e ]
  | _ => fail "rel_bind: goal is not an expression relation 'ℰ σ A e'"
  end.

Tactic Notation "rel_value" := iApply expr_interp_val.
Tactic Notation "rel_mono" := iApply expr_interp_mono.

Tactic Notation "smart_rel_bind"
    open_constr(efoc) constr(spat) ident(v) constr(Hv) :=
  rel_bind efoc;
  [ iApply (sem_typed_expr with spat); set_solver |];
  iIntros (v) Hv.

  (** * Compatibility lemmas and the fundamental theorem. *)

  Lemma compat_var Γ x A :
    Γ !! x = Some A → ⊢ Γ ⊨ Var x : A @ ∅.
  Proof.
    iIntros (HΓ). iModIntro. iIntros (vs) "#Henv".
    iDestruct (big_sepM2_lookup_l with "Henv") as (v Hvs) "#Hv"; first done.
    cbn [subst_map]. rewrite Hvs. by rel_value.
  Qed.

  Lemma compat_unit Γ : ⊢ Γ ⊨ (Val UnitV) : TUnit @ ∅.
  Proof.
    iModIntro. iIntros (vs) "_". cbn [subst_map]. rel_value. done.
  Qed.

  Lemma compat_pair Γ e1 e2 A B σ1 σ2 :
    (Γ ⊨ e1 : A @ σ1) -∗ (Γ ⊨ e2 : B @ σ2) -∗
    Γ ⊨ Pair e1 e2 : TProd A B @ (σ1 ∪ σ2).
  Proof.
    iIntros "#H1 #H2". iModIntro. iIntros (vs) "#Henv". cbn [subst_map].
    smart_rel_bind (subst_map vs e2) "H2 Henv" w2 "#Hw2".
    smart_rel_bind (subst_map vs e1) "H1 Henv" w1 "#Hw1".
    iIntros (σ' Hσ) "Hlive". wp_pures.
    iFrame "Hlive". iExists w1, w2. by iFrame "Hw1 Hw2".
  Qed.

  Lemma compat_fst Γ e A B σ :
    (Γ ⊨ e : TProd A B @ σ) -∗ Γ ⊨ Fst e : A @ σ.
  Proof.
    iIntros "#H". iModIntro. iIntros (vs) "#Henv". cbn [subst_map].
    smart_rel_bind (subst_map vs e) "H Henv" v "#Hv".
    iDestruct "Hv" as (v1 v2 ->) "[#Hv1 #Hv2]".
    iIntros (σ' Hσ) "Hlive". wp_pures. iModIntro. iFrame "Hlive Hv1".
  Qed.

  Lemma compat_snd Γ e A B σ :
    (Γ ⊨ e : TProd A B @ σ) -∗ Γ ⊨ Snd e : B @ σ.
  Proof.
    iIntros "#H". iModIntro. iIntros (vs) "#Henv". cbn [subst_map].
    smart_rel_bind (subst_map vs e) "H Henv" v "#Hv".
    iDestruct "Hv" as (v1 v2 ->) "[#Hv1 #Hv2]".
    iIntros (σ' Hσ) "Hlive". wp_pures. iModIntro. iFrame "Hlive Hv2".
  Qed.

  Lemma compat_injl Γ e A B σ :
    (Γ ⊨ e : A @ σ) -∗ Γ ⊨ InjL e : TSum A B @ σ.
  Proof.
    iIntros "#H". iModIntro. iIntros (vs) "#Henv". cbn [subst_map].
    smart_rel_bind (subst_map vs e) "H Henv" v "#Hv".
    iIntros (σ' Hσ) "Hlive". wp_pures. iModIntro.
    iFrame "Hlive". iLeft. iExists v. iSplit; [done|]. iFrame "Hv".
  Qed.

  Lemma compat_injr Γ e A B σ :
    (Γ ⊨ e : B @ σ) -∗ Γ ⊨ InjR e : TSum A B @ σ.
  Proof.
    iIntros "#H". iModIntro. iIntros (vs) "#Henv". cbn [subst_map].
    smart_rel_bind (subst_map vs e) "H Henv" v "#Hv".
    iIntros (σ' Hσ) "Hlive". wp_pures. iModIntro.
    iFrame "Hlive". iRight. iExists v. iSplit; [done|]. iFrame "Hv".
  Qed.

  Lemma compat_case Γ e0 x1 e1 x2 e2 A B C σ0 σ1 σ2 :
    (Γ ⊨ e0 : TSum A B @ σ0) -∗
    (binder_insert x1 A Γ ⊨ e1 : C @ σ1) -∗
    (binder_insert x2 B Γ ⊨ e2 : C @ σ2) -∗
    Γ ⊨ Case e0 x1 e1 x2 e2 : C @ (σ0 ∪ σ1 ∪ σ2).
  Proof.
    iIntros "#H0 #H1 #H2". iModIntro. iIntros (vs) "#Henv". cbn [subst_map].
    smart_rel_bind (subst_map vs e0) "H0 Henv" v "#Hv".
    iIntros (σ' Hσ) "Hlive".
    iDestruct "Hv" as "[Hl|Hr]".
    - iDestruct "Hl" as (u ->) "#Hu". wp_pures.
      rewrite -subst_map_binder_insert.
      iApply ("H1" $! (binder_insert x1 u vs) with "[] [%] Hlive"); last set_solver.
      iApply (interp_env_binder_insert with "Hu Henv").
    - iDestruct "Hr" as (u ->) "#Hu". wp_pures.
      rewrite -subst_map_binder_insert.
      iApply ("H2" $! (binder_insert x2 u vs) with "[] [%] Hlive"); last set_solver.
      iApply (interp_env_binder_insert with "Hu Henv").
  Qed.

  Lemma compat_rec Γ f x eb A σf B :
    (binder_insert f (TArrow A σf B) (binder_insert x A Γ) ⊨ eb : B @ σf) -∗
    Γ ⊨ Rec f x eb : TArrow A σf B @ ∅.
  Proof.
    iIntros "#He". iModIntro. iIntros (vs) "#Henv". cbn [subst_map].
    iIntros (σ' _) "Hlive". wp_pures. iModIntro. iFrame "Hlive".
    iLöb as "IH".
    iModIntro. iIntros (u) "#Hu". iIntros (σ2 Hσ2) "Hlive". wp_pures.
    rewrite -subst_map_binder_insert_2.
    iSpecialize ("He" $! (binder_insert f (RecV f x _) (binder_insert x u vs))
                   with "[]").
    { iApply (interp_env_binder_insert with "IH").
      iApply (interp_env_binder_insert with "Hu Henv"). }
    iApply ("He" $! σ2 with "[%//] Hlive").
  Qed.

  Lemma compat_app Γ e1 e2 A B σf σ1 σ2 :
    (Γ ⊨ e1 : TArrow A σf B @ σ1) -∗ (Γ ⊨ e2 : A @ σ2) -∗
    Γ ⊨ App e1 e2 : B @ (σ1 ∪ σ2 ∪ σf).
  Proof.
    iIntros "#H1 #H2". iModIntro. iIntros (vs) "#Henv". cbn [subst_map].
    smart_rel_bind (subst_map vs e2) "H2 Henv" w2 "#Hw2".
    smart_rel_bind (subst_map vs e1) "H1 Henv" w1 "#Hw1".
    iDestruct (interp_arrow_unfold with "Hw1") as "#Hf".
    iAssert (ℰ σf B (App (Val w1) (Val w2))) as "Happ".
    { by iApply ("Hf" with "Hw2"). }
    iApply (expr_interp_mono with "Happ"). set_solver.
  Qed.

  Lemma compat_alloc Γ ev A ρ σv :
    (Γ ⊨ ev : A @ σv) -∗ Γ ⊨ Alloc (RName ρ) ev : TRef ρ A @ (σv ∪ {[ρ]}).
  Proof.
    iIntros "#H". iModIntro. iIntros (vs) "#Henv". cbn [subst_map].
    smart_rel_bind (subst_map vs ev) "H Henv" w "#Hw".
    iIntros (σ' Hσ) "Hlive".
    iDestruct (big_sepS_elem_of_acc _ _ ρ with "Hlive") as "[Halρ Hclose]";
      first set_solver.
    iApply wp_fupd.
    iApply (wp_alloc with "Halρ"). iIntros "!>" (l) "[Halρ Hpt]".
    iMod (inv_alloc regN _ (∃ u, (ρ, l) ↦ u ∗ 𝒱 A u) with "[Hpt]") as "#Hinv".
    { iNext. iExists w. by iFrame "Hpt Hw". }
    iModIntro. iSplitL "Halρ Hclose"; first by iApply "Hclose".
    iExists l. by iFrame "Hinv".
  Qed.

  Lemma compat_load Γ e A ρ σe :
    (Γ ⊨ e : TRef ρ A @ σe) -∗ Γ ⊨ Load e : A @ (σe ∪ {[ρ]}).
  Proof.
    iIntros "#H". iModIntro. iIntros (vs) "#Henv". cbn [subst_map].
    smart_rel_bind (subst_map vs e) "H Henv" v "#Hv".
    iDestruct "Hv" as (l ->) "#Hinv".
    iIntros (σ' Hσ) "Hlive".
    change (fill [LoadCtx] (Val (RefV ρ l))) with (Load (Val (RefV ρ l))).
    iDestruct (big_sepS_elem_of_acc _ _ ρ with "Hlive") as "[Halρ Hclose]";
      first set_solver.
    iInv "Hinv" as (u) "[>Hpt #Hu]" "Hcl".
    iApply (wp_load with "[$Halρ $Hpt]"). iIntros "!> [Halρ Hpt]".
    iMod ("Hcl" with "[Hpt]") as "_". { iNext. iExists u. by iFrame "Hpt Hu". }
    iModIntro. iSplitL "Halρ Hclose"; [by iApply "Hclose"|]. done.
  Qed.

  Lemma compat_store Γ e1 e2 A ρ σ1 σ2 :
    (Γ ⊨ e1 : TRef ρ A @ σ1) -∗ (Γ ⊨ e2 : A @ σ2) -∗
    Γ ⊨ Store e1 e2 : TUnit @ (σ1 ∪ σ2 ∪ {[ρ]}).
  Proof.
    iIntros "#H1 #H2". iModIntro. iIntros (vs) "#Henv". cbn [subst_map].
    smart_rel_bind (subst_map vs e2) "H2 Henv" w2 "#Hw2".
    smart_rel_bind (subst_map vs e1) "H1 Henv" w1 "#Hw1".
    iDestruct "Hw1" as (l ->) "#Hinv".
    iIntros (σ' Hσ) "Hlive".
    change (fill [StoreLCtx w2] (Val (RefV ρ l)))
      with (Store (Val (RefV ρ l)) (Val w2)).
    iDestruct (big_sepS_elem_of_acc _ _ ρ with "Hlive") as "[Halρ Hclose]";
      first set_solver.
    iInv "Hinv" as (u) "[>Hpt #Hu]" "Hcl".
    iApply (wp_store with "[$Halρ $Hpt]"). iIntros "!> [Halρ Hpt]".
    iMod ("Hcl" with "[Hpt]") as "_". { iNext. iExists w2. by iFrame "Hpt Hw2". }
    iModIntro. iSplitL "Halρ Hclose"; [by iApply "Hclose"|]. done.
  Qed.

  Lemma compat_region Γ x e A σ :
    (∀ ρ, Γ ⊨ subst_region' x ρ e : A @ (σ ∪ {[ρ]})) -∗
    Γ ⊨ LetRegion x e : A @ σ.
  Proof.
    iIntros "#H". iModIntro. iIntros (vs) "#Henv". cbn [subst_map].
    iIntros (σ' Hσ) "Hlive". iApply wp_region. iIntros (ρ) "Halρ".
    (* Establish ρ ∉ σ' (else two liveness tokens for ρ). *)
    destruct (decide (ρ ∈ σ')) as [Hin|Hnin].
    { iDestruct (big_sepS_elem_of with "Hlive") as "Halρ2"; first done.
      iDestruct (is_alive_exclusive with "Halρ Halρ2") as %[]. }
    rewrite subst_region'_subst_map.
    iAssert (live ({[ρ]} ∪ σ')) with "[Hlive Halρ]" as "Hlive2".
    { rewrite /live big_sepS_insert //. iFrame. }
    iApply (wp_wand with "[Hlive2]").
    - iApply ("H" $! ρ vs with "Henv [%] Hlive2"). set_solver.
    - iIntros (w) "[Hlive2 #HA]". rewrite /live big_sepS_insert //.
      iDestruct "Hlive2" as "[Halρ Hlive]". iFrame "Halρ Hlive HA".
  Qed.

  Lemma compat_sub Γ e A σ σ' :
    σ ⊆ σ' → (Γ ⊨ e : A @ σ) -∗ Γ ⊨ e : A @ σ'.
  Proof.
    iIntros (Hsub) "#H". iModIntro. iIntros (vs) "#Henv".
    iApply expr_interp_mono; [done|]. by iApply "H".
  Qed.

  Theorem fundamental Γ e A σ :
    typed Γ e A σ → ⊢ Γ ⊨ e : A @ σ.
  Proof.
    induction 1 as
      [ Γ x A HΓ
      | Γ
      | Γ e1 e2 A B σ1 σ2 σ t1 IH1 t2 IH2 Heq
      | Γ e A B σ t IH
      | Γ e A B σ t IH
      | Γ e A B σ t IH
      | Γ e A B σ t IH
      | Γ e0 x1 e1 x2 e2 A B C σ0 σ1 σ2 σ t0 IH0 t1 IH1 t2 IH2 Heq
      | Γ f x e A B σf t IH
      | Γ e1 e2 A B σf σ1 σ2 σ t1 IH1 t2 IH2 Heq
      | Γ ρ ev A σv σ t IH Heq
      | Γ e A ρ σe σ t IH Heq
      | Γ e1 e2 A ρ σ1 σ2 σ t1 IH1 t2 IH2 Heq
      | Γ x e A σ Hall IH
      | Γ e A σ σ' t IH Hsub ];
      subst.
    - by iApply compat_var.
    - by iApply compat_unit.
    - iApply (compat_pair with "[] []"); [iApply IH1|iApply IH2].
    - iApply compat_fst; iApply IH.
    - iApply compat_snd; iApply IH.
    - iApply compat_injl; iApply IH.
    - iApply compat_injr; iApply IH.
    - iApply (compat_case with "[] [] []");
        [iApply IH0|iApply IH1|iApply IH2].
    - iApply compat_rec; iApply IH.
    - iApply (compat_app with "[] []"); [iApply IH1|iApply IH2].
    - iApply compat_alloc; iApply IH.
    - iApply compat_load; iApply IH.
    - iApply (compat_store with "[] []"); [iApply IH1|iApply IH2].
    - iApply compat_region. iIntros (ρ). iApply IH.
    - iApply (compat_sub with "[]"); [done|iApply IH].
  Qed.
End logrel.

(** Re-export the relation notations for downstream files (cleared at [End]). *)
Notation 𝒱 := interp.
Notation 𝒢 := interp_env.
Notation ℰ σ A e :=
  (∀ rs, ⌜σ ⊆ rs⌝ -∗ live rs -∗ WP e {{ w, live rs ∗ 𝒱 A w }})%I.
Notation "Γ ⊨ e : A @ σ" := (sem_typed Γ e A σ)
  (at level 74, e, A, σ at next level) : bi_scope.
