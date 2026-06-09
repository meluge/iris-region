From iris.program_logic Require Export adequacy.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
From iris_simp_lang Require Import primitive_laws typing metatheory logrel.
From iris_simp_lang Require Import lang.
From iris.prelude Require Import options.


Global Instance subG_regGpreS Σ : subG regΣ Σ → regGpreS Σ.
Proof. solve_inG. Qed.

Definition init_state : state := {| heap := ∅; alive := ∅ |}.


Lemma reg_adequacy Σ `{!regGpreS Σ, !invGpreS Σ}
    (s : stuckness) (e : expr) (σ : state) (φ : val → Prop) :
  (∀ (HregGS : regGS Σ), ⊢ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply (wp_adequacy Σ reg_lang). iIntros (Hinv κs) "".
  iMod (ghost_map_alloc σ.(heap)) as (γh) "[Hh _]".
  iMod (ghost_map_alloc σ.(alive)) as (γa) "[Ha _]".
  iModIntro.
  iExists (λ σ' _, (ghost_map_auth γh 1 σ'.(heap) ∗
                    ghost_map_auth γa 1 σ'.(alive))%I), (λ _, True%I).
  iFrame "Hh Ha".
  iApply (Hwp (@RegGS Σ Hinv _ _ γh γa)).
Qed.

Theorem sem_type_safety Σ `{!regGpreS Σ, !invGpreS Σ} e A :
  (∀ (HregGS : regGS Σ), ⊢ ∅ ⊨ e : A @ ∅) →
  adequate NotStuck e init_state (λ _ _, True).
Proof.
  intros Hsem. apply (reg_adequacy Σ). intros HregGS.
  iPoseProof (Hsem HregGS) as "#H".
  iSpecialize ("H" $! ∅ with "[]"); first iApply interp_env_empty.
  iSpecialize ("H" $! ∅ with "[%] []").
  { set_solver. }
  { iApply live_empty. }
  rewrite subst_map_empty.
  iApply (wp_wand with "H"). by iIntros (v) "_".
Qed.


Theorem type_safe e A tp σ' e' :
  typed ∅ e A ∅ →
  rtc erased_step ([e], init_state) (tp, σ') →
  e' ∈ tp →
  not_stuck e' σ'.
Proof.
  intros Ht Hsteps Hin.
  cut (adequate NotStuck e init_state (λ _ _, True)).
  { intros [_ Hns]. by eapply Hns. }
  apply (sem_type_safety regΣ e A). intros HregGS. by apply fundamental.
Qed.
