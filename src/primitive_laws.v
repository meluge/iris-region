From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris.base_logic.lib Require Import ghost_map.
From iris_simp_lang Require Import lang.
From iris.prelude Require Import options.

(** * Program logic for reglang


  state_interp (heap, alive) := ●heap @ γ_h  ∗  ●alive @ γ_a

  (ρ,ℓ) ↦ v  := ◯{(ρ,ℓ) := v} @ γ_h        (a heap points-to)
  is_alive ρ := ◯{ρ := true}    @ γ_a        (the liveness token for ρ)

We implement with ghost_maps.  *)

(** Ghost state: two [ghost_map]s, for the heap and the aliveness map. *)
Class regGpreS (Σ : gFunctors) := {
  regGpreS_heap :: ghost_mapG Σ (region * loc) val;
  regGpreS_alive :: ghost_mapG Σ region bool;
}.

Class regGS (Σ : gFunctors) := RegGS {
  reg_invGS : invGS Σ;
  reg_heapGS :: ghost_mapG Σ (region * loc) val;
  reg_aliveGS :: ghost_mapG Σ region bool;
  reg_heap_name : gname;
  reg_alive_name : gname;
}.


Notation γ_h := reg_heap_name (only parsing).
Notation γ_a := reg_alive_name (only parsing).

Definition regΣ : gFunctors :=
  #[ invΣ; ghost_mapΣ (region * loc) val; ghost_mapΣ region bool ].

Section definitions.
  Context `{!regGS Σ}.

  Definition pointsto (rl : region * loc) (v : val) : iProp Σ :=
    rl ↪[reg_heap_name] v.

  Definition is_alive (ρ : region) : iProp Σ :=
    ρ ↪[reg_alive_name] true.
End definitions.

Notation "rl ↦ v" := (pointsto rl v) (at level 20) : bi_scope.

Global Instance regGS_irisGS `{!regGS Σ} : irisGS reg_lang Σ := {
  iris_invGS := reg_invGS;
  state_interp σ _ _ _ :=
    (ghost_map_auth reg_heap_name 1 σ.(heap) ∗
     ghost_map_auth reg_alive_name 1 σ.(alive))%I;
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

Section lifting.
Context `{!regGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v w : val.
Implicit Types ρ : region.
Implicit Types l : loc.

Lemma is_alive_agree m ρ :
  ghost_map_auth reg_alive_name 1 m -∗ is_alive ρ -∗ ⌜m !! ρ = Some true⌝.
Proof. iIntros "Ha Hρ". iApply (ghost_map_lookup with "Ha Hρ"). Qed.

Lemma pointsto_agree m rl v :
  ghost_map_auth reg_heap_name 1 m -∗ rl ↦ v -∗ ⌜m !! rl = Some v⌝.
Proof. iIntros "Hh Hrl". iApply (ghost_map_lookup with "Hh Hrl"). Qed.


Lemma wp_alloc s E ρ v :
  {{{ is_alive ρ }}}
    Alloc (RName ρ) (Val v) @ s; E
  {{{ l, RET (RefV ρ l); is_alive ρ ∗ (ρ, l) ↦ v }}}.
Proof.
  iIntros (Φ) "Hal HΦ".
  iApply wp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κ κs nt) "[Hh Ha] !>".
  iDestruct (is_alive_agree with "Ha Hal") as %Hal.
  iSplit. { iPureIntro. eexists _, _, _, _. by eapply alloc_fresh. }
  iIntros "!>" (e2 σ2 efs Hstep) "_". inversion Hstep; simplify_eq.
  iMod (ghost_map_insert _ v with "Hh") as "[Hh Hpt]"; first done.
  iModIntro. iSplit; first done. iFrame "Hh Ha". iApply "HΦ". by iFrame.
Qed.

Lemma wp_load s E ρ l v :
  {{{ is_alive ρ ∗ (ρ, l) ↦ v }}}
    Load (Val (RefV ρ l)) @ s; E
  {{{ RET v; is_alive ρ ∗ (ρ, l) ↦ v }}}.
Proof.
  iIntros (Φ) "[Hal Hpt] HΦ".
  iApply wp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κ κs nt) "[Hh Ha] !>".
  iDestruct (is_alive_agree with "Ha Hal") as %Hal.
  iDestruct (pointsto_agree with "Hh Hpt") as %Hhl.
  iSplit. { iPureIntro. eexists _, _, _, _. by eapply LoadS. }
  iIntros "!>" (e2 σ2 efs Hstep) "_". inversion Hstep; simplify_eq.
  iModIntro. iSplit; first done. iFrame "Hh Ha". iApply "HΦ". by iFrame.
Qed.

Lemma wp_store s E ρ l v w :
  {{{ is_alive ρ ∗ (ρ, l) ↦ v }}}
    Store (Val (RefV ρ l)) (Val w) @ s; E
  {{{ RET (UnitV); is_alive ρ ∗ (ρ, l) ↦ w }}}.
Proof.
  iIntros (Φ) "[Hal Hpt] HΦ".
  iApply wp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κ κs nt) "[Hh Ha] !>".
  iDestruct (is_alive_agree with "Ha Hal") as %Hal.
  iDestruct (pointsto_agree with "Hh Hpt") as %Hhl.
  iSplit. { iPureIntro. eexists _, _, _, _. by eapply StoreS. }
  iIntros "!>" (e2 σ2 efs Hstep) "_". inversion Hstep; simplify_eq.
  iMod (ghost_map_update w with "Hh Hpt") as "[Hh Hpt]".
  iModIntro. iSplit; first done. iFrame "Hh Ha". iApply "HΦ". by iFrame.
Qed.

Lemma wp_endregion_val s E ρ v Φ :
  is_alive ρ -∗ Φ v -∗ WP EndRegion ρ (Val v) @ s; E {{ Φ }}.
Proof.
  iIntros "Hal HΦ".
  iApply wp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κ κs nt) "[Hh Ha] !>".
  iDestruct (is_alive_agree with "Ha Hal") as %Hal.
  iSplit. { iPureIntro. eexists _, _, _, _. by eapply EndRegionS. }
  iIntros "!>" (e2 σ2 efs Hstep) "_". inversion Hstep; simplify_eq.
  iMod (ghost_map_update false with "Ha Hal") as "[Ha _]".
  iModIntro. iSplit; first done. iFrame "Hh Ha". iApply "HΦ".
Qed.


Lemma wp_letregion s E x e Φ :
  (∀ ρ, is_alive ρ -∗ WP EndRegion ρ (subst_region' x ρ e) @ s; E {{ Φ }}) -∗
  WP LetRegion x e @ s; E {{ Φ }}.
Proof.
  iIntros "H".
  iApply wp_lift_base_step; first done.
  iIntros (σ1 ns κ κs nt) "[Hh Ha]".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iSplit. { iPureIntro. eexists _, _, _, _. eapply letregion_step_fresh. }
  iIntros "!>" (e2 σ2 efs Hstep) "_". inversion Hstep; simplify_eq.
  iMod "Hclose" as "_".
  iMod (ghost_map_insert _ true with "Ha") as "[Ha Hal]"; first done.
  iModIntro. iFrame "Hh Ha". iSplitL "H Hal".
  - iApply ("H" with "Hal").
  - done. 
Qed.


Lemma wp_region s E x e Φ :
  (∀ ρ, is_alive ρ -∗ WP subst_region' x ρ e @ s; E {{ v, is_alive ρ ∗ Φ v }}) -∗
  WP LetRegion x e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iApply wp_letregion. iIntros (ρ) "Hal".
  change (EndRegion ρ (subst_region' x ρ e))
    with (fill [EndRegionCtx ρ] (subst_region' x ρ e)).
  iApply wp_bind.
  iApply (wp_wand with "[H Hal]").
  - by iApply ("H" $! ρ with "Hal").
  - iIntros (v) "[Hal HΦ] /=". iApply (wp_endregion_val with "Hal HΦ").
Qed.

End lifting.
