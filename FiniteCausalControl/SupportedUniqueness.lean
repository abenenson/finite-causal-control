/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteCausalControl.SoftBellman

/-!
# Supported-history uniqueness for finite causal control

This file converts zero Bellman regret into equality of policy rows exactly on histories reached
by the selected law. It then proves literal uniqueness of the generated complete path law, while
making no claim about off-support policy rows.

## Main results

- `FiniteCausalControl.PolicyEqOnSupportedHistories`: supported behavioral-policy equality.
- `FiniteCausalControl.minimizer_eq_on_selected_support`: supported policy and path-law uniqueness.
-/

@[expose] public section

open FiniteMarkovKernels FiniteRelativeEntropy

open scoped BigOperators

universe u

namespace FiniteCausalControl

variable {H U Z : Type u} [Fintype H] [Fintype U] [Fintype Z]

/-- Generate one complete path law from an initial law, behavioral policy, and fixed kernel. -/
noncomputable def generatedLaw (horizon : ℕ)
    {H : Type u} [Fintype H] (law : ProbabilityVector H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (policy : BehavioralPolicy H U Z horizon) :
    ProbabilityVector (History H U Z horizon) :=
  match horizon with
  | 0 => law
  | remaining + 1 =>
      generatedLaw remaining
        (evolveLaw law (policy 0) (kernel 0) state)
        (fun history : HistoryExtension H U Z ↦ history.2)
        (fun t ↦ kernel (t + 1))
        policy.tail

/-- The numerator of a source-preserving pair is its directly generated policy law. -/
theorem sourcePreservingPair_numerator_eq_generatedLaw (horizon : ℕ)
    {H : Type u} [Fintype H] (pair : AdmissiblePair H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (policy passive : BehavioralPolicy H U Z horizon)
    (hpassive : passive.FullSupport) :
    (sourcePreservingPair horizon pair kernel state policy passive hpassive).numerator =
      generatedLaw horizon pair.numerator state kernel policy := by
  induction horizon generalizing H pair kernel with
  | zero =>
      simp only [sourcePreservingPair, generatedLaw]
  | succ horizon ih =>
      rw [sourcePreservingPair, generatedLaw]
      rw [ih
        (sourcePreservingStep pair (policy 0) (passive 0) (hpassive 0)
          (kernel 0) state)
        (fun history : HistoryExtension H U Z ↦ history.2)
        (fun t ↦ kernel (t + 1))
        policy.tail passive.tail hpassive.tail]
      rw (config := { transparency := .default }) [sourcePreservingStep_numerator]

/-- The reference of a source-preserving pair is its directly generated passive law. -/
theorem sourcePreservingPair_reference_eq_generatedLaw (horizon : ℕ)
    {H : Type u} [Fintype H] (pair : AdmissiblePair H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (policy passive : BehavioralPolicy H U Z horizon)
    (hpassive : passive.FullSupport) :
    (sourcePreservingPair horizon pair kernel state policy passive hpassive).reference =
      generatedLaw horizon pair.reference state kernel passive := by
  induction horizon generalizing H pair kernel with
  | zero =>
      simp only [sourcePreservingPair, generatedLaw]
  | succ horizon ih =>
      rw [sourcePreservingPair, generatedLaw]
      rw [ih
        (sourcePreservingStep pair (policy 0) (passive 0) (hpassive 0)
          (kernel 0) state)
        (fun history : HistoryExtension H U Z ↦ history.2)
        (fun t ↦ kernel (t + 1))
        policy.tail passive.tail hpassive.tail]
      rw (config := { transparency := .default }) [sourcePreservingStep_reference]

/-- The complete path law in `generatedPair` is the directly generated policy law. -/
theorem generatedPair_numerator_eq_generatedLaw (horizon : ℕ)
    (law : ProbabilityVector H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (policy passive : BehavioralPolicy H U Z horizon)
    (hpassive : passive.FullSupport) :
    (generatedPair law kernel state policy passive hpassive).numerator =
      generatedLaw horizon law state kernel policy := by
  rw [generatedPair, sourcePreservingPair_numerator_eq_generatedLaw]
  rfl

/-- The reference path law in `generatedPair` is the directly generated passive law. -/
theorem generatedPair_reference_eq_generatedLaw (horizon : ℕ)
    (law : ProbabilityVector H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (policy passive : BehavioralPolicy H U Z horizon)
    (hpassive : passive.FullSupport) :
    (generatedPair law kernel state policy passive hpassive).reference =
      generatedLaw horizon law state kernel passive := by
  rw [generatedPair, sourcePreservingPair_reference_eq_generatedLaw]
  rfl

/-- Equality of policy rows on every history reached by the first policy. -/
def PolicyEqOnSupportedHistories (horizon : ℕ)
    {H : Type u} [Fintype H] (law : ProbabilityVector H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (first second : BehavioralPolicy H U Z horizon) : Prop :=
  match horizon with
  | 0 => True
  | remaining + 1 =>
      (∀ history, 0 < law history → first 0 history = second 0 history) ∧
      PolicyEqOnSupportedHistories remaining
        (evolveLaw law (first 0) (kernel 0) state)
        (fun history : HistoryExtension H U Z ↦ history.2)
        (fun t ↦ kernel (t + 1))
        first.tail second.tail

/-- Rows equal on the support of a law induce the same one-step evolved law. -/
theorem evolveLaw_eq_of_rows_eq_on_support (law : ProbabilityVector H)
    (first second : H → ProbabilityVector U)
    (kernel : Z → U → ProbabilityVector Z) (state : H → Z)
    (hrows : ∀ history, 0 < law history → first history = second history) :
    evolveLaw law first kernel state = evolveLaw law second kernel state := by
  apply ProbabilityVector.ext
  rintro ⟨⟨history, action⟩, nextState⟩
  simp only [evolveLaw, ProbabilityVector.compound_apply]
  by_cases hzero : law history = 0
  · simp [hzero]
  · have hpositive : 0 < law history :=
      lt_of_le_of_ne (law.nonneg history) fun hEq ↦ hzero hEq.symm
    rw [hrows history hpositive]

/-- Supported policy equality forces literal equality of the generated complete path laws. -/
theorem generatedLaw_eq_of_policyEqOnSupportedHistories (horizon : ℕ)
    {H : Type u} [Fintype H] (law : ProbabilityVector H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (first second : BehavioralPolicy H U Z horizon)
    (hpolicy : PolicyEqOnSupportedHistories horizon law state kernel first second) :
    generatedLaw horizon law state kernel first =
      generatedLaw horizon law state kernel second := by
  induction horizon generalizing H law state kernel with
  | zero =>
      rfl
  | succ horizon ih =>
      rcases hpolicy with ⟨hrow, htail⟩
      have hevolve :=
        evolveLaw_eq_of_rows_eq_on_support law (first 0) (second 0)
          (kernel 0) state hrow
      rw [generatedLaw, generatedLaw, hevolve]
      exact ih
        (evolveLaw law (second 0) (kernel 0) state)
        (fun history : HistoryExtension H U Z ↦ history.2)
        (fun t ↦ kernel (t + 1))
        first.tail second.tail (by simpa [hevolve] using htail)

/-- A policy agrees with the Bellman row on every history in its own generated support. -/
def IsBellmanOnOwnSupportedHistories (horizon : ℕ)
    {H : Type u} [Fintype H] (law : ProbabilityVector H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (passive : ℕ → Z → ProbabilityVector U)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    (beta : ℝ) (policy : BehavioralPolicy H U Z horizon) : Prop :=
  match horizon with
  | 0 => True
  | remaining + 1 =>
      let continuation :=
        softValue remaining
          (fun t ↦ kernel (t + 1))
          (fun t ↦ passive (t + 1))
          (fun t ↦ runningCost (t + 1))
          terminalCost beta
      (∀ history, 0 < law history →
        policy 0 history =
          optimalRow (kernel 0) (passive 0) (runningCost 0)
            continuation beta (state history)) ∧
      IsBellmanOnOwnSupportedHistories remaining
        (evolveLaw law (policy 0) (kernel 0) state)
        (fun history : HistoryExtension H U Z ↦ history.2)
        (fun t ↦ kernel (t + 1))
        (fun t ↦ passive (t + 1))
        (fun t ↦ runningCost (t + 1))
        terminalCost beta policy.tail

/-- Zero global Bellman regret identifies every policy row on its reached histories. -/
theorem isBellmanOnOwnSupportedHistories_of_policyRegret_eq_zero (horizon : ℕ)
    {H : Type u} [Fintype H] (law : ProbabilityVector H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (passive : ℕ → Z → ProbabilityVector U)
    (hpassive : ∀ t state, (passive t state).FullSupport)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    (beta : ℝ) (policy : BehavioralPolicy H U Z horizon)
    (hzero : policyRegret horizon law state kernel passive hpassive
      runningCost terminalCost beta policy = 0) :
    IsBellmanOnOwnSupportedHistories horizon law state kernel passive
      runningCost terminalCost beta policy := by
  induction horizon generalizing H law state kernel passive runningCost with
  | zero =>
      trivial
  | succ horizon ih =>
      let continuation :=
        softValue horizon
          (fun t ↦ kernel (t + 1))
          (fun t ↦ passive (t + 1))
          (fun t ↦ runningCost (t + 1))
          terminalCost beta
      let currentRegret :=
        ∑ history, law history *
          finiteKL (finiteKL.gibbsPair
            (rowPair (policy 0 history) (passive 0 (state history))
              (hpassive 0 (state history)))
            (softActionValue (kernel 0) (runningCost 0) continuation
              (state history))
            beta)
      let tailRegret :=
        policyRegret horizon
          (evolveLaw law (policy 0) (kernel 0) state)
          (fun history : HistoryExtension H U Z ↦ history.2)
          (fun t ↦ kernel (t + 1))
          (fun t ↦ passive (t + 1))
          (fun t state ↦ hpassive (t + 1) state)
          (fun t ↦ runningCost (t + 1))
          terminalCost beta policy.tail
      have hdecomposition : currentRegret + tailRegret = 0 := by
        simpa only [policyRegret, continuation, currentRegret, tailRegret] using hzero
      have hcurrentNonneg : 0 ≤ currentRegret := by
        dsimp only [currentRegret]
        exact Finset.sum_nonneg fun history _hhistory ↦
          mul_nonneg (law.nonneg history) (finiteKL.nonneg _)
      have htailNonneg : 0 ≤ tailRegret := by
        dsimp only [tailRegret]
        exact policyRegret_nonneg horizon
          (evolveLaw law (policy 0) (kernel 0) state)
          (fun history : HistoryExtension H U Z ↦ history.2)
          (fun t ↦ kernel (t + 1))
          (fun t ↦ passive (t + 1))
          (fun t state ↦ hpassive (t + 1) state)
          (fun t ↦ runningCost (t + 1))
          terminalCost beta policy.tail
      have hcurrentZero : currentRegret = 0 := by
        linarith
      have htailZero : tailRegret = 0 := by
        linarith
      constructor
      · intro history hhistory
        have hterm :
            law history *
              finiteKL (finiteKL.gibbsPair
                (rowPair (policy 0 history) (passive 0 (state history))
                  (hpassive 0 (state history)))
                (softActionValue (kernel 0) (runningCost 0) continuation
                  (state history))
                beta) = 0 := by
          apply (Finset.sum_eq_zero_iff_of_nonneg
            (fun item _hitem ↦
              mul_nonneg (law.nonneg item) (finiteKL.nonneg _))).mp
            (by simpa only [currentRegret] using hcurrentZero)
          exact Finset.mem_univ history
        have hkl :
            finiteKL (finiteKL.gibbsPair
              (rowPair (policy 0 history) (passive 0 (state history))
                (hpassive 0 (state history)))
              (softActionValue (kernel 0) (runningCost 0) continuation
                (state history))
              beta) = 0 := by
          rcases mul_eq_zero.mp hterm with hlaw | hkl
          · exact (hhistory.ne' hlaw).elim
          · exact hkl
        have heq := (finiteKL.eq_zero_iff _).mp hkl
        change policy 0 history =
          optimalRow (kernel 0) (passive 0) (runningCost 0)
            continuation beta (state history) at heq
        exact heq
      · apply ih
          (evolveLaw law (policy 0) (kernel 0) state)
          (fun history : HistoryExtension H U Z ↦ history.2)
          (fun t ↦ kernel (t + 1))
          (fun t ↦ passive (t + 1))
          (fun t state ↦ hpassive (t + 1) state)
          (fun t ↦ runningCost (t + 1))
          policy.tail
        exact htailZero

/-- Bellman agreement on a policy's own support is equality on the selected policy's support. -/
theorem policyEqOnSelectedSupport_of_isBellmanOnOwnSupport (horizon : ℕ)
    {H : Type u} [Fintype H] (law : ProbabilityVector H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (passive : ℕ → Z → ProbabilityVector U)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    (beta : ℝ) (policy : BehavioralPolicy H U Z horizon)
    (hbellman : IsBellmanOnOwnSupportedHistories horizon law state kernel passive
      runningCost terminalCost beta policy) :
    PolicyEqOnSupportedHistories horizon law state kernel
      (optimalPolicy horizon state kernel passive runningCost terminalCost beta)
      policy := by
  induction horizon generalizing H law state kernel passive runningCost with
  | zero =>
      trivial
  | succ horizon ih =>
      rcases hbellman with ⟨hrow, htail⟩
      constructor
      · intro history hhistory
        exact (hrow history hhistory).symm
      · have hevolve :
            evolveLaw law
                (optimalPolicy (horizon + 1) state kernel passive
                  runningCost terminalCost beta 0)
                (kernel 0) state =
              evolveLaw law (policy 0) (kernel 0) state := by
          apply evolveLaw_eq_of_rows_eq_on_support
          intro history hhistory
          exact (hrow history hhistory).symm
        change PolicyEqOnSupportedHistories horizon
          (evolveLaw law
            (optimalPolicy (horizon + 1) state kernel passive
              runningCost terminalCost beta 0)
            (kernel 0) state)
          (fun history : HistoryExtension H U Z ↦ history.2)
          (fun t ↦ kernel (t + 1))
          (optimalPolicy horizon
            (fun history : HistoryExtension H U Z ↦ history.2)
            (fun t ↦ kernel (t + 1))
            (fun t ↦ passive (t + 1))
            (fun t ↦ runningCost (t + 1))
            terminalCost beta)
          policy.tail
        rw [hevolve]
        exact ih
          (evolveLaw law (policy 0) (kernel 0) state)
          (fun history : HistoryExtension H U Z ↦ history.2)
          (fun t ↦ kernel (t + 1))
          (fun t ↦ passive (t + 1))
          (fun t ↦ runningCost (t + 1))
          policy.tail htail

/-- Every global minimizer has the selected complete path law and agrees on selected support. -/
theorem minimizer_eq_on_selected_support (horizon : ℕ)
    {H : Type u} [Fintype H] (law : ProbabilityVector H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (passive : ℕ → Z → ProbabilityVector U)
    (hpassive : ∀ t state, (passive t state).FullSupport)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    {beta : ℝ} (hbeta : 0 < beta) (policy : BehavioralPolicy H U Z horizon)
    (hminimizer :
      controlObjective horizon law state kernel
          (stateFeedbackPolicy horizon state passive)
          (stateFeedbackPolicy_fullSupport horizon state passive hpassive)
          runningCost terminalCost beta policy =
        controlObjective horizon law state kernel
          (stateFeedbackPolicy horizon state passive)
          (stateFeedbackPolicy_fullSupport horizon state passive hpassive)
          runningCost terminalCost beta
          (optimalPolicy horizon state kernel passive runningCost terminalCost beta)) :
    let selected :=
      optimalPolicy horizon state kernel passive runningCost terminalCost beta
    generatedLaw horizon law state kernel selected =
        generatedLaw horizon law state kernel policy ∧
      PolicyEqOnSupportedHistories horizon law state kernel selected policy := by
  dsimp only
  have hpolicy := controlObjective_eq_value_add_regret horizon law state
    kernel passive hpassive runningCost terminalCost hbeta.ne' policy
  have hselected := controlObjective_eq_value_add_regret horizon law state
    kernel passive hpassive runningCost terminalCost hbeta.ne'
    (optimalPolicy horizon state kernel passive runningCost terminalCost beta)
  rw [policyRegret_optimalPolicy] at hselected
  simp only [add_zero] at hselected
  have hregret :
      policyRegret horizon law state kernel passive hpassive
        runningCost terminalCost beta policy = 0 := by
    linarith
  have hown :=
    isBellmanOnOwnSupportedHistories_of_policyRegret_eq_zero horizon law state
      kernel passive hpassive runningCost terminalCost beta policy hregret
  have hsupport :=
    policyEqOnSelectedSupport_of_isBellmanOnOwnSupport horizon law state
      kernel passive runningCost terminalCost beta policy hown
  exact ⟨generatedLaw_eq_of_policyEqOnSupportedHistories horizon law state
    kernel _ _ hsupport, hsupport⟩

end FiniteCausalControl
