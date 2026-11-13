/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteCausalControl.PathLaw

/-!
# Soft Bellman recursion for finite causal control

This file proves backward dynamic programming for finite perfect-recall behavioral policies over
one prospective policy-independent controlled kernel. The global objective is identified exactly
with the initial soft value plus accumulated rowwise KL regret.

## Main results

- `FiniteCausalControl.softValue`: the finite-horizon soft Bellman recursion.
- `FiniteCausalControl.optimalPolicy`: the normalized state-feedback Gibbs policy.
- `FiniteCausalControl.controlObjective_eq_value_add_regret`: global exact regret identity.
- `FiniteCausalControl.optimalPolicy_minimizes`: global behavioral-policy optimality.
-/

@[expose] public section

open FiniteMarkovKernels FiniteRelativeEntropy

open scoped BigOperators

universe u

namespace FiniteCausalControl

variable {H U Z : Type u} [Fintype H] [Fintype U] [Fintype Z]

/-- Expectation of a real observable under a finite probability vector. -/
noncomputable def expectation {A : Type u} [Fintype A]
    (law : ProbabilityVector A) (observable : A → ℝ) : ℝ :=
  ∑ a, law a * observable a

/-- Expectation distributes over pointwise addition. -/
theorem expectation_add {A : Type u} [Fintype A] (law : ProbabilityVector A)
    (first second : A → ℝ) :
    expectation law (fun a ↦ first a + second a) =
      expectation law first + expectation law second := by
  unfold expectation
  simp only [mul_add, Finset.sum_add_distrib]

/-- A constant scalar factors out of finite expectation. -/
theorem expectation_const_mul {A : Type u} [Fintype A] (law : ProbabilityVector A)
    (scalar : ℝ) (observable : A → ℝ) :
    expectation law (fun a ↦ scalar * observable a) =
      scalar * expectation law observable := by
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

/-- Expected continuation value under one row of the controlled kernel. -/
noncomputable def expectedNextValue (kernel : Z → U → ProbabilityVector Z)
    (continuation : Z → ℝ) (state : Z) (action : U) : ℝ :=
  expectation (kernel state action) continuation

/-- Running cost plus expected continuation value for one state-action pair. -/
noncomputable def softActionValue (kernel : Z → U → ProbabilityVector Z)
    (runningCost : Z → U → ℝ) (continuation : Z → ℝ)
    (state : Z) (action : U) : ℝ :=
  runningCost state action + expectedNextValue kernel continuation state action

/-- The entropy-regularized minimum value of one finite policy row. -/
noncomputable def softMinimum (passive : ProbabilityVector U) (energy : U → ℝ)
    (beta : ℝ) : ℝ :=
  -(1 / beta) * Real.log (passive.partitionFunction energy beta)

/-- Multiplying a soft minimum by a nonzero inverse temperature removes its scale factor. -/
theorem beta_mul_softMinimum (passive : ProbabilityVector U) (energy : U → ℝ)
    {beta : ℝ} (hbeta : beta ≠ 0) :
    beta * softMinimum passive energy beta =
      -Real.log (passive.partitionFunction energy beta) := by
  unfold softMinimum
  field_simp

/-- Backward soft Bellman value for a finite time-inhomogeneous controlled kernel. -/
noncomputable def softValue (horizon : ℕ)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (passive : ℕ → Z → ProbabilityVector U)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    (beta : ℝ) : Z → ℝ :=
  match horizon with
  | 0 => terminalCost
  | remaining + 1 =>
      fun state ↦
        softMinimum (passive 0 state)
          (softActionValue (kernel 0) (runningCost 0)
            (softValue remaining
              (fun t ↦ kernel (t + 1))
              (fun t ↦ passive (t + 1))
              (fun t ↦ runningCost (t + 1))
              terminalCost beta)
            state)
          beta

/-- The normalized Gibbs row selected by one Bellman step. -/
noncomputable def optimalRow (kernel : Z → U → ProbabilityVector Z)
    (passive : Z → ProbabilityVector U) (runningCost : Z → U → ℝ)
    (continuation : Z → ℝ) (beta : ℝ) (state : Z) : ProbabilityVector U :=
  (passive state).gibbsTilt
    (softActionValue kernel runningCost continuation state) beta

/-- The soft value obeys the one-step log-partition Bellman identity. -/
theorem beta_mul_softValue_succ (remaining : ℕ)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (passive : ℕ → Z → ProbabilityVector U)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    {beta : ℝ} (hbeta : beta ≠ 0) (state : Z) :
    beta * softValue (remaining + 1) kernel passive runningCost terminalCost beta state =
      -Real.log ((passive 0 state).partitionFunction
        (softActionValue (kernel 0) (runningCost 0)
          (softValue remaining
            (fun t ↦ kernel (t + 1))
            (fun t ↦ passive (t + 1))
            (fun t ↦ runningCost (t + 1))
            terminalCost beta)
          state)
        beta) := by
  rw [softValue]
  exact beta_mul_softMinimum _ _ hbeta

/-- The optimal row has the normalized exponential relative-advantage formula. -/
theorem optimalRow_apply (kernel : Z → U → ProbabilityVector Z)
    (passive : Z → ProbabilityVector U) (runningCost : Z → U → ℝ)
    (continuation : Z → ℝ) {beta : ℝ} (hbeta : beta ≠ 0)
    (state : Z) (action : U) :
    optimalRow kernel passive runningCost continuation beta state action =
      passive state action *
        Real.exp (-beta *
          (softActionValue kernel runningCost continuation state action -
            softMinimum (passive state)
              (softActionValue kernel runningCost continuation state) beta)) := by
  let energy := softActionValue kernel runningCost continuation state
  let partition := (passive state).partitionFunction energy beta
  have hpartition : 0 < partition :=
    ProbabilityVector.partitionFunction_pos (passive state) energy beta
  have hexponent :
      -beta * (energy action - softMinimum (passive state) energy beta) =
        -beta * energy action - Real.log partition := by
    unfold softMinimum
    field_simp
    ring
  rw [optimalRow, ProbabilityVector.gibbsTilt_apply]
  change passive state action * Real.exp (-beta * energy action) / partition =
    passive state action *
      Real.exp (-beta * (energy action - softMinimum (passive state) energy beta))
  rw [hexponent, Real.exp_sub, Real.exp_log hpartition]
  rw [div_eq_mul_inv]
  ring

/-- Optimal log action odds equal passive log odds minus scaled relative action value. -/
theorem optimalRow_log_ratio (kernel : Z → U → ProbabilityVector Z)
    (passive : Z → ProbabilityVector U)
    (hpassive : ∀ state, (passive state).FullSupport)
    (runningCost : Z → U → ℝ) (continuation : Z → ℝ)
    (beta : ℝ) (state : Z) (first second : U) :
    Real.log
        (optimalRow kernel passive runningCost continuation beta state first /
          optimalRow kernel passive runningCost continuation beta state second) =
      Real.log (passive state first / passive state second) -
        beta *
          (softActionValue kernel runningCost continuation state first -
            softActionValue kernel runningCost continuation state second) := by
  let energy := softActionValue kernel runningCost continuation state
  let partition := (passive state).partitionFunction energy beta
  have hpartition : partition ≠ 0 :=
    (ProbabilityVector.partitionFunction_pos (passive state) energy beta).ne'
  have hfirst : passive state first ≠ 0 := (hpassive state first).ne'
  have hsecond : passive state second ≠ 0 := (hpassive state second).ne'
  have hexpFirst : Real.exp (-beta * energy first) ≠ 0 := (Real.exp_pos _).ne'
  have hexpSecond : Real.exp (-beta * energy second) ≠ 0 := (Real.exp_pos _).ne'
  rw [optimalRow, ProbabilityVector.gibbsTilt_apply,
    ProbabilityVector.gibbsTilt_apply]
  change Real.log
      ((passive state first * Real.exp (-beta * energy first) / partition) /
        (passive state second * Real.exp (-beta * energy second) / partition)) = _
  rw [Real.log_div
    (div_ne_zero (mul_ne_zero hfirst hexpFirst) hpartition)
    (div_ne_zero (mul_ne_zero hsecond hexpSecond) hpartition)]
  rw [Real.log_div (mul_ne_zero hfirst hexpFirst) hpartition,
    Real.log_div (mul_ne_zero hsecond hexpSecond) hpartition]
  rw [Real.log_mul hfirst hexpFirst, Real.log_mul hsecond hexpSecond]
  rw [Real.log_exp, Real.log_exp, Real.log_div hfirst hsecond]
  ring

/-- The canonical finite-horizon state-feedback policy obtained by backward soft Bellman
recursion. -/
noncomputable def optimalPolicy (horizon : ℕ)
    {H : Type u} [Fintype H] (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (passive : ℕ → Z → ProbabilityVector U)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    (beta : ℝ) : BehavioralPolicy H U Z horizon :=
  match horizon with
  | 0 => fun t ↦ Fin.elim0 t
  | remaining + 1 =>
      fun t ↦ Fin.cases
        (fun history ↦
          optimalRow (kernel 0) (passive 0) (runningCost 0)
            (softValue remaining
              (fun s ↦ kernel (s + 1))
              (fun s ↦ passive (s + 1))
              (fun s ↦ runningCost (s + 1))
              terminalCost beta)
            beta (state history))
        (optimalPolicy remaining
          (fun history : HistoryExtension H U Z ↦ history.2)
          (fun s ↦ kernel (s + 1))
          (fun s ↦ passive (s + 1))
          (fun s ↦ runningCost (s + 1))
          terminalCost beta)
        t

/-- The first row of the optimal policy is the Bellman Gibbs row. -/
@[simp]
theorem optimalPolicy_zero (remaining : ℕ) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (passive : ℕ → Z → ProbabilityVector U)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    (beta : ℝ) (history : H) :
    optimalPolicy (remaining + 1) state kernel passive runningCost terminalCost beta 0 history =
      optimalRow (kernel 0) (passive 0) (runningCost 0)
        (softValue remaining
          (fun s ↦ kernel (s + 1))
          (fun s ↦ passive (s + 1))
          (fun s ↦ runningCost (s + 1))
          terminalCost beta)
        beta (state history) :=
  rfl

/-- Removing the first row from the optimal policy gives the shifted optimal policy. -/
@[simp]
theorem optimalPolicy_tail (remaining : ℕ) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (passive : ℕ → Z → ProbabilityVector U)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    (beta : ℝ) :
    (optimalPolicy (remaining + 1) state kernel passive runningCost terminalCost beta).tail =
      optimalPolicy remaining
        (fun history : HistoryExtension H U Z ↦ history.2)
        (fun s ↦ kernel (s + 1))
        (fun s ↦ passive (s + 1))
        (fun s ↦ runningCost (s + 1))
        terminalCost beta := by
  funext t history
  rfl

/-- Lift time-indexed state-feedback rows to a perfect-recall behavioral policy. -/
noncomputable def stateFeedbackPolicy (horizon : ℕ)
    {H : Type u} [Fintype H] (state : H → Z)
    (rows : ℕ → Z → ProbabilityVector U) : BehavioralPolicy H U Z horizon :=
  fun t history ↦
    rows t (currentState
      (fun initialHistory ↦
        let admittedHistory : {h : H // h ∈ (Finset.univ : Finset H)} :=
          ⟨initialHistory, Finset.mem_univ initialHistory⟩
        state admittedHistory.val)
      t history)

omit [Fintype Z] in
/-- The first state-feedback row uses the initial sufficient-state map. -/
@[simp]
theorem stateFeedbackPolicy_zero (remaining : ℕ) (state : H → Z)
    (rows : ℕ → Z → ProbabilityVector U) (history : H) :
    stateFeedbackPolicy (remaining + 1) state rows 0 history = rows 0 (state history) :=
  rfl

/-- The tail of a state-feedback policy is the time-shifted state-feedback policy. -/
@[simp]
theorem stateFeedbackPolicy_tail (remaining : ℕ) (state : H → Z)
    (rows : ℕ → Z → ProbabilityVector U) :
    (stateFeedbackPolicy (remaining + 1) state rows).tail =
      stateFeedbackPolicy remaining
        (fun history : HistoryExtension H U Z ↦ history.2)
        (fun t ↦ rows (t + 1)) := by
  funext t history
  rfl

omit [Fintype Z] in
/-- Full support of every state-feedback row gives full support of the behavioral policy. -/
theorem stateFeedbackPolicy_fullSupport (horizon : ℕ) (state : H → Z)
    (rows : ℕ → Z → ProbabilityVector U)
    (hrows : ∀ t state, (rows t state).FullSupport) :
    (stateFeedbackPolicy horizon state rows).FullSupport :=
  fun t history ↦ hrows t (currentState state t history)

/-- Expected additive running and terminal cost under a behavioral policy. -/
noncomputable def expectedCost (horizon : ℕ)
    {H : Type u} [Fintype H] (law : ProbabilityVector H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    (policy : BehavioralPolicy H U Z horizon) : ℝ :=
  match horizon with
  | 0 => expectation law fun history ↦ terminalCost (state history)
  | remaining + 1 =>
      (expectation law fun history ↦
        expectation (policy 0 history) (runningCost 0 (state history))) +
      expectedCost remaining
        (evolveLaw law (policy 0) (kernel 0) state)
        (fun history : HistoryExtension H U Z ↦ history.2)
        (fun t ↦ kernel (t + 1))
        (fun t ↦ runningCost (t + 1))
        terminalCost policy.tail

/-- The finite causal-control objective: strategic KL plus scaled expected additive cost. -/
noncomputable def controlObjective (horizon : ℕ)
    {H : Type u} [Fintype H] (law : ProbabilityVector H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (passive : BehavioralPolicy H U Z horizon) (hpassive : passive.FullSupport)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    (beta : ℝ) (policy : BehavioralPolicy H U Z horizon) : ℝ :=
  strategicKL horizon law kernel state policy passive hpassive +
    beta * expectedCost horizon law state kernel runningCost terminalCost policy

/-- The causal-control objective agrees with complete-path KL plus expected path cost. -/
theorem controlObjective_eq_pathKL (horizon : ℕ)
    (law : ProbabilityVector H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (passive : BehavioralPolicy H U Z horizon) (hpassive : passive.FullSupport)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    (beta : ℝ) (policy : BehavioralPolicy H U Z horizon) :
    controlObjective horizon law state kernel passive hpassive
        runningCost terminalCost beta policy =
      finiteKL (generatedPair law kernel state policy passive hpassive) +
        beta * expectedCost horizon law state kernel runningCost terminalCost policy := by
  rw [controlObjective, finiteKL_generatedPair]

/-- One nonterminal control objective separates into its first regularized row and shifted tail. -/
theorem controlObjective_succ (remaining : ℕ)
    (law : ProbabilityVector H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (passive : ℕ → Z → ProbabilityVector U)
    (hpassive : ∀ t state, (passive t state).FullSupport)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    (beta : ℝ) (policy : BehavioralPolicy H U Z (remaining + 1)) :
    controlObjective (remaining + 1) law state kernel
        (stateFeedbackPolicy (remaining + 1) state passive)
        (stateFeedbackPolicy_fullSupport (remaining + 1) state passive hpassive)
        runningCost terminalCost beta policy =
      expectation law (fun history ↦
        finiteKL (rowPair (policy 0 history) (passive 0 (state history))
          (hpassive 0 (state history))) +
        beta * expectation (policy 0 history) (runningCost 0 (state history))) +
      controlObjective remaining
        (evolveLaw law (policy 0) (kernel 0) state)
        (fun history : HistoryExtension H U Z ↦ history.2)
        (fun t ↦ kernel (t + 1))
        (stateFeedbackPolicy remaining
          (fun history : HistoryExtension H U Z ↦ history.2)
          (fun t ↦ passive (t + 1)))
        (stateFeedbackPolicy_fullSupport remaining
          (fun history : HistoryExtension H U Z ↦ history.2)
          (fun t ↦ passive (t + 1))
          (fun t state ↦ hpassive (t + 1) state))
        (fun t ↦ runningCost (t + 1))
        terminalCost beta policy.tail := by
  unfold controlObjective
  rw [strategicKL, expectedCost]
  simp only [stateFeedbackPolicy_zero, stateFeedbackPolicy_tail]
  unfold expectation
  simp only [mul_add, Finset.sum_add_distrib]
  have hscaled :
      (∑ history, law history *
        (beta * ∑ action, policy 0 history action * runningCost 0 (state history) action)) =
        beta * ∑ history, law history *
          ∑ action, policy 0 history action * runningCost 0 (state history) action := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro history _hhistory
    ring
  rw [hscaled]
  ring

/-- Accumulated rowwise KL regret relative to the Bellman Gibbs policy. -/
noncomputable def policyRegret (horizon : ℕ)
    {H : Type u} [Fintype H] (law : ProbabilityVector H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (passive : ℕ → Z → ProbabilityVector U)
    (hpassive : ∀ t state, (passive t state).FullSupport)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    (beta : ℝ) (policy : BehavioralPolicy H U Z horizon) : ℝ :=
  match horizon with
  | 0 => 0
  | remaining + 1 =>
      let continuation :=
        softValue remaining
          (fun t ↦ kernel (t + 1))
          (fun t ↦ passive (t + 1))
          (fun t ↦ runningCost (t + 1))
          terminalCost beta
      (∑ history, law history *
        finiteKL (finiteKL.gibbsPair
          (rowPair (policy 0 history) (passive 0 (state history))
            (hpassive 0 (state history)))
          (softActionValue (kernel 0) (runningCost 0) continuation
            (state history))
          beta)) +
      policyRegret remaining
        (evolveLaw law (policy 0) (kernel 0) state)
        (fun history : HistoryExtension H U Z ↦ history.2)
        (fun t ↦ kernel (t + 1))
        (fun t ↦ passive (t + 1))
        (fun t state ↦ hpassive (t + 1) state)
        (fun t ↦ runningCost (t + 1))
        terminalCost beta policy.tail

/-- Expectation under one evolved law is the corresponding iterated source-policy expectation. -/
theorem expectation_evolveLaw (law : ProbabilityVector H)
    (row : H → ProbabilityVector U) (kernel : Z → U → ProbabilityVector Z)
    (state : H → Z) (observable : HistoryExtension H U Z → ℝ) :
    expectation (evolveLaw law row kernel state) observable =
      expectation law fun history ↦
        expectation (row history) fun action ↦
          expectation (kernel (state history) action) fun nextState ↦
            observable ⟨⟨history, action⟩, nextState⟩ := by
  unfold expectation evolveLaw
  rw [Fintype.sum_sigma]
  simp only [ProbabilityVector.compound_apply]
  rw [Fintype.sum_sigma]
  simp only [ProbabilityVector.compound_apply]
  apply Finset.sum_congr rfl
  intro history _hhistory
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro action _haction
  calc
    (∑ nextState,
        (law history * row history action) *
          kernel (state history) action nextState *
            observable ⟨⟨history, action⟩, nextState⟩) =
        (law history * row history action) *
          ∑ nextState, kernel (state history) action nextState *
            observable ⟨⟨history, action⟩, nextState⟩ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro nextState _hnextState
            ring
    _ = law history *
        (row history action *
          expectation (kernel (state history) action) fun nextState ↦
            observable ⟨⟨history, action⟩, nextState⟩) := by
          unfold expectation
          ring

/-- Expectations of the new sufficient state use the controlled kernel's expected value. -/
theorem expectation_evolveLaw_currentState (law : ProbabilityVector H)
    (row : H → ProbabilityVector U) (kernel : Z → U → ProbabilityVector Z)
    (state : H → Z) (value : Z → ℝ) :
    expectation (evolveLaw law row kernel state)
        (fun history : HistoryExtension H U Z ↦ value history.2) =
      expectation law fun history ↦
        expectation (row history) fun action ↦
          expectedNextValue kernel value (state history) action := by
  rw [expectation_evolveLaw]
  rfl

/-- One Gibbs row splits its regularized objective into soft value and exact KL regret. -/
theorem rowObjective_eq_softMinimum_add_regret
    (row passive : ProbabilityVector U) (hpassive : passive.FullSupport)
    (energy : U → ℝ) {beta : ℝ} (hbeta : beta ≠ 0) :
    finiteKL (rowPair row passive hpassive) + beta * expectation row energy =
      beta * softMinimum passive energy beta +
        finiteKL (finiteKL.gibbsPair (rowPair row passive hpassive) energy beta) := by
  unfold expectation
  change finiteKL (rowPair row passive hpassive) +
      beta * ∑ a, (rowPair row passive hpassive).numerator a * energy a = _
  rw [finiteKL.gibbs_regret, beta_mul_softMinimum passive energy hbeta]
  change finiteKL (finiteKL.gibbsPair (rowPair row passive hpassive) energy beta) -
      Real.log (passive.partitionFunction energy beta) =
    -Real.log (passive.partitionFunction energy beta) +
      finiteKL (finiteKL.gibbsPair (rowPair row passive hpassive) energy beta)
  ring

/-- Running and continuation expectations form the exact one-step Bellman regret identity. -/
theorem rowObjective_eq_softValue_add_regret
    (row passive : ProbabilityVector U) (hpassive : passive.FullSupport)
    (kernel : Z → U → ProbabilityVector Z) (runningCost : Z → U → ℝ)
    (continuation : Z → ℝ) (state : Z) {beta : ℝ} (hbeta : beta ≠ 0) :
    finiteKL (rowPair row passive hpassive) +
        beta * expectation row (runningCost state) +
        beta * expectation row (expectedNextValue kernel continuation state) =
      beta * softMinimum passive
        (softActionValue kernel runningCost continuation state) beta +
        finiteKL (finiteKL.gibbsPair (rowPair row passive hpassive)
          (softActionValue kernel runningCost continuation state) beta) := by
  have henergy :
      expectation row (softActionValue kernel runningCost continuation state) =
        expectation row (runningCost state) +
          expectation row (expectedNextValue kernel continuation state) := by
    exact expectation_add row _ _
  calc
    finiteKL (rowPair row passive hpassive) +
          beta * expectation row (runningCost state) +
          beta * expectation row (expectedNextValue kernel continuation state) =
        finiteKL (rowPair row passive hpassive) +
          beta * expectation row
            (softActionValue kernel runningCost continuation state) := by
              rw [henergy]
              ring
    _ = beta * softMinimum passive
          (softActionValue kernel runningCost continuation state) beta +
        finiteKL (finiteKL.gibbsPair (rowPair row passive hpassive)
          (softActionValue kernel runningCost continuation state) beta) :=
      rowObjective_eq_softMinimum_add_regret row passive hpassive
        (softActionValue kernel runningCost continuation state) hbeta

/-- Accumulated Bellman KL regret is nonnegative. -/
theorem policyRegret_nonneg (horizon : ℕ)
    {H : Type u} [Fintype H] (law : ProbabilityVector H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (passive : ℕ → Z → ProbabilityVector U)
    (hpassive : ∀ t state, (passive t state).FullSupport)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    (beta : ℝ) (policy : BehavioralPolicy H U Z horizon) :
    0 ≤ policyRegret horizon law state kernel passive hpassive
      runningCost terminalCost beta policy := by
  induction horizon generalizing H law state kernel passive runningCost with
  | zero =>
      rfl
  | succ horizon ih =>
      rw [policyRegret]
      apply add_nonneg
      · exact Finset.sum_nonneg fun history _hhistory ↦
          mul_nonneg (law.nonneg history) (finiteKL.nonneg _)
      · exact ih
          (evolveLaw law (policy 0) (kernel 0) state)
          (fun history : HistoryExtension H U Z ↦ history.2)
          (fun t ↦ kernel (t + 1))
          (fun t ↦ passive (t + 1))
          (fun t state ↦ hpassive (t + 1) state)
          (fun t ↦ runningCost (t + 1))
          policy.tail

/-- The global causal-control objective is initial soft value plus exact accumulated KL regret. -/
theorem controlObjective_eq_value_add_regret (horizon : ℕ)
    {H : Type u} [Fintype H] (law : ProbabilityVector H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (passive : ℕ → Z → ProbabilityVector U)
    (hpassive : ∀ t state, (passive t state).FullSupport)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    {beta : ℝ} (hbeta : beta ≠ 0) (policy : BehavioralPolicy H U Z horizon) :
    controlObjective horizon law state kernel
        (stateFeedbackPolicy horizon state passive)
        (stateFeedbackPolicy_fullSupport horizon state passive hpassive)
        runningCost terminalCost beta policy =
      beta * expectation law
        (fun history ↦
          softValue horizon kernel passive runningCost terminalCost beta (state history)) +
      policyRegret horizon law state kernel passive hpassive
        runningCost terminalCost beta policy := by
  induction horizon generalizing H law state kernel passive runningCost with
  | zero =>
      unfold controlObjective strategicKL expectedCost softValue policyRegret
      ring
  | succ horizon ih =>
      let continuation :=
        softValue horizon
          (fun t ↦ kernel (t + 1))
          (fun t ↦ passive (t + 1))
          (fun t ↦ runningCost (t + 1))
          terminalCost beta
      have hfirst :
          expectation law (fun history ↦
              finiteKL (rowPair (policy 0 history) (passive 0 (state history))
                (hpassive 0 (state history))) +
              beta * expectation (policy 0 history) (runningCost 0 (state history))) +
            beta * expectation law (fun history ↦
              expectation (policy 0 history)
                (expectedNextValue (kernel 0) continuation (state history))) =
          beta * expectation law (fun history ↦
              softMinimum (passive 0 (state history))
                (softActionValue (kernel 0) (runningCost 0) continuation
                  (state history))
                beta) +
            expectation law (fun history ↦
              finiteKL (finiteKL.gibbsPair
                (rowPair (policy 0 history) (passive 0 (state history))
                  (hpassive 0 (state history)))
                (softActionValue (kernel 0) (runningCost 0) continuation
                  (state history))
                beta)) := by
        calc
          expectation law (fun history ↦
                finiteKL (rowPair (policy 0 history) (passive 0 (state history))
                  (hpassive 0 (state history))) +
                beta * expectation (policy 0 history) (runningCost 0 (state history))) +
              beta * expectation law (fun history ↦
                expectation (policy 0 history)
                  (expectedNextValue (kernel 0) continuation (state history))) =
            expectation law (fun history ↦
              (finiteKL (rowPair (policy 0 history) (passive 0 (state history))
                (hpassive 0 (state history))) +
                beta * expectation (policy 0 history) (runningCost 0 (state history))) +
              beta * expectation (policy 0 history)
                (expectedNextValue (kernel 0) continuation (state history))) := by
                  rw [← expectation_const_mul, ← expectation_add]
          _ = expectation law (fun history ↦
                beta * softMinimum (passive 0 (state history))
                  (softActionValue (kernel 0) (runningCost 0) continuation
                    (state history))
                  beta +
                finiteKL (finiteKL.gibbsPair
                  (rowPair (policy 0 history) (passive 0 (state history))
                    (hpassive 0 (state history)))
                  (softActionValue (kernel 0) (runningCost 0) continuation
                    (state history))
                  beta)) := by
                    apply congrArg (expectation law)
                    funext history
                    exact rowObjective_eq_softValue_add_regret
                      (policy 0 history) (passive 0 (state history))
                      (hpassive 0 (state history)) (kernel 0) (runningCost 0)
                      continuation (state history) hbeta
          _ = beta * expectation law (fun history ↦
                softMinimum (passive 0 (state history))
                  (softActionValue (kernel 0) (runningCost 0) continuation
                    (state history))
                  beta) +
              expectation law (fun history ↦
                finiteKL (finiteKL.gibbsPair
                  (rowPair (policy 0 history) (passive 0 (state history))
                    (hpassive 0 (state history)))
                  (softActionValue (kernel 0) (runningCost 0) continuation
                    (state history))
                  beta)) := by
                    rw [expectation_add, expectation_const_mul]
      rw [controlObjective_succ]
      rw [ih
        (evolveLaw law (policy 0) (kernel 0) state)
        (fun history : HistoryExtension H U Z ↦ history.2)
        (fun t ↦ kernel (t + 1))
        (fun t ↦ passive (t + 1))
        (fun t state ↦ hpassive (t + 1) state)
        (fun t ↦ runningCost (t + 1))
        policy.tail]
      rw (transparency := .default) [expectation_evolveLaw_currentState]
      change
        expectation law (fun history ↦
            finiteKL (rowPair (policy 0 history) (passive 0 (state history))
              (hpassive 0 (state history))) +
            beta * expectation (policy 0 history) (runningCost 0 (state history))) +
          (beta * expectation law (fun history ↦
              expectation (policy 0 history)
                (expectedNextValue (kernel 0) continuation (state history))) +
            policyRegret horizon
              (evolveLaw law (policy 0) (kernel 0) state)
              (fun history : HistoryExtension H U Z ↦ history.2)
              (fun t ↦ kernel (t + 1))
              (fun t ↦ passive (t + 1))
              (fun t state ↦ hpassive (t + 1) state)
              (fun t ↦ runningCost (t + 1))
              terminalCost beta policy.tail) = _
      rw [← add_assoc, hfirst]
      rw [softValue, policyRegret]
      dsimp only [continuation]
      unfold expectation
      ring

/-- The Bellman policy has full support whenever every passive row has full support. -/
theorem optimalPolicy_fullSupport (horizon : ℕ)
    {H : Type u} [Fintype H] (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (passive : ℕ → Z → ProbabilityVector U)
    (hpassive : ∀ t state, (passive t state).FullSupport)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    (beta : ℝ) :
    (optimalPolicy horizon state kernel passive runningCost terminalCost beta).FullSupport := by
  induction horizon generalizing H state kernel passive runningCost with
  | zero =>
      intro t
      exact Fin.elim0 t
  | succ horizon ih =>
      intro t
      refine Fin.cases ?_ (fun later ↦ ?_) t
      · intro history action
        rw (transparency := .default) [optimalPolicy_zero, optimalRow]
        exact (ProbabilityVector.gibbsTilt_pos_iff
          (passive 0 (state history))
          (softActionValue (kernel 0) (runningCost 0)
            (softValue horizon
              (fun s ↦ kernel (s + 1))
              (fun s ↦ passive (s + 1))
              (fun s ↦ runningCost (s + 1))
              terminalCost beta)
            (state history))
          beta action).mpr (hpassive 0 (state history) action)
      · intro history action
        exact ih
          (fun prior : HistoryExtension H U Z ↦ prior.2)
          (fun s ↦ kernel (s + 1))
          (fun s ↦ passive (s + 1))
          (fun s sufficientState ↦ hpassive (s + 1) sufficientState)
          (fun s ↦ runningCost (s + 1))
          later history action

/-- The Bellman policy has zero accumulated rowwise KL regret. -/
theorem policyRegret_optimalPolicy (horizon : ℕ)
    {H : Type u} [Fintype H] (law : ProbabilityVector H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (passive : ℕ → Z → ProbabilityVector U)
    (hpassive : ∀ t state, (passive t state).FullSupport)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    (beta : ℝ) :
    policyRegret horizon law state kernel passive hpassive
        runningCost terminalCost beta
        (optimalPolicy horizon state kernel passive runningCost terminalCost beta) = 0 := by
  induction horizon generalizing H law state kernel passive runningCost with
  | zero =>
      rfl
  | succ horizon ih =>
      rw [policyRegret]
      have hrow (history : H) :
          finiteKL (finiteKL.gibbsPair
            (rowPair
              (optimalPolicy (horizon + 1) state kernel passive
                runningCost terminalCost beta 0 history)
              (passive 0 (state history))
              (hpassive 0 (state history)))
            (softActionValue (kernel 0) (runningCost 0)
              (softValue horizon
                (fun t ↦ kernel (t + 1))
                (fun t ↦ passive (t + 1))
                (fun t ↦ runningCost (t + 1))
                terminalCost beta)
              (state history))
            beta) = 0 := by
        apply (finiteKL.eq_zero_iff _).mpr
        rfl
      simp only [hrow, mul_zero, Finset.sum_const_zero, zero_add]
      rw [optimalPolicy_tail]
      exact ih
        (evolveLaw law
          (optimalPolicy (horizon + 1) state kernel passive
            runningCost terminalCost beta 0)
          (kernel 0) state)
        (fun history : HistoryExtension H U Z ↦ history.2)
        (fun t ↦ kernel (t + 1))
        (fun t ↦ passive (t + 1))
        (fun t state ↦ hpassive (t + 1) state)
        (fun t ↦ runningCost (t + 1))

/-- The Bellman policy attains the global minimum over all perfect-recall behavioral policies. -/
theorem optimalPolicy_minimizes (horizon : ℕ)
    {H : Type u} [Fintype H] (law : ProbabilityVector H) (state : H → Z)
    (kernel : ℕ → Z → U → ProbabilityVector Z)
    (passive : ℕ → Z → ProbabilityVector U)
    (hpassive : ∀ t state, (passive t state).FullSupport)
    (runningCost : ℕ → Z → U → ℝ) (terminalCost : Z → ℝ)
    {beta : ℝ} (hbeta : 0 < beta) :
    let selected :=
      optimalPolicy horizon state kernel passive runningCost terminalCost beta
    controlObjective horizon law state kernel
        (stateFeedbackPolicy horizon state passive)
        (stateFeedbackPolicy_fullSupport horizon state passive hpassive)
        runningCost terminalCost beta selected =
      beta * expectation law
        (fun history ↦
          softValue horizon kernel passive runningCost terminalCost beta (state history)) ∧
    ∀ policy : BehavioralPolicy H U Z horizon,
      controlObjective horizon law state kernel
          (stateFeedbackPolicy horizon state passive)
          (stateFeedbackPolicy_fullSupport horizon state passive hpassive)
          runningCost terminalCost beta selected ≤
        controlObjective horizon law state kernel
          (stateFeedbackPolicy horizon state passive)
          (stateFeedbackPolicy_fullSupport horizon state passive hpassive)
          runningCost terminalCost beta policy := by
  dsimp only
  have hselected := controlObjective_eq_value_add_regret horizon law state
    kernel passive hpassive runningCost terminalCost hbeta.ne'
    (optimalPolicy horizon state kernel passive runningCost terminalCost beta)
  rw [policyRegret_optimalPolicy] at hselected
  simp only [add_zero] at hselected
  constructor
  · exact hselected
  · intro policy
    rw [hselected]
    rw [controlObjective_eq_value_add_regret horizon law state kernel passive
      hpassive runningCost terminalCost hbeta.ne' policy]
    exact le_add_of_nonneg_right <|
      policyRegret_nonneg horizon law state kernel passive hpassive
        runningCost terminalCost beta policy

end FiniteCausalControl
