/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteCausalControl
public import Mathlib.Tactic.NormNum

/-!
# Two-step stochastic control and support qualifications

The Boolean transition keeps the chosen action with probability `3/4`. Starting at false,
the two-step always-false controller assigns probability `3/16` to one specified word.
Uniform passive actions and a cost of one for true give a nonuniform Gibbs row. The same
system instantiates the exact Bellman regret and minimizer-law uniqueness theorems.
-/

@[expose] public section

open FiniteMarkovKernels FiniteRelativeEntropy

namespace FiniteCausalControl.Examples

/-- The uniform passive law on Boolean actions. -/
noncomputable def fair : ProbabilityVector Bool :=
  ProbabilityVector.boolBinary (1 / 2) (by norm_num)

/-- Both passive Boolean actions have positive probability. -/
theorem fair_fullSupport : fair.FullSupport := by
  intro action
  cases action <;> norm_num [fair, ProbabilityVector.boolBinary]

/-- A stochastic next state equals the chosen action with probability `3/4`. -/
noncomputable def noisyKernel (_time : ℕ) (_state action : Bool) : ProbabilityVector Bool :=
  ProbabilityVector.boolBinary (if action then 1 / 4 else 3 / 4) (by
    cases action <;> norm_num)

/-- The passive action law is uniform at every time and state. -/
noncomputable def passive (_time : ℕ) (_state : Bool) : ProbabilityVector Bool := fair

/-- Every row of the passive policy has full support. -/
theorem passive_fullSupport (time : ℕ) (state : Bool) : (passive time state).FullSupport :=
  fair_fullSupport

/-- Choosing true costs one; choosing false costs zero. -/
def actionCost (_time : ℕ) (_state action : Bool) : ℝ := if action then 1 else 0

/-- The terminal cost vanishes. -/
def terminalCost (_state : Bool) : ℝ := 0

/-- The initial sufficient state is false with probability one. -/
noncomputable def initial : ProbabilityVector Bool := ProbabilityVector.dirac false

/-- A two-step controller that always chooses false. -/
noncomputable def alwaysFalse : BehavioralPolicy Bool Bool Bool 2 :=
  fun _time _history ↦ ProbabilityVector.dirac false

/-- The complete word false/false/false/false/true over two transitions. -/
def stochasticWord : History Bool Bool Bool 2 := ⟨⟨⟨⟨false, false⟩, false⟩, false⟩, true⟩

/-- The generated complete law retains the exact nonzero stochastic transition masses. -/
theorem twoStep_word_mass :
    generatedLaw 2 initial id noisyKernel alwaysFalse stochasticWord = 3 / 16 := by
  change (1 : ℝ) * 1 * (3 / 4) * 1 * (1 - 3 / 4) = 3 / 16
  norm_num

/-- The Gibbs row strictly favors the cheaper false action in a terminal Bellman step. -/
theorem gibbs_prefers_cheaper_action :
    optimalRow (noisyKernel 0) (passive 0) (actionCost 0) terminalCost 1 false true <
      optimalRow (noisyKernel 0) (passive 0) (actionCost 0) terminalCost 1 false false := by
  dsimp only [optimalRow]
  rw [ProbabilityVector.gibbsTilt_apply, ProbabilityVector.gibbsTilt_apply]
  apply (div_lt_div_iff_of_pos_right
    (ProbabilityVector.partitionFunction_pos _ _ _)).2
  have hexp : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  norm_num [passive, fair, ProbabilityVector.boolBinary, softActionValue, expectedNextValue,
    expectation, terminalCost, actionCost]

/-- The full two-step objective with inverse temperature one. -/
noncomputable def objective (policy : BehavioralPolicy Bool Bool Bool 2) : ℝ :=
  controlObjective 2 initial id noisyKernel
    (stateFeedbackPolicy 2 id passive)
    (stateFeedbackPolicy_fullSupport 2 id passive passive_fullSupport)
    actionCost terminalCost 1 policy

/-- The canonical two-step Gibbs controller. -/
noncomputable def selected : BehavioralPolicy Bool Bool Bool 2 :=
  optimalPolicy 2 id noisyKernel passive actionCost terminalCost 1

/-- The objective/regret identity applies to every two-step history-dependent competitor. -/
theorem twoStep_objective_eq_value_add_regret
    (policy : BehavioralPolicy Bool Bool Bool 2) :
    objective policy =
      expectation initial (softValue 2 noisyKernel passive actionCost terminalCost 1) +
        policyRegret 2 initial id noisyKernel passive passive_fullSupport
          actionCost terminalCost 1 policy := by
  simpa [objective] using controlObjective_eq_value_add_regret 2 initial id noisyKernel
    passive passive_fullSupport actionCost terminalCost (by norm_num : (1 : ℝ) ≠ 0) policy

/-- Any policy attaining the selected objective has its complete law and supported rows. -/
theorem twoStep_minimizer_law_and_support
    (policy : BehavioralPolicy Bool Bool Bool 2)
    (hmin : objective policy = objective selected) :
    generatedLaw 2 initial id noisyKernel selected =
        generatedLaw 2 initial id noisyKernel policy ∧
      PolicyEqOnSupportedHistories 2 initial id noisyKernel selected policy := by
  exact minimizer_eq_on_selected_support 2 initial id noisyKernel passive passive_fullSupport
    actionCost terminalCost (by norm_num : (0 : ℝ) < 1) policy hmin

/-- A one-step baseline policy chooses false even at the unreachable true initial history. -/
noncomputable def baseline : BehavioralPolicy Bool Bool Bool 1 :=
  fun _time _history ↦ ProbabilityVector.dirac false

/-- This policy changes only the unreachable true initial history. -/
noncomputable def changedOffSupport : BehavioralPolicy Bool Bool Bool 1 :=
  fun time history ↦ ProbabilityVector.dirac (currentState id time history)

/-- Unreachable policy rows can differ without changing the generated complete law. -/
theorem offSupport_change_preserves_law :
    generatedLaw 1 initial id noisyKernel baseline =
      generatedLaw 1 initial id noisyKernel changedOffSupport := by
  apply generatedLaw_eq_of_policyEqOnSupportedHistories
  constructor
  · intro history hhistory
    cases history
    · rfl
    · norm_num [initial, ProbabilityVector.dirac_apply] at hhistory
  · trivial

/-- Literal equality of all policy rows is stronger than equality of complete laws. -/
theorem offSupport_policies_differ : baseline ≠ changedOffSupport := by
  intro h
  have heq := congrArg (fun policy : BehavioralPolicy Bool Bool Bool 1 ↦ policy 0 true true) h
  norm_num [baseline, changedOffSupport, currentState, ProbabilityVector.dirac_apply] at heq

end FiniteCausalControl.Examples
