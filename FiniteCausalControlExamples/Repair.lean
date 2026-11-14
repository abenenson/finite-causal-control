/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteCausalControl
public import Mathlib.Tactic.NormNum

/-!
# A one-decision repair problem

An asset is either working (`false`) or failed (`true`). Repair (`true`) costs one and
restores a working asset; waiting (`false`) leaves its state unchanged. A failed asset at
the end costs three. Both starting states and both passive actions have probability `1/2`.
The Gibbs decision therefore favors waiting when working and repair when failed.
-/

@[expose] public section

open FiniteMarkovKernels FiniteRelativeEntropy

namespace FiniteCausalControl.Examples.Repair

/-- The fair law used for the starting state and passive action. -/
noncomputable def fair : ProbabilityVector Bool :=
  ProbabilityVector.boolBinary (1 / 2) (by norm_num)

/-- Both outcomes have positive mass under the fair law. -/
theorem fair_fullSupport : fair.FullSupport := by
  intro outcome
  cases outcome <;> norm_num [fair, ProbabilityVector.boolBinary]

/-- Both working and failed assets occur initially. -/
noncomputable def initial : ProbabilityVector Bool := fair

/-- Every initial state is reached with positive probability. -/
theorem initial_fullSupport (state : Bool) : 0 < initial state :=
  fair_fullSupport state

/-- Repair restores the asset; waiting preserves its state. -/
noncomputable def transition (_time : ℕ) (state repair : Bool) : ProbabilityVector Bool :=
  ProbabilityVector.dirac (if repair then false else state)

/-- The reference action is a fair choice at either state. -/
noncomputable def passive (_time : ℕ) (_state : Bool) : ProbabilityVector Bool := fair

/-- The passive action rows have full support at every time and state. -/
theorem passive_fullSupport (time : ℕ) (state : Bool) :
    (passive time state).FullSupport := fair_fullSupport

/-- A repair costs one; waiting costs zero. -/
def runningCost (_time : ℕ) (_state repair : Bool) : ℝ := if repair then 1 else 0

/-- Ending in the failed state costs three. -/
def terminalCost (state : Bool) : ℝ := if state then 3 else 0

/-- In a working state, waiting has zero total action value. -/
theorem working_wait_value :
    softActionValue (transition 0) (runningCost 0) terminalCost false false = 0 := by
  norm_num [softActionValue, expectedNextValue, expectation, transition, runningCost,
    terminalCost, ProbabilityVector.dirac_apply, Fintype.sum_bool]

/-- In a working state, repair costs one without changing the terminal state. -/
theorem working_repair_value :
    softActionValue (transition 0) (runningCost 0) terminalCost false true = 1 := by
  norm_num [softActionValue, expectedNextValue, expectation, transition, runningCost,
    terminalCost, ProbabilityVector.dirac_apply, Fintype.sum_bool]

/-- In a failed state, waiting incurs the terminal penalty. -/
theorem failed_wait_value :
    softActionValue (transition 0) (runningCost 0) terminalCost true false = 3 := by
  norm_num [softActionValue, expectedNextValue, expectation, transition, runningCost,
    terminalCost, ProbabilityVector.dirac_apply, Fintype.sum_bool]

/-- In a failed state, repair avoids the terminal penalty. -/
theorem failed_repair_value :
    softActionValue (transition 0) (runningCost 0) terminalCost true true = 1 := by
  norm_num [softActionValue, expectedNextValue, expectation, transition, runningCost,
    terminalCost, ProbabilityVector.dirac_apply, Fintype.sum_bool]

/-- The selected controller uses the terminal cost to choose a state-dependent Gibbs row. -/
noncomputable def selected : BehavioralPolicy Bool Bool Bool 1 :=
  optimalPolicy 1 id transition passive runningCost terminalCost 1

/-- An alternative controller that always waits. -/
noncomputable def alwaysWait : BehavioralPolicy Bool Bool Bool 1 :=
  fun _time _history ↦ ProbabilityVector.dirac false

/-- When working, the selected row assigns more mass to waiting. -/
theorem working_prefers_wait : selected 0 false true < selected 0 false false := by
  change optimalRow (transition 0) (passive 0) (runningCost 0) terminalCost 1 false true <
    optimalRow (transition 0) (passive 0) (runningCost 0) terminalCost 1 false false
  dsimp only [optimalRow]
  rw [ProbabilityVector.gibbsTilt_apply, ProbabilityVector.gibbsTilt_apply]
  apply (div_lt_div_iff_of_pos_right
    (ProbabilityVector.partitionFunction_pos _ _ _)).2
  rw [working_repair_value, working_wait_value]
  have hexp : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  norm_num [passive, fair, ProbabilityVector.boolBinary] at ⊢

/-- When failed, the selected row assigns more mass to repair. -/
theorem failed_prefers_repair : selected 0 true false < selected 0 true true := by
  change optimalRow (transition 0) (passive 0) (runningCost 0) terminalCost 1 true false <
    optimalRow (transition 0) (passive 0) (runningCost 0) terminalCost 1 true true
  dsimp only [optimalRow]
  rw [ProbabilityVector.gibbsTilt_apply, ProbabilityVector.gibbsTilt_apply]
  apply (div_lt_div_iff_of_pos_right
    (ProbabilityVector.partitionFunction_pos _ _ _)).2
  rw [failed_wait_value, failed_repair_value]
  have hexp : Real.exp (-3) < Real.exp (-1) := Real.exp_lt_exp.mpr (by norm_num)
  norm_num [passive, fair, ProbabilityVector.boolBinary] at ⊢

/-- The complete one-step objective: expected cost plus strategic KL at temperature one. -/
noncomputable def objective (policy : BehavioralPolicy Bool Bool Bool 1) : ℝ :=
  controlObjective 1 initial id transition
    (stateFeedbackPolicy 1 id passive)
    (stateFeedbackPolicy_fullSupport 1 id passive passive_fullSupport)
    runningCost terminalCost 1 policy

/-- Each competitor's excess objective is exactly its nonnegative policy regret. -/
theorem objective_eq_value_add_regret (policy : BehavioralPolicy Bool Bool Bool 1) :
    objective policy =
      expectation initial (softValue 1 transition passive runningCost terminalCost 1) +
        policyRegret 1 initial id transition passive passive_fullSupport
          runningCost terminalCost 1 policy := by
  simpa [objective] using controlObjective_eq_value_add_regret 1 initial id transition
    passive passive_fullSupport runningCost terminalCost (by norm_num : (1 : ℝ) ≠ 0) policy

/-- The selected repair policy minimizes the objective against every behavioral policy. -/
theorem selected_optimal (policy : BehavioralPolicy Bool Bool Bool 1) :
    objective selected ≤ objective policy := by
  simpa [objective, selected] using
    (optimalPolicy_minimizes 1 initial id transition passive passive_fullSupport
      runningCost terminalCost (by norm_num : (0 : ℝ) < 1)).2 policy

/-- Every minimizer has the selected path law and agrees at both initial states. -/
theorem minimizer_law_and_rows (policy : BehavioralPolicy Bool Bool Bool 1)
    (hmin : objective policy = objective selected) :
    generatedLaw 1 initial id transition selected =
        generatedLaw 1 initial id transition policy ∧
      ∀ state : Bool, policy 0 state = selected 0 state := by
  have h := minimizer_eq_on_selected_support 1 initial id transition passive
    passive_fullSupport runningCost terminalCost (by norm_num : (0 : ℝ) < 1)
    policy hmin
  constructor
  · exact h.1
  · intro state
    exact (h.2.1 state (initial_fullSupport state)).symm

/-- Waiting in both states is strictly worse than the selected repair policy. -/
theorem selected_strictly_better_than_alwaysWait :
    objective selected < objective alwaysWait := by
  rcases (selected_optimal alwaysWait).lt_or_eq with hlt | heq
  · exact hlt
  · have hrow := (minimizer_law_and_rows alwaysWait heq.symm).2 true
    have hfalse := congrArg (fun row : ProbabilityVector Bool ↦ row false) hrow
    have htrue := congrArg (fun row : ProbabilityVector Bool ↦ row true) hrow
    have hp := failed_prefers_repair
    rw [← hfalse, ← htrue] at hp
    norm_num [alwaysWait, ProbabilityVector.dirac_apply] at hp

end FiniteCausalControl.Examples.Repair
