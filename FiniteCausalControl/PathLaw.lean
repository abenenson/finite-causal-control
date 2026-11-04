/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteRelativeEntropy.GibbsVariational

/-!
# Finite causal path laws

This file generates complete finite histories from behavioral policy rows and one fixed
policy-independent controlled kernel. It proves that all shared source conditionals cancel from
the pathwise KL divergence.

## Main results

- `FiniteCausalControl.History`: complete alternating action-state histories.
- `FiniteCausalControl.sourcePreservingPair`: two generated laws using one controlled kernel.
- `FiniteCausalControl.finiteKL_sourcePreservingPair`: the strategic causal-KL chain rule.
-/

open FiniteMarkovKernels FiniteRelativeEntropy

open scoped BigOperators

universe u

namespace FiniteCausalControl

/-- Extend a complete history by one action and one next sufficient state. -/
abbrev HistoryExtension (H U Z : Type u) :=
  Σ _ : (Σ _ : H, U), Z

/-- Complete histories after a finite number of causal action-state extensions. -/
def History (H U Z : Type u) : ℕ → Type u
  | 0 => H
  | n + 1 => History (HistoryExtension H U Z) U Z n

/-- Complete histories over finite initial, action, and state spaces form a finite type. -/
noncomputable instance historyFintype
    {H U Z : Type u}
    [Fintype H] [Fintype U] [Fintype Z] (n : ℕ) :
    Fintype (History H U Z n) := by
  induction n generalizing H with
  | zero =>
      simp only [History]
      infer_instance
  | succ n ih =>
      simp only [History]
      exact ih

/-- The current sufficient state carried by a complete history. -/
def currentState {H U Z : Type u}
    (initialState : H → Z) : ∀ n, History H U Z n → Z
  | 0 => initialState
  | n + 1 => currentState (fun history : HistoryExtension H U Z ↦ history.2) n

/-- A finite-horizon randomized behavioral policy on complete histories. -/
abbrev BehavioralPolicy
    (H U Z : Type u) [Fintype U] (horizon : ℕ) :=
  ∀ t : Fin horizon, History H U Z t → ProbabilityVector U

namespace BehavioralPolicy

variable {H U Z : Type u}
  [Fintype H] [Fintype U] [Fintype Z]

/-- Every row of a behavioral policy has full support. -/
def FullSupport {horizon : ℕ} (policy : BehavioralPolicy H U Z horizon) : Prop :=
  ∀ t history, (policy t history).FullSupport

/-- Remove the first row from a nonempty behavioral policy. -/
def tail {horizon : ℕ} (policy : BehavioralPolicy H U Z (horizon + 1)) :
    BehavioralPolicy (HistoryExtension H U Z) U Z horizon :=
  fun t ↦ policy t.succ

omit [Fintype H] [Fintype Z] in
/-- Full support is inherited by the tail of a behavioral policy. -/
theorem FullSupport.tail {horizon : ℕ} {policy : BehavioralPolicy H U Z (horizon + 1)}
    (h : policy.FullSupport) : policy.tail.FullSupport :=
  fun t history ↦ h t.succ history

end BehavioralPolicy

variable {H U Z : Type u}
  [Fintype H] [Fintype U] [Fintype Z]

/-- Advance a complete-history law by one policy row and one fixed controlled kernel. -/
noncomputable def evolveLaw (law : ProbabilityVector H)
    (row : H → ProbabilityVector U) (kernel : Z → U → ProbabilityVector Z)
    (state : H → Z) : ProbabilityVector (HistoryExtension H U Z) :=
  (law.compound row).compound fun historyAction ↦
    kernel (state historyAction.1) historyAction.2

/-- A policy row is admissible relative to a full-support passive row. -/
def rowPair (row passive : ProbabilityVector U) (hpassive : passive.FullSupport) :
    AdmissiblePair U where
  numerator := row
  reference := passive
  absolutelyContinuous := fun u hzero ↦ (hpassive u).ne' hzero |>.elim

/-- Extend an admissible pair by policy rows and then by one shared controlled kernel. -/
noncomputable def sourcePreservingStep (pair : AdmissiblePair H)
    (row passive : H → ProbabilityVector U)
    (hpassive : ∀ history, (passive history).FullSupport)
    (kernel : Z → U → ProbabilityVector Z) (state : H → Z) :
    AdmissiblePair (HistoryExtension H U Z) :=
  (pair.compound fun history ↦ rowPair (row history) (passive history) (hpassive history)).compound
    fun historyAction ↦ AdmissiblePair.diagonal
      (kernel (state historyAction.1) historyAction.2)

/-- The numerator of a shared-kernel step is the corresponding evolved law. -/
@[simp]
theorem sourcePreservingStep_numerator (pair : AdmissiblePair H)
    (row passive : H → ProbabilityVector U)
    (hpassive : ∀ history, (passive history).FullSupport)
    (kernel : Z → U → ProbabilityVector Z) (state : H → Z) :
    (sourcePreservingStep pair row passive hpassive kernel state).numerator =
      evolveLaw pair.numerator row kernel state :=
  rfl

/-- The reference of a shared-kernel step is the corresponding passive evolved law. -/
@[simp]
theorem sourcePreservingStep_reference (pair : AdmissiblePair H)
    (row passive : H → ProbabilityVector U)
    (hpassive : ∀ history, (passive history).FullSupport)
    (kernel : Z → U → ProbabilityVector Z) (state : H → Z) :
    (sourcePreservingStep pair row passive hpassive kernel state).reference =
      evolveLaw pair.reference passive kernel state :=
  rfl

/-- One shared-kernel extension adds only the expected policy-row KL. -/
theorem finiteKL_sourcePreservingStep (pair : AdmissiblePair H)
    (row passive : H → ProbabilityVector U)
    (hpassive : ∀ history, (passive history).FullSupport)
    (kernel : Z → U → ProbabilityVector Z) (state : H → Z) :
    finiteKL (sourcePreservingStep pair row passive hpassive kernel state) =
      finiteKL pair +
        ∑ history, pair.numerator history *
          finiteKL (rowPair (row history) (passive history) (hpassive history)) := by
  unfold sourcePreservingStep
  rw [finiteKL.compound, finiteKL.compound]
  simp only [finiteKL.diagonal, mul_zero, Finset.sum_const_zero, add_zero]

/-- Generate an admissible pair of complete path laws using the same controlled kernel. -/
noncomputable def sourcePreservingPair (horizon : ℕ)
    {H : Type u} [Fintype H] (pair : AdmissiblePair H)
    (kernel : ℕ → Z → U → ProbabilityVector Z) (state : H → Z)
    (policy passive : BehavioralPolicy H U Z horizon)
    (hpassive : passive.FullSupport) : AdmissiblePair (History H U Z horizon) :=
  match horizon with
  | 0 => pair
  | remaining + 1 =>
      sourcePreservingPair remaining
        (sourcePreservingStep pair (policy 0) (passive 0) (hpassive 0)
          (kernel 0) state)
        (fun t ↦ kernel (t + 1))
        (fun history : HistoryExtension H U Z ↦ history.2)
        policy.tail passive.tail hpassive.tail
termination_by horizon

/-- The accumulated policy-row KL, weighted by the generated numerator history law. -/
noncomputable def strategicKL (horizon : ℕ)
    {H : Type u} [Fintype H] (law : ProbabilityVector H)
    (kernel : ℕ → Z → U → ProbabilityVector Z) (state : H → Z)
    (policy passive : BehavioralPolicy H U Z horizon)
    (hpassive : passive.FullSupport) : ℝ :=
  match horizon with
  | 0 => 0
  | remaining + 1 =>
      (∑ history, law history *
        finiteKL (rowPair (policy 0 history) (passive 0 history)
          (hpassive 0 history))) +
      strategicKL remaining
        (evolveLaw law (policy 0) (kernel 0) state)
        (fun t ↦ kernel (t + 1))
        (fun history : HistoryExtension H U Z ↦ history.2)
        policy.tail passive.tail hpassive.tail
termination_by horizon

/-- Shared policy-independent source conditionals cancel from complete-path finite KL. -/
theorem finiteKL_sourcePreservingPair (horizon : ℕ)
    {H : Type u} [Fintype H] (pair : AdmissiblePair H)
    (kernel : ℕ → Z → U → ProbabilityVector Z) (state : H → Z)
    (policy passive : BehavioralPolicy H U Z horizon)
    (hpassive : passive.FullSupport) :
    finiteKL (sourcePreservingPair horizon pair kernel state policy passive hpassive) =
      finiteKL pair +
        strategicKL horizon pair.numerator kernel state policy passive hpassive := by
  induction horizon generalizing H kernel with
  | zero =>
      simp! only [sourcePreservingPair, strategicKL, add_zero]
  | succ horizon ih =>
      rw (config := { transparency := .default }) [sourcePreservingPair, ih
        (sourcePreservingStep pair (policy 0) (passive 0) (hpassive 0)
          (kernel 0) state)
        (fun t ↦ kernel (t + 1))
        (fun history : HistoryExtension H U Z ↦ history.2)
        policy.tail passive.tail hpassive.tail]
      rw (config := { transparency := .default }) [finiteKL_sourcePreservingStep]
      rw (config := { transparency := .default }) [strategicKL]
      rw (config := { transparency := .default }) [sourcePreservingStep_numerator]
      ring

/-- The two complete path laws generated from one common initial law. -/
noncomputable def generatedPair (initial : ProbabilityVector H)
    (kernel : ℕ → Z → U → ProbabilityVector Z) (state : H → Z)
    {horizon : ℕ} (policy passive : BehavioralPolicy H U Z horizon)
    (hpassive : passive.FullSupport) : AdmissiblePair (History H U Z horizon) :=
  sourcePreservingPair horizon (AdmissiblePair.diagonal initial) kernel state
    policy passive hpassive

/-- Exact strategic causal-KL chain rule for laws with a common initial law and source kernel. -/
theorem finiteKL_generatedPair (initial : ProbabilityVector H)
    (kernel : ℕ → Z → U → ProbabilityVector Z) (state : H → Z)
    {horizon : ℕ} (policy passive : BehavioralPolicy H U Z horizon)
    (hpassive : passive.FullSupport) :
    finiteKL (generatedPair initial kernel state policy passive hpassive) =
      strategicKL horizon initial kernel state policy passive hpassive := by
  rw [generatedPair, finiteKL_sourcePreservingPair, finiteKL.diagonal, zero_add]
  rfl

end FiniteCausalControl
