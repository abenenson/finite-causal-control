/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteCausalControlExamples.Basic
public import FiniteMarkovKernels.MarkovKernelContraction

/-!
# Observation stability of an optimal controlled law

The two-step Bellman minimizer determines one complete law even when policy rows differ off
support. A finite observation kernel transports that law and contracts any error in an
approximate rollout distribution by its Dobrushin coefficient. The coefficient can equal one;
no strict mixing assumption is added.

## Main result

* `twoStep_minimizer_observation_stability`: readout error for every objective minimizer.
-/

@[expose] public section

open FiniteMarkovKernels
open FiniteMarkovKernel ProbabilityVector

namespace FiniteCausalControl.Examples

/-- Every equal-objective controller inherits the same quantitative observation-error bound. -/
theorem twoStep_minimizer_observation_stability {Observation : Type*} [Fintype Observation]
    (policy : BehavioralPolicy Bool Bool Bool 2)
    (hmin : objective policy = objective selected)
    (observer : FiniteMarkovKernel (History Bool Bool Bool 2) Observation)
    (approximation : ProbabilityVector (History Bool Bool Bool 2)) :
    totalVariation (observer.apply (generatedLaw 2 initial id noisyKernel selected))
        (observer.apply approximation) ≤
      contractionCoefficient observer *
        totalVariation (generatedLaw 2 initial id noisyKernel policy) approximation := by
  let : Nonempty (History Bool Bool Bool 2) := ⟨stochasticWord⟩
  rw [(twoStep_minimizer_law_and_support policy hmin).1]
  exact totalVariation_apply_le_contractionCoefficient observer _ _

end FiniteCausalControl.Examples
