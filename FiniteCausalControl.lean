/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteCausalControl.PathLaw
public import FiniteCausalControl.SoftBellman
public import FiniteCausalControl.SupportedUniqueness

/-!
# Finite causal control

Finite-horizon behavioral control with a policy-independent stochastic kernel, exact soft
Bellman regret, and equality of minimizing complete path laws. See `README.md` for hypotheses.
-/

@[expose] public section
