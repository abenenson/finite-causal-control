# finite-causal-control

[![Lean verification](https://github.com/abenenson/finite-causal-control/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/abenenson/finite-causal-control/actions/workflows/lean.yml)

Finite-horizon, entropy-regularized stochastic control in Lean and Mathlib.
The library constructs complete action–state histories from behavioral policies and
one policy-independent controlled transition kernel. Kernels and costs may vary with time.

The main results are:

- **Causal KL chain rule:** the KL divergence between two generated complete path laws
  with the same initial law and transition kernel is the expected sum of policy-row KLs.
- **Soft Bellman recursion:** backward log-partition recursion constructs a state-feedback
  Gibbs policy. The global objective is exactly `beta` times the initial expected soft value
  plus accumulated nonnegative KL regret.
- **Supported uniqueness:** every minimizing policy generates the same complete path law
  as the Gibbs policy and agrees with it on every reached history. Policy rows on
  unreachable histories remain unconstrained.

For a positive inverse temperature `beta`, the objective is
`beta * expectedCost + strategicKL`, including the terminal cost. The passive action rows
have full support. Transition rows may have zero coordinates. The initial law, transition
kernel, passive rows, costs, horizon, and temperature are fixed while policies vary.

## Use

```lean
import FiniteCausalControl

open FiniteMarkovKernels FiniteRelativeEntropy FiniteCausalControl

-- PathLaw: sourcePreservingPair, generatedPair, finiteKL_generatedPair
-- SoftBellman: optimalPolicy, controlObjective_eq_value_add_regret
-- SupportedUniqueness: minimizer_eq_on_selected_support
```

The opt-in `FiniteCausalControlExamples` target contains a two-step stochastic Boolean
system, an exact nonzero complete-history probability, a Gibbs preference for a cheaper
action, the complete objective/regret identity, and supported-law uniqueness.

## Dependencies and build

The library reuses the probability-vector type from
[`finite-markov-kernels`](https://github.com/abenenson/finite-markov-kernels) and the finite
KL/Gibbs theory from
[`finite-relative-entropy`](https://github.com/abenenson/finite-relative-entropy).
It uses the shared probability and KL APIs supplied by those dependencies.

The supported compiler is **Lean 4.35.0** with Mathlib
**`56a005855ea17e0b0958f73ec801ae140b0a1679`**.
The release manifest records exact dependency revisions.

```bash
python3 scripts/fetch_mathlib_cache.py
lake --rehash --wfail build
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/verify.py
```

Run these commands from the checkout root. Lake resolves the exact pinned
dependencies from their public GitHub repositories. CI uses the same public
dependency graph; see the [dependency notes](docs/overview.md#public-dependencies).

Verification rebuilds the exact authored source, runs all 16 source linters with warnings
fatal, checks public declaration coverage, and audits named public declarations' transitive
axioms against `Classical.choice`, `Quot.sound`, and `propext`.
Local release evidence is retained in [the qualification notes](docs/qualification.md).

## Scope and attribution

These are classical finite-horizon KL-control and dynamic-programming results, packaged as
a checked Lean API. The library proves no infinite-horizon or continuous-state result,
policy-dependent source theorem, numerical convergence guarantee, or global equality of
policy rows away from generated support. See [the API and overlap notes](docs/overview.md).

Copyright 2026 Adam Benenson. Apache 2.0. [LICENSE](LICENSE), [NOTICE](NOTICE), and
[ORIGIN.json](ORIGIN.json) record the public source identities and license notices.

The public entropy dependency is pinned to `ed8aadca604ae6ef79b6cf2e66dcd6157d070318`,
and its Markov dependency to `e37ed564fcc193ace7c48a94cf8f7090c2a31390`.

The checked [observation stability example](FiniteCausalControlExamples/ObservationStability.lean)
combines Bellman minimizer-law uniqueness with finite-kernel contraction: every equal-objective
controller has the same complete law, and a finite observer scales rollout distribution error
by its Dobrushin coefficient. The coefficient need not be strictly below one.

The fresh [compatibility qualification](docs/compatibility-qualification.json) records this pair.
