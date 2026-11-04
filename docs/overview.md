# Finite causal control: API and assumptions

`FiniteCausalControl.PathLaw` builds complete histories recursively. Each step adds an
action chosen from a history-dependent behavioral-policy row and a next state sampled
from a fixed controlled kernel. The kernel depends on time, sufficient state, and action;
it does not depend on the policy being compared. Consequently the shared initial and
source conditionals cancel in `finiteKL_generatedPair`.

`FiniteCausalControl.SoftBellman` constructs the backward soft value and normalized Gibbs
rows. `controlObjective_eq_value_add_regret` identifies the objective with `beta` times
the initial expected soft value plus KL regret, for every behavioral policy at nonzero
inverse temperature. `optimalPolicy_minimizes` advertises the positive
temperature minimization theorem. Full support is required of the passive action rows,
not of the initial law or transition rows. Perfect recall is represented by the complete
finite history, even though the selected policy uses time and sufficient state only.

`FiniteCausalControl.SupportedUniqueness` proves that zero regret identifies policy rows
on reached histories. The equality is weighted by generated history mass: an unreachable
history supplies no row constraint. Every minimizer nevertheless has the same complete
path law as the selected policy. The theorem does not erase this support qualification.

The package exports these three focused modules through `FiniteCausalControl`. The
separate example target is built by the default build and is not imported by that root.
Its shared probability and relative-entropy types come from the pinned public dependencies.

## Mathematical sources and overlap

Dynamic programming and entropy-regularized control are classical. Relevant precedents
include Richard Bellman's *Dynamic Programming* (1957), H. J. Kappen's path-integral
control work (2005), Emanuel Todorov's linearly-solvable control work, and Brian Ziebart's
maximum-causal-entropy formulation (2010). This package claims neither mathematical
priority nor an exhaustive comparison with those formulations.

The source files were extracted from the generic mathematical layer of SFT/OmegaFlow at
the commit recorded in `ORIGIN.json`. The extraction remaps package imports and the enclosing
namespace and adds a missing instance docstring. Finite KL and its Gibbs identity are shared through
`finite-relative-entropy`; finite probability vectors are shared through
`finite-markov-kernels`. The extracted source's mathematical hypotheses remain explicit.

A bounded filename search of the pinned Mathlib tree found information-theoretic and
probability-kernel foundations, but no file named for Bellman recursion or Markov decision
processes. Filename absence does not establish that an equivalent theorem is absent.
Mathlib's `Control` hierarchy concerns functional programming, not these stochastic-control
theorems. This inspection is not an upstream acceptance or novelty claim.

## Verification contract

The verifier checks every authored module and example, complete explicit public-name
coverage, exact locked dependency revisions, source hashes, warning-fatal elaboration,
all 16 source linters, and transitive axioms. Compiler and lint logs are retained for the
exact checked source. The allowed axiom set is `Classical.choice`, `Quot.sound`, and
`propext`; no custom axiom, proof hole, or warning suppression is part of the library.

The CI workflow uses read-only repository permissions and immutable action revisions.
A workflow definition, historical local receipt, hosted execution, and public release
are separate outcomes. Current source qualification is recorded with the exact release
candidate rather than inferred from the SFT source's earlier checks.

## Private CI dependencies

The `vendor` Git bundles contain the exact private dependency commits pinned by Lake.
The setup script verifies bundle hashes, manifest URLs/revisions, checkout identity and
tracked cleanliness before Lean setup. CI needs no additional repository credential.
The mathematical sources and their qualification identities are unchanged.
