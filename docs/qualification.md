# Local release qualification

The release candidate passed local qualification on 2026-11-04 with Lean 4.34.1 and
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The exact source hashes, pinned
dependency revisions, commands, and results are retained in
[the receipt](release-logs/qualification.json).
[Configuration and verifier hashes](release-logs/input-hashes.json) identify the other inputs.

- All six authored library and example modules were rebuilt from their actual source,
  after removing previously built authored artifacts, with warnings fatal.
- Each module passed all 16 environment linters, including definition and theorem
  documentation checks. No warning suppression was used.
- All 84 explicit public declarations passed the transitive axiom audit. The allowed
  axiom set was `Classical.choice`, `Quot.sound`, and `propext`.
- All 14 verifier regression controls passed, including stale-artifact, diagnostic,
  dependency-name, and import-boundary rejection checks.

The guarded verification completed in approximately 48 seconds with two CPUs and a
16 GiB memory ceiling. Peak sampled process-tree RSS was 2,497,961,984 bytes. The
[resource receipt](release-logs/resources.json) records no surviving processes. Raw build,
lint, axiom, regression-control, resource, and disk evidence is in [release-logs](release-logs/).

The checked examples include a two-step stochastic path of mass `3/16`, a Gibbs row
strictly preferring the cheaper action, the exact global regret identity, supported
minimizer uniqueness, and unequal policies producing equal laws through an unreachable row.

Qualification reused the shared probability and KL libraries at the exact revisions
`de78502c3f191840bc6b3ff55d2be5e9d66ca122` and
`ab89211562f15ebff49e9bda0d88a4bc8cdf32dd`, respectively. Both local dependency checkouts
were clean and matched those pins before the run. All release dependencies are recorded
as Git URLs and exact revisions, with no local dependency paths in the Lake manifest.

This is local qualification of that dependency graph. Fresh remote dependency replay,
hosted CI, and public repository publication are separate steps. The immutable CI workflow
repeats the same source verifier on pushes and pull requests.
