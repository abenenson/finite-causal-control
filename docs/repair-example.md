# A one-decision repair example

[`FiniteCausalControlExamples/Repair.lean`](../FiniteCausalControlExamples/Repair.lean)
works through a small finite control problem. An asset starts either **working** or
**failed**, each with probability `1/2`. The controller chooses **wait** or **repair**.
Repair costs `1` and restores a working asset; waiting preserves the state. A failed
asset at the end costs `3`. The passive action law assigns probability `1/2` to each
choice, and the inverse temperature is `1`.

| Starting state | Wait: cost plus terminal cost | Repair: cost plus terminal cost | Selected preference |
| --- | ---: | ---: | --- |
| Working | `0` | `1` | Wait |
| Failed | `3` | `1` | Repair |

The one-step Bellman row tilts the passive probabilities by `exp(-action value)`.
Consequently, the selected repair probability is
`exp(-1) / (1 + exp(-1))` when working and
`exp(-1) / (exp(-3) + exp(-1))` when failed. Both choices keep positive probability:
the controller is entropy-regularized, and each passive action has positive mass.

The Lean example proves each of the four action values and both strict preferences.
For every behavioral policy, it then applies the library's exact identity

```text
objective(policy) = E_initial[softValue] + policyRegret(policy).
```

The selected policy minimizes this objective. Because **both** initial states have
positive mass, every policy attaining the same objective matches the selected action
row at each state and generates the same complete state–action–state law. In particular,
the example proves that always waiting has **strictly larger** objective: equality
would force its failed-state row to equal the selected row, contradicting the selected
row's strict preference for repair.

This is a finite-horizon, one-decision result. The transition is deterministic, so
its zero-probability coordinates are permitted; full support is assumed of the passive
action law. The result concerns the stated expected-cost-plus-KL objective and makes
no claim about an unregularized optimum or a numerical algorithm.
