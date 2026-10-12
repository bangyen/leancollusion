# Leancollusion

A Lean 4 formalization of the static game theory behind collusion-detection screens.

## What this is

The simulation repositories
[bangyen/oligopoly](https://github.com/bangyen/oligopoly) and
[bangyen/regulator](https://github.com/bangyen/regulator) study collusion
detection computationally: they simulate firms (including Q-learning agents),
compute Nash benchmarks, and calibrate detection screens against those
benchmarks. Every number in those repos reproduces from seeded scripts.

This repository formalizes the **static mathematics those screens are
calibrated against**:

- **Theorem 1** (`Leancollusion.CournotNash`): in the n-firm linear Cournot
  game, the profile qᵢ = (a−c)/(b(n+1)) is the unique symmetric pure Nash
  equilibrium.
- **Theorem 2** (`Leancollusion.MonopolyGap`): joint-monopoly output is
  strictly below Nash output for n ≥ 2, with an explicit price gap
  Δp = (a−c)(n−1)/(2b(n+1)) > 0. Hence the markup screen
  S = (p̄ − pᴺ)/(pᴹ − pᴺ) is well-defined with S(Nash) = 0 and
  S(monopoly) = 1.

Equilibrium definitions are reused from
[danlyng/Econlib](https://github.com/danlyng/Econlib), not redefined here.

## Scope & Limitations

Please read this before citing anything in this repository.

1. **These theorems justify the screens' calibration endpoints, not the
   detection itself.** Theorem 2 proves the markup screen's [0,1] scale is
   mathematically well-defined with genuinely separated endpoints. It does
   **not** prove anything about detection rates.
2. **The empirical detection findings are out of scope.** Statements like
   "the markup screen detects 100% of cartels with 25% false positives on
   myopic learners" are about *learned price trajectories from Q-learning
   dynamics* in the regulator simulations. No formalization of those
   dynamics exists here, and none is planned. Do not read this repository
   as a "Lean-proven collusion detector."
3. **Static, symmetric, linear.** The model is one-shot Cournot with linear
   inverse demand, symmetric constant marginal costs, and nonnegative
   quantities. Asymmetric costs, capacity constraints, repeated-game
   collusion sustainability, and the logit-share Bertrand model used in the
   regulator repo are all out of scope for v1.
4. **Proof discipline.** No `sorry`, no `admit`, no custom axioms. Every
   theorem traces to a textbook proposition (Tirole 1988 Ch. 7 or
   Mas-Colell Ch. 12). CI runs `#print axioms` on the main theorems and
   fails on anything beyond Mathlib's standard axioms
   (`propext`, `Classical.choice`, `Quot.sound`).

## Building

Requires [elan](https://github.com/leanprover/elan):

```sh
lake update
lake build
```

To check the axiom footprint of the main theorems:

```sh
./scripts/check_axioms.sh
```

## Layout

- `Leancollusion/Basic.lean` — Cournot game model, profit functions,
  best-response characterization.
- `Leancollusion/CournotNash.lean` — Theorem 1.
- `Leancollusion/MonopolyGap.lean` — Theorem 2 and screen calibration.
- `Leancollusion/Examples.lean` — `#eval` numeric anchors cross-checked
  against the verified simulation outputs.
