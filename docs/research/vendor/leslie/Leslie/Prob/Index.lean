/-
Randomized-leslie extension build root.

This file is the import-aggregator for the randomized-leslie extension.
It exists so `lake build Leslie.Prob.Index` validates every production
file in the extension in one shot, instead of relying on per-file
`lake env lean` invocations.

Default `lake build` (which builds `Leslie.lean`'s import graph) does
**not** include the randomized-leslie extension — `Leslie.lean` is
main-branch code and the conservativity gate (`scripts/check-conservative.sh`)
forbids modifying it from this branch. Once randomized-leslie merges
to main, a single line `import «Leslie».Prob.Index` in `Leslie.lean`
will fold the whole extension into the default build.

## Usage

```bash
lake build Leslie.Prob.Index
```

Builds every `Leslie.Prob.*` library module and every
`Leslie.Examples.Prob.*` example. Equivalent to running
`lake env lean` on each file individually but reuses the build cache.

## What's included

  * **Library** (`Leslie.Prob.*`): the framework — `Action`,
    `Adversary`, `Coupling`, `DeterministicSimulate`, `Embed`, `PMF`,
    `Polynomial`, `Refinement`, `Secrecy`, `Trace`. Sorry-free.
  * **Examples** (`Leslie.Examples.Prob.*`): protocols + calibration —
    `AVSS`, `BenOrAsync`, `BivariateShamir`, `BrachaRBC`, `CommonCoin`,
    `CouplingDemo`, `ITMAC`, `KnuthDice`, `OneTimePad`, `RandomWalker1D`,
    `Shamir`, `Smoke`, `SyncVSS`. Sorry-free; key liveness theorems
    (`BrachaRBC.brbProb_totality_AS_fair`, `AVSS.avss_termination_AS_fair`,
    `AVSS.avss_termination_AS_fair_traj`) are axiom-clean
    (`[propext, Classical.choice, Quot.sound]`).

## What's excluded

  * `Leslie.Prob.Spike.*` — M0 spike / calibration files. `ASTSanity`
    carries a known proof placeholder that is M3-tracked separately. Spike files
    are intentionally not part of the production build.
-/

-- Mathlib-upstream candidate (parameterised Ionescu–Tulcea trajectory)
import Leslie.Mathlib.Probability.Kernel.IonescuTulcea.Bind
import Leslie.Mathlib.Probability.Kernel.IonescuTulcea.InfinitePiFubini

-- Library
import Leslie.Prob.Action
import Leslie.Prob.Adversary
import Leslie.Prob.Coupling
import Leslie.Prob.DeterministicSimulate
import Leslie.Prob.Embed
import Leslie.Prob.Liveness
import Leslie.Prob.PMF
import Leslie.Prob.Polynomial
import Leslie.Prob.RandomisedAdversary
import Leslie.Prob.Refinement
import Leslie.Prob.Secrecy
import Leslie.Prob.Trace

-- Examples
import Leslie.Examples.Prob.AVSS
import Leslie.Examples.Prob.AVSSFaithful
import Leslie.Examples.Prob.AVSSAbstract
import Leslie.Examples.Prob.BenOrAsync
import Leslie.Examples.Prob.BivariateShamir
import Leslie.Examples.Prob.BrachaRBC
import Leslie.Examples.Prob.CommonCoin
import Leslie.Examples.Prob.CouplingDemo
import Leslie.Examples.Prob.ITMAC
import Leslie.Examples.Prob.KnuthDice
import Leslie.Examples.Prob.OneTimePad
import Leslie.Examples.Prob.RandomWalker1D
import Leslie.Examples.Prob.Shamir
import Leslie.Examples.Prob.Smoke
import Leslie.Examples.Prob.SyncVSS
