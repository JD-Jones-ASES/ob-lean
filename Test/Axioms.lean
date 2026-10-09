module

import Solution
import Lean.Util.CollectAxioms

/-!
# Axiom audit

A module file importing `Solution` (not `Challenge.lean`). Walks every constant of the environment
whose name begins with `OddBarker.`, `_private.OB.` or `_private.Solution.` (the public declarations
of this development; the private auxiliaries that Lean generates are not enumerated under the module
system, but `collectAxioms` reaches every private constant a public proof refers to, including a
private `axiom`), and collects the axioms each depends on. Anything outside `propext`,
`Classical.choice`, `Quot.sound` is reported with `logError`, which fails `lake build`. The audit
also fails if it matched fewer constants than the floor below (so a renamed namespace cannot make it
pass vacuously) or if any of the compared theorems is missing from the environment.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in env.constants.toList do
    let label := name.toString
    if label.startsWith "OddBarker." || label.startsWith "_private.OB." ||
        label.startsWith "_private.Solution." then
      checked := checked + 1
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          rejected := rejected + 1
          logError m!"Unexpected axiom dependency: {name} -> {ax}"
  unless checked ≥ 80 do
    logError m!"Axiom audit matched only {checked} project constants; expected at least 80"
  for n in [`OddBarker.odd_length_mem,
      `OddBarker.odd_exists_iff,
      `OddBarker.aperiodic_eq,
      `OddBarker.skew,
      `OddBarker.fold,
      `OddBarker.doubling,
      `OddBarker.run_bounds,
      `OddBarker.four_dvd_of_even,
      `OddBarker.existsRealCirculantHadamard_of_even,
      `OddBarker.exists_iff_of_even,
      `OddBarker.length_le_thirteen_of_even,
      `OddBarker.exists_iff_of_circulantHadamard,
      `OddBarker.length_le_thirteen_of_circulantHadamard] do
    unless env.contains n do
      logError m!"Compared theorem is missing from the environment: {n}"
  logInfo m!"Audited {checked} project constants; unexpected axiom dependencies: {rejected}."
