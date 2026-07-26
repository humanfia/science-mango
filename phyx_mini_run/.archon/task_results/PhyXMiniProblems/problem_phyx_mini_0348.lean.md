# Prover result: `problem_phyx_mini_0348.lean`

## Status

Complete. Both proof obligations are closed:

- `PhyXMiniProblems.ProblemPhyXMini0348.netWorkInJoules_eq_temperature_formula`
- `PhyXMiniProblems.ProblemPhyXMini0348.problem_phyx_mini_0348`

The frozen declaration signatures and physical hypotheses were preserved. No
`sorry`, `admit`, axiom, or other escape hatch remains in the assigned file.

## Proof summary

- Specialized the supplied work laws to the isochoric, adiabatic, and
  isobaric legs.
- Used the supplied constant-pressure law and the ideal-gas equations at
  states 1 and 3 to rewrite the isobaric work as
  `n * R * (T₁ - T₃)`.
- Combined the three leg works with the supplied net-work balance to obtain
  the temperature formula.
- Substituted the figure temperatures, amount of gas, heat-capacity ratio,
  and standard molar gas constant, obtaining exactly
  `1134861 / 5000 J = 226.9722 J`.
- Exhausted the four finite answer choices and proved that `220 J` (choice B)
  is the unique nearest displayed value.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0348.lean` exits 0.
- Lean LSP diagnostics report no errors.
- Source scan finds no `sorry`, `admit`, `axiom`, or suspicious proof escape.
- `lean_verify` reports only the standard foundational axioms `propext`,
  `Classical.choice`, and `Quot.sound` for both declarations.
- The compiler's only warning is that the frozen `hPhysical` hypothesis is
  unused; the supplied algebraic laws already suffice for the result.

## Blueprint

The lemma and target theorem proof environments are ready for deterministic
`\leanok` synchronization. Per prover write permissions, the blueprint chapter
was not edited; the sync phase owns this marker update.

The requested run-local `.archon/AGENTS.md` is absent. The canonical archived
`AGENTS.md` identified by `.archon/PROGRESS.md` was read instead.

## Redraft needed

None.
