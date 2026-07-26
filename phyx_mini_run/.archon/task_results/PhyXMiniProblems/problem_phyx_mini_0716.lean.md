# PhyXMiniProblems/problem_phyx_mini_0716.lean

## Summary

- Created the previously missing physics formalization file.
- Added unit-independent quantities for mass, duration, length, force, and Newton's gravitational constant, plus explicit SI/day/solar-mass readouts.
- Added a dimensionally and physically faithful equal-mass binary-star model, a derived two-body Kepler relation, and the final rounded-distance/unique-answer target.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0716.lean` succeeds with exactly the two expected `sorry` warnings.

The requested `.archon/AGENTS.md` was absent at the specified path. I used the available `.archon/prover-modes/physics-formalize.md` role document and the injected task instructions. The assigned Lean source was also absent, so there were no pre-existing `/- USER: ... -/` hints to preserve; the new file records that fact in a `USER` comment.

## Assumption/target split

### Governing laws

- `SatisfiesNewtonianCircularOrbitLaws.inverseSquareGravity` states the force-magnitude law `F = G m₁ m₂ / d²` for each directed force label.
- `SatisfiesNewtonianCircularOrbitLaws.forceSuppliesCentripetalAcceleration` states `F = m (2π/T)² r` for each star.
- `SatisfiesNewtonianCircularOrbitLaws.actionReactionMagnitudesEqual` states equality of the two action-reaction force magnitudes.
- `UsesStandardGravitationalConstant` supplies the independent SI calibration `G = 6.67430 × 10⁻¹¹ m³ kg⁻¹ s⁻²`.
- `HasPhysicalBinaryStarParameters` supplies the positivity/nondegeneracy conditions needed to eliminate denominators and select positive roots.

### Previous-part results

- None; the source report has an empty `previous_parts` array.

### Figure/data readouts

- `MatchesPrimaryBinaryStarFigure` records stars 1 and 2, the center-of-mass marker, circular orbits, the two `r` labels, force arrows and labels `F_(2 on 1)` and `F_(1 on 2)`, their mutually inward directions, the counterclockwise orbit arrows, equal radii, and the printed geometry `d = 2r`.
- `MatchesBinaryStarScenario` records the common 90-day period and mass of two nominal solar masses for each star. Coherent SI conversions are stated explicitly as 7,776,000 seconds and `2 × 1.988416 × 10³⁰ kg`.
- `BinaryStarSystem.separation` remains an independent physical length observable and is not defined using an answer choice.

### Current target conclusions

- `binaryStarSeparationCubed` derives the two-body Kepler relation
  `d³ = G (m₁ + m₂) T² / (4π²)`.
- `problem_phyx_mini_0716` concludes that the independent separation is within the displayed rounding half-width of `9.3 × 10¹⁰ m` and that answer C is strictly closer than every other displayed choice.

## Goal-faithfulness audit

No premise field contains `9.3 × 10¹⁰ m`, answer label C, the rounding predicate, or the closest-answer predicate. The target separation is stored independently in `BinaryStarSystem`; the figure premise constrains it only by the source-visible geometry `d = 2r`. The scenario premises contain only the stated period/masses and standard unit conversions, while the law premises contain only general Newtonian gravity and circular-motion relations. `RoundsToDisplayedDistance` and `IsUniqueClosestAnswer` merely name target propositions and do not unfold to a tautology.

A numerical sanity check using the exact formalized calibrations gives
`d = 9.333443662822 × 10¹⁰ m`, whose difference from choice C is
`3.344366282179 × 10⁸ m`; this is below the formalized rounding half-width
`5 × 10⁸ m`.

## Declarations created and blueprint coverage

- `PhyXMiniProblems.ProblemPhyXMini0716.problem_phyx_mini_0716` corresponds to `thm:physics:phyx_mini_0716:target`.
- `binaryStarSeparationCubed` is a supporting derived lemma for the later physics prover.
- Supporting declarations include the dimensionful quantity aliases/readouts, `Star`, `DirectedForceLabel`, `BinaryStarFigure`, `BinaryStarSystem`, the four assumption structures, `AnswerChoice`, and the two target predicates.

The blueprint theorem environment is ready for `\lean{PhyXMiniProblems.ProblemPhyXMini0716.problem_phyx_mini_0716}` and `\leanok`. I did not edit the chapter because the task's explicit write-permission section restricts this prover to the assigned Lean file and task-result file.

## LeanExplore queries and candidates

Queries were run with `packages: ["Mathlib", "Physlib"]`:

- `dimensionful physical mass length time force gravitational constant SI units`
  - used `UnitChoices.SI`, `Dimension`, and `Dimension.L𝓭` as grounding;
- `Dimensionful WithDim DimMass DimLength DimTime`
  - used `Dimensionful` and `WithDim`;
- `TimeUnit.days`
  - used `TimeUnit.days`;
- `solar mass gravitational constant Newtonian gravity physical constants` and `MassUnit.nominalSolarMasses`
  - used `MassUnit.nominalSolarMasses`;
- `Newton law of universal gravitation force magnitude`
  - found dimension-checking/Newton-second-law examples but no universal-gravitation law suitable for this system;
- `Kepler third law binary star orbital period separation`, `gravitationalConstant`, and `Constants gravitational constant G`
  - found `ClassicalMechanics.VisViva.speedCircular` and `speedCircular_sq`, but not a dimensionful equal-mass binary/Kepler API.

Source/module details were fetched for the declarations actually used: `Dimensionful` (`Physlib.Units.Basic`), `WithDim` (`Physlib.Units.WithDim.Basic`), `UnitChoices.SI` (`Physlib.Units.Basic`), `TimeUnit.days` (`Physlib.SpaceAndTime.Time.TimeUnit`), and `MassUnit.nominalSolarMasses` (`Physlib.ClassicalMechanics.Mass.MassUnit`). Source was also inspected for the near-miss `ClassicalMechanics.VisViva.speedCircular`/`speedCircular_sq` to confirm its incompatibility.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension`, `Dimension.L𝓭`, `Dimension.M𝓭`, `Dimension.T𝓭`, `UnitChoices`, `UnitChoices.SI`, `TimeUnit.days`, and `MassUnit.nominalSolarMasses`.
- Mathlib: `NNReal`, `Real.pi`, real absolute-value notation, integer powers, and finite/decidable derivations.

## Local abstractions introduced

- `BinaryStarSystem` preserves the distinct roles of each star, both orbit radii, separation, period, mutual force magnitudes, and gravitational constant as physical quantities.
- `BinaryStarFigure` and the label/direction enumerations preserve the literal image evidence without treating schematic drawing coordinates as measured distances.
- `SatisfiesNewtonianCircularOrbitLaws` is a local two-body governing-law interface because the available Vis-viva structure is scalar and models an orbiting body around a single central mass.
- The answer predicates distinguish a physically computed separation from its rounded multiple-choice display.

## Grounding gaps

- LeanExplore exposed no ready-made dimensionful Newtonian universal-gravitation law or equal-mass binary form of Kepler's third law.
- `ClassicalMechanics.VisViva` stores `G`, masses, and radius as plain reals and uses a one-central-mass test-body model, so reusing it would lose both dimensional roles and the two-body mass sum.
- Physlib provides the nominal solar-mass unit but no matching dimensionful gravitational constant declaration was found; the file therefore models `G` as a dimensionful independent quantity with an explicit standard SI calibration.
- The read-only `archon dag-query` navigation command was unavailable in this shell (`archon: command not found`), so no DAG dependency was used.

## Redraft requests

- None. The primary image, source report, and chapter agree on the geometry and recorded answer.

## Why I stopped

Real progress: the missing file was created with two faithful declaration stubs, all supporting model declarations elaborate, and standalone Lean compilation succeeds with only expected `sorry` warnings.
