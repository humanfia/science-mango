# Autoformalization result: `problem_phyx_mini_0965.lean`

## Assumption/target split

### Governing laws

- `SatisfiesSymmetricSuspensionGeometry.separationLaw` states the symmetric common-axis geometry
  `d = 2 ℓ sin θ`.
- `SatisfiesParallelWireMagneticForceLaw` states that opposite conventional currents repel and that the magnetic force per unit length is
  `μ₀ I₁ I₂ / (2 π d)`.
- `SatisfiesStaticCordEquilibrium` separately states the vertical and horizontal component balances for the combined cord-support resultant per unit wire length. It retains the unevaluated sine and cosine equations rather than assuming the derived tangent relation.
- `UsesStandardVacuumPermeability` connects the dimensionful permeability to `Electromagnetism.EMSystem.μ₀` and calibrates its SI readout to `4 π / 10^7`.
- `UsesStandardGravitationalAcceleration` calibrates the acceleration readout to `49/5 m/s²`.

### Previous-part results

- None; the source report lists no previous parts.

### Figure/data readouts

- Two long straight parallel wires suspended symmetrically from a common axis.
- Two visible support stations and all four depicted cords.
- Cord length `4.00 cm`; the primary raster places this label along the cord, consistent with the prose.
- One `6.00°` deflection marker for each wire and the common physical angle `π/30` radians.
- Linear mass density `0.0125 kg/m = 1/80 kg/m` for both wires.
- Equal current magnitudes with opposed directions: the upper raster arrow points right and the lower arrow points left.
- Opposite deflection sides and the qualitative repulsive interaction.
- All physical length, current, density, acceleration, permeability, and force-density observables are unit-independent `Dimensionful (WithDim ... NNReal)` quantities; scalars are confined to named coherent-SI readouts, angles, and answer metadata.

### Current target conclusions

- `currentInAmperes_sq`: each current squared is
  `49000 * sin (π/30) * tan (π/30)`.
- `problem_phyx_mini_0965`: each positive current is the square root of that expression, rounds at `0.1 A` precision to `23.2 A`, and has answer B as its unique closest displayed choice.

## Goal-faithfulness audit

The current magnitude is an independent field `currentMagnitude : WireLabel → ElectricCurrentMagnitude`. Neither it nor any setup field is defined from the answer choices, `23.2`, the square-root expression, or a target predicate. The scenario premises assert only the given equality of the two unknown magnitudes and their opposite directions. The geometry, magnetic-force, calibration, and equilibrium premise structures contain only general physical relations or stated data. The exact radicand and rounded answer occur only in lemma/theorem conclusions and in literal answer-choice metadata.

The final theorem does not claim that the physical current is exactly `23.2 A`: the governing equations give approximately `23.202 A`, so the formalization states an exact square-root relation plus a separate nearest-tenth rounding predicate. This preserves the semantics of the multiple-choice answer.

## Declarations and blueprint correspondence

- Namespace: `PhyXMiniProblems.ProblemPhyXMini0965`.
- Dimension/readout declarations: `electricCurrentDimension`, `linearMassDensityDimension`, `accelerationDimension`, `magneticPermeabilityDimension`, `forcePerLengthDimension`, their dimensionful quantity types, and named SI readouts.
- Apparatus/figure declarations: `WireLabel`, `SupportStation`, `AlongWireDirection`, `DeflectionSide`, `WireModel`, `MagneticMediumModel`, `WireInteraction`, `SuspendedWiresFigure`, and `SuspendedParallelWiresSetup`.
- Premise declarations: `MatchesSuspendedParallelWiresProblem`, `MatchesPrimarySuspendedWiresFigure`, `HasPhysicalSuspendedWireParameters`, `SatisfiesSymmetricSuspensionGeometry`, `UsesStandardGravitationalAcceleration`, `UsesStandardVacuumPermeability`, `SatisfiesParallelWireMagneticForceLaw`, and `SatisfiesStaticCordEquilibrium`.
- Derived declaration: `currentInAmperes_sq` (`by sorry`).
- Main declaration: `problem_phyx_mini_0965` corresponds to `thm:physics:phyx_mini_0965:target` (`by sorry`).
- Answer declarations: `AnswerChoice`, `AnswerChoice.displayedCurrentInAmperes`, `recordedDatasetAnswer`, `RoundsToNearestTenthAmpere`, and `IsUniqueClosestDisplayedAnswer`.

The target blueprint theorem is ready for a `\lean{PhyXMiniProblems.ProblemPhyXMini0965.problem_phyx_mini_0965}` annotation and `\leanok`. I did not edit the blueprint because this prover lane's explicit write permissions allow only the assigned Lean file and this result file.

## LeanExplore queries and candidates used

All supported searches passed `packages: ["Mathlib", "Physlib"]`.

- `physical quantity SI electric current length mass density units`
  - Used candidates: `UnitChoices.SI`, `Dimension`; also confirmed SI length/mass/charge infrastructure.
- `magnetic force per unit length between two parallel current-carrying wires`
  - Near matches: `Electromagnetism.DistElectromagneticPotential.infiniteWire` and `wireCurrentDensity`; neither exposes the required mechanical force-per-length law.
- `PhysLean SIUnit electricCurrent` and `Dimension mass length time electric current`
  - Used candidates: `Dimension.C𝓭`, `Dimension.T𝓭`, `Dimension.M𝓭`, `Dimension.L𝓭`.
- `PhysicalQuantity`, `Quantity dimension units physical value`, and `UnitChoices SI evaluate physical quantity`
  - Used candidates: `Dimensionful`, `WithDim`, `UnitChoices.SI`, and the `.val` readout pattern.
- `WithDim`, `WithDim.val`, and `dimension force acceleration`
  - Used `WithDim`; inspected `UnitExamples.NewtonsSecondWithDim` to confirm the established dimension-tag/readout style.
- `Electromagnetism.EMSystem` and `EMSystem μ₀ vacuum permeability`
  - Used `Electromagnetism.EMSystem` and its `μ₀` field.

Fetched source/module/docstrings for the selected grounding declarations, including `Dimension` (`Physlib.Units.Dimension`), `Dimensionful` and `UnitChoices.SI` (`Physlib.Units.Basic`), `WithDim` (`Physlib.Units.WithDim.Basic`), and `Electromagnetism.EMSystem` (`Physlib.Electromagnetism.Basic`).

## Physlib/Mathlib names grounded

- Physlib: `Dimension`, `Dimension.L𝓭`, `Dimension.T𝓭`, `Dimension.M𝓭`, `Dimension.C𝓭`, `Dimensionful`, `WithDim`, `UnitChoices`, `UnitChoices.SI`, and `Electromagnetism.EMSystem.μ₀`.
- Mathlib: `NNReal`, `Real.pi`, `Real.sin`, `Real.cos`, `Real.tan`, `Real.sqrt`, real absolute value, finite inductive types, and real arithmetic notation.
- An `archon-lean-lsp` standalone snippet confirmed all selected imports and names before editing. File diagnostics then reported success with only the two expected `declaration uses sorry` warnings.

## Local abstractions introduced

- `SuspendedWiresFigure` preserves the primary raster's named objects, cord stations, arrows, angle markers, length marker, and deflection sides without treating pixels or labels as physical laws.
- `SuspendedParallelWiresSetup` separates independent dimensionful observables from figure metadata and governing relations.
- The symmetric geometry, long-parallel-wire magnetic force, and two-component static equilibrium are expressed as separate predicates. This is the smallest local law interface that preserves the route from apparatus data to current while keeping the target out of premises.
- `RoundsToNearestTenthAmpere` and `IsUniqueClosestDisplayedAnswer` distinguish a rounded displayed answer from the exact physical current.

## Grounding gaps and redraft requests

- LeanExplore found Physlib infrastructure for an infinite wire's electromagnetic potential/current density but no declaration for the magnetic mechanical force per unit length between two parallel wires. `SatisfiesParallelWireMagneticForceLaw` is therefore a faithful local governing-law abstraction rather than a guessed library name.
- No library declaration was found for the suspended-cord equilibrium or the symmetric common-axis separation geometry; these are represented by explicit component and geometry predicates.
- The blueprint chapter contains the physics source and `% archon:physics`, but its proof block is only an autoformalization instruction; it does not give the planned equations or a `\lean{...}` declaration name. A later blueprint pass should add the standard derivation and link the main theorem named above.
- The requested `.archon/AGENTS.md` is absent in this workspace. The injected prover-role instructions and the existing `.archon/prover-modes/physics-formalize.md` were followed instead.

## Verification

- `archon-lean-lsp` diagnostics: success.
- Warnings: exactly two expected `declaration uses sorry` warnings, at `currentInAmperes_sq` and `problem_phyx_mini_0965`.
- No other Lean errors or warnings.
