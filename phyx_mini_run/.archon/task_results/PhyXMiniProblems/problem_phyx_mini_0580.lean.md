# Autoformalization result: `problem_phyx_mini_0580.lean`

## Assumption/target split

### Governing laws

- `SatisfiesIndependentElectronFillingLaws.energyScaleFormula` states that the independent dimensionful energy scale has SI readout `h² / (8 m L²)`.
- `oneParticleSpectrumFollowsFigure` relates every independent one-particle energy to the multiplier printed beside its level.
- `IsPauliAllowedOccupation` requires the total electron count and bounds each level by two spin states times its spatial degeneracy.
- `groundOccupationMinimizesEnergy` characterizes the represented ground-state occupation by minimization over all Pauli-allowed 22-electron occupations.
- `electronInteractionsAreNegligible` implements the stated independent-electron approximation by setting the electron-interaction energy contribution to zero.
- `totalGroundEnergyIsAdditive` makes the many-electron energy the occupied one-particle sum plus that interaction contribution.

### Previous-part results

- None; the source report lists no previous parts.

### Figure/data readouts

- `MatchesInfiniteWellScenario` records a three-dimensional infinite potential well, electrons, one electron in the source diagram, and 22 electrons in the requested system.
- `MatchesInfiniteWellFigure` records the vertical-axis quantity and printed unit `h²/(8mL²)`, multipliers `3, 6, 9, 11, 12, 14`, labels ground/triple/nondegenerate, top-to-bottom order, and horizontal blue lines.
- `HasPhysicalInfiniteWellParameters` records strict positivity of `h`, electron mass, side length, and the energy scale.

### Current target conclusions

- `ground_state_occupation_for_twenty_two_electrons` derives occupations `2, 6, 6, 6, 2, 0` at multipliers `3, 6, 9, 11, 12, 14`.
- `problem_phyx_mini_0580` derives the total energy `186 h²/(8mL²)` and connects it to recorded answer choice C.

## Goal-faithfulness audit

The number `186` occurs only in explanatory comments, the answer-choice lookup, and the conclusion of `problem_phyx_mini_0580`. The six derived occupations occur only in the conclusion of the helper lemma. Neither result occurs in `ManyElectronInfiniteWellSetup`, any scenario/readout/physical structure, `IsPauliAllowedOccupation`, or `SatisfiesIndependentElectronFillingLaws`.

The answer-choice table is source data, but it does not imply which choice agrees with the independent many-electron energy. The substantive first conjunct of the target states the numerical multiplier directly. The named helper `infiniteWellEnergyScaleInJoules` only expands the axis unit `h²/(8mL²)` and does not encode the requested multiplier.

## Declarations created and blueprint correspondence

- Dimensionful quantities/readouts: `LengthQuantity`, `MassQuantity`, `actionDimension`, `ActionQuantity`, `lengthInMeters`, `massInKilograms`, `actionInJouleSeconds`, `energyInJoules`.
- Figure vocabulary/data: `InfiniteWellLevel`, `ElectronSpin`, `DegeneracyLabel`, `InfiniteWellEnergyFigure`, and associated label/geometry types.
- Physical model: `ManyElectronInfiniteWellSetup`, `infiniteWellEnergyScaleInJoules`, `levelElectronCapacity`, `IsPauliAllowedOccupation`, `occupationEnergyInJoules`.
- Assumption interfaces: `MatchesInfiniteWellScenario`, `MatchesInfiniteWellFigure`, `HasPhysicalInfiniteWellParameters`, `SatisfiesIndependentElectronFillingLaws`.
- Derived lemma: `ground_state_occupation_for_twenty_two_electrons`.
- Main theorem `problem_phyx_mini_0580` corresponds to blueprint label `thm:physics:phyx_mini_0580:target`.
- Answer data: `AnswerChoice`, `displayedGroundEnergyMultiplier`, `recordedAnswerChoice`.

## LeanExplore queries and candidates

Queries were run with packages `Mathlib` and `Physlib`:

- `fermion Pauli exclusion principle occupation number energy levels`: returned field-theory/Pauli-matrix declarations such as `FieldStatistic.fermionic`, `Fermion.Dirac`, and `PauliMatrix.pauliMatrix`, but no finite-level occupation or exclusion-principle API suitable for this problem.
- `many particle ground state energy sum occupied one particle energies`: returned canonical-ensemble declarations, including `CanonicalEnsemble.energy_add_apply` and `CanonicalEnsemble.meanEnergy_add`; these concern thermal ensembles rather than a zero-temperature fermion filling rule.
- `physical dimensions energy mass length Planck constant` and `DimEnergy dimensional energy`: found `DimEnergy`, `Dimension`, `Dimensionful`, `CarriesDimension`, and `Constants.ℏ`.
- `Constants.h Planck constant`: found only the reduced Planck constant `Constants.ℏ`; it was not substituted for the ordinary `h` printed in the problem.
- `Finset sum cardinality bounded occupation`: found `Fintype.card` and general finite-cardinality/sum infrastructure.

Source/module details were fetched for `DimEnergy` (`Physlib.Units.WithDim.Energy`), `Dimensionful` and `CarriesDimension` (`Physlib.Units.Basic`), `Constants.ℏ` (`Physlib.QuantumMechanics.PlanckConstant`), `LengthUnit`, and `MassUnit` before selecting the model.

## Physlib/Mathlib names grounded

- Physlib: `DimEnergy`, `Dimensionful`, `WithDim`, `Dimension`, `M𝓭`, `L𝓭`, `T𝓭`, and `UnitChoices.SI`.
- Mathlib/core finite infrastructure: `NNReal`, `Fintype`, `Fintype.card`, finite sums via `∑`, `List`, and real-number arithmetic for explicit SI readouts.
- `DimEnergy` has no direct additive or real-scalar instances in the tested API, so energy laws are stated on explicit coherent-SI readouts while the underlying stored quantities remain dimensionful.

## Local abstractions introduced

- `InfiniteWellLevel` and the figure enums preserve the six actual diagram labels, degeneracy words, axis expression, line order, orientation, and color.
- `ManyElectronInfiniteWellSetup` keeps Planck action, electron mass, well length, one-particle energies, interaction contribution, and total energy as distinct physical data.
- `IsPauliAllowedOccupation` is the smallest local abstraction found for particle-number conservation plus the Pauli cap.
- `SatisfiesIndependentElectronFillingLaws` expresses a minimum-energy noninteracting fermion model uniformly over candidates; it does not hard-code the filled shells or answer.

## Grounding gaps and redraft requests

- LeanExplore exposed no Mathlib/Physlib declaration for Pauli exclusion in a finite degenerate spectrum or for the zero-temperature independent-fermion filling principle, so faithful local predicates were necessary.
- Physlib provides `Constants.ℏ`, not the ordinary Planck constant `h` used by this axis label. The formalization therefore stores `h` as a dimensionful action parameter instead of incorrectly identifying it with `ℏ`.
- The requested `.archon/AGENTS.md` is absent in this project. The available `.archon/prover-modes/physics-formalize.md` was read and followed.
- The `archon` executable was not on `PATH`, so the optional DAG node query could not be performed.
- The blueprint theorem should be marked `\leanok` by the coordinator/plan agent. This prover did not edit the chapter because the task's explicit write permissions allow edits only to the assigned Lean file and this result file.

## Verification

`archon-lean-lsp` reports successful elaboration with exactly two expected `declaration uses sorry` warnings, at the derived occupation lemma and the main theorem. There are no errors or other warnings.
