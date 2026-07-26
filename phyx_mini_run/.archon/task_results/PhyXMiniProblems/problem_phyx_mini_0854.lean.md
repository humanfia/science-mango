# Autoformalization result: `problem_phyx_mini_0854.lean`

Post-formalization review evidence for Archon iteration 003. The final retry
gate reported an evidence-only failure: the revised Lean model itself was not
rejected, but it lacked a genuine report tied to the declarations actually
used. The model was therefore preserved after a fresh source, image, API, and
compilation audit.

## Assumption/target split

### Governing laws

- `SatisfiesPointChargeCoulombPotentialEnergyLaw` states that, with zero potential energy at infinite separation, the proton's energy is the sum of the two general pair contributions `k q₁ q₂ / r`.
- `UsesVacuumCoulombConstant` calibrates the dimensionful Coulomb constant to `Electromagnetism.EMSystem.coulombConstant` and its vacuum SI readout. This is a universal-constant calibration, not the requested energy.
- `UsesElectronAndProtonCharges` gives the two electrons charge `-e` and the proton charge `+e`, using Physlib's elementary-charge unit.
- `HasPhysicalElectrostaticParameters` supplies positivity needed for the physical distances, elementary charge, and Coulomb constant.

### Previous-part results

- None. The source report lists no previous parts.

### Figure/data readouts

- `MatchesThreeParticleScenario` identifies the upper and lower particles as electrons and the right-hand particle as a proton.
- `ElectronsAreFixed` formalizes “fixed and cannot move” as constancy of both electron worldlines for every SI-seconds time readout.
- `MatchesSuppliedElectrostaticFigure` records the two blue electron markers with printed minus signs, the red proton marker with no printed sign, the `Electrons` and `Proton` text, both dashed guides, the two separate `0.50 nm` labels, and the `2.0 nm` label.
- `UsesSuppliedFigureGeometry` calibrates those three labels to independent dimensionful lengths and states the relative planar geometry. Direct inspection of image 854 shows that each `0.50 nm` label is an offset from the dashed horizontal midline; hence the full electron separation is `1.0 nm`.
- `FixedElectronsProtonSetup.protonElectricPotentialEnergy` is an independent dimensionful observable. It is not initialized from an answer choice.

### Current target conclusions

- `electronProtonDistances_fromFigure` derives the two Pythagorean electron-proton separations.
- `protonPotentialEnergy_coulombFormula` derives the exact attractive two-electron Coulomb expression for the proton's energy.
- `problem_phyx_mini_0854` derives the same exact SI formula and concludes that `-2.2 × 10⁻¹⁹ J` matches at displayed precision and uniquely selects answer D.

## Goal-faithfulness audit

No current conclusion occurs in `FixedElectronsProtonSetup` or any premise structure. In particular:

- The setup stores the proton energy independently.
- The figure and geometry premises contain positions, physical offsets, and literal raster readouts only; they contain no energy equation.
- The charge and Coulomb-constant premises calibrate physical inputs only.
- The governing-law premise supplies the general two-term `k q₁ q₂ / r` relation, not the simplified formula, numerical energy, rounding match, or answer label.
- `recordedDatasetAnswer` is metadata and is deliberately not used in the theorem statement.
- `MatchesDisplayedPotentialEnergy` merely defines displayed-precision agreement. The substantive assertion that choice D satisfies it appears only in the theorem conclusion.

Thus the exact simplification, numerical scale, and unique choice D remain proof obligations rather than consequences of unfolding a target-shaped premise.

## Source/law/answer audit

- Source evidence: direct inspection of `phyx_data/test_image/854.png` confirms
  the two separate `0.50 nm` offsets, the `2.0 nm` horizontal distance, the
  particle labels, colors, electron minus signs, and dashed alignment guides.
  The source report confirms there are no previous parts.
- Governing law: the only premise involving the requested energy is the general
  superposition law, expressed as the sum of two unsimplified `k q₁ q₂ / r`
  contributions with zero at infinity. It does not identify a choice or state
  a rounded numerical result.
- Answer audit: the source transcription displays `10¹⁹ J`, which is
  incompatible with the nanometre geometry and elementary-charge scale. Using
  the source's recorded label D as metadata, the coherent intended choices are
  interpreted with exponent `10⁻¹⁹`. The theorem must derive both the energy
  match and uniqueness of D; `recordedDatasetAnswer` is not a theorem premise.

## Declarations and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0854:target` corresponds to theorem `PhyXMiniProblems.ProblemPhyXMini0854.problem_phyx_mini_0854`.
- Supporting derived declarations are `electronProtonDistances_fromFigure` and `protonPotentialEnergy_coulombFormula`.
- Supporting model declarations include the dimensionful readouts, `PlanePoint`, `FixedElectronsProtonFigure`, `FixedElectronsProtonSetup`, the scenario/figure/calibration structures, the local Coulomb-law interface, and displayed-choice predicates.

## LeanExplore queries and candidates used

Queries were run with package filters `Mathlib` and `Physlib`:

- `dimensionful electric charge elementary charge Coulomb units`
  - Used `ChargeUnit.elementaryCharge` and `Dimensionful`.
- `Electromagnetism.EMSystem.coulombConstant`
  - Used the exact candidate `Electromagnetism.EMSystem.coulombConstant`.
- `length unit nanometers dimensionful length`
  - Used `LengthUnit.nanometers` and `Dimensionful`.
- `DimEnergy dimensionful energy joules`
  - Used the exact candidate `DimEnergy`.
- `electrostatic potential energy of two point charges Coulomb law`
- `coulombPotentialEnergy`
  - Inspected `Electromagnetism.DistElectromagneticPotential.threeDimPointParticle` as a near match. It constructs a distribution-valued electromagnetic potential for a stationary point source; it does not expose the scalar pairwise test-particle potential energy needed here.

Source, module, and docstring data were fetched for
`ChargeUnit.elementaryCharge`, `ChargeUnit.coulombs`,
`Electromagnetism.EMSystem.coulombConstant`, `LengthUnit.nanometers`,
`DimEnergy`, `Dimensionful`, and the point-particle near match.
The corresponding LeanExplore declaration IDs inspected in this review were
`385585`, `385584`, `385566`, `393157`, `394468`, `394284`, and `385965`.

## Physlib/Mathlib names grounded

- `Dimensionful`, `WithDim`, `Dimension`, `L𝓭`, `C𝓭`, `M𝓭`, and `T𝓭`
- `DimEnergy`
- `LengthUnit.meters` and `LengthUnit.nanometers`
- `ChargeUnit.elementaryCharge` and `ChargeUnit.coulombs`
- `Electromagnetism.EMSystem` and `Electromagnetism.EMSystem.coulombConstant`
- `Real.sqrt`

## Local abstractions introduced

- `SignedLengthQuantity`, `SignedChargeQuantity`, and `CoulombConstantQuantity` retain physical dimensions instead of replacing charge, position, or Coulomb's constant with scalar aliases.
- `PlanePoint` keeps both Cartesian coordinates dimensionful.
- `FixedElectronsProtonSetup` distinguishes physical particles, time-indexed positions, physical length inputs, charge inputs, Coulomb's constant, and the independent energy observable.
- `particleSeparationInMeters` is the Euclidean readout of the dimensionful positions.
- `pointChargeCoulombEnergyInJoules` and `SatisfiesPointChargeCoulombPotentialEnergyLaw` form the smallest local interface for the missing pairwise-energy API. They preserve the source/target particle roles, signed charges, separation, Coulomb constant, and joule result.

## Grounding gaps

- LeanExplore found Physlib's distribution-valued point-particle electromagnetic potential, but no directly compatible declaration for the scalar electrostatic potential energy `k q₁ q₂ / r` of a test charge. The local law interface records that mismatch without guessing a library name.
- The requested `.archon/AGENTS.md` does not exist in this project state. The stage-specific `.archon/prover-modes/physics-formalize.md` was read as the available role document instead.
- The `archon` executable was not available on `PATH`, so the requested
  read-only dependency-graph query could not be run. Manual inspection of the
  chapter's topology found the target wired to this file's local declarations;
  no external proven ancestor was identified for reuse.

## Redraft requests and blueprint status

- The source transcription writes all answer energies with `10¹⁹ J`, but the nanometre geometry, elementary charges, Coulomb constant, recorded label D, and ordinary electrostatic scale jointly imply `10⁻¹⁹ J`. The formalization uses the physically coherent values `±1.2 × 10⁻¹⁹ J` and `±2.2 × 10⁻¹⁹ J`. The blueprint/source should restore the missing minus sign in each exponent.
- The auxiliary caption first says the electron-to-electron distance is `0.50 nm`, but the primary image shows two separate `0.50 nm` offsets. The caption should state a full separation of `1.0 nm`.
- The chapter was not edited to add `\leanok` because the task's explicit write permissions allow edits only to the assigned Lean file and this result file. A coordinator with blueprint write permission should add `\leanok` after accepting the formalization.

## Verification

- Retry-gate resolution: the gate's exact complaint was the absence of a
  genuine post-formalization task result. This file now records searches and
  candidates actually checked against the completed Lean model, plus its
  abstractions, gaps, source/law/answer split, and compilation result.
- Lean LSP diagnostics report no errors and exactly three expected `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0854.lean` exits successfully with the same three expected warnings.
