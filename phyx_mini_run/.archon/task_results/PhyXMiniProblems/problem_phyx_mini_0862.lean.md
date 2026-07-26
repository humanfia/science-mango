# Autoformalization result: `problem_phyx_mini_0862.lean`

## Assumption/target split

### Governing laws

- Each named source is represented by
  `Electromagnetism.DistElectromagneticPotential.threeDimPointParticle` in a
  positive-permittivity/permeability `Electromagnetism.FreeSpace`.
- `physlibSourcePointChargeElectricFieldLaw` specializes the library theorem
  `Electromagnetism.DistElectromagneticPotential.threeDimPointParticle_electricField`
  to each source.  The theorem's ordinary profile is proportional to
  `q • (r-r₀) / ‖r-r₀‖³`.
- `sourceAxialElectricFieldInNewtonsPerCoulomb` is the coherent-SI x-axis
  restriction of `sourcePointChargeElectricFieldOrdinaryProfile`, which is
  literally the ordinary vector function inside that 3D theorem.  The lemma
  `source_axial_profile_eq_coulomb_formula` exposes the equivalent textbook
  scalar form.  Its constant is the library definition
  `Electromagnetism.EMSystem.coulombConstant` with the free-space `ε₀` and
  `μ₀`.
- `netPointChargePotential` and
  `netAxialElectricFieldInNewtonsPerCoulomb` use finite linear superposition
  over the two source sites.

### Previous-part results

- None.  The source report has an empty `previous_parts` list, and the chapter
  declares no supporting blueprint labels.

### Figure/data readouts

- The horizontal axis is the position axis and is printed `x`; the unlabelled
  ordinate is interpreted as the magnitude of the `E_x` readout because the
  source calls it `E_x` while the raster draws only nonnegative heights.
- The raster shows vertical dashed lines at the source positions, printed
  labels `a` and `b`, all three green branches, a trace above the axis, and a
  vertical asymptote at each source.
- The visible mirror symmetry is idealized by equal trace heights at one pair
  of exterior sample positions reflected through `(a+b)/2`.
- `TraceHeightCalibratesAxialFieldMagnitude` connects those two visible trace
  heights to the magnitudes of the signed, superposed axial field readouts.
- The charges are nonzero, `a < b`, and the selected samples lie strictly
  outside the sources.  These are physical/nondegeneracy conditions, not
  answer data.

### Current target conclusions

- Derived lemma: the net axial field magnitudes agree at the mirror exterior
  samples.
- Derived lemma: the two coherent-SI charge readouts have equal magnitudes.
- Blueprint target `thm:physics:phyx_mini_0862:target`:
  `|q_a / q_b| = 1`, selecting recorded answer D.

## Goal-faithfulness audit

- No setup field, graph-evidence field, calibration field, or geometry field
  states `|q_a| = |q_b|`, `|q_a/q_b| = 1`, or an equivalent charge relation.
- The graph premise equates only two observed trace heights.  Its separate
  calibration premise equates each height with the magnitude of a physical
  field readout.  Charge-magnitude equality still requires the Coulomb
  profile, superposition, strict source ordering, and mirror-sample algebra.
- The Coulomb profile is not defined to be the requested ratio: it is the
  standard `k q (x-x₀)/|x-x₀|³` x-component for each individual source.
- Nonzero `q_b` is assumed only to make the requested quotient meaningful.
- `recordedDatasetAnswer := .D` and the answer-choice ratios are metadata and
  do not occur in any theorem hypothesis or in the definition of the physical
  field.
- The raster's nonnegative curve is not silently treated as a signed field.
  The formalization explicitly distinguishes the signed superposed component
  from its displayed magnitude.

## Declarations created and blueprint correspondence

- Blueprint label `thm:physics:phyx_mini_0862:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0862.problem_phyx_mini_0862`.
- Derived proof-route declarations:
  `source_axial_profile_eq_coulomb_formula`,
  `symmetric_sample_field_magnitudes_equal` and
  `charge_readout_magnitudes_equal`.
- Dimension/readout declarations: `electricFieldDimension`,
  `SignedChargeQuantity`, `AxialPositionQuantity`, `chargeInCoulombs`,
  `positionInMeters`, and `xAxisPointInMeters`.
- Figure/setup declarations: `ChargeSite`, `GraphAxis`, `GraphAxisRole`,
  `GraphBranch`, `ElectricFieldComponentFigure`,
  `TwoPointChargeXAxisSetup`, `HasSymmetricExteriorSampleGeometry`,
  `MatchesSuppliedElectricFieldGraph`, and
  `TraceHeightCalibratesAxialFieldMagnitude`.
- Physics grounding/profile declarations: `sourcePointChargePotential`,
  `netPointChargePotential`, `physlibSourcePointChargeElectricFieldLaw`,
  `sourcePointChargeElectricFieldOrdinaryProfile`,
  `coulombConstantInNewtonMetersSquaredPerCoulombSquared`,
  `displacementFromSourceInMeters`,
  `sourceAxialElectricFieldInNewtonsPerCoulomb`, and
  `netAxialElectricFieldInNewtonsPerCoulomb`.
- Multiple-choice metadata: `AnswerChoice`, `AnswerChoice.ratio`, and
  `recordedDatasetAnswer`.
- The chapter currently contains only the target environment.  The helper
  declarations above are public because they expose the typed model and proof
  route; a later blueprint-maintenance pass may add environments for the two
  derived lemmas after names stabilize.

## LeanExplore queries/candidates actually used

All searches passed `packages: ["Mathlib", "Physlib"]`.

1. Query: `electric field of a finite point charge Coulomb law q r divided by norm r cubed`
   - Used candidate:
     `Electromagnetism.DistElectromagneticPotential.threeDimPointParticle_electricField`.
   - Used constructor:
     `Electromagnetism.DistElectromagneticPotential.threeDimPointParticle`.
   - Rejected near miss:
     `oneDimPointParticle_electricField`; it is electrostatics intrinsic to
     one spatial dimension and has the `‖x-r₀‖⁻¹ (x-r₀)` profile, not the
     restriction of the ordinary 3D inverse-square point-charge field to an
     axis.

2. Query: `Electromagnetism pointCharge electricField coulombConstant`
   - Used candidates:
     `Electromagnetism.EMSystem.coulombConstant`,
     `Electromagnetism.DistElectromagneticPotential.threeDimPointParticle`,
     and
     `Electromagnetism.DistElectromagneticPotential.threeDimPointParticle_electricField`.
   - `Electromagnetism.ElectricField` was inspected but not used as the source
     law: it is only a generic spacetime-to-vector function type.

3. Query: `dimensionful electric charge quantity SI coulomb WithDim`
   - Used candidates: `Dimensionful`, `UnitChoices.SI`, and the charge/length
     dimensions provided by `WithDim`/`Dimension`.
   - `ChargeUnit.coulombs` and `UnitChoices.SI_charge` confirmed that the SI
     charge readout is in coulombs; the file uses the more general
     `UnitChoices.SI` evaluation boundary directly.

4. Query: `superposition of electric fields from finitely many point charges`
   - Used the fact that
     `Electromagnetism.DistElectromagneticPotential.electricField` is a linear
     map, as shown by its fetched source signature, and represented the two
     sources with a finite sum.
   - `fieldStrengthMatrix_add` was a compatible but unnecessary near miss;
     the model needs electric-field rather than field-strength-matrix
     superposition.

5. Queries: `Electromagnetism.FreeSpace electromagnetic constants epsilon mu speed of light`,
   `FreeSpace to EMSystem coulombConstant`, and
   `Electromagnetism.FreeSpace`
   - Used `Electromagnetism.FreeSpace`, whose positive `ε₀` and `μ₀` fields
     select the intended physical medium and imply a positive Coulomb
     constant.

For the selected candidates, source/module/docstring data were fetched.  The
point-particle declarations are in
`Physlib.Electromagnetism.PointParticle.ThreeDimension`, `FreeSpace` is in
`Physlib.Electromagnetism.Dynamics.Basic`, `EMSystem.coulombConstant` is in
`Physlib.Electromagnetism.Basic`, and `Dimensionful`/`UnitChoices.SI` are in
`Physlib.Units.Basic`.

## Physlib/Mathlib names grounded

- `Electromagnetism.FreeSpace`
- `Electromagnetism.DistElectromagneticPotential`
- `Electromagnetism.DistElectromagneticPotential.threeDimPointParticle`
- `Electromagnetism.DistElectromagneticPotential.threeDimPointParticle_electricField`
- `Electromagnetism.DistElectromagneticPotential.electricField`
- `Electromagnetism.EMSystem`
- `Electromagnetism.EMSystem.coulombConstant`
- `Space`
- `Dimension`
- `Dimensionful`
- `WithDim`
- `UnitChoices.SI`
- `Finset.univ`/finite-sum notation through the `Fintype ChargeSite` instance

## Local abstractions introduced

- `SignedChargeQuantity` and `AxialPositionQuantity` are aliases of Physlib
  dimensionful types, not aliases of `ℝ`.  Scalar values appear only at named
  coherent-SI readout boundaries.
- `xAxisPointInMeters` embeds the pictured metre coordinate into the first
  axis of Physlib's `Space 3`.
- `sourceAxialElectricFieldInNewtonsPerCoulomb` is the smallest scalar bridge
  needed for the graph: by definition it selects coordinate zero of
  `sourcePointChargeElectricFieldOrdinaryProfile` at a collinear observation.
  That vector profile reproduces the exact ordinary function inside Physlib's
  distributional 3D point-charge field theorem.  The bridge names the SI
  component unit and does not encode any relation between the two charges.
- The graph vocabulary records literal features separately from the physical
  calibration.  This preserves the ambiguity between a signed component and
  the nonnegative raster height instead of collapsing the two.
- `HasSymmetricExteriorSampleGeometry` uses independent dimensionful samples;
  the mirror-coordinate equality captures the figure readout without defining
  either sample from a charge or from the target ratio.

## Source/law/answer audit

- The recorded answer D (`1`) is physically supported.  At exterior points
  reflected about the source midpoint, the two inverse-square coefficients
  swap.  Equality of the net-field magnitudes then gives
  `(A²-B²)(q_a²-q_b²)=0`; strict exterior geometry gives `A ≠ B`, hence the
  charge magnitudes agree.
- The detailed curve is consistent with `|E_x|` for equal-magnitude opposite
  charges: it remains positive between the sources and diverges at both.
  Mirror symmetry alone is sufficient for the requested magnitude ratio, so
  no charge-sign relation was added.
- The auxiliary caption's “semicircular” and “closed regions” language does
  not match the raster and was not used.  The primary raster clearly shows
  three open branches and two vertical asymptotes.

## Grounding gaps and redraft requests

- No unresolved Mathlib/Physlib grounding gap remains for the governing
  point-charge law: the iteration-2 search found and used the exact Physlib 3D
  point-particle electric-field theorem that the prior retry report had not
  adopted.
- The source would be clearer if it labelled the ordinate `|E_x|` (or stated
  that the plot shows magnitude), since a signed `E_x` graph would normally
  include negative branches.  The present formalization records this as an
  explicit magnitude calibration rather than changing the recorded answer.
- `.archon/AGENTS.md` was absent at the instructed project path.  The injected
  role instructions, `.archon/prover-modes/physics-formalize.md`, and
  `.archon/PROGRESS.md` were followed.
- The advertised `archon` executable was not available on `PATH`, so the
  read-only DAG node/ancestor queries could not be executed.  The chapter
  itself declares no dependencies.
- The blueprint was not edited to add `\leanok`, because the task's explicit
  write permissions allow edits only to the assigned Lean file and this
  result file.  The plan/orchestration stage should add the marker after
  accepting the formalization.

## Verification

- `archon-lean-lsp` elaboration: no errors; exactly four expected
  `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0862.lean`: exit code 0;
  exactly the same four expected `sorry` warnings and no errors.
