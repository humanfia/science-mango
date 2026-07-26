# Autoformalization result: `problem_phyx_mini_0181.lean`

## Iteration 003 review-gate remediation

- The exact review-gate reason is evidence-only: it says that no genuine post-formalization result established the searches and candidates actually used, grounded library names, local abstractions, grounding gaps, or source/law/answer split for the revised model.
- I reread the source report, inspected the primary image, audited the current Lean declaration, and performed fresh LeanExplore searches in this iteration. The audit found no semantic defect, so the physical statement and its public declarations were preserved unchanged, as required for evidence-only retries.
- The primary image confirms a horizontal `2.0 m` bar hinged to the wall, a `4.0 kg` bar label, an `8.0 kg` load at the free end, and a `75 g` steel wire running from that end to the wall at `45°`.
- There are no `/- USER: ... -/` comments in the assigned Lean file.

## Physical model extracted

- Named quantities: bar mass and length, bar center-of-mass lever arm, hanging mass, wire mass and length, gravitational acceleration, wire tension, wire linear mass density, and wire fundamental frequency.
- Dimensional roles: masses have dimension `M`, lengths have dimension `L`, acceleration has `L T⁻²`, tension has `M L T⁻²`, linear density has `M L⁻¹`, and frequency has `T⁻¹`. The wire angle and the final numerical SI readouts are real scalars.
- Figure geometry: the bar is horizontal and hinged at its left wall endpoint; the wire and hanging load meet the bar at its right endpoint; the wall anchor lies above the hinge; and the uniform bar's center-of-mass lever arm is half the bar length.
- Laws used: right-triangle projection, static torque balance about the hinge, `μ = m_wire / L_wire`, and the fixed-end fundamental-mode relation `f₁ = (1 / (2 L_wire)) sqrt (T / μ)`.
- Final relation: the derived physical frequency agrees to within `0.5 Hz` with the recorded whole-hertz answer D, `13 Hz`.

## Assumption/target split

### Governing laws

- `HasUniformBarMassDistribution`: the uniform bar's center-of-mass lever arm is half its length.
- `SatisfiesWireGeometry`: the wire's horizontal projection equals the hinge-to-bar-end distance.
- `SatisfiesStaticTorqueBalance`: the moment of the wire's vertical tension component balances the end load and bar-weight moments about the hinge.
- `SatisfiesWireLinearDensityLaw`: the wire's linear mass density is its total mass divided by its length.
- `SatisfiesFixedEndFundamentalFrequencyLaw`: a taut uniform wire fixed at both ends obeys `f₁ = (1 / (2 L)) sqrt (T / μ)`.
- `HasPositivePhysicalParameters`: the masses, relevant lengths, gravity, tension, and linear density have positive coherent-SI readouts.
- `UsesStandardGravity`: the auxiliary classroom calibration is `g = 9.8 m/s²`.

### Previous-part results

- None. The source report's `previous_parts` list is empty.

### Figure/data readouts

- `MatchesPrimaryFigure` records the image values: bar mass `4.0 kg`, bar length `2.0 m`, hanging mass `8.0 kg`, wire mass `75 g = 75/1000 kg`, and wire angle `45° = π/4`.
- `AnswerChoice.hertz` records A = `72.3 Hz`, B = `17.4 Hz`, C = `6.5 Hz`, and D = `13 Hz`.
- `recordedAnswerChoice` records the dataset metadata label D; it is source metadata rather than a derived physics fact.

### Current target conclusions

- `fundamentalFrequency_matches_recordedAnswerD` concludes `MatchesAnswerChoice setup.wireFundamentalFrequency recordedAnswerChoice`, i.e. that the fundamental-frequency readout is within `0.5 Hz` of D's displayed `13 Hz`.

## Goal-faithfulness audit

- `SteelWireBarSetup` merely names the physical quantities. In particular, it does not assign values to wire length, tension, linear density, or fundamental frequency.
- `MatchesPrimaryFigure` contains only values visible in the primary image. It does not constrain the target frequency, tension, linear density, or derived wire length.
- The geometry, torque, density, and fixed-end frequency predicates state reusable governing relations. None mentions `13`, answer D, `recordedAnswerChoice`, or `MatchesAnswerChoice`.
- `recordedAnswerChoice := .D` faithfully preserves dataset metadata but does not imply the generic `MatchesAnswerChoice` predicate. Unfolding metadata and helper definitions therefore does not close the theorem.
- The conclusion uses a half-hertz display tolerance rather than the physically false exact equality `f = 13 Hz`; the laws yield an unrounded value of approximately `12.8 Hz`.
- Thus no current target conclusion is present as a hypothesis, setup field relation, law field, validity predicate, or local definition.

## Declarations and blueprint correspondence

- Dimensionful quantities: `MassQuantity`, `LengthQuantity`, `AccelerationMagnitude`, `ForceMagnitude`, `LinearMassDensity`, and `Frequency` correspond to the six quantity-definition environments in the declaration topology.
- Coherent-SI projections: `massInKilograms`, `lengthInMeters`, `accelerationInMetersPerSecondSquared`, `forceInNewtons`, `linearMassDensityInKilogramsPerMeter`, and `frequencyInHertz` correspond to the six readout-definition environments.
- System and assumptions: `SteelWireBarSetup`, `MatchesPrimaryFigure`, `UsesStandardGravity`, `HasUniformBarMassDistribution`, `SatisfiesWireGeometry`, `SatisfiesStaticTorqueBalance`, `SatisfiesWireLinearDensityLaw`, `SatisfiesFixedEndFundamentalFrequencyLaw`, and `HasPositivePhysicalParameters` correspond to the physical-model environments.
- Answer metadata: `AnswerChoice`, `AnswerChoice.hertz`, `recordedAnswerChoice`, and `MatchesAnswerChoice` correspond to the answer-model environments.
- `fundamentalFrequency_matches_recordedAnswerD` formalizes `thm:physics:phyx_mini_0181:target`.
- The theorem environment is ready for `\leanok`. I did not edit the blueprint because the prover role and this task's explicit write permissions make blueprint chapters read-only; marker synchronization is handled outside this prover lane.

## LeanExplore queries and candidates actually used

Fresh iteration-003 searches used `packages: ["Mathlib", "Physlib"]` throughout.

- Natural-language query `dimensionful physical quantity with SI unit choices mass length time` returned `UnitChoices.SI` (id `394270`), `Dimensionful` (`394284`), `UnitChoices` (`394255`), and `Dimension` (`394292`) as the leading relevant candidates.
- Likely-name query `Dimensionful WithDim UnitChoices.SI` independently returned `Dimensionful`, `UnitChoices.SI`, and the related conversion `CarriesDimension.toDimensionful`.
- Likely-name query `WithDim` returned `WithDim` (id `394425`) as the exact dimension-tagged type used in the file.
- Source, module, and docstring were fetched for the four retained candidates: `UnitChoices.SI`, `Dimensionful`, `Dimension`, and `WithDim`. Their fetched modules are respectively `Physlib.Units.Basic`, `Physlib.Units.Basic`, `Physlib.Units.Dimension`, and `Physlib.Units.WithDim.Basic`.
- The fetched source confirms that `UnitChoices.SI` selects metres, seconds, kilograms, coulombs, and kelvin; `Dimension` stores the five base-dimension exponents; `WithDim d M` tags a carrier with dimension `d`; and `Dimensionful M` is the subtype of unit-choice-indexed representations satisfying the required scaling law.
- Natural-language query `fundamental frequency of a fixed stretched string from tension and linear mass density` found no matching string-mode declaration. `ClassicalMechanics.HarmonicOscillator.ω` is a spring-mass angular frequency, and `FluidDynamics.MassDensity` is volumetric density, so neither models this wire law.
- Natural-language query `static torque balance force lever arm` returned general rigid-body dynamics declarations such as `RigidBody.rotational_equation_inertial`, but no theorem specialized to the pictured static bar, its scalar force components, and its lever arms.
- Likely-name query `Real.sin Real.cos Real.sqrt` confirmed Mathlib's real trigonometric vocabulary (including `Real.sin`) used by the explicit geometry and law relations; the complete file diagnostics and compilation ground the exact `Real.cos`, `Real.sqrt`, and real absolute-value names as well.

## PhysLean/Mathlib names grounded

- Physlib/PhysLean: `Dimensionful`, `WithDim`, `Dimension`, `Dimension.M𝓭`, `Dimension.L𝓭`, `Dimension.T𝓭`, and `UnitChoices.SI`.
- Mathlib: `NNReal`, `Real.pi`, `Real.sin`, `Real.cos`, `Real.sqrt`, and real absolute-value notation.
- The assigned file imports `Mathlib` and `Physlib.Units.WithDim.Basic`; live diagnostics report no failed dependencies.

## Local abstractions introduced

- The six quantity abbreviations are not transparent scalar aliases: each is a Physlib `Dimensionful (WithDim d NNReal)` type carrying the appropriate physical dimension, with separate named SI readout functions.
- `SteelWireBarSetup` is the smallest local system object that retains the distinct roles of the wall-hinged bar, its center-of-mass lever arm, end load, and supporting wire.
- `MatchesPrimaryFigure` and `UsesStandardGravity` separate primary-image evidence from auxiliary calibration.
- Local geometry, torque-balance, linear-density, and fixed-end mode predicates are necessary because the searches found no compatible packaged law. They preserve the physical content explicitly in coherent SI components instead of assuming the requested numerical answer.
- `AnswerChoice` and `MatchesAnswerChoice` preserve the four displayed choices and the distinction between an unrounded physical frequency and a whole-hertz answer label.

## Source/law/answer audit

- Source: all numeric figure hypotheses are directly supported by the inspected image and source report; standard gravity is separately labeled auxiliary.
- Law: every non-readout premise is a physical modeling law or positivity condition, not a disguised answer.
- Answer: D = `13 Hz` appears only in generic answer metadata and on the conclusion side of the main theorem.

## Grounding gaps and redraft requests

- No Mathlib/PhysLean declaration was found for a fixed-end stretched wire's fundamental frequency in terms of tension and linear mass density.
- No packaged declaration matched the pictured scalar static torque balance.
- The advertised `archon` executable is not present on `PATH` (`archon: command not found`), so the optional dependency-graph query could not be run. The source report has no previous parts, and the target's blueprint `\uses{...}` list contains only declarations local to this file.
- The requested `.archon/AGENTS.md` is absent in this workspace. I read the archived matching project `AGENTS.md` as the available role guidance; it confirms that provers may write only their assigned Lean file and own result, and must not edit blueprint chapters.
- No semantic redraft is requested; the review failure was missing post-formalization evidence, and this report supplies it.

## Verification

- `archon-lean-lsp` diagnostics: one expected `declaration uses sorry` warning at line 220, no errors, and no failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0181.lean`: exit code `0` with the same single expected warning at line 220.
