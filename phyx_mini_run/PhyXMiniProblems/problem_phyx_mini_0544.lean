import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0544

open Dimension

/-!
# Above-step scattering at a one-dimensional potential step

The primary image shows `V(x) = 0` to the left of `x = 0`, a vertical jump at
the origin, and a constant plateau labelled `V₀` to the right.  The prose adds
a beam incident from the left and assumes that its total energy `E` is greater
than `V₀`.

Energies and wave numbers below are unit-independent dimensionful quantities.
Real numbers occur only as coherent-SI readouts, normalized stationary-wave
amplitudes, dimensionless coefficients, positions measured in metres, or
labels displayed by the source.

Assumption/target split:

* `MatchesProblemScenario` records incidence from the left;
* `MatchesPrimaryPotentialStepFigure` records the two axes, the origin, the
  zero left level, the vertical jump, and the right plateau labelled `V₀`;
* `HasPhysicalAboveStepParameters` records `V₀ > 0`, `E > V₀`, positive wave
  numbers, a nonzero incident amplitude, and the coefficient range;
* `SatisfiesAboveStepDispersionLaw` and `SatisfiesStepBoundaryMatchingLaws`
  state the governing nonrelativistic dispersion and interface laws; and
* the requested closed form and answer label D occur only in conclusions.

The recorded answer is the standard above-step transmitted-flux expression,
although the source question calls it a reflection coefficient.  The source's
name and recorded expression are retained here; the terminology discrepancy is
reported in the task result rather than silently changing the target.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A unit-independent one-dimensional wave number, of dimension `length⁻¹`. -/
abbrev WaveNumberQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- Coherent-SI readout of an energy, in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Coherent-SI readout of a wave number, in inverse metres. -/
def waveNumberInInverseMeters (waveNumber : WaveNumberQuantity) : ℝ :=
  ((waveNumber UnitChoices.SI).val : ℝ)

/-! ## Scenario and primary-figure vocabulary -/

/-- Horizontal propagation directions for the particle beam. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- The side of the interface from which a beam approaches. -/
inductive InterfaceSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- The particle beam described in the prose. -/
structure IncidentParticleBeam where
  totalEnergy : DimEnergy
  incidenceSide : InterfaceSide
  propagationDirection : HorizontalDirection

/-- Horizontal and vertical axes in the supplied potential-energy diagram. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Literal symbols printed at the ends of the two axes. -/
inductive AxisSymbol where
  | x
  | VofX
  deriving DecidableEq, Repr

/-- Potential-level symbols printed in the image. -/
inductive PotentialLevelLabel where
  | zero
  | V₀
  deriving DecidableEq, Repr

/-!
Raster-visible data from image 544.  Booleans record the qualitative line
segments; the interface coordinate is the displayed scalar label `0`.
-/
structure PotentialStepFigure where
  axisSymbol : FigureAxis → AxisSymbol
  interfaceCoordinateMeters : ℝ
  leftLevelLabel : PotentialLevelLabel
  rightPlateauLabel : PotentialLevelLabel
  leftHorizontalSegmentShown : Bool
  verticalJumpShown : Bool
  rightHorizontalPlateauShown : Bool

/-!
The scattering setup.  The potential and step height are physical energies.
The three real amplitudes are the normalized coefficients of the incident,
reflected, and transmitted stationary plane-wave components at the interface.
-/
structure PotentialStepScatteringSetup where
  potentialEnergyAt : ℝ → DimEnergy
  stepHeight : DimEnergy
  interfacePositionMeters : ℝ
  incidentBeam : IncidentParticleBeam
  incidentWaveNumber : WaveNumberQuantity
  transmittedWaveNumber : WaveNumberQuantity
  incidentAmplitude : ℝ
  reflectedAmplitude : ℝ
  transmittedAmplitude : ℝ
  reflectionCoefficient : ℝ
  figure : PotentialStepFigure

/-- Joule readout of the incident particle energy `E`. -/
def incidentEnergyJoules (setup : PotentialStepScatteringSetup) : ℝ :=
  energyInJoules setup.incidentBeam.totalEnergy

/-- Joule readout of the step height `V₀`. -/
def stepHeightJoules (setup : PotentialStepScatteringSetup) : ℝ :=
  energyInJoules setup.stepHeight

/-- Left-region wave number `k₁`, in inverse metres. -/
def incidentWaveNumberSI (setup : PotentialStepScatteringSetup) : ℝ :=
  waveNumberInInverseMeters setup.incidentWaveNumber

/-- Right-region wave number `k₂`, in inverse metres. -/
def transmittedWaveNumberSI (setup : PotentialStepScatteringSetup) : ℝ :=
  waveNumberInInverseMeters setup.transmittedWaveNumber

/-! ## Source data and governing physics -/

/-- The incident beam approaches the step from the left and travels rightward. -/
structure MatchesProblemScenario
    (setup : PotentialStepScatteringSetup) : Prop where
  incidentFromLeft : setup.incidentBeam.incidenceSide = .left
  incidentDirection :
    setup.incidentBeam.propagationDirection = .rightward

/-!
All geometric and potential-energy readouts supplied by the primary bitmap.
The value exactly at the discontinuity is intentionally left unspecified.
-/
structure MatchesPrimaryPotentialStepFigure
    (setup : PotentialStepScatteringSetup) : Prop where
  horizontalAxis : setup.figure.axisSymbol .horizontal = .x
  verticalAxis : setup.figure.axisSymbol .vertical = .VofX
  displayedInterfaceAtOrigin :
    setup.figure.interfaceCoordinateMeters = 0
  physicalInterfaceAtOrigin : setup.interfacePositionMeters = 0
  leftLevelIsZeroLabel : setup.figure.leftLevelLabel = .zero
  rightPlateauIsV₀Label : setup.figure.rightPlateauLabel = .V₀
  leftSegmentShown : setup.figure.leftHorizontalSegmentShown = true
  jumpShown : setup.figure.verticalJumpShown = true
  rightPlateauShown : setup.figure.rightHorizontalPlateauShown = true
  potentialLeftOfStep :
    ∀ x : ℝ, x < setup.interfacePositionMeters →
      energyInJoules (setup.potentialEnergyAt x) = 0
  potentialRightOfStep :
    ∀ x : ℝ, setup.interfacePositionMeters < x →
      energyInJoules (setup.potentialEnergyAt x) =
        stepHeightJoules setup

/-! The positive, propagating branch specified by `E > V₀`. -/
structure HasPhysicalAboveStepParameters
    (setup : PotentialStepScatteringSetup) : Prop where
  stepHeightPositive : 0 < stepHeightJoules setup
  energyAboveStep : stepHeightJoules setup < incidentEnergyJoules setup
  incidentWaveNumberPositive : 0 < incidentWaveNumberSI setup
  transmittedWaveNumberPositive : 0 < transmittedWaveNumberSI setup
  incidentAmplitudeNonzero : setup.incidentAmplitude ≠ 0
  coefficientNonnegative : 0 ≤ setup.reflectionCoefficient
  coefficientAtMostOne : setup.reflectionCoefficient ≤ 1

/-!
For a fixed particle mass and reduced Planck constant, the nonrelativistic
wave number is a common positive multiple of the square root of the kinetic
energy.  The existential scale has coherent-SI units
`m⁻¹ J⁻¹/²`; introducing it avoids representing mass or `ℏ`, neither of which
is a stated problem parameter.
-/
def SatisfiesAboveStepDispersionLaw
    (setup : PotentialStepScatteringSetup) : Prop :=
  ∃ waveNumberPerSqrtJoule : ℝ,
    0 < waveNumberPerSqrtJoule ∧
      incidentWaveNumberSI setup =
        waveNumberPerSqrtJoule * Real.sqrt (incidentEnergyJoules setup) ∧
      transmittedWaveNumberSI setup =
        waveNumberPerSqrtJoule *
          Real.sqrt (incidentEnergyJoules setup - stepHeightJoules setup)

/-!
Continuity of a stationary state and its derivative at a finite potential
step gives the first two fields.  The final field states the flux-ratio
interpretation used by the recorded expression: right-moving transmitted
flux divided by incident flux.  This is a governing relation in amplitudes
and wave numbers, not the requested energy-only closed form.
-/
structure SatisfiesStepBoundaryMatchingLaws
    (setup : PotentialStepScatteringSetup) : Prop where
  waveFunctionContinuous :
    setup.incidentAmplitude + setup.reflectedAmplitude =
      setup.transmittedAmplitude
  derivativeContinuous :
    incidentWaveNumberSI setup *
        (setup.incidentAmplitude - setup.reflectedAmplitude) =
      transmittedWaveNumberSI setup * setup.transmittedAmplitude
  sourceCoefficientIsFluxRatio :
    setup.reflectionCoefficient =
      (transmittedWaveNumberSI setup / incidentWaveNumberSI setup) *
        (setup.transmittedAmplitude / setup.incidentAmplitude) ^ 2

/-! ## Answer choices and formalization target -/

/-- Labels of the four multiple-choice expressions in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The coefficient expression printed beside each answer label. -/
def displayedCoefficient
    (choice : AnswerChoice) (incidentEnergy stepHeight : ℝ) : ℝ :=
  match choice with
  | .A =>
      3 * Real.sqrt incidentEnergy * Real.sqrt (incidentEnergy - stepHeight) /
        (Real.sqrt incidentEnergy + Real.sqrt (incidentEnergy - stepHeight)) ^ 2
  | .B =>
      4 * Real.sqrt incidentEnergy * Real.sqrt (incidentEnergy - stepHeight) /
        (Real.sqrt incidentEnergy + Real.sqrt (incidentEnergy + stepHeight)) ^ 2
  | .C =>
      3 * Real.sqrt incidentEnergy * Real.sqrt (incidentEnergy - stepHeight) /
        (Real.sqrt incidentEnergy + Real.sqrt (incidentEnergy + stepHeight)) ^ 2
  | .D =>
      4 * Real.sqrt incidentEnergy * Real.sqrt (incidentEnergy - stepHeight) /
        (Real.sqrt incidentEnergy + Real.sqrt (incidentEnergy - stepHeight)) ^ 2

/-- The modeled coefficient agrees with the expression at a displayed label. -/
def MatchesAnswerChoice
    (setup : PotentialStepScatteringSetup) (choice : AnswerChoice) : Prop :=
  setup.reflectionCoefficient =
    displayedCoefficient choice
      (incidentEnergyJoules setup) (stepHeightJoules setup)

/-- Answer label recorded by the dataset; this is source metadata, not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
The dispersion and boundary-matching laws yield the source's energy-only
coefficient expression.  This derived statement is not included in any
premise structure.
-/
lemma reflectionCoefficient_energy_formula
    (setup : PotentialStepScatteringSetup)
    (hPhysical : HasPhysicalAboveStepParameters setup)
    (hDispersion : SatisfiesAboveStepDispersionLaw setup)
    (hMatching : SatisfiesStepBoundaryMatchingLaws setup) :
    setup.reflectionCoefficient =
      4 * Real.sqrt (incidentEnergyJoules setup) *
          Real.sqrt (incidentEnergyJoules setup - stepHeightJoules setup) /
        (Real.sqrt (incidentEnergyJoules setup) +
          Real.sqrt (incidentEnergyJoules setup - stepHeightJoules setup)) ^ 2 := by
  rcases hDispersion with ⟨scale, hscale_pos, hk₁, hk₂⟩
  have htransmitted :
      (incidentWaveNumberSI setup + transmittedWaveNumberSI setup) *
          setup.transmittedAmplitude =
        2 * incidentWaveNumberSI setup * setup.incidentAmplitude := by
    calc
      _ = incidentWaveNumberSI setup * setup.transmittedAmplitude +
            transmittedWaveNumberSI setup * setup.transmittedAmplitude := by ring
      _ = incidentWaveNumberSI setup *
              (setup.incidentAmplitude + setup.reflectedAmplitude) +
            incidentWaveNumberSI setup *
              (setup.incidentAmplitude - setup.reflectedAmplitude) := by
        rw [← hMatching.derivativeContinuous,
          ← hMatching.waveFunctionContinuous]
      _ = _ := by ring
  have hk_sum_ne :
      incidentWaveNumberSI setup + transmittedWaveNumberSI setup ≠ 0 :=
    ne_of_gt (add_pos hPhysical.incidentWaveNumberPositive
      hPhysical.transmittedWaveNumberPositive)
  have hratio :
      setup.transmittedAmplitude / setup.incidentAmplitude =
        2 * incidentWaveNumberSI setup /
          (incidentWaveNumberSI setup + transmittedWaveNumberSI setup) := by
    field_simp [hPhysical.incidentAmplitudeNonzero, hk_sum_ne]
    simpa [mul_comm, mul_left_comm, mul_assoc] using htransmitted
  rw [hMatching.sourceCoefficientIsFluxRatio, hratio, hk₁, hk₂]
  have hE_pos : 0 < incidentEnergyJoules setup := by
    nlinarith [hPhysical.stepHeightPositive, hPhysical.energyAboveStep]
  have hEV_pos :
      0 < incidentEnergyJoules setup - stepHeightJoules setup := by
    linarith [hPhysical.energyAboveStep]
  have hsqrtE_pos : 0 < Real.sqrt (incidentEnergyJoules setup) :=
    Real.sqrt_pos.2 hE_pos
  have hsqrtEV_pos :
      0 < Real.sqrt
        (incidentEnergyJoules setup - stepHeightJoules setup) :=
    Real.sqrt_pos.2 hEV_pos
  field_simp [ne_of_gt hscale_pos, ne_of_gt hsqrtE_pos,
    ne_of_gt hsqrtEV_pos,
    ne_of_gt (add_pos hsqrtE_pos hsqrtEV_pos)]
  norm_num

/-!
For the left-incident beam and the step shown in image 544, the requested
coefficient is the expression printed as answer D.

This formalizes `thm:physics:phyx_mini_0544:target`.
-/
theorem problem_phyx_mini_0544
    (setup : PotentialStepScatteringSetup)
    (hScenario : MatchesProblemScenario setup)
    (hFigure : MatchesPrimaryPotentialStepFigure setup)
    (hPhysical : HasPhysicalAboveStepParameters setup)
    (hDispersion : SatisfiesAboveStepDispersionLaw setup)
    (hMatching : SatisfiesStepBoundaryMatchingLaws setup) :
    setup.reflectionCoefficient =
        4 * Real.sqrt (incidentEnergyJoules setup) *
            Real.sqrt (incidentEnergyJoules setup - stepHeightJoules setup) /
          (Real.sqrt (incidentEnergyJoules setup) +
            Real.sqrt (incidentEnergyJoules setup - stepHeightJoules setup)) ^ 2 ∧
      MatchesAnswerChoice setup .D ∧
      recordedDatasetAnswer = .D := by
  have hformula :=
    reflectionCoefficient_energy_formula setup hPhysical hDispersion hMatching
  refine ⟨hformula, ?_, rfl⟩
  simpa [MatchesAnswerChoice, displayedCoefficient] using hformula

end PhyXMiniProblems.ProblemPhyXMini0544
