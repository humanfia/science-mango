import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0650

open Dimension

/-!
# Proper length of a relativistically moving oblique rod

An observer moves at `0.995 c` relative to a rod and reports an apparent
length of `2.00 m` at `30.0°` to the direction of relative motion.  Only the
component parallel to that direction is Lorentz contracted.  The transverse
component is unchanged.

The supplied raster `phyx_data/test_image/650.png` does not depict this rod:
it is a triangular plot of `|ψ(x)|²` against `x`.  The actual raster readouts
are retained below as independent source evidence, without using them to infer
the rod's proper length.
-/

/-! ## Dimensionful rod quantities and scalar readouts -/

/-- A nonnegative, unit-independent physical length magnitude. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent component of a spatial displacement. -/
abbrev SignedLength : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical length magnitude in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthMagnitude) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed displacement component in a selected length unit. -/
def signedLengthReadout (unit : LengthUnit) (length : SignedLength) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

/-- Meter readout used by the scenario and answer choices. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical speed in meters per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Physlib's exact vacuum light speed, read in meters per second. -/
def vacuumSpeedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-- Convert a degree readout to Mathlib's angle type. -/
def angleOfDegrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-! ## Frames and actual primary-image vocabulary -/

/-- The rod rest frame and the inertial frame of the moving observer. -/
inductive InertialFrameLabel where
  | rodRest
  | movingObserver
  deriving DecidableEq, Fintype, Repr

/-- Positive and negative directions along the relative-motion axis. -/
inductive AxialDirection where
  | positiveX
  | negativeX
  deriving DecidableEq, Fintype, Repr

/-- Literal axis labels visible in the supplied (mismatched) raster. -/
inductive ProbabilityPlotAxisLabel where
  | positionX
  | wavefunctionDensity
  deriving DecidableEq, Fintype, Repr

/-- Unit label printed on the vertical probability-density axis. -/
inductive InverseLengthUnitLabel where
  | inverseCentimeter
  deriving DecidableEq, Fintype, Repr

/-- Named graphical features visible in image 650. -/
inductive ProbabilityPlotFeature where
  | horizontalAxis
  | verticalAxis
  | minusOneTick
  | zeroTick
  | plusOneTick
  | leftDescendingSegment
  | rightAscendingSegment
  | leftEndpointDrop
  | rightEndpointDrop
  deriving DecidableEq, Fintype, Repr

/-!
Typed scalar readout of the actual image.  The function is explicitly a
plotted value in inverse centimeters, rather than a replacement for a
dimensionful rod quantity.
-/
structure SuppliedProbabilityDensityFigure where
  featureShown : ProbabilityPlotFeature → Bool
  horizontalAxisLabel : ProbabilityPlotAxisLabel
  verticalAxisLabel : ProbabilityPlotAxisLabel
  horizontalAxisUnit : LengthUnit
  verticalAxisUnit : InverseLengthUnitLabel
  probabilityDensityReadoutPerCentimeter : ℝ → ℝ
  rodDepicted : Bool
  observerMotionArrowDepicted : Bool

/-!
The independent physical observables used in the rod problem.  The proper
length and all rest-frame components are fields, not definitions made from an
answer choice or from the requested numerical result.
-/
structure ObliqueRelativisticRodSetup where
  suppliedFigure : SuppliedProbabilityDensityFigure
  rodRestFrame : InertialFrameLabel
  observerFrame : InertialFrameLabel
  properLengthMeasurementFrame : InertialFrameLabel
  apparentLengthMeasurementFrame : InertialFrameLabel
  relativeMotionDirection : AxialDirection
  relativeSpeed : DimSpeed
  apparentLength : LengthMagnitude
  properLength : LengthMagnitude
  apparentLongitudinalComponent : SignedLength
  apparentTransverseComponent : SignedLength
  properLongitudinalComponent : SignedLength
  properTransverseComponent : SignedLength
  apparentAngleFromMotion : Real.Angle

/-- The dimensionless relative speed `β = v/c`. -/
def speedFractionOfLight (setup : ObliqueRelativisticRodSetup) : ℝ :=
  speedInMetersPerSecond setup.relativeSpeed /
    vacuumSpeedOfLightInMetersPerSecond

/-- Physlib's Lorentz factor for the setup's dimensionless speed. -/
def lorentzFactor (setup : ObliqueRelativisticRodSetup) : ℝ :=
  LorentzGroup.γ (speedFractionOfLight setup)

/-! ## Scenario, source readouts, and governing laws -/

/-- Frame and direction assignments stated by the rod scenario. -/
structure MatchesObliqueRodScenario
    (setup : ObliqueRelativisticRodSetup) : Prop where
  restFrameIsRodRest : setup.rodRestFrame = .rodRest
  observerFrameIsMovingObserver :
    setup.observerFrame = .movingObserver
  properLengthMeasuredInRestFrame :
    setup.properLengthMeasurementFrame = .rodRest
  apparentLengthMeasuredInObserverFrame :
    setup.apparentLengthMeasurementFrame = .movingObserver
  observerMovesAlongPositiveX :
    setup.relativeMotionDirection = .positiveX

/-!
Literal evidence in the actual primary image: `x` is in centimeters,
`|ψ(x)|²` is in inverse centimeters, and the green graph is `|x|` on
`[-1,1]` with vertical endpoint drops and zero exterior.  The final two
fields make the source mismatch explicit.
-/
structure MatchesSuppliedImage650
    (figure : SuppliedProbabilityDensityFigure) : Prop where
  everyNamedPlotFeatureShown : ∀ feature, figure.featureShown feature = true
  horizontalAxisIsPosition :
    figure.horizontalAxisLabel = .positionX
  verticalAxisIsWavefunctionDensity :
    figure.verticalAxisLabel = .wavefunctionDensity
  positionAxisUsesCentimeters :
    figure.horizontalAxisUnit = LengthUnit.centimeters
  densityAxisUsesInverseCentimeters :
    figure.verticalAxisUnit = .inverseCentimeter
  leftSegmentReadout : ∀ x : ℝ,
    -1 ≤ x → x ≤ 0 →
      figure.probabilityDensityReadoutPerCentimeter x = -x
  rightSegmentReadout : ∀ x : ℝ,
    0 ≤ x → x ≤ 1 →
      figure.probabilityDensityReadoutPerCentimeter x = x
  zeroToLeftOfSupport : ∀ x : ℝ,
    x < -1 → figure.probabilityDensityReadoutPerCentimeter x = 0
  zeroToRightOfSupport : ∀ x : ℝ,
    1 < x → figure.probabilityDensityReadoutPerCentimeter x = 0
  noRodAppearsInRaster : figure.rodDepicted = false
  noObserverMotionArrowAppearsInRaster :
    figure.observerMotionArrowDepicted = false

/-!
Numerical readouts from the problem prose.  `199/200 = 0.995`; the angle and
length equalities describe only what the moving observer reports.
-/
structure MatchesProblemStatementReadouts
    (setup : ObliqueRelativisticRodSetup) : Prop where
  apparentLengthIsTwoMeters :
    lengthInMeters setup.apparentLength = 2
  apparentAngleIsThirtyDegrees :
    setup.apparentAngleFromMotion = angleOfDegrees 30
  relativeSpeedIsPoint995c :
    speedFractionOfLight setup = (199 / 200 : ℝ)

/-- Positivity and the subluminal domain required by the physical model. -/
structure HasPhysicalObliqueRodParameters
    (setup : ObliqueRelativisticRodSetup) : Prop where
  apparentLengthPositive : ∀ unit,
    0 < lengthReadout unit setup.apparentLength
  properLengthPositive : ∀ unit,
    0 < lengthReadout unit setup.properLength
  speedFractionNonnegative : 0 ≤ speedFractionOfLight setup
  speedFractionSubluminal : speedFractionOfLight setup < 1
  apparentLongitudinalNonnegative :
    0 ≤ signedLengthReadout LengthUnit.meters
      setup.apparentLongitudinalComponent
  apparentTransverseNonnegative :
    0 ≤ signedLengthReadout LengthUnit.meters
      setup.apparentTransverseComponent

/-!
Euclidean component geometry for the independently measured length vectors.
The observer-frame orientation determines its two components, while the
proper magnitude is the norm of the independent rest-frame components.
-/
structure SatisfiesRodComponentGeometry
    (setup : ObliqueRelativisticRodSetup) : Prop where
  apparentLongitudinalFromAngle : ∀ unit,
    signedLengthReadout unit setup.apparentLongitudinalComponent =
      lengthReadout unit setup.apparentLength *
        Real.Angle.cos setup.apparentAngleFromMotion
  apparentTransverseFromAngle : ∀ unit,
    signedLengthReadout unit setup.apparentTransverseComponent =
      lengthReadout unit setup.apparentLength *
        Real.Angle.sin setup.apparentAngleFromMotion
  apparentMagnitudePythagorean : ∀ unit,
    lengthReadout unit setup.apparentLength ^ 2 =
      signedLengthReadout unit setup.apparentLongitudinalComponent ^ 2 +
        signedLengthReadout unit setup.apparentTransverseComponent ^ 2
  properMagnitudePythagorean : ∀ unit,
    lengthReadout unit setup.properLength ^ 2 =
      signedLengthReadout unit setup.properLongitudinalComponent ^ 2 +
        signedLengthReadout unit setup.properTransverseComponent ^ 2

/-!
The generic special-relativistic component law: only the component parallel
to the boost is divided by `γ`; the perpendicular component is unchanged.
It contains no numerical proper length and no answer-choice value.
-/
structure SatisfiesRelativisticRodLengthTransformation
    (setup : ObliqueRelativisticRodSetup) : Prop where
  longitudinalLengthContraction : ∀ unit,
    signedLengthReadout unit setup.apparentLongitudinalComponent =
      signedLengthReadout unit setup.properLongitudinalComponent /
        lorentzFactor setup
  transverseLengthInvariant : ∀ unit,
    signedLengthReadout unit setup.apparentTransverseComponent =
      signedLengthReadout unit setup.properTransverseComponent

/-! ## Multiple-choice data and current target -/

/-- Labels of the four source answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed proper-length choices in meters, represented exactly. -/
def displayedProperLengthMeters : AnswerChoice → ℝ
  | .A => 121 / 10
  | .B => 174 / 10
  | .C => 115 / 10
  | .D => 133 / 10

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
Agreement with a proper length displayed to the nearest tenth of a meter.
The half-tenth tolerance is `0.05 m = 1/20 m`.
-/
def MatchesDisplayedProperLengthChoice
    (setup : ObliqueRelativisticRodSetup)
    (choice : AnswerChoice) : Prop :=
  |lengthInMeters setup.properLength -
      displayedProperLengthMeters choice| ≤ (1 / 20 : ℝ)

/-!
At `β = 0.995`, the longitudinal part of the apparent `2.00 m` vector is
restored by `γ`, while the transverse part is unchanged.  The resulting
proper length is approximately `17.37 m`, which is displayed as `17.4 m`,
answer B.

This formalizes `thm:physics:phyx_mini_0650:target`.
-/
theorem problem_phyx_mini_0650
    (setup : ObliqueRelativisticRodSetup)
    (hScenario : MatchesObliqueRodScenario setup)
    (hImage : MatchesSuppliedImage650 setup.suppliedFigure)
    (hReadouts : MatchesProblemStatementReadouts setup)
    (hPhysical : HasPhysicalObliqueRodParameters setup)
    (hGeometry : SatisfiesRodComponentGeometry setup)
    (hRelativity : SatisfiesRelativisticRodLengthTransformation setup) :
    MatchesDisplayedProperLengthChoice setup .B := by
  have hApparentLength := hReadouts.apparentLengthIsTwoMeters
  unfold lengthInMeters at hApparentLength
  have hApparentLongitudinal :=
    hGeometry.apparentLongitudinalFromAngle LengthUnit.meters
  rw [hApparentLength, hReadouts.apparentAngleIsThirtyDegrees] at hApparentLongitudinal
  have hThirtyDegreesInRadians :
      (30 * Real.pi / 180 : ℝ) = Real.pi / 6 := by
    ring
  simp only [angleOfDegrees, Real.Angle.cos_coe] at hApparentLongitudinal
  rw [hThirtyDegreesInRadians, Real.cos_pi_div_six] at hApparentLongitudinal
  ring_nf at hApparentLongitudinal
  have hApparentTransverse :=
    hGeometry.apparentTransverseFromAngle LengthUnit.meters
  rw [hApparentLength, hReadouts.apparentAngleIsThirtyDegrees] at hApparentTransverse
  simp only [angleOfDegrees, Real.Angle.sin_coe] at hApparentTransverse
  rw [hThirtyDegreesInRadians, Real.sin_pi_div_six] at hApparentTransverse
  norm_num at hApparentTransverse
  have hApparentLongitudinalSq :
      signedLengthReadout LengthUnit.meters
          setup.apparentLongitudinalComponent ^ 2 = 3 := by
    rw [hApparentLongitudinal]
    exact Real.sq_sqrt (by norm_num)
  have hLorentzFactorSq :
      lorentzFactor setup ^ 2 = (40000 / 399 : ℝ) := by
    rw [lorentzFactor, hReadouts.relativeSpeedIsPoint995c,
      LorentzGroup.γ_sq]
    · norm_num
    · norm_num [abs_of_nonneg]
  have hLorentzFactorNe : lorentzFactor setup ≠ 0 := by
    intro hZero
    rw [hZero] at hLorentzFactorSq
    norm_num at hLorentzFactorSq
  have hProperLongitudinal :
      signedLengthReadout LengthUnit.meters
          setup.properLongitudinalComponent =
        signedLengthReadout LengthUnit.meters
            setup.apparentLongitudinalComponent *
          lorentzFactor setup :=
    (div_eq_iff hLorentzFactorNe).mp
      (hRelativity.longitudinalLengthContraction LengthUnit.meters).symm
  have hProperLongitudinalSq :
      signedLengthReadout LengthUnit.meters
          setup.properLongitudinalComponent ^ 2 =
        (120000 / 399 : ℝ) := by
    rw [hProperLongitudinal, mul_pow, hApparentLongitudinalSq,
      hLorentzFactorSq]
    norm_num
  have hProperTransverse :
      signedLengthReadout LengthUnit.meters
          setup.properTransverseComponent = 1 := by
    rw [← hRelativity.transverseLengthInvariant LengthUnit.meters]
    exact hApparentTransverse
  have hProperLengthSq :
      lengthReadout LengthUnit.meters setup.properLength ^ 2 =
        (120399 / 399 : ℝ) := by
    rw [hGeometry.properMagnitudePythagorean LengthUnit.meters,
      hProperLongitudinalSq, hProperTransverse]
    norm_num
  have hProperLengthPos :
      0 < lengthReadout LengthUnit.meters setup.properLength :=
    hPhysical.properLengthPositive LengthUnit.meters
  have hLower :
      (347 / 20 : ℝ) <
        lengthReadout LengthUnit.meters setup.properLength := by
    rw [← sq_lt_sq₀ (by norm_num) hProperLengthPos.le, hProperLengthSq]
    norm_num
  have hUpper :
      lengthReadout LengthUnit.meters setup.properLength <
        (349 / 20 : ℝ) := by
    rw [← sq_lt_sq₀ hProperLengthPos.le (by norm_num), hProperLengthSq]
    norm_num
  change
    |lengthReadout LengthUnit.meters setup.properLength -
        (174 / 10 : ℝ)| ≤ (1 / 20 : ℝ)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end PhyXMiniProblems.ProblemPhyXMini0650
