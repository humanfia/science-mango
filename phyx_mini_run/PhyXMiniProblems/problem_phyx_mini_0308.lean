import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Apparent direction of a submerged sound

A distant source produces an approximately planar acoustic wavefront at two
ears labelled `L` and `R`.  Their physical separation is the segment `D` in
the supplied figure.  The same interaural delay has two associated path
differences: the actual one in fresh water and the one inferred by an auditory
system calibrated for propagation in air.  The figure's lowercase `d` is the
generic path-difference leg used in either geometric interpretation.

Lengths, durations, and speeds are Physlib dimensionful quantities.  Real
numbers are used only for coherent SI readouts, temperatures, angle readouts,
and the explicit signed remainder of the far-field approximation.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0308

open Dimension

/-! ## Dimensionful acoustic quantities and coherent SI readouts -/

/-- A nonnegative physical one-dimensional distance. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical arrival-time delay. -/
abbrev AcousticDuration : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical propagation speed. -/
abbrev AcousticSpeed : Type := DimSpeed

/-- Metre readout of a physical acoustic length. -/
def lengthInMeters (length : AcousticLength) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Second readout of a physical acoustic duration. -/
def durationInSeconds (duration : AcousticDuration) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Metre-per-second readout of a physical acoustic speed. -/
def speedInMetersPerSecond (speed : AcousticSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-! ## Labels and qualitative geometry in the primary image -/

/-- Labels printed beside the two ear points. -/
inductive EarPointLabel where
  | L
  | R
  deriving DecidableEq, Repr

/-- Labels printed on the baseline and perpendicular offset segments. -/
inductive DistanceLabel where
  | D
  | d
  deriving DecidableEq, Repr

/-- The angular symbol printed twice in the image. -/
inductive BearingLabel where
  | theta
  deriving DecidableEq, Repr

/-- Geometric meanings of the two displayed copies of `theta`. -/
inductive BearingMeaning where
  | fromForwardDirection
  | betweenEarBaselineAndWavefront
  deriving DecidableEq, Repr

/-- Relationship between the two drawn wavefront lines. -/
inductive WavefrontArrangement where
  | parallelPlanar
  deriving DecidableEq, Repr

/-- The marked intersection of `d` with a wavefront. -/
inductive IntersectionKind where
  | perpendicular
  deriving DecidableEq, Repr

/-- Sense of the arrows normal to the wavefronts. -/
inductive PropagationArrowSense where
  | towardEarBaseline
  deriving DecidableEq, Repr

/--
A structured transcription of the primary raster.  It records only labels and
qualitative incidence data; the image supplies no numerical length or angle.
-/
structure SourceFigure where
  leftPointLabel : EarPointLabel
  rightPointLabel : EarPointLabel
  earBaselineLabel : DistanceLabel
  pathOffsetLabel : DistanceLabel
  leftBearingLabel : BearingLabel
  rightBearingLabel : BearingLabel
  leftBearingMeaning : BearingMeaning
  rightBearingMeaning : BearingMeaning
  wavefrontArrangement : WavefrontArrangement
  pathOffsetIntersection : IntersectionKind
  propagationArrowSense : PropagationArrowSense
  containsNumericalLength : Bool
  containsNumericalAngle : Bool

/-! ## Acoustic localization setup -/

/-- The distance regime stated in the prose. -/
inductive SourceDistanceRegime where
  | distant
  deriving DecidableEq, Repr

/-- Medium whose speed is used for actual or interpreted propagation. -/
inductive SoundMedium where
  | airCalibration
  | freshWater
  deriving DecidableEq, Repr

/-!
Physical data for one localization event.

The actual submerged path difference and the air-calibrated inferred path
difference are independent dimensionful quantities.  The interpreted bearing
is also an independent observation; no requested numerical answer is built
into this record.  The residual and error fields quantify the far-field
approximation rather than silently identifying an approximately planar wave
with an exact plane wave.
-/
structure SoundLocalizationSetup where
  figure : SourceFigure
  earSeparationD : AcousticLength
  actualSubmergedPathDifference : AcousticLength
  auditorilyInferredPathDifference_d : AcousticLength
  interauralDelay : AcousticDuration
  soundSpeed : SoundMedium → AcousticSpeed
  propagationMedium : SoundMedium
  freshWaterTemperatureCelsius : ℝ
  actualUnderwaterBearingRadians : ℝ
  interpretedBearingRadians : ℝ
  sourceDistanceToEarMidpoint : AcousticLength
  sourceDistanceRegime : SourceDistanceRegime
  closerEar : EarPointLabel
  fartherEar : EarPointLabel
  farFieldRelativeTolerance : ℝ
  farFieldPathDifferenceResidualMeters : ℝ
  farFieldErrorBoundMeters : ℝ

/-! ## Problem, figure, and calibration data -/

/--
Label and incidence information read from `308.png`.  The primary raster, not
the auxiliary caption, shows `D` along the ear baseline and lowercase `d`
perpendicular to a wavefront.  For the arrow orientation, `R` is reached
before `L`.
-/
structure MatchesSourceFigure (setup : SoundLocalizationSetup) : Prop where
  leftPointIsL : setup.figure.leftPointLabel = .L
  rightPointIsR : setup.figure.rightPointLabel = .R
  baselineIsD : setup.figure.earBaselineLabel = .D
  perpendicularOffsetIsd : setup.figure.pathOffsetLabel = .d
  leftAngleIsTheta : setup.figure.leftBearingLabel = .theta
  rightAngleIsTheta : setup.figure.rightBearingLabel = .theta
  leftThetaIsMeasuredFromForward :
    setup.figure.leftBearingMeaning = .fromForwardDirection
  rightThetaIsMeasuredToWavefront :
    setup.figure.rightBearingMeaning = .betweenEarBaselineAndWavefront
  wavefrontsAreParallelInSchematic :
    setup.figure.wavefrontArrangement = .parallelPlanar
  dIsPerpendicularToWavefront :
    setup.figure.pathOffsetIntersection = .perpendicular
  arrowsPointTowardEars :
    setup.figure.propagationArrowSense = .towardEarBaseline
  rightEarIsCloser : setup.closerEar = .R
  leftEarIsFarther : setup.fartherEar = .L
  noNumericalLengthInFigure : setup.figure.containsNumericalLength = false
  noNumericalAngleInFigure : setup.figure.containsNumericalAngle = false

/-- Distant-source and fresh-water data stated in the problem. -/
structure MatchesProblemStatement (setup : SoundLocalizationSetup) : Prop where
  sourceIsDistant : setup.sourceDistanceRegime = .distant
  mediumIsFreshWater : setup.propagationMedium = .freshWater
  freshWaterTemperature : setup.freshWaterTemperatureCelsius = 20

/-- Positivity and principal-angle conditions for the physical setup. -/
structure HasPhysicalParameters (setup : SoundLocalizationSetup) : Prop where
  earSeparationPositive : 0 < lengthInMeters setup.earSeparationD
  delayPositive : 0 < durationInSeconds setup.interauralDelay
  actualPathDifferencePositive :
    0 < lengthInMeters setup.actualSubmergedPathDifference
  inferredPathDifferencePositive :
    0 < lengthInMeters setup.auditorilyInferredPathDifference_d
  sourceDistancePositive :
    0 < lengthInMeters setup.sourceDistanceToEarMidpoint
  airCalibrationSpeedPositive :
    0 < speedInMetersPerSecond (setup.soundSpeed .airCalibration)
  freshWaterSpeedPositive :
    0 < speedInMetersPerSecond (setup.soundSpeed .freshWater)
  earsAreDistinct : setup.closerEar ≠ setup.fartherEar
  actualBearingNonnegative : 0 ≤ setup.actualUnderwaterBearingRadians
  actualBearingAtMostRightAngle :
    setup.actualUnderwaterBearingRadians ≤ Real.pi / 2
  interpretedBearingNonnegative : 0 ≤ setup.interpretedBearingRadians
  interpretedBearingAtMostRightAngle :
    setup.interpretedBearingRadians ≤ Real.pi / 2
  farFieldToleranceNonnegative : 0 ≤ setup.farFieldRelativeTolerance
  farFieldToleranceLessThanOne : setup.farFieldRelativeTolerance < 1
  farFieldErrorBoundNonnegative : 0 ≤ setup.farFieldErrorBoundMeters

/-! ## Explicit approximation contract and exact governing laws -/

/-!
Quantitative meaning of “approximately planar.”  The actual finite-distance
path difference equals the plane-wave first term plus a signed residual.  Its
absolute error is bounded, and both the baseline-to-distance ratio and the
relative error are controlled by the stored tolerance.  Thus no far-field
approximation is globalized into an exact equality.
-/
structure SatisfiesBoundedFarFieldApproximation
    (setup : SoundLocalizationSetup) : Prop where
  residualIdentity :
    lengthInMeters setup.actualSubmergedPathDifference =
      lengthInMeters setup.earSeparationD *
          Real.sin setup.actualUnderwaterBearingRadians +
        setup.farFieldPathDifferenceResidualMeters
  residualBound :
    |setup.farFieldPathDifferenceResidualMeters| ≤
      setup.farFieldErrorBoundMeters
  baselineSmallRelativeToSourceDistance :
    lengthInMeters setup.earSeparationD ≤
      setup.farFieldRelativeTolerance *
        lengthInMeters setup.sourceDistanceToEarMidpoint
  errorSmallRelativeToBaseline :
    setup.farFieldErrorBoundMeters ≤
      setup.farFieldRelativeTolerance *
        lengthInMeters setup.earSeparationD

/-- Constant-speed water propagation converts actual path difference to delay. -/
def SatisfiesWaterDelayLaw (setup : SoundLocalizationSetup) : Prop :=
  durationInSeconds setup.interauralDelay *
      speedInMetersPerSecond (setup.soundSpeed .freshWater) =
    lengthInMeters setup.actualSubmergedPathDifference

/-!
The auditory system converts the measured delay to a distance using its air
sound-speed calibration.
-/
def SatisfiesAirCalibratedDelayDistanceLaw
    (setup : SoundLocalizationSetup) : Prop :=
  durationInSeconds setup.interauralDelay *
      speedInMetersPerSecond (setup.soundSpeed .airCalibration) =
    lengthInMeters setup.auditorilyInferredPathDifference_d

/-!
The exact right triangle in the interpretation schematic relates the inferred
distance `d`, ear separation `D`, and the interpreted principal bearing.
-/
def SatisfiesInterpretedBearingGeometry
    (setup : SoundLocalizationSetup) : Prop :=
  lengthInMeters setup.auditorilyInferredPathDifference_d =
    lengthInMeters setup.earSeparationD *
      Real.sin setup.interpretedBearingRadians

/-!
The governing physical and auditory laws.  The current numerical conclusion
does not occur in any field.  In particular, the far-field law retains an
explicit bounded remainder.
-/
structure SatisfiesSoundLocalizationPhysics
    (setup : SoundLocalizationSetup) : Prop where
  boundedFarFieldApproximation :
    SatisfiesBoundedFarFieldApproximation setup
  waterDelay : SatisfiesWaterDelayLaw setup
  airCalibratedDelayDistance :
    SatisfiesAirCalibratedDelayDistanceLaw setup
  interpretedBearingGeometry : SatisfiesInterpretedBearingGeometry setup

/-! ## Recorded answer metadata -/

/-- Labels of the four answer choices in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Degree readout printed beside each displayed answer choice. -/
def answerChoiceDegrees : AnswerChoice → ℝ
  | .A => 4
  | .B => 7
  | .C => 10
  | .D => 13

/-- Dataset answer retained as metadata, not as a physics premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
The source and raster do not specify the actual submerged bearing or numerical
sound speeds, so they do not determine a numerical apparent bearing.  What
does follow is the residual-aware symbolic relation between the actual and
interpreted bearings.  Its second conjunct turns the stored residual bound
into an explicit error bound for the ideal plane-wave speed-ratio relation.

The historical declaration name is retained to preserve the blueprint target;
the recorded `13°` answer is metadata and is not asserted by this theorem.

This declaration corresponds to `thm:physics:phyx_mini_0308:target`.
-/
theorem submergedSound_interpretedAngle_is_thirteen_degrees
    (setup : SoundLocalizationSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesSourceFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_physics : SatisfiesSoundLocalizationPhysics setup) :
    speedInMetersPerSecond (setup.soundSpeed .freshWater) *
          (lengthInMeters setup.earSeparationD *
            Real.sin setup.interpretedBearingRadians) =
        speedInMetersPerSecond (setup.soundSpeed .airCalibration) *
          (lengthInMeters setup.earSeparationD *
              Real.sin setup.actualUnderwaterBearingRadians +
            setup.farFieldPathDifferenceResidualMeters) ∧
      |speedInMetersPerSecond (setup.soundSpeed .freshWater) *
              (lengthInMeters setup.earSeparationD *
                Real.sin setup.interpretedBearingRadians) -
          speedInMetersPerSecond (setup.soundSpeed .airCalibration) *
              (lengthInMeters setup.earSeparationD *
                Real.sin setup.actualUnderwaterBearingRadians)| ≤
        speedInMetersPerSecond (setup.soundSpeed .airCalibration) *
          setup.farFieldErrorBoundMeters := by
  have hactual := _physics.boundedFarFieldApproximation.residualIdentity
  have hwater := _physics.waterDelay
  have hair := _physics.airCalibratedDelayDistance
  have hgeometry := _physics.interpretedBearingGeometry
  change
    durationInSeconds setup.interauralDelay *
          speedInMetersPerSecond (setup.soundSpeed .freshWater) =
      lengthInMeters setup.actualSubmergedPathDifference at hwater
  change
    durationInSeconds setup.interauralDelay *
          speedInMetersPerSecond (setup.soundSpeed .airCalibration) =
      lengthInMeters setup.auditorilyInferredPathDifference_d at hair
  change
    lengthInMeters setup.auditorilyInferredPathDifference_d =
      lengthInMeters setup.earSeparationD *
        Real.sin setup.interpretedBearingRadians at hgeometry
  have hcross :
      speedInMetersPerSecond (setup.soundSpeed .freshWater) *
            (lengthInMeters setup.earSeparationD *
              Real.sin setup.interpretedBearingRadians) =
        speedInMetersPerSecond (setup.soundSpeed .airCalibration) *
          (lengthInMeters setup.earSeparationD *
              Real.sin setup.actualUnderwaterBearingRadians +
            setup.farFieldPathDifferenceResidualMeters) := by
    rw [← hgeometry, ← hactual, ← hair, ← hwater]
    ring
  refine ⟨hcross, ?_⟩
  have hdiff :
      speedInMetersPerSecond (setup.soundSpeed .freshWater) *
              (lengthInMeters setup.earSeparationD *
                Real.sin setup.interpretedBearingRadians) -
          speedInMetersPerSecond (setup.soundSpeed .airCalibration) *
              (lengthInMeters setup.earSeparationD *
                Real.sin setup.actualUnderwaterBearingRadians) =
        speedInMetersPerSecond (setup.soundSpeed .airCalibration) *
          setup.farFieldPathDifferenceResidualMeters := by
    rw [hcross]
    ring
  rw [hdiff, abs_mul,
    abs_of_pos _physical.airCalibrationSpeedPositive]
  exact mul_le_mul_of_nonneg_left
    _physics.boundedFarFieldApproximation.residualBound
    (le_of_lt _physical.airCalibrationSpeedPositive)

end PhyXMiniProblems.ProblemPhyXMini0308
