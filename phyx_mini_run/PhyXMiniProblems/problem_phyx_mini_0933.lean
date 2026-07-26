import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0933

open Dimension

/-!
# Eye-tracking coil and Faraday induction

The primary raster `933.png` shows a fine circular coil surrounding the
cornea.  Four horizontal arrows labelled `B` pass through the eye from left
to right.  The coil diameter is labelled `6.0 mm`; the prose supplies twenty
turns, a `1.0 T` uniform field, a `5 degree` gaze shift, and an elapsed time
of `0.20 s`.

Physical magnitudes below use Physlib's unit-covariant
`Dimensionful (WithDim ...)` types.  Real numbers occur only at explicit SI
readout boundaries, as a dimensionless angle, and in literal figure or answer
data.  In particular, the average induced emf is an independent field of the
setup.  It is constrained by circular-area, magnetic-flux, and Faraday laws;
it is not defined from answer choice B.

Assumption/target split:

* `MatchesEyeTrackingScenario` and `MatchesSuppliedEyeCoilFigure` record the
  prose and primary-raster data;
* `HasPhysicalEyeCoilParameters` and `MatchesEyeCoilRotationGeometry` record
  nondegeneracy and the initial/final geometry;
* `SatisfiesCircularCoilAreaLaw`, `SatisfiesUniformFieldFluxLinkageLaw`, and
  `SatisfiesAverageFaradayLaw` are the governing physical laws; and
* `problem_phyx_mini_0933` alone identifies the induced-emf readout with the
  recorded displayed choice, to the precision printed in the source.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- Magnetic flux density has physical dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Area has physical dimension `L²`. -/
def areaDimension : Dimension :=
  L𝓭 * L𝓭

/-- Magnetic flux, and hence flux linkage, has dimension `M L² T⁻¹ C⁻¹`. -/
def magneticFluxDimension : Dimension :=
  magneticFluxDensityDimension * areaDimension

/-- Electromotive force has the dimension of magnetic-flux change per time. -/
def electromotiveForceDimension : Dimension :=
  magneticFluxDimension * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaQuantity : Type :=
  Dimensionful (WithDim areaDimension NNReal)

/-- A nonnegative, unit-independent elapsed time. -/
abbrev TimeIntervalQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- Signed magnetic flux linkage relative to the selected coil normal. -/
abbrev SignedMagneticFluxLinkageQuantity : Type :=
  Dimensionful (WithDim magneticFluxDimension ℝ)

/-- A nonnegative, unit-independent magnitude of electromotive force. -/
abbrev EmfMagnitudeQuantity : Type :=
  Dimensionful (WithDim electromotiveForceDimension NNReal)

/-- Read a physical length in a selected Physlib length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in millimetres. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- Read physical area in coherent-SI square metres. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read elapsed time in coherent-SI seconds. -/
def timeInSeconds (duration : TimeIntervalQuantity) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Read magnetic-flux-density magnitude in coherent-SI teslas. -/
def magneticFluxDensityInTeslas
    (density : MagneticFluxDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Read signed magnetic flux linkage in coherent-SI weber-turns. -/
def magneticFluxLinkageInWeberTurns
    (linkage : SignedMagneticFluxLinkageQuantity) : ℝ :=
  (linkage UnitChoices.SI).val

/-- Read an emf magnitude in coherent-SI volts. -/
def emfMagnitudeInVolts (emf : EmfMagnitudeQuantity) : ℝ :=
  ((emf UnitChoices.SI).val : ℝ)

/-- Convert a dimensionless angle read in radians to a degree readout. -/
def angleInDegrees (angleInRadians : ℝ) : ℝ :=
  angleInRadians * 180 / Real.pi

/-! ## Coil orientation and primary-figure vocabulary -/

/-- The two instants relevant to the finite gaze shift. -/
inductive GazeState where
  | initial
  | final
  deriving DecidableEq, Fintype, Repr

/-- A dimensionless direction vector in physical three-space. -/
abbrev DirectionVector : Type := EuclideanSpace ℝ (Fin 3)

/-- Unit direction pointing right along the magnetic-field arrows. -/
def rightwardUnitVector : DirectionVector :=
  EuclideanSpace.single (0 : Fin 3) 1

/-- Unit direction pointing outward through the straight-ahead cornea. -/
def straightAheadUnitVector : DirectionVector :=
  EuclideanSpace.single (1 : Fin 3) 1

/-- The elementary geometry assigned to the fine wire loop. -/
inductive CoilShape where
  | circular
  | other
  deriving DecidableEq, Repr

/-- Qualitative directions available in the two-dimensional raster. -/
inductive DiagramDirection where
  | leftward
  | rightward
  | upward
  | downward
  | intoPage
  | outOfPage
  deriving DecidableEq, Fintype, Repr

/-- Physical or graphical objects visible in the supplied raster. -/
inductive FigureObject where
  | eyeOutline
  | corneaSurface
  | leftCoilCrossSection
  | rightCoilCrossSection
  | coilEllipse
  | magneticFieldArrow
  deriving DecidableEq, Fintype, Repr

/-- Textual and symbolic labels printed in the supplied raster. -/
inductive FigureLabel where
  | cornea
  | coilDiameter
  | magneticFieldB
  | eye
  deriving DecidableEq, Fintype, Repr

/-!
Literal presentation data from `933.png`.  This record intentionally has no
emf value or answer label.
-/
structure EyeCoilFigure where
  objectShown : FigureObject → Bool
  labelShown : FigureLabel → Bool
  magneticFieldArrowCount : ℕ
  coilCrossSectionCount : ℕ
  magneticFieldArrowDirection : DiagramDirection
  printedCoilDiameterMillimeters : ℝ
  coilDrawnAroundCornea : Bool
  containsEmfValue : Bool

/-! ## Independent physical setup -/

/-!
A physical corneal coil retains its turn count, dimensionful diameter and
area, and its independently specified normal at each gaze state.
-/
structure CornealCoil where
  shape : CoilShape
  turnCount : ℕ
  diameter : LengthQuantity
  enclosedArea : AreaQuantity
  normalAt : GazeState → DirectionVector
  circlesCornea : Bool

/-!
A spatially uniform magnetic field is represented by a dimensionful strength
and a dimensionless direction.  This preserves the uniform finite-coil model
without identifying magnetic field with a bare scalar.
-/
structure UniformMagneticField where
  fluxDensityMagnitude : MagneticFluxDensityQuantity
  direction : DirectionVector

/-!
Independent apparatus and observables.  Flux linkage and induced emf are not
defined from the numerical inputs or answer choices.
-/
structure EyeTrackingInductionSetup where
  coil : CornealCoil
  magneticField : UniformMagneticField
  startsLookingStraightAhead : Bool
  gazeShiftAngleRadians : ℝ
  gazeShiftDuration : TimeIntervalQuantity
  fluxLinkageAt : GazeState → SignedMagneticFluxLinkageQuantity
  averageInducedEmfMagnitude : EmfMagnitudeQuantity
  figure : EyeCoilFigure

/-- Directional cosine between the field and the selected coil normal. -/
def fieldNormalAlignment
    (setup : EyeTrackingInductionSetup) (state : GazeState) : ℝ :=
  inner ℝ setup.magneticField.direction (setup.coil.normalAt state)

/-! ## Scenario, figure evidence, geometry, and governing laws -/

/-- Numerical and prose-level data, excluding the requested emf result. -/
structure MatchesEyeTrackingScenario
    (setup : EyeTrackingInductionSetup) : Prop where
  circularCoil : setup.coil.shape = .circular
  coilCirclesCornea : setup.coil.circlesCornea = true
  twentyTurns : setup.coil.turnCount = 20
  diameterIsSixMillimeters :
    lengthInMillimeters setup.coil.diameter = 6.0
  fieldMagnitudeIsOneTesla :
    magneticFluxDensityInTeslas
      setup.magneticField.fluxDensityMagnitude = 1.0
  initiallyLookingStraightAhead : setup.startsLookingStraightAhead = true
  gazeShiftIsFiveDegrees :
    angleInDegrees setup.gazeShiftAngleRadians = 5
  gazeShiftTakesPointTwoSeconds :
    timeInSeconds setup.gazeShiftDuration = 0.20

/-! Literal labels, counts, orientation, and calibration from `933.png`. -/
structure MatchesSuppliedEyeCoilFigure
    (setup : EyeTrackingInductionSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.objectShown object = true
  everyLabelShown : ∀ label, setup.figure.labelShown label = true
  fourHorizontalFieldArrows : setup.figure.magneticFieldArrowCount = 4
  twoCoilCrossSections : setup.figure.coilCrossSectionCount = 2
  fieldArrowsPointRight :
    setup.figure.magneticFieldArrowDirection = .rightward
  fieldDirectionMatchesRightwardArrows :
    setup.magneticField.direction = rightwardUnitVector
  diameterLabelReadsSixMillimeters :
    setup.figure.printedCoilDiameterMillimeters = 6.0
  diameterLabelCalibratesPhysicalCoil :
    lengthInMillimeters setup.coil.diameter =
      setup.figure.printedCoilDiameterMillimeters
  coilIsDrawnAroundCornea : setup.figure.coilDrawnAroundCornea = true
  noEmfValueIsPrinted : setup.figure.containsEmfValue = false

/-- Positivity and nondegeneracy of the physical experiment. -/
structure HasPhysicalEyeCoilParameters
    (setup : EyeTrackingInductionSetup) : Prop where
  turnCountPositive : 0 < setup.coil.turnCount
  diameterPositive : 0 < lengthInMeters setup.coil.diameter
  areaPositive : 0 < areaInSquareMeters setup.coil.enclosedArea
  fieldMagnitudePositive :
    0 < magneticFluxDensityInTeslas
      setup.magneticField.fluxDensityMagnitude
  durationPositive : 0 < timeInSeconds setup.gazeShiftDuration
  anglePositive : 0 < setup.gazeShiftAngleRadians
  angleLessThanRightAngle : setup.gazeShiftAngleRadians < Real.pi / 2

/-!
The field direction and both coil normals are unit vectors.  Looking straight
ahead makes the initial normal perpendicular to the horizontal field.  The
five-degree eye rotation changes the magnitude of their directional cosine
from zero to `sin(angle)`; its sign is irrelevant because the question asks
for emf magnitude.
-/
structure MatchesEyeCoilRotationGeometry
    (setup : EyeTrackingInductionSetup) : Prop where
  fieldDirectionIsUnit : ‖setup.magneticField.direction‖ = 1
  coilNormalsAreUnit : ∀ state, ‖setup.coil.normalAt state‖ = 1
  straightAheadNormal :
    setup.coil.normalAt .initial = straightAheadUnitVector
  straightAheadIsPerpendicular :
    fieldNormalAlignment setup .initial = 0
  finalAlignmentMagnitude :
    |fieldNormalAlignment setup .final| =
      Real.sin setup.gazeShiftAngleRadians

/-! The enclosed area of a circular coil is `pi (diameter / 2)^2`. -/
structure SatisfiesCircularCoilAreaLaw
    (setup : EyeTrackingInductionSetup) : Prop where
  circularAreaLaw :
    areaInSquareMeters setup.coil.enclosedArea =
      Real.pi * (lengthInMeters setup.coil.diameter / 2) ^ 2

/-!
For a uniform field, the flux linkage is the number of turns times
`B A` times the directional cosine between the field and coil normal.
-/
structure SatisfiesUniformFieldFluxLinkageLaw
    (setup : EyeTrackingInductionSetup) : Prop where
  uniformFluxLinkageLaw : ∀ state,
    magneticFluxLinkageInWeberTurns (setup.fluxLinkageAt state) =
      (setup.coil.turnCount : ℝ) *
        magneticFluxDensityInTeslas
          setup.magneticField.fluxDensityMagnitude *
        areaInSquareMeters setup.coil.enclosedArea *
        fieldNormalAlignment setup state

/-!
Finite-interval Faraday law for the magnitude of the average induced emf.
Multiplication by the positive duration avoids building division into the
law itself.
-/
structure SatisfiesAverageFaradayLaw
    (setup : EyeTrackingInductionSetup) : Prop where
  averageFaradayLaw :
    emfMagnitudeInVolts setup.averageInducedEmfMagnitude *
        timeInSeconds setup.gazeShiftDuration =
      |magneticFluxLinkageInWeberTurns (setup.fluxLinkageAt .final) -
        magneticFluxLinkageInWeberTurns (setup.fluxLinkageAt .initial)|

/-! ## Derived formula and displayed answer -/

/-!
The ideal-model closed form is derived from the independent observables and
the three governing laws.  It is not a setup field or law premise.
-/
theorem averageInducedEmfMagnitude_closedForm
    (setup : EyeTrackingInductionSetup)
    (_scenario : MatchesEyeTrackingScenario setup)
    (_physical : HasPhysicalEyeCoilParameters setup)
    (_geometry : MatchesEyeCoilRotationGeometry setup)
    (_areaLaw : SatisfiesCircularCoilAreaLaw setup)
    (_fluxLaw : SatisfiesUniformFieldFluxLinkageLaw setup)
    (_faradayLaw : SatisfiesAverageFaradayLaw setup) :
    emfMagnitudeInVolts setup.averageInducedEmfMagnitude =
      (setup.coil.turnCount : ℝ) *
        magneticFluxDensityInTeslas
          setup.magneticField.fluxDensityMagnitude *
        Real.pi * (lengthInMeters setup.coil.diameter / 2) ^ 2 *
        Real.sin setup.gazeShiftAngleRadians /
        timeInSeconds setup.gazeShiftDuration := by
  have hturnNonnegative : 0 ≤ (setup.coil.turnCount : ℝ) := by
    positivity
  have hfieldNonnegative :
      0 ≤ magneticFluxDensityInTeslas
        setup.magneticField.fluxDensityMagnitude :=
    _physical.fieldMagnitudePositive.le
  have hareaNonnegative :
      0 ≤ areaInSquareMeters setup.coil.enclosedArea :=
    _physical.areaPositive.le
  have hdurationNonzero :
      timeInSeconds setup.gazeShiftDuration ≠ 0 :=
    ne_of_gt _physical.durationPositive
  have hfaraday := _faradayLaw.averageFaradayLaw
  rw [_fluxLaw.uniformFluxLinkageLaw .final,
    _fluxLaw.uniformFluxLinkageLaw .initial,
    _geometry.straightAheadIsPerpendicular] at hfaraday
  simp only [mul_zero, sub_zero] at hfaraday
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hturnNonnegative,
    abs_of_nonneg hfieldNonnegative, abs_of_nonneg hareaNonnegative,
    _geometry.finalAlignmentMagnitude] at hfaraday
  apply (eq_div_iff hdurationNonzero).2
  rw [_areaLaw.circularAreaLaw] at hfaraday
  nlinarith only [hfaraday]

/-- Labels of the four displayed emf choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Literal emf magnitude, in volts, printed beside each answer label. -/
def answerChoiceEmfInVolts : AnswerChoice → ℝ
  | .A => (5.0 : ℝ) * 10 ^ (-4 : ℤ)
  | .B => (2.5 : ℝ) * 10 ^ (-4 : ℤ)
  | .C => (1.5 : ℝ) * 10 ^ (-4 : ℤ)
  | .D => (3.0 : ℝ) * 10 ^ (-4 : ℤ)

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Half of the last decimal place displayed in choice B. -/
def choiceBDisplayToleranceInVolts : ℝ :=
  (0.05 : ℝ) * 10 ^ (-4 : ℤ)

/-! A displayed value is closest to the independently modeled emf readout. -/
def IsClosestDisplayedEmf
    (setup : EyeTrackingInductionSetup) (choice : AnswerChoice) : Prop :=
  ∀ alternative,
    |emfMagnitudeInVolts setup.averageInducedEmfMagnitude -
        answerChoiceEmfInVolts choice| ≤
      |emfMagnitudeInVolts setup.averageInducedEmfMagnitude -
        answerChoiceEmfInVolts alternative|

/-!
The average induced emf is approximately `2.5 * 10^-4 V`, within half of
the last displayed decimal place, and this makes B the closest displayed
choice.

This declaration formalizes `thm:physics:phyx_mini_0933:target`.  Neither the
choice-B value nor the closeness conclusion occurs in any premise structure.
-/
theorem problem_phyx_mini_0933
    (setup : EyeTrackingInductionSetup)
    (_scenario : MatchesEyeTrackingScenario setup)
    (_figure : MatchesSuppliedEyeCoilFigure setup)
    (_physical : HasPhysicalEyeCoilParameters setup)
    (_geometry : MatchesEyeCoilRotationGeometry setup)
    (_areaLaw : SatisfiesCircularCoilAreaLaw setup)
    (_fluxLaw : SatisfiesUniformFieldFluxLinkageLaw setup)
    (_faradayLaw : SatisfiesAverageFaradayLaw setup) :
    |emfMagnitudeInVolts setup.averageInducedEmfMagnitude -
        answerChoiceEmfInVolts recordedDatasetAnswer| <
      choiceBDisplayToleranceInVolts ∧
    IsClosestDisplayedEmf setup recordedDatasetAnswer := by
  have millimeters_eq_meters (length : LengthQuantity) :
      lengthInMillimeters length = 1000 * lengthInMeters length := by
    have hunit := length.2
      ({UnitChoices.SI with length := LengthUnit.meters} : UnitChoices)
      ({UnitChoices.SI with length := LengthUnit.millimeters} : UnitChoices)
    have hval := congrArg WithDim.val hunit
    have hvalReal := congrArg (fun value : NNReal => (value : ℝ)) hval
    norm_num [lengthInMillimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.meters, LengthUnit.millimeters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def] at hvalReal ⊢
    exact hvalReal
  have hdiameter :
      lengthInMeters setup.coil.diameter = (3 : ℝ) / 500 := by
    nlinarith only [_scenario.diameterIsSixMillimeters,
      millimeters_eq_meters setup.coil.diameter]
  have hangle :
      setup.gazeShiftAngleRadians = Real.pi / 36 := by
    have h := _scenario.gazeShiftIsFiveDegrees
    rw [angleInDegrees] at h
    field_simp [Real.pi_ne_zero] at h
    nlinarith only [h]
  have hemfFormula :=
    averageInducedEmfMagnitude_closedForm setup _scenario _physical
      _geometry _areaLaw _fluxLaw _faradayLaw
  rw [_scenario.twentyTurns, _scenario.fieldMagnitudeIsOneTesla,
    hdiameter, hangle, _scenario.gazeShiftTakesPointTwoSeconds] at hemfFormula
  norm_num at hemfFormula
  have hsmallAnglePositive : 0 < Real.pi / 36 := by
    positivity
  have hsmallAngleUpper : Real.pi / 36 < (7 : ℝ) / 80 := by
    linarith only [Real.pi_lt_d2]
  have hsmallAngleLower : (157 : ℝ) / 1800 < Real.pi / 36 := by
    linarith only [Real.pi_gt_d2]
  have hsmallAngleCubeUpper :
      (Real.pi / 36) ^ 3 < ((7 : ℝ) / 80) ^ 3 := by
    gcongr
  have hsinLower :
      (87 : ℝ) / 1000 < Real.sin (Real.pi / 36) := by
    have hpolynomialLower :
        (87 : ℝ) / 1000 <
          Real.pi / 36 - (Real.pi / 36) ^ 3 / 4 := by
      nlinarith only [hsmallAngleLower, hsmallAngleCubeUpper]
    exact hpolynomialLower.trans
      (Real.sin_gt_sub_cube hsmallAnglePositive
        (by linarith only [hsmallAngleUpper]))
  have hsinUpper :
      Real.sin (Real.pi / 36) < (7 : ℝ) / 80 :=
    (Real.sin_lt hsmallAnglePositive).trans hsmallAngleUpper
  have hpiSinLower :
      (157 : ℝ) / 50 * ((87 : ℝ) / 1000) <
        Real.pi * Real.sin (Real.pi / 36) := by
    have hpiLower : (157 : ℝ) / 50 < Real.pi := by
      have h := Real.pi_gt_d2
      norm_num at h ⊢
      exact h
    exact mul_lt_mul hpiLower hsinLower.le (by norm_num) Real.pi_pos.le
  have hpiSinUpper :
      Real.pi * Real.sin (Real.pi / 36) <
        (63 : ℝ) / 20 * ((7 : ℝ) / 80) := by
    have hpiUpper : Real.pi < (63 : ℝ) / 20 := by
      have h := Real.pi_lt_d2
      norm_num at h ⊢
      exact h
    exact mul_lt_mul hpiUpper hsinUpper.le
      (Real.sin_pos_of_pos_of_lt_pi hsmallAnglePositive
        (by nlinarith only [Real.pi_pos]))
      (by norm_num)
  have hemfLower :
      (245 : ℝ) / 1000000 <
        emfMagnitudeInVolts setup.averageInducedEmfMagnitude := by
    nlinarith only [hemfFormula, hpiSinLower]
  have hemfUpper :
      emfMagnitudeInVolts setup.averageInducedEmfMagnitude <
        (1 : ℝ) / 4000 := by
    nlinarith only [hemfFormula, hpiSinUpper]
  have htolerance :
      |emfMagnitudeInVolts setup.averageInducedEmfMagnitude -
          answerChoiceEmfInVolts recordedDatasetAnswer| <
        choiceBDisplayToleranceInVolts := by
    norm_num [answerChoiceEmfInVolts, recordedDatasetAnswer,
      choiceBDisplayToleranceInVolts, abs_lt]
    constructor <;> linarith only [hemfLower, hemfUpper]
  have hfarA :
      choiceBDisplayToleranceInVolts <
        |emfMagnitudeInVolts setup.averageInducedEmfMagnitude -
          answerChoiceEmfInVolts .A| := by
    rw [abs_of_neg]
    · norm_num [answerChoiceEmfInVolts, choiceBDisplayToleranceInVolts]
      linarith only [hemfUpper]
    · norm_num [answerChoiceEmfInVolts]
      linarith only [hemfUpper]
  have hfarC :
      choiceBDisplayToleranceInVolts <
        |emfMagnitudeInVolts setup.averageInducedEmfMagnitude -
          answerChoiceEmfInVolts .C| := by
    rw [abs_of_pos]
    · norm_num [answerChoiceEmfInVolts, choiceBDisplayToleranceInVolts]
      linarith only [hemfLower]
    · norm_num [answerChoiceEmfInVolts]
      linarith only [hemfLower]
  have hfarD :
      choiceBDisplayToleranceInVolts <
        |emfMagnitudeInVolts setup.averageInducedEmfMagnitude -
          answerChoiceEmfInVolts .D| := by
    rw [abs_of_neg]
    · norm_num [answerChoiceEmfInVolts, choiceBDisplayToleranceInVolts]
      linarith only [hemfUpper]
    · norm_num [answerChoiceEmfInVolts]
      linarith only [hemfUpper]
  refine ⟨htolerance, ?_⟩
  intro alternative
  cases alternative with
  | A => exact htolerance.le.trans hfarA.le
  | B => exact le_rfl
  | C => exact htolerance.le.trans hfarC.le
  | D => exact htolerance.le.trans hfarD.le

end PhyXMiniProblems.ProblemPhyXMini0933
