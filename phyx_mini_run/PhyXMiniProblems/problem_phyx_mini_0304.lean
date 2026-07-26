import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0304

open Dimension

/-!
# Radius of a body-armor dent

A bullet drives a conical dent into body armor.  The primary image shows an
outer longitudinal pulse front, an inner transverse pulse front, and a graph
of bullet speed against time.  Its axes are scaled by `v_s = 300 m/s` and
`t_s = 40 μs`; the prose additionally gives a bullet mass of `10.2 g`, a
longitudinal-pulse speed of `2000 m/s`, and a cone half-angle of `60°`.

The graph is represented by a dimensionless normalized profile on `[0, 1]`.
Thus its physical ordinate is `v_s` times the profile and its physical time is
`t_s` times the normalized abscissa.  The graph-area enclosure below is a
figure readout, while integration of speed, pulse-front propagation, and the
conical geometry are kept in a separate governing-law structure.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, used for dent depths and pulse radii. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- Physlib's unit-independent type of nonnegative physical speeds. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Second readout of a physical duration. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Meter-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Convert a degree readout to Mathlib's physical angle type. -/
def angleFromDegrees (degreeMeasure : ℝ) : Real.Angle :=
  ((degreeMeasure * Real.pi / 180 : ℝ) : Real.Angle)

/-! ## Labels and geometry transcribed from the primary image -/

/-- The two radial pulse fronts named in the schematic. -/
inductive PulseKind where
  | longitudinal
  | transverse
  deriving DecidableEq, Repr

/-- The four mathematical labels printed in the schematic. -/
inductive FigureLabel where
  | bulletSpeed_v
  | longitudinalSpeed_vl
  | transverseSpeed_vt
  | coneHalfAngle_theta
  deriving DecidableEq, Repr

/-- Features to which the four labels are attached. -/
inductive FigureFeature where
  | bulletVelocityArrow
  | longitudinalPulseArrow
  | transversePulseArrow
  | coneHalfAngleArc
  deriving DecidableEq, Repr

/-- The bullet moves along the normal to the initially planar armor. -/
inductive AxialDirection where
  | outwardNormal
  deriving DecidableEq, Repr

/-- Both pulse fronts propagate radially away from the impact point. -/
inductive RadialDirection where
  | awayFromImpact
  deriving DecidableEq, Repr

/--
A structured transcription of the supplied schematic and speed--time graph.

`normalizedBulletSpeed` is a dimensionless ordinate fraction.  At normalized
time `u`, the plotted SI speed is
`speedInMetersPerSecond verticalScale_vs * normalizedBulletSpeed u`.
The pulse-front radii are physical lengths and are not assigned numerical
values by this structure.
-/
structure BodyArmorImpactFigure where
  labelOf : FigureFeature → FigureLabel
  bulletDirection : AxialDirection
  pulseDirection : PulseKind → RadialDirection
  pulseFrontRadiusAtCollisionEnd : PulseKind → LengthQuantity
  coneHalfAngle : Real.Angle
  verticalScale_vs : SpeedQuantity
  horizontalScale_ts : TimeQuantity
  normalizedBulletSpeed : ℝ → ℝ
  horizontalGridIntervalCount : ℕ
  verticalGridIntervalCount : ℕ

/-! ## Physical setup -/

/--
The physical quantities needed for the armor-impact model.

The transverse-pulse speed and the wearer's normal velocity are calibrated SI
scalar profiles indexed by the same normalized time as the graph.  They are
readouts of velocity components, not replacements for the physical bullet,
fabric, pulse fronts, or dimensionful scale quantities.
-/
structure BodyArmorImpactSetup where
  figure : BodyArmorImpactFigure
  bulletMass : MassQuantity
  longitudinalPulseSpeed : SpeedQuantity
  dentDepth : LengthQuantity
  transversePulseSpeedMetersPerSecondAtNormalizedTime : ℝ → ℝ
  wearerNormalVelocityMetersPerSecondAtNormalizedTime : ℝ → ℝ

/-- The inner radius labelled "Radius reached by transverse pulse." -/
def dentRadius (setup : BodyArmorImpactSetup) : LengthQuantity :=
  setup.figure.pulseFrontRadiusAtCollisionEnd .transverse

/-- The outer radius labelled "Radius reached by longitudinal pulse." -/
def longitudinalPulseRadius
    (setup : BodyArmorImpactSetup) : LengthQuantity :=
  setup.figure.pulseFrontRadiusAtCollisionEnd .longitudinal

/-! ## Stated measurements and primary-image readouts -/

/--
Data stated in the prose and read from the primary image.

The normalized area enclosure `9/20 ≤ ∫v ≤ 1/2` is a conservative reading of
the plotted curve relative to its enclosing `v_s × t_s` rectangle.  It records
graph evidence only: no dent radius or answer-choice value occurs here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : BodyArmorImpactSetup) : Prop where
  bulletMassKilograms : massInKilograms setup.bulletMass = 51 / 5000
  longitudinalPulseSpeedMetersPerSecond :
    speedInMetersPerSecond setup.longitudinalPulseSpeed = 2000
  graphVerticalScaleMetersPerSecond :
    speedInMetersPerSecond setup.figure.verticalScale_vs = 300
  graphHorizontalScaleSeconds :
    timeInSeconds setup.figure.horizontalScale_ts = 1 / 25000
  halfAngleReadout :
    setup.figure.coneHalfAngle = angleFromDegrees 60
  bulletArrowLabel :
    setup.figure.labelOf .bulletVelocityArrow = .bulletSpeed_v
  longitudinalArrowLabel :
    setup.figure.labelOf .longitudinalPulseArrow = .longitudinalSpeed_vl
  transverseArrowLabel :
    setup.figure.labelOf .transversePulseArrow = .transverseSpeed_vt
  halfAngleArcLabel :
    setup.figure.labelOf .coneHalfAngleArc = .coneHalfAngle_theta
  bulletMovesNormally : setup.figure.bulletDirection = .outwardNormal
  pulsesMoveRadiallyOutward :
    ∀ pulse, setup.figure.pulseDirection pulse = .awayFromImpact
  fourHorizontalGridIntervals :
    setup.figure.horizontalGridIntervalCount = 4
  threeVerticalGridIntervals :
    setup.figure.verticalGridIntervalCount = 3
  graphStartsAtVerticalScale : setup.figure.normalizedBulletSpeed 0 = 1
  graphEndsAtRest : setup.figure.normalizedBulletSpeed 1 = 0
  graphNonnegative :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 ≤ setup.figure.normalizedBulletSpeed u
  graphDoesNotExceedScale :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, setup.figure.normalizedBulletSpeed u ≤ 1
  graphIntervalIntegrable :
    IntervalIntegrable setup.figure.normalizedBulletSpeed
      MeasureTheory.volume 0 1
  graphAreaLowerReadout :
    (9 / 20 : ℝ) ≤
      ∫ u in (0 : ℝ)..1, setup.figure.normalizedBulletSpeed u
  graphAreaUpperReadout :
    (∫ u in (0 : ℝ)..1, setup.figure.normalizedBulletSpeed u) ≤
      (1 / 2 : ℝ)
  transverseFrontInsideLongitudinalFront :
    lengthInMeters (dentRadius setup) <
      lengthInMeters (longitudinalPulseRadius setup)

/-! ## Governing kinematics and conical-dent laws -/

/--
The physical laws used to infer the final radius.

* `wearerStationary` implements the problem's stated stationary-person
  assumption in the normal direction.
* `bulletDisplacementLaw` integrates the normalized speed graph to obtain the
  dent depth.
* `transverseFrontSpeedLaw` says that the radial front speed is the relative
  normal denting speed multiplied by `tan θ`.
* `transverseFrontPropagationLaw` integrates that speed to obtain the radius.
* `coneGeometryLaw` independently records `r = h tan θ` for the conical dent.
* `longitudinalFrontPropagationLaw` retains the stated `v_l` quantity and the
  outer radius shown in the figure.

No numerical radius or answer choice occurs in this structure.
-/
structure SatisfiesBodyArmorImpactPhysics
    (setup : BodyArmorImpactSetup) : Prop where
  transverseProfileIntervalIntegrable :
    IntervalIntegrable
      setup.transversePulseSpeedMetersPerSecondAtNormalizedTime
      MeasureTheory.volume 0 1
  wearerStationary :
    ∀ u ∈ Set.Icc (0 : ℝ) 1,
      setup.wearerNormalVelocityMetersPerSecondAtNormalizedTime u = 0
  bulletDisplacementLaw :
    lengthInMeters setup.dentDepth =
      timeInSeconds setup.figure.horizontalScale_ts *
        speedInMetersPerSecond setup.figure.verticalScale_vs *
          ∫ u in (0 : ℝ)..1, setup.figure.normalizedBulletSpeed u
  transverseFrontSpeedLaw :
    ∀ u ∈ Set.Icc (0 : ℝ) 1,
      setup.transversePulseSpeedMetersPerSecondAtNormalizedTime u =
        (speedInMetersPerSecond setup.figure.verticalScale_vs *
            setup.figure.normalizedBulletSpeed u -
          setup.wearerNormalVelocityMetersPerSecondAtNormalizedTime u) *
            Real.Angle.tan setup.figure.coneHalfAngle
  transversePulseSlowerThanLongitudinalPulse :
    ∀ u ∈ Set.Icc (0 : ℝ) 1,
      setup.transversePulseSpeedMetersPerSecondAtNormalizedTime u <
        speedInMetersPerSecond setup.longitudinalPulseSpeed
  transverseFrontPropagationLaw :
    lengthInMeters (dentRadius setup) =
      timeInSeconds setup.figure.horizontalScale_ts *
        ∫ u in (0 : ℝ)..1,
          setup.transversePulseSpeedMetersPerSecondAtNormalizedTime u
  coneGeometryLaw :
    lengthInMeters (dentRadius setup) =
      lengthInMeters setup.dentDepth *
        Real.Angle.tan setup.figure.coneHalfAngle
  longitudinalFrontPropagationLaw :
    lengthInMeters (longitudinalPulseRadius setup) =
      speedInMetersPerSecond setup.longitudinalPulseSpeed *
        timeInSeconds setup.figure.horizontalScale_ts

/-! ## Multiple-choice target -/

/-- Labels of the four radii printed in the answer list. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Meter readout printed beside an answer label. -/
def AnswerChoice.radiusInMeters : AnswerChoice → ℝ
  | .A => 1 / 250
  | .B => 3 / 500
  | .C => 1 / 125
  | .D => 1 / 100

/-- A choice is strictly nearer to the physical radius than every alternative. -/
def IsUniqueClosestRadiusChoice
    (setup : BodyArmorImpactSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |lengthInMeters (dentRadius setup) - choice.radiusInMeters| <
      |lengthInMeters (dentRadius setup) - other.radiusInMeters|

/--
At collision end, the conical-dent radius is within `10⁻³ m` of
`1.0 × 10⁻² m`, and this makes D the unique closest displayed answer.

This declaration formalizes blueprint label
`thm:physics:phyx_mini_0304:target`.
-/
theorem problem_phyx_mini_0304
    (setup : BodyArmorImpactSetup)
    (_data : MatchesProblemAndPrimaryFigure setup)
    (_physics : SatisfiesBodyArmorImpactPhysics setup) :
    |lengthInMeters (dentRadius setup) - (1 / 100 : ℝ)| < 1 / 1000 ∧
      IsUniqueClosestRadiusChoice setup .D := by
  have htan :
      Real.Angle.tan setup.figure.coneHalfAngle = Real.sqrt 3 := by
    rw [_data.halfAngleReadout]
    unfold angleFromDegrees
    rw [Real.Angle.tan_coe]
    rw [show (60 : ℝ) * Real.pi / 180 = Real.pi / 3 by ring,
      Real.tan_pi_div_three]
  have hsqrt_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_lower : (5 / 3 : ℝ) < Real.sqrt 3 := by
    nlinarith
  have hsqrt_upper : Real.sqrt 3 < (11 / 6 : ℝ) := by
    nlinarith
  have hdepth := _physics.bulletDisplacementLaw
  rw [_data.graphHorizontalScaleSeconds,
    _data.graphVerticalScaleMetersPerSecond] at hdepth
  have hdepth_lower :
      (27 / 5000 : ℝ) ≤ lengthInMeters setup.dentDepth := by
    nlinarith [_data.graphAreaLowerReadout]
  have hdepth_upper :
      lengthInMeters setup.dentDepth ≤ (3 / 500 : ℝ) := by
    nlinarith [_data.graphAreaUpperReadout]
  have hradius := _physics.coneGeometryLaw
  rw [htan] at hradius
  have hlower_product_nonneg :
      0 ≤
        (lengthInMeters setup.dentDepth - 27 / 5000) *
          Real.sqrt 3 :=
    mul_nonneg (sub_nonneg.mpr hdepth_lower) hsqrt_nonneg
  have hlower_product_pos :
      0 < (27 / 5000 : ℝ) * (Real.sqrt 3 - 5 / 3) :=
    mul_pos (by norm_num) (sub_pos.mpr hsqrt_lower)
  have hradius_lower :
      (9 / 1000 : ℝ) < lengthInMeters (dentRadius setup) := by
    nlinarith
  have hupper_product_nonneg :
      0 ≤
        (3 / 500 - lengthInMeters setup.dentDepth) *
          Real.sqrt 3 :=
    mul_nonneg (sub_nonneg.mpr hdepth_upper) hsqrt_nonneg
  have hupper_product_pos :
      0 < (3 / 500 : ℝ) * (11 / 6 - Real.sqrt 3) :=
    mul_pos (by norm_num) (sub_pos.mpr hsqrt_upper)
  have hradius_upper :
      lengthInMeters (dentRadius setup) < (11 / 1000 : ℝ) := by
    nlinarith
  have hD :
      |lengthInMeters (dentRadius setup) - (1 / 100 : ℝ)| <
        1 / 1000 := by
    rw [abs_lt]
    constructor <;> nlinarith
  constructor
  · exact hD
  · unfold IsUniqueClosestRadiusChoice
    intro other hother
    cases other with
    | A =>
        change
          |lengthInMeters (dentRadius setup) - (1 / 100 : ℝ)| <
            |lengthInMeters (dentRadius setup) - (1 / 250 : ℝ)|
        have hpos :
            0 <
              lengthInMeters (dentRadius setup) - (1 / 250 : ℝ) := by
          nlinarith
        rw [abs_of_pos hpos]
        nlinarith
    | B =>
        change
          |lengthInMeters (dentRadius setup) - (1 / 100 : ℝ)| <
            |lengthInMeters (dentRadius setup) - (3 / 500 : ℝ)|
        have hpos :
            0 <
              lengthInMeters (dentRadius setup) - (3 / 500 : ℝ) := by
          nlinarith
        rw [abs_of_pos hpos]
        nlinarith
    | C =>
        change
          |lengthInMeters (dentRadius setup) - (1 / 100 : ℝ)| <
            |lengthInMeters (dentRadius setup) - (1 / 125 : ℝ)|
        have hpos :
            0 <
              lengthInMeters (dentRadius setup) - (1 / 125 : ℝ) := by
          nlinarith
        rw [abs_of_pos hpos]
        nlinarith
    | D => exact (hother rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0304
