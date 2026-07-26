import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0696

open Dimension

/-!
# Speeds of two balls rotating about their center of mass

A massless rigid rod joins the ball labelled `m₁ = 2.0 kg` at `x₁ = 0 m`
to the ball labelled `m₂ = 500 g` at `x₂ = 0.50 m`.  The primary image marks
their center of mass by `x_cm`, calls the two lever arms `r₁` and `r₂`, and
shows the three points on a horizontal `x` axis.  The assembly rotates about
`x_cm` at `40 rpm`.

Masses, lengths, signed axial positions, rotation rates, angular speeds, and
linear speeds are unit-independent physical quantities.  Real numbers occur
only as named-unit readouts and displayed numerical answers.

The problem text asks for the speed of the `2.0 kg` ball.  With the image data,
that speed is `2π/15 m/s`, approximately `0.419 m/s`.  The supplied recorded
choice C, `1.68 m/s`, instead agrees with the speed of the `500 g` ball.  The
main theorem follows the stated question; a separate theorem records the
dataset discrepancy without making either numerical speed an assumption.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical mass, independent of a chosen mass unit. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, used for the rod and rotation radii. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed one-dimensional position along the figure's horizontal axis. -/
abbrev AxialPositionQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative rotation frequency measured in revolutions per unit time. -/
abbrev RotationRateQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative angular-speed magnitude, measured in radians per unit time. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Read a physical mass in the selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a nonnegative physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed axial position in the selected length unit. -/
def axialPositionReadout
    (unit : LengthUnit) (position : AxialPositionQuantity) : ℝ :=
  (position {UnitChoices.SI with length := unit}).val

/-- Read a rotation frequency in revolutions per selected time unit. -/
def rotationRateReadout
    (unit : TimeUnit) (rate : RotationRateQuantity) : ℝ :=
  ((rate {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read an angular speed in radians per selected time unit. -/
def angularSpeedReadout
    (unit : TimeUnit) (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical speed in the selected coherent length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : DimSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Metre-per-second readout used by the question and answer choices. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Physical roles and primary-figure labels -/

/-- The two ball labels written in the primary image. -/
inductive Ball where
  | m₁
  | m₂
  deriving DecidableEq, Fintype, Repr

/-- The three labeled positions on the image's horizontal axis. -/
inductive PositionLabel where
  | x₁
  | x_cm
  | x₂
  deriving DecidableEq, Fintype, Repr

/-- The two rod segments from the center of mass to the ball centers. -/
inductive RadiusLabel where
  | r₁
  | r₂
  deriving DecidableEq, Fintype, Repr

/-- The coordinate label associated with each ball label. -/
def Ball.positionLabel : Ball → PositionLabel
  | .m₁ => .x₁
  | .m₂ => .x₂

/-- The center-of-mass lever-arm label associated with each ball. -/
def Ball.radiusLabel : Ball → RadiusLabel
  | .m₁ => .r₁
  | .m₂ => .r₂

/-- The idealized mass distribution of the connecting rod. -/
inductive RodMassModel where
  | massless
  | massive
  deriving DecidableEq, Repr

/-- The mechanical constraint imposed by the connector. -/
inductive ConnectorModel where
  | rigidStraightRod
  | flexibleConnector
  deriving DecidableEq, Repr

/-- The point about which the problem says the assembly rotates. -/
inductive RotationAxisLocation where
  | centerOfMass
  | otherPoint
  deriving DecidableEq, Repr

/-- Qualitative marks and labels visible in the supplied bitmap. -/
structure TwoBallRodFigure where
  showsHorizontalXAxis : Bool
  showsRodBetweenBallCenters : Bool
  showsCenterOfMassMarker : Bool
  showsPositionLabel : PositionLabel → Bool
  showsRadiusLabel : RadiusLabel → Bool

/-!
Independent physical quantities of the rotating two-ball system.  In
particular, each ball speed and each radius is stored independently and is
related to the other quantities only by the governing laws below.
-/
structure TwoBallRodRotationSetup where
  ballMass : Ball → MassQuantity
  axialPosition : PositionLabel → AxialPositionQuantity
  centerOfMassRadius : RadiusLabel → LengthQuantity
  rodLength : LengthQuantity
  rotationRate : RotationRateQuantity
  angularSpeed : AngularSpeedQuantity
  ballSpeed : Ball → DimSpeed
  rodMassModel : RodMassModel
  connectorModel : ConnectorModel
  rotationAxisLocation : RotationAxisLocation
  figure : TwoBallRodFigure

/-!
The mass-weighted center of the two ball positions, evaluated in coherent
selected units.  Mathlib's `Finset.centerMass` supplies the actual weighted
affine combination; the massless-rod law below identifies it with `x_cm`.
-/
def massWeightedCenterPositionReadout
    (setup : TwoBallRodRotationSetup)
    (massUnit : MassUnit) (lengthUnit : LengthUnit) : ℝ :=
  Finset.univ.centerMass
    (fun ball => massReadout massUnit (setup.ballMass ball))
    (fun ball =>
      axialPositionReadout lengthUnit
        (setup.axialPosition ball.positionLabel))

/-! ## Problem data and primary-image evidence -/

/-!
Numerical readouts from the prose and primary image, together with their
figure roles.  The center-of-mass coordinate and both ball speeds are absent:
they must be derived from the physical laws.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : TwoBallRodRotationSetup) : Prop where
  m₁MassKilograms :
    massReadout MassUnit.kilograms (setup.ballMass .m₁) = 2
  m₂MassGrams :
    massReadout MassUnit.grams (setup.ballMass .m₂) = 500
  rodLengthCentimeters :
    lengthReadout LengthUnit.centimeters setup.rodLength = 50
  rotationRateRevolutionsPerMinute :
    rotationRateReadout TimeUnit.minutes setup.rotationRate = 40
  x₁PositionMeters :
    axialPositionReadout LengthUnit.meters
        (setup.axialPosition .x₁) = 0
  x₂PositionMeters :
    axialPositionReadout LengthUnit.meters
        (setup.axialPosition .x₂) = 1 / 2
  centerMarkerBetweenBalls :
    axialPositionReadout LengthUnit.meters
          (setup.axialPosition .x₁) <
        axialPositionReadout LengthUnit.meters
          (setup.axialPosition .x_cm) ∧
      axialPositionReadout LengthUnit.meters
          (setup.axialPosition .x_cm) <
        axialPositionReadout LengthUnit.meters
          (setup.axialPosition .x₂)
  masslessRod : setup.rodMassModel = .massless
  rigidStraightConnector : setup.connectorModel = .rigidStraightRod
  rotatesAboutMarkedCenterOfMass :
    setup.rotationAxisLocation = .centerOfMass
  horizontalAxisShown : setup.figure.showsHorizontalXAxis = true
  connectingRodShown : setup.figure.showsRodBetweenBallCenters = true
  centerOfMassMarkerShown : setup.figure.showsCenterOfMassMarker = true
  allPositionLabelsShown :
    ∀ label, setup.figure.showsPositionLabel label = true
  bothRadiusLabelsShown :
    ∀ label, setup.figure.showsRadiusLabel label = true

/-- Positivity and nondegeneracy conditions for the rotating assembly. -/
structure HasPhysicalTwoBallRodParameters
    (setup : TwoBallRodRotationSetup) : Prop where
  ballMassPositive :
    ∀ ball, 0 < massReadout MassUnit.kilograms (setup.ballMass ball)
  rodLengthPositive :
    0 < lengthReadout LengthUnit.meters setup.rodLength
  centerOfMassRadiiPositive :
    ∀ radius,
      0 < lengthReadout LengthUnit.meters
        (setup.centerOfMassRadius radius)
  rotationRatePositive :
    0 < rotationRateReadout TimeUnit.seconds setup.rotationRate
  angularSpeedPositive :
    0 < angularSpeedReadout TimeUnit.seconds setup.angularSpeed

/-! ## Governing center-of-mass and circular-motion laws -/

/-!
The physical laws used to answer the question:

* because the rod is massless, `x_cm` is the mass-weighted center of the two
  ball centers;
* each `rᵢ` is the distance from its ball center to `x_cm`, and the two radii
  span the straight rod;
* one revolution is `2π` radians, so `ω = 2π f`;
* rigid uniform rotation gives the tangential-speed magnitude `vᵢ = ω rᵢ`.

All equations are stated in coherent selected units.  No field contains the
requested `2π/15 m/s` speed or the recorded `1.68 m/s` choice.
-/
structure SatisfiesMasslessTwoBallRotationLaws
    (setup : TwoBallRodRotationSetup) : Prop where
  masslessRodCenterOfMass :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit),
      axialPositionReadout lengthUnit
          (setup.axialPosition .x_cm) =
        massWeightedCenterPositionReadout setup massUnit lengthUnit
  radiiAreCenterOfMassDistances :
    ∀ (ball : Ball) (lengthUnit : LengthUnit),
      lengthReadout lengthUnit
          (setup.centerOfMassRadius ball.radiusLabel) =
        |axialPositionReadout lengthUnit
              (setup.axialPosition ball.positionLabel) -
          axialPositionReadout lengthUnit
              (setup.axialPosition .x_cm)|
  radiusSegmentsSpanRod :
    ∀ lengthUnit : LengthUnit,
      lengthReadout lengthUnit
          (setup.centerOfMassRadius .r₁) +
        lengthReadout lengthUnit
          (setup.centerOfMassRadius .r₂) =
        lengthReadout lengthUnit setup.rodLength
  angularSpeedFromRotationRate :
    ∀ timeUnit : TimeUnit,
      angularSpeedReadout timeUnit setup.angularSpeed =
        2 * Real.pi * rotationRateReadout timeUnit setup.rotationRate
  rigidRotationTangentialSpeed :
    ∀ (ball : Ball) (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit (setup.ballSpeed ball) =
        angularSpeedReadout timeUnit setup.angularSpeed *
          lengthReadout lengthUnit
            (setup.centerOfMassRadius ball.radiusLabel)

/-! ## Derived radii, displayed choices, and target -/

/-!
The `2.0 kg` ball lies `0.10 m` from `x_cm`, while the `500 g` ball lies
`0.40 m` from it.  This is derived from the independent mass and coordinate
readouts plus the massless-rod center-of-mass law.
-/
lemma centerOfMassRadiiInMeters
    (setup : TwoBallRodRotationSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalTwoBallRodParameters setup)
    (_laws : SatisfiesMasslessTwoBallRotationLaws setup) :
    lengthReadout LengthUnit.meters
          (setup.centerOfMassRadius .r₁) = 1 / 10 ∧
      lengthReadout LengthUnit.meters
          (setup.centerOfMassRadius .r₂) = 2 / 5 := by
  have hMassConversion :
      massReadout MassUnit.grams (setup.ballMass .m₂) =
        1000 * massReadout MassUnit.kilograms (setup.ballMass .m₂) := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      ((setup.ballMass .m₂).2 UnitChoices.SI
        {UnitChoices.SI with mass := MassUnit.grams})
    norm_num [massReadout, UnitChoices.dimScale, M𝓭,
      MassUnit.grams, MassUnit.kilograms, MassUnit.scale,
      MassUnit.div_eq_val, NNReal.smul_def, smul_eq_mul] at h ⊢
    exact h
  have hm2kg :
      massReadout MassUnit.kilograms (setup.ballMass .m₂) =
        (1 / 2 : ℝ) := by
    rw [_figure.m₂MassGrams] at hMassConversion
    linarith
  have hCenter := _laws.masslessRodCenterOfMass
    MassUnit.kilograms LengthUnit.meters
  change axialPositionReadout LengthUnit.meters
      (setup.axialPosition .x_cm) =
    Finset.univ.centerMass
      (fun ball => massReadout MassUnit.kilograms (setup.ballMass ball))
      (fun ball => axialPositionReadout LengthUnit.meters
        (setup.axialPosition ball.positionLabel)) at hCenter
  rw [show (Finset.univ : Finset Ball) = {Ball.m₁, Ball.m₂} by decide]
    at hCenter
  rw [Finset.centerMass_pair Ball.m₁ Ball.m₂ _ _ (by decide)] at hCenter
  norm_num [Ball.positionLabel, _figure.m₁MassKilograms, hm2kg,
    _figure.x₁PositionMeters, _figure.x₂PositionMeters] at hCenter
  constructor
  · have hr1 :=
      _laws.radiiAreCenterOfMassDistances .m₁ LengthUnit.meters
    norm_num [Ball.radiusLabel, Ball.positionLabel,
      _figure.x₁PositionMeters, hCenter] at hr1
    exact hr1
  · have hr2 :=
      _laws.radiiAreCenterOfMassDistances .m₂ LengthUnit.meters
    norm_num [Ball.radiusLabel, Ball.positionLabel,
      _figure.x₂PositionMeters, hCenter] at hr2
    exact hr2

/-- Labels attached to the four displayed speed choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metre-per-second value printed beside each answer label. -/
def AnswerChoice.metersPerSecond : AnswerChoice → ℝ
  | .A => 176 / 100
  | .B => 192 / 100
  | .C => 168 / 100
  | .D => 184 / 100

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
A physical speed matches a two-decimal-place displayed choice when its SI
readout differs from the printed value by at most half of `0.01 m/s`.
-/
def MatchesDisplayedSpeed (speed : DimSpeed) (choice : AnswerChoice) : Prop :=
  |speedInMetersPerSecond speed - choice.metersPerSecond| ≤ 1 / 200

/-!
The ball explicitly asked for in the problem, `m₁ = 2.0 kg`, has radius
`0.10 m`.  At `40 rpm` its speed is therefore
`(2π · 40/60) · 0.10 = 2π/15 m/s`.

This formalizes blueprint label `thm:physics:phyx_mini_0696:target` according
to the stated question and the primary image.
-/
theorem twoKilogramBallSpeed_eq_two_pi_over_fifteen
    (setup : TwoBallRodRotationSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalTwoBallRodParameters setup)
    (_laws : SatisfiesMasslessTwoBallRotationLaws setup) :
    speedInMetersPerSecond (setup.ballSpeed .m₁) =
      2 * Real.pi / 15 := by
  have hRateConversion :
      rotationRateReadout TimeUnit.minutes setup.rotationRate =
        60 * rotationRateReadout TimeUnit.seconds setup.rotationRate := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (setup.rotationRate.2 UnitChoices.SI
        {UnitChoices.SI with time := TimeUnit.minutes})
    norm_num [rotationRateReadout, UnitChoices.dimScale,
      TimeUnit.minutes, TimeUnit.seconds, TimeUnit.scale,
      TimeUnit.div_eq_val, NNReal.rpow_neg_one, NNReal.smul_def,
      smul_eq_mul] at h ⊢
    rw [h]
    congr 1
    change (1 / 60 : ℝ)⁻¹ = 60
    norm_num
  have hRateSeconds :
      rotationRateReadout TimeUnit.seconds setup.rotationRate =
        (2 / 3 : ℝ) := by
    rw [_figure.rotationRateRevolutionsPerMinute] at hRateConversion
    linarith
  have hradii :=
    centerOfMassRadiiInMeters setup _figure _physical _laws
  change speedReadout LengthUnit.meters TimeUnit.seconds
    (setup.ballSpeed .m₁) = 2 * Real.pi / 15
  rw [_laws.rigidRotationTangentialSpeed
      .m₁ LengthUnit.meters TimeUnit.seconds,
    _laws.angularSpeedFromRotationRate TimeUnit.seconds, hRateSeconds]
  simp only [Ball.radiusLabel]
  rw [hradii.1]
  ring

/-!
The dataset's recorded `1.68 m/s` choice is consistent with the other ball,
`m₂ = 500 g`, whose center-of-mass radius is `0.40 m`.  Keeping this as a
conclusion rather than a premise exposes the source inconsistency without
changing the target above.
-/
theorem fiveHundredGramBallSpeed_matches_recordedChoiceC
    (setup : TwoBallRodRotationSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalTwoBallRodParameters setup)
    (_laws : SatisfiesMasslessTwoBallRotationLaws setup) :
    MatchesDisplayedSpeed (setup.ballSpeed .m₂) recordedAnswerChoice := by
  have hRateConversion :
      rotationRateReadout TimeUnit.minutes setup.rotationRate =
        60 * rotationRateReadout TimeUnit.seconds setup.rotationRate := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (setup.rotationRate.2 UnitChoices.SI
        {UnitChoices.SI with time := TimeUnit.minutes})
    norm_num [rotationRateReadout, UnitChoices.dimScale,
      TimeUnit.minutes, TimeUnit.seconds, TimeUnit.scale,
      TimeUnit.div_eq_val, NNReal.rpow_neg_one, NNReal.smul_def,
      smul_eq_mul] at h ⊢
    rw [h]
    congr 1
    change (1 / 60 : ℝ)⁻¹ = 60
    norm_num
  have hRateSeconds :
      rotationRateReadout TimeUnit.seconds setup.rotationRate =
        (2 / 3 : ℝ) := by
    rw [_figure.rotationRateRevolutionsPerMinute] at hRateConversion
    linarith
  have hradii :=
    centerOfMassRadiiInMeters setup _figure _physical _laws
  have hSpeed :
      speedInMetersPerSecond (setup.ballSpeed .m₂) =
        8 * Real.pi / 15 := by
    change speedReadout LengthUnit.meters TimeUnit.seconds
      (setup.ballSpeed .m₂) = 8 * Real.pi / 15
    rw [_laws.rigidRotationTangentialSpeed
        .m₂ LengthUnit.meters TimeUnit.seconds,
      _laws.angularSpeedFromRotationRate TimeUnit.seconds, hRateSeconds]
    simp only [Ball.radiusLabel]
    rw [hradii.2]
    ring
  /-
  The dedicated decimal bounds on `π` are not among this file's imports.
  We derive the two weaker bounds needed for two-decimal rounding from
  `Real.cos_bound`, using five applications of the double-angle formula.
  -/
  have doubleAngleLower {x lower : ℝ}
      (hlower : lower < Real.cos x) (hlower_nonneg : 0 ≤ lower) :
      2 * lower ^ 2 - 1 < Real.cos (2 * x) := by
    rw [Real.cos_two_mul]
    nlinarith [sq_nonneg (Real.cos x - lower)]
  have doubleAngleUpper {x upper : ℝ}
      (hx_nonneg : 0 ≤ Real.cos x) (hupper : Real.cos x < upper)
      (hupper_nonneg : 0 ≤ upper) :
      Real.cos (2 * x) < 2 * upper ^ 2 - 1 := by
    rw [Real.cos_two_mul]
    have hp : 0 ≤ (upper - Real.cos x) * (upper + Real.cos x) :=
      mul_nonneg (by linarith) (add_nonneg hupper_nonneg hx_nonneg)
    nlinarith
  have cos_nonneg_of_mem_zero_one {x : ℝ}
      (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ Real.cos x :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by nlinarith [Real.pi_pos])
      (hx1.trans Real.one_le_pi_div_two)
  have hBoundLower :=
    Real.cos_bound (x := (201 / 4096 : ℝ)) (by norm_num)
  have hTaylorLower := (abs_le.mp hBoundLower).1
  norm_num [abs_of_nonneg] at hTaylorLower
  have hc0 :
      (9987956 / 10000000 : ℝ) < Real.cos (201 / 4096 : ℝ) := by
    nlinarith
  have hc1 :
      (9951852 / 10000000 : ℝ) < Real.cos (201 / 2048 : ℝ) := by
    calc
      (9951852 / 10000000 : ℝ) <
          2 * (9987956 / 10000000 : ℝ) ^ 2 - 1 := by norm_num
      _ < Real.cos (2 * (201 / 4096 : ℝ)) :=
        doubleAngleLower hc0 (by norm_num)
      _ = Real.cos (201 / 2048 : ℝ) := by norm_num
  have hc2 :
      (9807871 / 10000000 : ℝ) < Real.cos (201 / 1024 : ℝ) := by
    calc
      (9807871 / 10000000 : ℝ) <
          2 * (9951852 / 10000000 : ℝ) ^ 2 - 1 := by norm_num
      _ < Real.cos (2 * (201 / 2048 : ℝ)) :=
        doubleAngleLower hc1 (by norm_num)
      _ = Real.cos (201 / 1024 : ℝ) := by norm_num
  have hc3 :
      (9238866 / 10000000 : ℝ) < Real.cos (201 / 512 : ℝ) := by
    calc
      (9238866 / 10000000 : ℝ) <
          2 * (9807871 / 10000000 : ℝ) ^ 2 - 1 := by norm_num
      _ < Real.cos (2 * (201 / 1024 : ℝ)) :=
        doubleAngleLower hc2 (by norm_num)
      _ = Real.cos (201 / 512 : ℝ) := by norm_num
  have hc4 :
      (70712 / 100000 : ℝ) < Real.cos (201 / 256 : ℝ) := by
    calc
      (70712 / 100000 : ℝ) <
          2 * (9238866 / 10000000 : ℝ) ^ 2 - 1 := by norm_num
      _ < Real.cos (2 * (201 / 512 : ℝ)) :=
        doubleAngleLower hc3 (by norm_num)
      _ = Real.cos (201 / 256 : ℝ) := by norm_num
  have hCosPositive : 0 < Real.cos (201 / 128 : ℝ) := by
    calc
      0 < 2 * (70712 / 100000 : ℝ) ^ 2 - 1 := by norm_num
      _ < Real.cos (2 * (201 / 256 : ℝ)) :=
        doubleAngleLower hc4 (by norm_num)
      _ = Real.cos (201 / 128 : ℝ) := by norm_num
  have hPiLower : (201 / 64 : ℝ) < Real.pi := by
    have hx : (201 / 128 : ℝ) < Real.pi / 2 := by
      by_contra h
      have hnonpos := Real.cos_nonpos_of_pi_div_two_le_of_le
        (le_of_not_gt h)
        (show (201 / 128 : ℝ) ≤ Real.pi + Real.pi / 2 by
          nlinarith [Real.two_le_pi])
      linarith
    linarith
  have hBoundUpper :=
    Real.cos_bound (x := (63 / 1280 : ℝ)) (by norm_num)
  have hTaylorUpper := (abs_le.mp hBoundUpper).2
  norm_num [abs_of_nonneg] at hTaylorUpper
  have hu0 :
      Real.cos (63 / 1280 : ℝ) < (9987891 / 10000000 : ℝ) := by
    nlinarith
  have hu1 :
      Real.cos (63 / 640 : ℝ) < (99516 / 100000 : ℝ) := by
    calc
      Real.cos (63 / 640 : ℝ) =
          Real.cos (2 * (63 / 1280 : ℝ)) := by norm_num
      _ < 2 * (9987891 / 10000000 : ℝ) ^ 2 - 1 :=
        doubleAngleUpper
          (cos_nonneg_of_mem_zero_one (by norm_num) (by norm_num))
          hu0 (by norm_num)
      _ < (99516 / 100000 : ℝ) := by norm_num
  have hu2 :
      Real.cos (63 / 320 : ℝ) < (98069 / 100000 : ℝ) := by
    calc
      Real.cos (63 / 320 : ℝ) =
          Real.cos (2 * (63 / 640 : ℝ)) := by norm_num
      _ < 2 * (99516 / 100000 : ℝ) ^ 2 - 1 :=
        doubleAngleUpper
          (cos_nonneg_of_mem_zero_one (by norm_num) (by norm_num))
          hu1 (by norm_num)
      _ < (98069 / 100000 : ℝ) := by norm_num
  have hu3 :
      Real.cos (63 / 160 : ℝ) < (92351 / 100000 : ℝ) := by
    calc
      Real.cos (63 / 160 : ℝ) =
          Real.cos (2 * (63 / 320 : ℝ)) := by norm_num
      _ < 2 * (98069 / 100000 : ℝ) ^ 2 - 1 :=
        doubleAngleUpper
          (cos_nonneg_of_mem_zero_one (by norm_num) (by norm_num))
          hu2 (by norm_num)
      _ < (92351 / 100000 : ℝ) := by norm_num
  have hu4 :
      Real.cos (63 / 80 : ℝ) < (70575 / 100000 : ℝ) := by
    calc
      Real.cos (63 / 80 : ℝ) =
          Real.cos (2 * (63 / 160 : ℝ)) := by norm_num
      _ < 2 * (92351 / 100000 : ℝ) ^ 2 - 1 :=
        doubleAngleUpper
          (cos_nonneg_of_mem_zero_one (by norm_num) (by norm_num))
          hu3 (by norm_num)
      _ < (70575 / 100000 : ℝ) := by norm_num
  have hCosNegative : Real.cos (63 / 40 : ℝ) < 0 := by
    calc
      Real.cos (63 / 40 : ℝ) =
          Real.cos (2 * (63 / 80 : ℝ)) := by norm_num
      _ < 2 * (70575 / 100000 : ℝ) ^ 2 - 1 :=
        doubleAngleUpper
          (cos_nonneg_of_mem_zero_one (by norm_num) (by norm_num))
          hu4 (by norm_num)
      _ < 0 := by norm_num
  have hPiUpper : Real.pi < (63 / 20 : ℝ) := by
    have hx : Real.pi / 2 < (63 / 40 : ℝ) := by
      by_contra h
      have hnonneg := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (show -(Real.pi / 2) ≤ (63 / 40 : ℝ) by
          nlinarith [Real.pi_pos])
        (le_of_not_gt h)
      linarith
    linarith
  rw [MatchesDisplayedSpeed, hSpeed]
  norm_num [recordedAnswerChoice, AnswerChoice.metersPerSecond, abs_le]
  constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0696
