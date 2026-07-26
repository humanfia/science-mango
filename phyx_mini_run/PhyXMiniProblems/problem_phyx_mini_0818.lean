import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Maximum radius of an airplane propeller

An airplane moves forward through the air at `75.0 m/s`.  Its propeller turns
at `2400 rev/min`, and the speed of a blade tip through the air may not exceed
`270 m/s`.  The primary image labels the propeller radius by `r`, shows the
forward velocity to the right, and shows the tangential velocity downward with
the formula `v_tan = r * omega`.

The forward and tangential velocities are perpendicular, so the blade-tip
velocity through the air is their vector sum.  Physical lengths, speed
magnitudes, inverse-time rates, and spatial velocity vectors are represented
by Physlib dimensionful quantities.  Real numbers occur only at coherent-unit
readout boundaries, as dimensionless ratios, or as displayed answer values.

Assumption/target split:

* governing laws: one revolution is `2*pi` radians, tangential tip speed is
  `r*omega`, forward and tangential velocity vectors are perpendicular, the
  through-air tip velocity is their vector sum, and an admissible radius is
  exactly one whose through-air tip speed respects the cap;
* previous-part results: none;
* figure/data readouts: `75.0 m/s`, `2400 rev/min`, the `270 m/s` cap, the
  radius arrow `r`, the downward `v_tan = r*omega` arrow, and the rightward
  airplane-velocity arrow;
* target conclusions: existence and maximality of a physical radius whose SI
  readout is `sqrt (270^2 - 75^2) / (80*pi)`, its agreement with `1.03 m` to
  the displayed precision, and selection of answer B.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0818

open Dimension

/-! ## Dimensionful physical quantities and coherent-unit readouts -/

/-- A nonnegative physical length, used for a candidate propeller radius. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical revolution rate, with dimension inverse time. -/
abbrev RevolutionRateQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative angular-speed magnitude; radians are dimensionless. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A dimensionful spatial velocity with three signed Cartesian components. -/
abbrev SpatialVelocityQuantity : Type :=
  Dimensionful
    (WithDim (L𝓭 * T𝓭⁻¹) (EuclideanSpace ℝ (Fin 3)))

/-- Read a nonnegative physical length in a coherent choice of units. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  ((length units).val : ℝ)

/-- Read a revolution rate in inverse units of the selected time unit. -/
def revolutionRateReadout
    (units : UnitChoices) (rate : RevolutionRateQuantity) : ℝ :=
  ((rate units).val : ℝ)

/-- Read an angular speed in inverse units of the selected time unit. -/
def angularSpeedReadout
    (units : UnitChoices) (speed : AngularSpeedQuantity) : ℝ :=
  ((speed units).val : ℝ)

/-- Read a nonnegative speed magnitude in coherent units. -/
def speedReadout (units : UnitChoices) (speed : SpeedQuantity) : ℝ :=
  ((speed units).val : ℝ)

/-- Read a spatial velocity vector in coherent units. -/
def spatialVelocityReadout
    (units : UnitChoices) (velocity : SpatialVelocityQuantity) :
    EuclideanSpace ℝ (Fin 3) :=
  (velocity units).val

/-- SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout UnitChoices.SI length

/-- SI revolutions-per-second readout of a physical revolution rate. -/
def revolutionRateInHertz (rate : RevolutionRateQuantity) : ℝ :=
  revolutionRateReadout UnitChoices.SI rate

/-- SI radians-per-second readout of an angular-speed magnitude. -/
def angularSpeedInRadiansPerSecond (speed : AngularSpeedQuantity) : ℝ :=
  angularSpeedReadout UnitChoices.SI speed

/-- SI metre-per-second readout of a speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout UnitChoices.SI speed

/-- SI metre-per-second readout of a spatial velocity vector. -/
def spatialVelocityInMetersPerSecond
    (velocity : SpatialVelocityQuantity) : EuclideanSpace ℝ (Fin 3) :=
  spatialVelocityReadout UnitChoices.SI velocity

/-! ## Physical scenario and primary-image vocabulary -/

/-- Location of the propeller on the depicted airplane. -/
inductive PropellerLocation where
  | atAircraftNose
  | elsewhere
  deriving DecidableEq, Repr

/-- Directions of the two green arrows visible in the supplied image. -/
inductive FigureArrowDirection where
  | right
  | downward
  deriving DecidableEq, Repr

/-- Literal symbolic and numerical labels visible in the supplied image. -/
inductive FigureLabel where
  | radiusR
  | airplaneVelocity75MetersPerSecond
  | tangentialVelocityEqualsROmega
  | rotationRate2400RevolutionsPerMinute
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative and numerical information transcribed from primary image `818.png`.
No metric radius is inferred from the drawing: the radius arrow carries only
the symbolic label `r`.
-/
structure PropellerFigure where
  showsAirplane : Bool
  showsPropeller : Bool
  propellerLocation : PropellerLocation
  showsCircularTipPath : Bool
  showsRotationArrow : Bool
  showsRadiusSegmentFromHubToTip : Bool
  showsLabel : FigureLabel → Bool
  airplaneVelocityArrowDirection : FigureArrowDirection
  tangentialVelocityArrowDirection : FigureArrowDirection
  printedAirplaneSpeedMetersPerSecond : ℝ
  printedRotationRateRevolutionsPerMinute : ℝ

/-!
Independent physical data for the design problem.  The functions assigning
tangential and resultant tip velocities to a candidate physical radius are
not defined from the requested maximum.  Their relations are imposed only by
the governing-law interfaces below.
-/
structure PropellerDesignSetup where
  figure : PropellerFigure
  revolutionRate : RevolutionRateQuantity
  angularSpeed : AngularSpeedQuantity
  airplaneForwardSpeed : SpeedQuantity
  maximumPermittedTipSpeed : SpeedQuantity
  ambientSpeedOfSound : SpeedQuantity
  aboutSoundFractionTolerance : ℝ
  airplaneForwardVelocity : SpatialVelocityQuantity
  tangentialTipVelocity : LengthQuantity → SpatialVelocityQuantity
  tipVelocityThroughAir : LengthQuantity → SpatialVelocityQuantity
  physicallyAdmissibleRadius : LengthQuantity → Prop
  speedCapChosenToLimitNoise : Bool
  speedCapDescribedAsAboutEightyPercentOfSoundSpeed : Bool

/-! ## Figure evidence, problem data, and physical laws -/

/-- Exact transcription of the labels, placements, and arrow directions. -/
structure MatchesPrimaryPropellerFigure
    (setup : PropellerDesignSetup) : Prop where
  airplaneShown : setup.figure.showsAirplane = true
  propellerShown : setup.figure.showsPropeller = true
  propellerAtNose :
    setup.figure.propellerLocation = .atAircraftNose
  circularTipPathShown : setup.figure.showsCircularTipPath = true
  rotationArrowShown : setup.figure.showsRotationArrow = true
  radiusSegmentShown :
    setup.figure.showsRadiusSegmentFromHubToTip = true
  everyLiteralLabelShown :
    ∀ label, setup.figure.showsLabel label = true
  airplaneVelocityPointsRight :
    setup.figure.airplaneVelocityArrowDirection = .right
  tangentialVelocityPointsDownward :
    setup.figure.tangentialVelocityArrowDirection = .downward
  printedForwardSpeed :
    setup.figure.printedAirplaneSpeedMetersPerSecond = 75
  printedRotationRate :
    setup.figure.printedRotationRateRevolutionsPerMinute = 2400

/-!
Numerical data from the prose and its connection to the image.  The printed
`2400 rev/min` is `2400/60 = 40` revolutions per coherent-SI second.  The
approximately-eighty-percent remark is retained as contextual data with an
explicit, setup-supplied tolerance; it plays no role in solving for radius.
No radius or answer choice occurs here.
-/
structure MatchesPropellerProblemData
    (setup : PropellerDesignSetup) : Prop where
  airplaneSpeedMatchesFigure :
    speedInMetersPerSecond setup.airplaneForwardSpeed =
      setup.figure.printedAirplaneSpeedMetersPerSecond
  rotationRateMatchesFigure :
    revolutionRateInHertz setup.revolutionRate =
      setup.figure.printedRotationRateRevolutionsPerMinute / 60
  tipSpeedCapMetersPerSecond :
    speedInMetersPerSecond setup.maximumPermittedTipSpeed = 270
  noiseControlMotivation : setup.speedCapChosenToLimitNoise = true
  statedSoundSpeedComparison :
    setup.speedCapDescribedAsAboutEightyPercentOfSoundSpeed = true
  approximatelyEightyPercentOfAmbientSoundSpeed :
    |speedInMetersPerSecond setup.maximumPermittedTipSpeed /
          speedInMetersPerSecond setup.ambientSpeedOfSound - 4 / 5| ≤
      setup.aboutSoundFractionTolerance

/-- Positivity and nondegeneracy conditions selecting the physical branch. -/
structure HasPhysicalPropellerParameters
    (setup : PropellerDesignSetup) : Prop where
  revolutionRatePositive :
    0 < revolutionRateInHertz setup.revolutionRate
  angularSpeedPositive :
    0 < angularSpeedInRadiansPerSecond setup.angularSpeed
  airplaneSpeedNonnegative :
    0 ≤ speedInMetersPerSecond setup.airplaneForwardSpeed
  capExceedsForwardSpeed :
    speedInMetersPerSecond setup.airplaneForwardSpeed <
      speedInMetersPerSecond setup.maximumPermittedTipSpeed
  ambientSoundSpeedPositive :
    0 < speedInMetersPerSecond setup.ambientSpeedOfSound
  soundFractionToleranceNonnegative :
    0 ≤ setup.aboutSoundFractionTolerance
  radiusReadoutsNonnegative :
    ∀ radius, 0 ≤ lengthInMeters radius

/-- One complete propeller revolution is `2*pi` radians. -/
structure SatisfiesPropellerAngularRateConversion
    (setup : PropellerDesignSetup) : Prop where
  angularSpeedFromRevolutionRate :
    ∀ units : UnitChoices,
      angularSpeedReadout units setup.angularSpeed =
        2 * Real.pi * revolutionRateReadout units setup.revolutionRate

/-!
Vector kinematics for each candidate radius.  The forward velocity is the
airplane velocity through the air, the tangential velocity is relative to the
airframe, and their sum is the blade-tip velocity through the air.

The perpendicularity field is the geometric fact displayed by the horizontal
and vertical green arrows.  It is the hypothesis needed for Mathlib's
`norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero` Pythagorean theorem.
The admissibility equivalence only states the design speed cap; it contains no
maximum-radius formula.
-/
structure SatisfiesPropellerTipKinematics
    (setup : PropellerDesignSetup) : Prop where
  forwardVelocityMagnitude :
    ∀ units : UnitChoices,
      ‖spatialVelocityReadout units setup.airplaneForwardVelocity‖ =
        speedReadout units setup.airplaneForwardSpeed
  tangentialVelocityMagnitude :
    ∀ (units : UnitChoices) (radius : LengthQuantity),
      ‖spatialVelocityReadout units (setup.tangentialTipVelocity radius)‖ =
        lengthReadout units radius *
          angularSpeedReadout units setup.angularSpeed
  forwardTangentialPerpendicular :
    ∀ (units : UnitChoices) (radius : LengthQuantity),
      inner ℝ
          (spatialVelocityReadout units setup.airplaneForwardVelocity)
          (spatialVelocityReadout units
            (setup.tangentialTipVelocity radius)) = 0
  throughAirVelocityIsVectorSum :
    ∀ (units : UnitChoices) (radius : LengthQuantity),
      spatialVelocityReadout units (setup.tipVelocityThroughAir radius) =
        spatialVelocityReadout units setup.airplaneForwardVelocity +
          spatialVelocityReadout units
            (setup.tangentialTipVelocity radius)
  admissibleExactlyWhenWithinSpeedCap :
    ∀ radius : LengthQuantity,
      setup.physicallyAdmissibleRadius radius ↔
        ‖spatialVelocityInMetersPerSecond
            (setup.tipVelocityThroughAir radius)‖ ≤
          speedInMetersPerSecond setup.maximumPermittedTipSpeed

/-! ## Derived kinematics and requested maximum -/

/-!
The angular rate conversion and the printed `2400 rev/min` imply
`omega = 80*pi rad/s`.  This is a derived result, not problem data.
-/
lemma angularSpeed_is_eighty_pi_radians_per_second
    (setup : PropellerDesignSetup)
    (_figure : MatchesPrimaryPropellerFigure setup)
    (_data : MatchesPropellerProblemData setup)
    (_conversion : SatisfiesPropellerAngularRateConversion setup) :
    angularSpeedInRadiansPerSecond setup.angularSpeed = 80 * Real.pi := by
  calc
    angularSpeedInRadiansPerSecond setup.angularSpeed =
        2 * Real.pi * revolutionRateInHertz setup.revolutionRate := by
      simpa only [angularSpeedInRadiansPerSecond,
        revolutionRateInHertz] using
        _conversion.angularSpeedFromRevolutionRate UnitChoices.SI
    _ = 80 * Real.pi := by
      rw [_data.rotationRateMatchesFigure, _figure.printedRotationRate]
      ring

/-!
Pythagoras for the forward and tangential components of the blade-tip
velocity.  This lemma is a generic consequence of the vector laws and does
not solve the maximum-radius optimization.
-/
lemma tipSpeedSquared_pythagorean
    (setup : PropellerDesignSetup)
    (_kinematics : SatisfiesPropellerTipKinematics setup)
    (radius : LengthQuantity) :
    ‖spatialVelocityInMetersPerSecond
        (setup.tipVelocityThroughAir radius)‖ ^ 2 =
      speedInMetersPerSecond setup.airplaneForwardSpeed ^ 2 +
        (lengthInMeters radius *
          angularSpeedInRadiansPerSecond setup.angularSpeed) ^ 2 := by
  rw [spatialVelocityInMetersPerSecond,
    _kinematics.throughAirVelocityIsVectorSum UnitChoices.SI radius]
  have hPythagorean :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (spatialVelocityReadout UnitChoices.SI
        setup.airplaneForwardVelocity)
      (spatialVelocityReadout UnitChoices.SI
        (setup.tangentialTipVelocity radius))
      (_kinematics.forwardTangentialPerpendicular UnitChoices.SI radius)
  rw [pow_two, hPythagorean,
    _kinematics.forwardVelocityMagnitude UnitChoices.SI,
    _kinematics.tangentialVelocityMagnitude UnitChoices.SI radius]
  simp only [speedInMetersPerSecond, lengthInMeters,
    angularSpeedInRadiansPerSecond, pow_two]

/-- A physical radius is maximal when it is admissible and bounds every other
admissible physical radius in the SI metre readout. -/
def IsMaximumAdmissibleRadius
    (setup : PropellerDesignSetup) (radius : LengthQuantity) : Prop :=
  setup.physicallyAdmissibleRadius radius ∧
    ∀ otherRadius : LengthQuantity,
      setup.physicallyAdmissibleRadius otherRadius →
        lengthInMeters otherRadius ≤ lengthInMeters radius

/-- The SI radius candidate obtained algebraically by saturating the speed cap.
Its maximality is not definitional; that is the substantive theorem below. -/
def radiusFromSaturatedSpeedBudgetMeters : ℝ :=
  Real.sqrt ((270 : ℝ) ^ 2 - (75 : ℝ) ^ 2) /
    (80 * Real.pi)

/-- Labels of the four radius choices displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metre readout printed beside each displayed answer choice. -/
def displayedRadiusMeters : AnswerChoice → ℝ
  | .A => 187 / 100
  | .B => 103 / 100
  | .C => 212 / 100
  | .D => 208 / 100

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A displayed radius is closest to a computed radius readout. -/
def IsClosestDisplayedRadius
    (radiusMeters : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice : AnswerChoice,
    |radiusMeters - displayedRadiusMeters choice| ≤
      |radiusMeters - displayedRadiusMeters otherChoice|

/-!
There exists a physically admissible maximum radius with exact SI readout

`sqrt (270^2 - 75^2) / (80*pi)`.

That readout is within `0.01 m` of `1.03 m` and is closest to displayed choice
B.  Maximality, the exact expression, and the answer selection occur only in
this conclusion.

Blueprint: `thm:physics:phyx_mini_0818:target`.
-/
theorem maximumPossiblePropellerRadius_is_one_point_zero_three_meters
    (setup : PropellerDesignSetup)
    (_figure : MatchesPrimaryPropellerFigure setup)
    (_data : MatchesPropellerProblemData setup)
    (_physical : HasPhysicalPropellerParameters setup)
    (_conversion : SatisfiesPropellerAngularRateConversion setup)
    (_kinematics : SatisfiesPropellerTipKinematics setup) :
    (∃ radius : LengthQuantity,
      IsMaximumAdmissibleRadius setup radius ∧
        lengthInMeters radius = radiusFromSaturatedSpeedBudgetMeters) ∧
      |radiusFromSaturatedSpeedBudgetMeters - displayedRadiusMeters .B| <
        1 / 100 ∧
      IsClosestDisplayedRadius radiusFromSaturatedSpeedBudgetMeters .B := by
  have hAngularSpeed :
      angularSpeedInRadiansPerSecond setup.angularSpeed =
        80 * Real.pi :=
    angularSpeed_is_eighty_pi_radians_per_second
      setup _figure _data _conversion
  have hForwardSpeed :
      speedInMetersPerSecond setup.airplaneForwardSpeed = 75 := by
    rw [_data.airplaneSpeedMatchesFigure, _figure.printedForwardSpeed]
  have hTipSpeedCap :
      speedInMetersPerSecond setup.maximumPermittedTipSpeed = 270 :=
    _data.tipSpeedCapMetersPerSecond
  have hRadicandNonnegative :
      0 ≤ (270 : ℝ) ^ 2 - (75 : ℝ) ^ 2 := by
    norm_num
  have hSqrtNonnegative :
      0 ≤ Real.sqrt ((270 : ℝ) ^ 2 - (75 : ℝ) ^ 2) :=
    Real.sqrt_nonneg _
  have hSqrtSquared :
      Real.sqrt ((270 : ℝ) ^ 2 - (75 : ℝ) ^ 2) ^ 2 =
        (270 : ℝ) ^ 2 - (75 : ℝ) ^ 2 :=
    Real.sq_sqrt hRadicandNonnegative
  have hAngularFactorPositive : 0 < 80 * Real.pi :=
    mul_pos (by norm_num) Real.pi_pos
  have hRadiusNonnegative :
      0 ≤ radiusFromSaturatedSpeedBudgetMeters := by
    unfold radiusFromSaturatedSpeedBudgetMeters
    exact div_nonneg hSqrtNonnegative hAngularFactorPositive.le
  have hRadiusTimesAngularFactor :
      radiusFromSaturatedSpeedBudgetMeters * (80 * Real.pi) =
        Real.sqrt ((270 : ℝ) ^ 2 - (75 : ℝ) ^ 2) := by
    unfold radiusFromSaturatedSpeedBudgetMeters
    exact div_mul_cancel₀ _
      (ne_of_gt hAngularFactorPositive)
  let maximumRadius : LengthQuantity :=
    CarriesDimension.toDimensionful UnitChoices.SI
      (⟨⟨radiusFromSaturatedSpeedBudgetMeters,
        hRadiusNonnegative⟩⟩ : WithDim L𝓭 NNReal)
  have hMaximumRadiusReadout :
      lengthInMeters maximumRadius =
        radiusFromSaturatedSpeedBudgetMeters := by
    norm_num [maximumRadius, lengthInMeters, lengthReadout,
      CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale_apply, L𝓭, LengthUnit.meters,
      LengthUnit.div_eq_val]
    rfl
  have hMaximumTipSpeedSquared :
      ‖spatialVelocityInMetersPerSecond
          (setup.tipVelocityThroughAir maximumRadius)‖ ^ 2 =
        (270 : ℝ) ^ 2 := by
    rw [tipSpeedSquared_pythagorean setup _kinematics maximumRadius,
      hForwardSpeed, hMaximumRadiusReadout, hAngularSpeed,
      hRadiusTimesAngularFactor, hSqrtSquared]
    ring
  have hMaximumTipSpeed :
      ‖spatialVelocityInMetersPerSecond
          (setup.tipVelocityThroughAir maximumRadius)‖ = 270 := by
    have hNormNonnegative :
        0 ≤ ‖spatialVelocityInMetersPerSecond
          (setup.tipVelocityThroughAir maximumRadius)‖ :=
      norm_nonneg _
    nlinarith only [hNormNonnegative, hMaximumTipSpeedSquared]
  have hMaximumRadiusAdmissible :
      setup.physicallyAdmissibleRadius maximumRadius := by
    apply
      (_kinematics.admissibleExactlyWhenWithinSpeedCap
        maximumRadius).2
    rw [hMaximumTipSpeed, hTipSpeedCap]
  have hMaximumRadiusIsMaximum :
      IsMaximumAdmissibleRadius setup maximumRadius := by
    refine ⟨hMaximumRadiusAdmissible, ?_⟩
    intro otherRadius hOtherAdmissible
    have hOtherWithinCap :=
      (_kinematics.admissibleExactlyWhenWithinSpeedCap
        otherRadius).1 hOtherAdmissible
    rw [hTipSpeedCap] at hOtherWithinCap
    have hOtherSpeedSquared :=
      tipSpeedSquared_pythagorean setup _kinematics otherRadius
    rw [hForwardSpeed, hAngularSpeed] at hOtherSpeedSquared
    have hOtherSpeedNonnegative :
        0 ≤ ‖spatialVelocityInMetersPerSecond
          (setup.tipVelocityThroughAir otherRadius)‖ :=
      norm_nonneg _
    have hOtherRadiusNonnegative :
        0 ≤ lengthInMeters otherRadius :=
      _physical.radiusReadoutsNonnegative otherRadius
    have hOtherTangentialNonnegative :
        0 ≤ lengthInMeters otherRadius * (80 * Real.pi) :=
      mul_nonneg hOtherRadiusNonnegative hAngularFactorPositive.le
    have hOtherTangentialSquaredBound :
        (lengthInMeters otherRadius * (80 * Real.pi)) ^ 2 ≤
          (270 : ℝ) ^ 2 - (75 : ℝ) ^ 2 := by
      nlinarith only [hOtherWithinCap, hOtherSpeedSquared,
        hOtherSpeedNonnegative]
    have hOtherTangentialBound :
        lengthInMeters otherRadius * (80 * Real.pi) ≤
          Real.sqrt ((270 : ℝ) ^ 2 - (75 : ℝ) ^ 2) := by
      nlinarith only [hOtherTangentialSquaredBound,
        hOtherTangentialNonnegative, hSqrtNonnegative,
        hSqrtSquared]
    rw [← hRadiusTimesAngularFactor] at hOtherTangentialBound
    rw [hMaximumRadiusReadout]
    exact
      le_of_mul_le_mul_right hOtherTangentialBound
        hAngularFactorPositive
  have hSinLt (x : ℝ) (hx : 0 < x) : Real.sin x < x := by
    rcases lt_or_ge 1 x with hLarge | hSmall
    · exact (Real.sin_le_one x).trans_lt hLarge
    have hxAbs : |x| = x := abs_of_nonneg hx.le
    have hBound :=
      le_of_abs_le
        (Real.sin_bound (show |x| ≤ 1 by rwa [hxAbs]))
    rw [sub_le_iff_le_add', hxAbs] at hBound
    apply hBound.trans_lt
    rw [sub_add, sub_lt_self_iff, sub_pos,
      div_eq_mul_inv (x ^ 3)]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num)
      (pow_pos hx 3)
    apply pow_le_pow_of_le_one hx.le hSmall
    simp
  have hSinGtSubCube
      (x : ℝ) (hx : 0 < x) (hxOne : x ≤ 1) :
      x - x ^ 3 / 4 < Real.sin x := by
    have hxAbs : |x| = x := abs_of_nonneg hx.le
    have hBound :=
      neg_le_of_abs_le
        (Real.sin_bound (show |x| ≤ 1 by rwa [hxAbs]))
    rw [le_sub_iff_add_le, hxAbs] at hBound
    refine lt_of_lt_of_le ?_ hBound
    have hDifference :
        x ^ 3 / (4 : ℝ) - x ^ 3 / 6 = x ^ 3 * 12⁻¹ := by
      norm_num [div_eq_mul_inv, ← mul_sub]
    rw [add_comm, sub_add, sub_neg_eq_add,
      sub_lt_sub_iff_left, ← lt_sub_iff_add_lt', hDifference]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num)
      (pow_pos hx 3)
    apply pow_le_pow_of_le_one hx.le hxOne
    simp
  have hSqrtTwoNonnegative :
      0 ≤ Real.sqrt (2 : ℝ) :=
    Real.sqrt_nonneg _
  have hSqrtTwoSquared :
      Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hSqrtTwoUpper :
      Real.sqrt (2 : ℝ) < 14143 / 10000 := by
    nlinarith only [hSqrtTwoNonnegative, hSqrtTwoSquared]
  have hInnerNonnegative :
      0 ≤ Real.sqrt (2 + Real.sqrt (2 : ℝ)) :=
    Real.sqrt_nonneg _
  have hInnerSquared :
      Real.sqrt (2 + Real.sqrt (2 : ℝ)) ^ 2 =
        2 + Real.sqrt 2 :=
    Real.sq_sqrt (by positivity)
  have hInnerUpper :
      Real.sqrt (2 + Real.sqrt (2 : ℝ)) < 9239 / 5000 := by
    nlinarith only [hInnerNonnegative, hInnerSquared,
      hSqrtTwoUpper]
  have hOuterNonnegative :
      0 ≤ Real.sqrt
        (2 - Real.sqrt (2 + Real.sqrt (2 : ℝ))) :=
    Real.sqrt_nonneg _
  have hInnerLeTwo :
      Real.sqrt (2 + Real.sqrt (2 : ℝ)) ≤ 2 := by
    nlinarith only [hInnerNonnegative, hInnerSquared,
      hSqrtTwoUpper]
  have hOuterSquared :
      Real.sqrt
          (2 - Real.sqrt (2 + Real.sqrt (2 : ℝ))) ^ 2 =
        2 - Real.sqrt (2 + Real.sqrt 2) :=
    Real.sq_sqrt (by linarith)
  have hOuterLower :
      39 / 100 <
        Real.sqrt
          (2 - Real.sqrt (2 + Real.sqrt (2 : ℝ))) := by
    nlinarith only [hOuterNonnegative, hOuterSquared,
      hInnerUpper]
  have hPiLower : (3.12 : ℝ) < Real.pi := by
    have h :=
      hSinLt (Real.pi / 16)
        (div_pos Real.pi_pos (by norm_num))
    rw [Real.sin_pi_div_sixteen] at h
    nlinarith only [h, hOuterLower]
  have hSqrtTwoLower :
      707 / 500 < Real.sqrt (2 : ℝ) := by
    nlinarith only [hSqrtTwoNonnegative, hSqrtTwoSquared]
  have hInnerLower :
      18477 / 10000 <
        Real.sqrt (2 + Real.sqrt (2 : ℝ)) := by
    nlinarith only [hInnerNonnegative, hInnerSquared,
      hSqrtTwoLower]
  have hDeepNonnegative :
      0 ≤ Real.sqrt
        (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ))) :=
    Real.sqrt_nonneg _
  have hDeepSquared :
      Real.sqrt
          (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ))) ^ 2 =
        2 + Real.sqrt (2 + Real.sqrt 2) :=
    Real.sq_sqrt (by positivity)
  have hDeepLower :
      3923 / 2000 <
        Real.sqrt
          (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ))) := by
    nlinarith only [hDeepNonnegative, hDeepSquared,
      hInnerLower]
  have hOuterDeepNonnegative :
      0 ≤ Real.sqrt
        (2 - Real.sqrt
          (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ)))) :=
    Real.sqrt_nonneg _
  have hDeepLeTwo :
      Real.sqrt
        (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ))) ≤ 2 := by
    nlinarith only [hDeepNonnegative, hDeepSquared,
      hInnerLeTwo]
  have hOuterDeepSquared :
      Real.sqrt
          (2 - Real.sqrt
            (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ)))) ^ 2 =
        2 - Real.sqrt
          (2 + Real.sqrt (2 + Real.sqrt 2)) :=
    Real.sq_sqrt (by linarith)
  have hOuterDeepUpper :
      Real.sqrt
          (2 - Real.sqrt
            (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ)))) <
        1963 / 10000 := by
    nlinarith only [hOuterDeepNonnegative,
      hOuterDeepSquared, hDeepLower]
  have hPiUpper : Real.pi < (3.16 : ℝ) := by
    by_contra hNotUpper
    have hPiLowerBound : (3.16 : ℝ) ≤ Real.pi :=
      le_of_not_gt hNotUpper
    have hXPositive : 0 < Real.pi / 32 :=
      div_pos Real.pi_pos (by norm_num)
    have hXLe : Real.pi / 32 ≤ (1 : ℝ) / 8 := by
      nlinarith only [Real.pi_le_four]
    have hXCubeLe :
        (Real.pi / 32) ^ 3 ≤ ((1 : ℝ) / 8) ^ 3 :=
      pow_le_pow_left₀ hXPositive.le hXLe 3
    have h :=
      hSinGtSubCube (Real.pi / 32) hXPositive
        (by linarith)
    rw [Real.sin_pi_div_thirty_two] at h
    nlinarith only [hPiLowerBound, hXCubeLe, h,
      hOuterDeepUpper]
  have hSqrtTooSmallImpossible
      (s : ℝ) (hs : 0 ≤ s)
      (hsSquared :
        s ^ 2 = (270 : ℝ) ^ 2 - (75 : ℝ) ^ 2)
      (hsUpper :
        s ≤ (102 : ℝ) / 100 * (80 * 3.16)) :
      False := by
    nlinarith only [hs, hsSquared, hsUpper]
  have hSqrtTooLargeImpossible
      (s : ℝ) (hs : 0 ≤ s)
      (hsSquared :
        s ^ 2 = (270 : ℝ) ^ 2 - (75 : ℝ) ^ 2)
      (hsLower :
        (104 : ℝ) / 100 * (80 * 3.12) ≤ s) :
      False := by
    nlinarith only [hs, hsSquared, hsLower]
  have hRadiusLower :
      (102 : ℝ) / 100 < radiusFromSaturatedSpeedBudgetMeters := by
    by_contra hNotLower
    have hRadiusUpperBound :
        radiusFromSaturatedSpeedBudgetMeters ≤ (102 : ℝ) / 100 :=
      le_of_not_gt hNotLower
    have hAngularFactorUpper :
        80 * Real.pi ≤ 80 * (3.16 : ℝ) :=
      mul_le_mul_of_nonneg_left hPiUpper.le (by norm_num)
    have hSqrtUpper :
        Real.sqrt ((270 : ℝ) ^ 2 - (75 : ℝ) ^ 2) ≤
          (102 : ℝ) / 100 * (80 * 3.16) := by
      rw [← hRadiusTimesAngularFactor]
      exact mul_le_mul hRadiusUpperBound hAngularFactorUpper
        hAngularFactorPositive.le (by norm_num)
    exact hSqrtTooSmallImpossible _ hSqrtNonnegative
      hSqrtSquared hSqrtUpper
  have hRadiusUpper :
      radiusFromSaturatedSpeedBudgetMeters < (104 : ℝ) / 100 := by
    by_contra hNotUpper
    have hRadiusLowerBound :
        (104 : ℝ) / 100 ≤ radiusFromSaturatedSpeedBudgetMeters :=
      le_of_not_gt hNotUpper
    have hAngularFactorLower :
        80 * (3.12 : ℝ) ≤ 80 * Real.pi :=
      mul_le_mul_of_nonneg_left hPiLower.le (by norm_num)
    have hSqrtLower :
        (104 : ℝ) / 100 * (80 * 3.12) ≤
          Real.sqrt ((270 : ℝ) ^ 2 - (75 : ℝ) ^ 2) := by
      rw [← hRadiusTimesAngularFactor]
      exact mul_le_mul hRadiusLowerBound hAngularFactorLower
        (by norm_num) hRadiusNonnegative
    exact hSqrtTooLargeImpossible _ hSqrtNonnegative
      hSqrtSquared hSqrtLower
  have hRounded :
      |radiusFromSaturatedSpeedBudgetMeters -
          displayedRadiusMeters .B| < 1 / 100 := by
    simp only [displayedRadiusMeters]
    rw [abs_lt]
    constructor <;>
      nlinarith only [hRadiusLower, hRadiusUpper]
  refine ⟨?_, hRounded, ?_⟩
  · exact
      ⟨maximumRadius, hMaximumRadiusIsMaximum,
        hMaximumRadiusReadout⟩
  · unfold IsClosestDisplayedRadius
    intro otherChoice
    have hRoundedLe := hRounded.le
    fin_cases otherChoice
    · simp only [displayedRadiusMeters] at hRoundedLe ⊢
      rw [abs_of_neg (by nlinarith only [hRadiusUpper] :
        radiusFromSaturatedSpeedBudgetMeters - 187 / 100 < 0)]
      nlinarith only [hRoundedLe, hRadiusUpper]
    · exact le_rfl
    · simp only [displayedRadiusMeters] at hRoundedLe ⊢
      rw [abs_of_neg (by nlinarith only [hRadiusUpper] :
        radiusFromSaturatedSpeedBudgetMeters - 212 / 100 < 0)]
      nlinarith only [hRoundedLe, hRadiusUpper]
    · simp only [displayedRadiusMeters] at hRoundedLe ⊢
      rw [abs_of_neg (by nlinarith only [hRadiusUpper] :
        radiusFromSaturatedSpeedBudgetMeters - 208 / 100 < 0)]
      nlinarith only [hRoundedLe, hRadiusUpper]

end PhyXMiniProblems.ProblemPhyXMini0818
