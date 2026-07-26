import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0779

open Dimension

/-!
# Speed of a hoop unwinding from a fixed string

A uniform thin hoop of radius `8.00 cm` and mass `0.180 kg` is released from
rest while a string wrapped around its rim has its free end held fixed.  The
hoop descends `75.0 cm` as the string unwinds without slipping.  The requested
observable is the speed of the hoop's center after that descent.

Physical magnitudes use Physlib's unit-independent `Dimensionful` and
`DimSpeed` types.  Real numbers occur only as named-unit readouts and as the
dimensionless numerical values printed in the exercise.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- The physical dimension `L T⁻²` of an acceleration magnitude. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L²` of an axial moment of inertia. -/
def momentOfInertiaDimension : Dimension := M𝓭 * L𝓭 * L𝓭

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative angular speed; radians are dimensionless. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative axial moment of inertia. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- Read a mass in a selected Physlib mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a length in a selected Physlib length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : DimSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read an acceleration in coherent selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read angular speed in radians per selected time unit. -/
def angularSpeedReadout
    (timeUnit : TimeUnit) (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- Read a moment of inertia in coherent selected mass and length units. -/
def momentOfInertiaReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimeter readout used by the problem statement. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- SI readout of a speed in meters per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- SI readout of an acceleration in meters per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- SI readout of an angular speed in radians per second. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  angularSpeedReadout TimeUnit.seconds angularSpeed

/-- SI readout of a moment of inertia in kilogram-meter squared. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  momentOfInertiaReadout MassUnit.kilograms LengthUnit.meters inertia

/-! ## Physical roles and primary-figure vocabulary -/

/-- Idealized mass distribution associated with the word "hoop". -/
inductive HoopMassModel where
  | uniformThinHoop
  | other
  deriving DecidableEq, Repr

/-- Idealization of the string whose own energy is neglected. -/
inductive StringModel where
  | masslessInextensible
  | other
  deriving DecidableEq, Repr

/-- Contact condition between the wound string and the rim. -/
inductive StringHoopContact where
  | wrappedWithoutSlip
  | other
  deriving DecidableEq, Repr

/-- Constraint on the upper free end of the string. -/
inductive StringEndCondition where
  | fixedByHand
  | other
  deriving DecidableEq, Repr

/-- Direction of the center-of-mass motion in the pictured experiment. -/
inductive CenterMotionDirection where
  | verticallyDownward
  | other
  deriving DecidableEq, Repr

/-- Rotation sense as viewed in the plane of the supplied image. -/
inductive RotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Individually visible objects or annotations in image `779.png`. -/
inductive FigureObject where
  | hand
  | verticalString
  | circularHoop
  | curvedRotationArrow
  | radiusIndicator
  | radiusText
  deriving DecidableEq, Fintype, Repr

/-- Structured transcription of the primary raster. -/
structure SuppliedHoopFigure where
  showsObject : FigureObject → Bool
  radiusLabelText : String
  radiusLabelMeters : ℝ
  stringRunsVertically : Bool
  stringIsTangentToRim : Bool
  freeEndIsHeldByHand : Bool
  radiusIndicatorRunsFromCenterToRim : Bool
  rotationArrowSense : RotationSense

/-!
Independent physical quantities and endpoint observables.  In particular,
`finalCenterSpeed` is not defined from an answer choice or from a solved
formula; it is constrained only by the governing laws below.
-/
structure UnwindingHoopSetup where
  hoopMass : MassQuantity
  hoopRadius : LengthQuantity
  descentDistance : LengthQuantity
  gravitationalAcceleration : AccelerationQuantity
  hoopMomentOfInertia : MomentOfInertiaQuantity
  initialCenterSpeed : DimSpeed
  initialAngularSpeed : AngularSpeedQuantity
  finalCenterSpeed : DimSpeed
  finalAngularSpeed : AngularSpeedQuantity
  numberOfWraps : ℕ
  hoopMassModel : HoopMassModel
  stringModel : StringModel
  stringHoopContact : StringHoopContact
  freeEndCondition : StringEndCondition
  centerMotionDirection : CenterMotionDirection
  positiveRotationSense : RotationSense
  figure : SuppliedHoopFigure

/-! ## Scenario, source data, figure evidence, and governing laws -/

/-!
The qualitative physical model stated or conventionally idealized by the
exercise.  "Several times" is recorded conservatively as at least two full
wraps; the exact count does not enter the endpoint energy calculation.
-/
structure MatchesProblemScenario (setup : UnwindingHoopSetup) : Prop where
  bodyIsUniformThinHoop : setup.hoopMassModel = .uniformThinHoop
  stringIsIdeal : setup.stringModel = .masslessInextensible
  stringIsWrappedWithoutSlip : setup.stringHoopContact = .wrappedWithoutSlip
  freeEndIsFixed : setup.freeEndCondition = .fixedByHand
  centerDescendsVertically :
    setup.centerMotionDirection = .verticallyDownward
  severalWraps : 2 ≤ setup.numberOfWraps
  clockwiseDirectionIsPositive : setup.positiveRotationSense = .clockwise

/-!
Numerical data from the prose and the release-from-rest initial condition.
No final speed or answer choice occurs in this structure.
-/
structure MatchesProblemReadouts (setup : UnwindingHoopSetup) : Prop where
  massInKilograms : massInKilograms setup.hoopMass = 9 / 50
  radiusInCentimeters : lengthInCentimeters setup.hoopRadius = 8
  descentInCentimeters : lengthInCentimeters setup.descentDistance = 75
  initialCenterAtRest :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.initialCenterSpeed = 0
  initialRotationAtRest :
    ∀ timeUnit : TimeUnit,
      angularSpeedReadout timeUnit setup.initialAngularSpeed = 0

/-!
Literal primary-image evidence: a hand holds a vertical string tangent to the
hoop, the hoop has a clockwise curved arrow, and the radial indicator is
labeled `0.0800 m`.  It contains no final-speed readout.
-/
structure MatchesPrimaryFigure (setup : UnwindingHoopSetup) : Prop where
  everyObjectShown :
    ∀ object : FigureObject, setup.figure.showsObject object = true
  radiusText : setup.figure.radiusLabelText = "0.0800 m"
  radiusValueMeters : setup.figure.radiusLabelMeters = 2 / 25
  physicalRadiusMatchesLabel :
    lengthInMeters setup.hoopRadius = setup.figure.radiusLabelMeters
  verticalString : setup.figure.stringRunsVertically = true
  tangentString : setup.figure.stringIsTangentToRim = true
  heldByHand : setup.figure.freeEndIsHeldByHand = true
  radialIndicator :
    setup.figure.radiusIndicatorRunsFromCenterToRim = true
  clockwiseArrow : setup.figure.rotationArrowSense = .clockwise

/-- Standard near-Earth gravitational acceleration used by the numerical
multiple-choice calculation. -/
structure UsesStandardEarthGravity (setup : UnwindingHoopSetup) : Prop where
  gravitationalAccelerationSI :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5

/-- Positivity and nondegeneracy of the physical parameters. -/
structure HasPhysicalParameters (setup : UnwindingHoopSetup) : Prop where
  hoopMassPositive :
    ∀ massUnit, 0 < massReadout massUnit setup.hoopMass
  hoopRadiusPositive :
    ∀ lengthUnit, 0 < lengthReadout lengthUnit setup.hoopRadius
  descentDistancePositive :
    ∀ lengthUnit, 0 < lengthReadout lengthUnit setup.descentDistance
  gravityPositive :
    ∀ lengthUnit timeUnit,
      0 < accelerationReadout lengthUnit timeUnit
        setup.gravitationalAcceleration
  momentOfInertiaPositive :
    ∀ massUnit lengthUnit,
      0 < momentOfInertiaReadout massUnit lengthUnit
        setup.hoopMomentOfInertia

/-!
Axial moment of inertia of a uniform thin hoop, `I = m R²`.  This is a
general constitutive law for the selected body model, not the requested speed.
-/
structure SatisfiesThinHoopInertiaLaw
    (setup : UnwindingHoopSetup) : Prop where
  axialMomentOfInertia :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit),
      momentOfInertiaReadout massUnit lengthUnit
          setup.hoopMomentOfInertia =
        massReadout massUnit setup.hoopMass *
          (lengthReadout lengthUnit setup.hoopRadius) ^ 2

/-!
For a fixed string that unwinds without sliding, the center speed equals the
rim radius times the angular-speed magnitude, `v = R ω`, at each endpoint.
-/
structure SatisfiesFixedStringNoSlipKinematics
    (setup : UnwindingHoopSetup) : Prop where
  initialNoSlip :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.initialCenterSpeed =
        lengthReadout lengthUnit setup.hoopRadius *
          angularSpeedReadout timeUnit setup.initialAngularSpeed
  finalNoSlip :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.finalCenterSpeed =
        lengthReadout lengthUnit setup.hoopRadius *
          angularSpeedReadout timeUnit setup.finalAngularSpeed

/-!
Mechanical-energy balance between release and the endpoint after descent:

`m g h + 1/2 m v₀² + 1/2 I ω₀² = 1/2 m v² + 1/2 I ω²`.

The ideal string and static hand contact do no net work on the combined hoop
motion in this model.  The law is stated in every coherent system of selected
mechanical base units and contains no solved final-speed value.
-/
structure ConservesMechanicalEnergyDuringDescent
    (setup : UnwindingHoopSetup) : Prop where
  energyBalance :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      massReadout massUnit setup.hoopMass *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration *
            lengthReadout lengthUnit setup.descentDistance +
          (1 / 2 : ℝ) * massReadout massUnit setup.hoopMass *
            (speedReadout lengthUnit timeUnit
              setup.initialCenterSpeed) ^ 2 +
          (1 / 2 : ℝ) *
            momentOfInertiaReadout massUnit lengthUnit
              setup.hoopMomentOfInertia *
            (angularSpeedReadout timeUnit
              setup.initialAngularSpeed) ^ 2 =
        (1 / 2 : ℝ) * massReadout massUnit setup.hoopMass *
            (speedReadout lengthUnit timeUnit
              setup.finalCenterSpeed) ^ 2 +
          (1 / 2 : ℝ) *
            momentOfInertiaReadout massUnit lengthUnit
              setup.hoopMomentOfInertia *
            (angularSpeedReadout timeUnit
              setup.finalAngularSpeed) ^ 2

/-! ## Derived endpoint formula -/

/-!
Combining release from rest, energy conservation, `I = m R²`, and
`v = R ω` makes the equal translational and rotational kinetic-energy terms
sum to `m v²`.  Hence the nonnegative center speed is `sqrt (g h)`.
-/
lemma finalCenterSpeed_eq_sqrt_gravity_mul_descent
    (setup : UnwindingHoopSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalParameters setup)
    (hInertia : SatisfiesThinHoopInertiaLaw setup)
    (hNoSlip : SatisfiesFixedStringNoSlipKinematics setup)
    (hEnergy : ConservesMechanicalEnergyDuringDescent setup) :
    speedInMetersPerSecond setup.finalCenterSpeed =
      Real.sqrt
        (accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters setup.descentDistance) := by
  change
    speedReadout LengthUnit.meters TimeUnit.seconds
        setup.finalCenterSpeed =
      Real.sqrt
        (accelerationReadout LengthUnit.meters TimeUnit.seconds
            setup.gravitationalAcceleration *
          lengthReadout LengthUnit.meters setup.descentDistance)
  have hmass_pos :
      0 < massReadout MassUnit.kilograms setup.hoopMass :=
    hPhysical.hoopMassPositive MassUnit.kilograms
  have hmass_ne :
      massReadout MassUnit.kilograms setup.hoopMass ≠ 0 :=
    ne_of_gt hmass_pos
  have hinertia :=
    hInertia.axialMomentOfInertia
      MassUnit.kilograms LengthUnit.meters
  have hnoSlip :=
    hNoSlip.finalNoSlip LengthUnit.meters TimeUnit.seconds
  have hinitialCenter :=
    hReadouts.initialCenterAtRest LengthUnit.meters TimeUnit.seconds
  have hinitialAngular :=
    hReadouts.initialRotationAtRest TimeUnit.seconds
  have henergy :=
    hEnergy.energyBalance
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  rw [hinitialCenter, hinitialAngular, hinertia, hnoSlip] at henergy
  have hmass_mul :
      massReadout MassUnit.kilograms setup.hoopMass *
          (accelerationReadout LengthUnit.meters TimeUnit.seconds
              setup.gravitationalAcceleration *
            lengthReadout LengthUnit.meters setup.descentDistance) =
        massReadout MassUnit.kilograms setup.hoopMass *
          (lengthReadout LengthUnit.meters setup.hoopRadius *
            angularSpeedReadout TimeUnit.seconds
              setup.finalAngularSpeed) ^ 2 := by
    nlinarith [henergy]
  have hsquared :
      (speedReadout LengthUnit.meters TimeUnit.seconds
          setup.finalCenterSpeed) ^ 2 =
        accelerationReadout LengthUnit.meters TimeUnit.seconds
            setup.gravitationalAcceleration *
          lengthReadout LengthUnit.meters setup.descentDistance := by
    rw [hnoSlip]
    exact (mul_left_cancel₀ hmass_ne hmass_mul).symm
  have hspeed_nonnegative :
      0 ≤ speedReadout LengthUnit.meters TimeUnit.seconds
        setup.finalCenterSpeed := by
    rw [hnoSlip]
    apply mul_nonneg
    · exact le_of_lt
        (hPhysical.hoopRadiusPositive LengthUnit.meters)
    · unfold angularSpeedReadout
      exact NNReal.coe_nonneg _
  calc
    speedReadout LengthUnit.meters TimeUnit.seconds
        setup.finalCenterSpeed =
        |speedReadout LengthUnit.meters TimeUnit.seconds
          setup.finalCenterSpeed| :=
      (abs_of_nonneg hspeed_nonnegative).symm
    _ = Real.sqrt
          ((speedReadout LengthUnit.meters TimeUnit.seconds
            setup.finalCenterSpeed) ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ = Real.sqrt
          (accelerationReadout LengthUnit.meters TimeUnit.seconds
              setup.gravitationalAcceleration *
            lengthReadout LengthUnit.meters setup.descentDistance) := by
      rw [hsquared]

/-! ## Displayed choices and target conclusion -/

/-- Labels of the four speed choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Printed speed beside each answer choice, in meters per second. -/
def displayedSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 96 / 25
  | .B => 271 / 100
  | .C => 39 / 25
  | .D => 321 / 100

/-- Dataset metadata; this declaration is not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- The exact modeled speed rounds to a displayed hundredth-meter-per-second
value. -/
def RoundsToDisplayedHundredth
    (setup : UnwindingHoopSetup) (choice : AnswerChoice) : Prop :=
  |speedInMetersPerSecond setup.finalCenterSpeed -
      displayedSpeedInMetersPerSecond choice| < 1 / 200

/-- The physical speed is strictly closer to one displayed value than to
every other displayed value. -/
def IsUniqueClosestDisplayedSpeed
    (setup : UnwindingHoopSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |speedInMetersPerSecond setup.finalCenterSpeed -
        displayedSpeedInMetersPerSecond choice| <
      |speedInMetersPerSecond setup.finalCenterSpeed -
        displayedSpeedInMetersPerSecond other|

/-!
For `g = 9.8 m/s²` and `h = 0.750 m`, the exact modeled center speed is
`sqrt (147 / 20) m/s`.  It rounds to `2.71 m/s` and is uniquely closest to
choice B.

This formalizes `thm:physics:phyx_mini_0779:target`.
-/
theorem problem_phyx_mini_0779
    (setup : UnwindingHoopSetup)
    (hScenario : MatchesProblemScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hGravity : UsesStandardEarthGravity setup)
    (hPhysical : HasPhysicalParameters setup)
    (hInertia : SatisfiesThinHoopInertiaLaw setup)
    (hNoSlip : SatisfiesFixedStringNoSlipKinematics setup)
    (hEnergy : ConservesMechanicalEnergyDuringDescent setup) :
    speedInMetersPerSecond setup.finalCenterSpeed =
        Real.sqrt (147 / 20) ∧
      RoundsToDisplayedHundredth setup .B ∧
      IsUniqueClosestDisplayedSpeed setup .B := by
  have centimeters_eq_hundred_meters (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have hunit := length.2
      ({UnitChoices.SI with length := LengthUnit.meters} : UnitChoices)
      ({UnitChoices.SI with length := LengthUnit.centimeters} : UnitChoices)
    have hval := congrArg WithDim.val hunit
    norm_num [lengthInCentimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.meters, LengthUnit.centimeters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def] at hval ⊢
    exact_mod_cast hval
  have hdescent :
      lengthInMeters setup.descentDistance = 3 / 4 := by
    have hconversion :=
      centimeters_eq_hundred_meters setup.descentDistance
    rw [hReadouts.descentInCentimeters] at hconversion
    norm_num at hconversion ⊢
    linarith
  have hspeed_formula :=
    finalCenterSpeed_eq_sqrt_gravity_mul_descent
      setup hReadouts hPhysical hInertia hNoSlip hEnergy
  have hspeed :
      speedInMetersPerSecond setup.finalCenterSpeed =
        Real.sqrt (147 / 20) := by
    rw [hspeed_formula, hGravity.gravitationalAccelerationSI, hdescent]
    norm_num
  have hsqrt_nonnegative :
      0 ≤ Real.sqrt (147 / 20 : ℝ) :=
    Real.sqrt_nonneg _
  have hsqrt_sq :
      (Real.sqrt (147 / 20 : ℝ)) ^ 2 = 147 / 20 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_lower :
      (541 / 200 : ℝ) < Real.sqrt (147 / 20) := by
    nlinarith
  have hsqrt_upper :
      Real.sqrt (147 / 20) < (543 / 200 : ℝ) := by
    nlinarith
  have hrounding :
      |Real.sqrt (147 / 20 : ℝ) - 271 / 100| < 1 / 200 := by
    rw [abs_lt]
    constructor <;> nlinarith
  refine ⟨hspeed, ?_, ?_⟩
  · unfold RoundsToDisplayedHundredth
    rw [hspeed]
    exact hrounding
  · unfold IsUniqueClosestDisplayedSpeed
    intro other hother
    cases other with
    | A =>
        simp only [displayedSpeedInMetersPerSecond]
        rw [hspeed]
        calc
          |Real.sqrt (147 / 20) - 271 / 100| < 1 / 200 :=
            hrounding
          _ < |Real.sqrt (147 / 20) - 96 / 25| := by
            rw [abs_of_nonpos]
            · nlinarith
            · nlinarith
    | B =>
        exact (hother rfl).elim
    | C =>
        simp only [displayedSpeedInMetersPerSecond]
        rw [hspeed]
        calc
          |Real.sqrt (147 / 20) - 271 / 100| < 1 / 200 :=
            hrounding
          _ < |Real.sqrt (147 / 20) - 39 / 25| := by
            rw [abs_of_nonneg]
            · nlinarith
            · nlinarith
    | D =>
        simp only [displayedSpeedInMetersPerSecond]
        rw [hspeed]
        calc
          |Real.sqrt (147 / 20) - 271 / 100| < 1 / 200 :=
            hrounding
          _ < |Real.sqrt (147 / 20) - 321 / 100| := by
            rw [abs_of_nonpos]
            · nlinarith
            · nlinarith

end PhyXMiniProblems.ProblemPhyXMini0779
