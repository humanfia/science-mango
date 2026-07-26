import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

/-!
# A center-pivoted bar after one endpoint ball detaches

A thin uniform bar of mass `3.80 kg` and length `80.0 cm` is initially
horizontal.  Identical small balls of mass `2.50 kg` are glued at its two
ends.  A thin horizontal frictionless axle passes through the center of the
bar, perpendicular to it.  The right ball detaches while the left ball
remains glued, and the remaining system swings in a vertical plane.

The quantity requested by the multiple-choice problem is the magnitude of
the angular velocity when the bar is vertical and the remaining ball is
below the axle.  Hence it is represented below as a nonnegative angular
speed.  Radians are dimensionless, so angular speed has dimension inverse
time.  Mass, length, acceleration, moment of inertia, angular speed, and
energy are all unit-independent Physlib quantities; real numbers occur only
in coherent-unit readouts and in the displayed answer data.

Assumption/target split:

* `MatchesCenteredBarReleaseScenario` records the thin uniform bar, centered
  frictionless axle, endpoint point-mass idealization, left/right attachment
  states, and the horizontal-to-vertical geometry.
* `MatchesProblemReadouts` records the bar mass and length, both endpoint
  masses, and release from rest.
* `MatchesSuppliedFigure` records only what is visible in the primary bitmap:
  the bar, two endpoint balls, centered end-on axle, and printed labels.
* `UsesStandardTerrestrialGravity`, `HasPositivePhysicalParameters`,
  `SatisfiesCenteredBarInertiaLaws`, and
  `SatisfiesDetachedBarEnergyLaws` are governing physical assumptions.
* There are no previous-part results.
* The four option values, including `5.70 rad/s`, are source metadata.  The
  exact vertical angular speed, the claim that it rounds near `5.70 rad/s`,
  and the selection of answer B occur only in lemma/theorem conclusions.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0782

open Dimension

/-! ## Dimensionful physical quantities and coherent-unit readouts -/

/-- Gravitational acceleration has dimension length divided by time squared. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Moment of inertia has dimension mass times length squared. -/
def momentOfInertiaDimension : Dimension := M𝓭 * L𝓭 * L𝓭

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative angular-speed magnitude; radians are dimensionless. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative moment of inertia about the fixed axle. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- Mechanical energy with Physlib's energy dimension. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read acceleration in coherent selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read angular speed in inverse units of the selected time unit. -/
def angularSpeedReadout
    (timeUnit : TimeUnit) (speed : AngularSpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- Read moment of inertia in coherent selected mass and length units. -/
def momentOfInertiaReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Read energy in the coherent unit induced by the selected base units. -/
def energyReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (energy : EnergyQuantity) : ℝ :=
  (energy {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- Kilogram-metre-squared readout of a moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  momentOfInertiaReadout MassUnit.kilograms LengthUnit.meters inertia

/-- Radian-per-second readout of angular-speed magnitude. -/
def angularSpeedInRadiansPerSecond (speed : AngularSpeedQuantity) : ℝ :=
  angularSpeedReadout TimeUnit.seconds speed

/-! ## Physical stages, geometry, and primary-figure vocabulary -/

/-- The two ends of the horizontal bar in the primary figure. -/
inductive BarEnd where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- The two instants relevant to the energy balance. -/
inductive SwingStage where
  | horizontalImmediatelyAfterDetachment
  | verticalWithRemainingBallBelowAxle
  deriving DecidableEq, Fintype, Repr

/-- Orientation of the bar in the vertical plane of its swing. -/
inductive BarOrientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Location of the axle along the bar. -/
inductive AxleLocation where
  | throughBarCenter
  | other
  deriving DecidableEq, Repr

/-- Idealized friction model for the axle. -/
inductive AxleFrictionModel where
  | frictionless
  | other
  deriving DecidableEq, Repr

/-- Mass-distribution model for the bar. -/
inductive BarMassModel where
  | thinUniform
  | other
  deriving DecidableEq, Repr

/-- Geometric idealization for either very small endpoint ball. -/
inductive EndpointBallModel where
  | pointMassAtBarEnd
  | other
  deriving DecidableEq, Repr

/-- Attachment state of an endpoint ball immediately after release. -/
inductive PostReleaseAttachment where
  | remainsGlued
  | detachedAndFalling
  deriving DecidableEq, Repr

/-- Objects literally visible in the supplied bitmap. -/
inductive FigureObject where
  | bar
  | axleEndOn
  | leftBall
  | rightBall
  deriving DecidableEq, Fintype, Repr

/-- Presentation-level evidence transcribed from the primary bitmap. -/
structure SuppliedBarAxleFigure where
  showsObject : FigureObject → Bool
  ballShownAtBarEnd : BarEnd → Bool
  printedBallMassKilograms : BarEnd → ℝ
  axleMarkerShownAtBarCenter : Bool
  printedBarLabel : String
  printedAxleLabel : String

/-! ## Independent setup data -/

/--
The independent physical data for the bar-plus-one-ball system after the
right ball detaches.  Energy and inertia fields are not defined from the
answer; the governing-law predicates below relate them to the setup.
-/
structure CenterAxleBarSetup where
  barMass : MassQuantity
  barLength : LengthQuantity
  endpointBallMass : BarEnd → MassQuantity
  gravitationalAcceleration : AccelerationQuantity
  angularSpeed : SwingStage → AngularSpeedQuantity
  barMomentOfInertiaAboutAxle : MomentOfInertiaQuantity
  remainingBallMomentOfInertiaAboutAxle : MomentOfInertiaQuantity
  totalMomentOfInertiaAboutAxle : MomentOfInertiaQuantity
  rotationalKineticEnergy : SwingStage → EnergyQuantity
  gravitationalPotentialEnergy : SwingStage → EnergyQuantity
  barMassModel : BarMassModel
  endpointBallModel : BarEnd → EndpointBallModel
  axleLocation : AxleLocation
  axleFrictionModel : AxleFrictionModel
  axleIsHorizontal : Bool
  axleIsPerpendicularToBar : Bool
  postReleaseAttachment : BarEnd → PostReleaseAttachment
  barOrientation : SwingStage → BarOrientation
  figure : SuppliedBarAxleFigure

/-! ## Scenario, readout, and figure assumptions -/

/-- Qualitative mechanics and geometry stated in the problem. -/
structure MatchesCenteredBarReleaseScenario
    (setup : CenterAxleBarSetup) : Prop where
  barIsThinAndUniform : setup.barMassModel = .thinUniform
  ballsAreEndpointPointMasses :
    ∀ barEnd, setup.endpointBallModel barEnd = .pointMassAtBarEnd
  axlePassesThroughCenter : setup.axleLocation = .throughBarCenter
  axleIsFrictionless : setup.axleFrictionModel = .frictionless
  axleHorizontal : setup.axleIsHorizontal = true
  axlePerpendicularToBar : setup.axleIsPerpendicularToBar = true
  leftBallRemainsGlued :
    setup.postReleaseAttachment .left = .remainsGlued
  rightBallDetaches :
    setup.postReleaseAttachment .right = .detachedAndFalling
  initiallyHorizontal :
    setup.barOrientation .horizontalImmediatelyAfterDetachment = .horizontal
  verticalAtRequestedInstant :
    setup.barOrientation .verticalWithRemainingBallBelowAxle = .vertical

/-- Numerical data stated in the text, including release from rest. -/
structure MatchesProblemReadouts (setup : CenterAxleBarSetup) : Prop where
  barMassKilograms : massInKilograms setup.barMass = 19 / 5
  barLengthMeters : lengthInMeters setup.barLength = 4 / 5
  eachBallMassKilograms :
    ∀ barEnd, massInKilograms (setup.endpointBallMass barEnd) = 5 / 2
  releasedFromRest :
    angularSpeedInRadiansPerSecond
      (setup.angularSpeed .horizontalImmediatelyAfterDetachment) = 0

/-- Standard terrestrial gravity used to evaluate the multiple-choice data. -/
structure UsesStandardTerrestrialGravity
    (setup : CenterAxleBarSetup) : Prop where
  gravitationalAccelerationSI :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5

/-- Literal information visible in the supplied raster. -/
structure MatchesSuppliedFigure (setup : CenterAxleBarSetup) : Prop where
  barShown : setup.figure.showsObject .bar = true
  axleShownEndOn : setup.figure.showsObject .axleEndOn = true
  leftBallShown : setup.figure.showsObject .leftBall = true
  rightBallShown : setup.figure.showsObject .rightBall = true
  eachBallShownAtAnEnd :
    ∀ barEnd, setup.figure.ballShownAtBarEnd barEnd = true
  axleShownAtCenter : setup.figure.axleMarkerShownAtBarCenter = true
  eachPrintedBallMass :
    ∀ barEnd, setup.figure.printedBallMassKilograms barEnd = 5 / 2
  printedMassMatchesPhysicalBall :
    ∀ barEnd,
      setup.figure.printedBallMassKilograms barEnd =
        massInKilograms (setup.endpointBallMass barEnd)
  barLabel : setup.figure.printedBarLabel = "Bar"
  axleLabel : setup.figure.printedAxleLabel = "Axle (seen end-on)"

/-- Positivity conditions for the nondegenerate physical system. -/
structure HasPositivePhysicalParameters
    (setup : CenterAxleBarSetup) : Prop where
  barMassPositive :
    ∀ massUnit, 0 < massReadout massUnit setup.barMass
  endpointBallMassPositive :
    ∀ massUnit barEnd,
      0 < massReadout massUnit (setup.endpointBallMass barEnd)
  barLengthPositive :
    ∀ lengthUnit, 0 < lengthReadout lengthUnit setup.barLength
  gravityPositive :
    ∀ lengthUnit timeUnit,
      0 < accelerationReadout lengthUnit timeUnit
        setup.gravitationalAcceleration
  totalInertiaPositive :
    ∀ massUnit lengthUnit,
      0 < momentOfInertiaReadout massUnit lengthUnit
        setup.totalMomentOfInertiaAboutAxle

/-! ## Governing mechanics -/

/-!
For a thin uniform bar pivoted through its center,
`I_bar = M L² / 12`.  The remaining very small ball is a point mass a
distance `L/2` from the axle, and the total inertia is the sum of the two.
-/
structure SatisfiesCenteredBarInertiaLaws
    (setup : CenterAxleBarSetup) : Prop where
  uniformBarInertia :
    ∀ massUnit lengthUnit,
      momentOfInertiaReadout massUnit lengthUnit
          setup.barMomentOfInertiaAboutAxle =
        massReadout massUnit setup.barMass *
          (lengthReadout lengthUnit setup.barLength) ^ 2 / 12
  remainingEndpointBallInertia :
    ∀ massUnit lengthUnit,
      momentOfInertiaReadout massUnit lengthUnit
          setup.remainingBallMomentOfInertiaAboutAxle =
        massReadout massUnit (setup.endpointBallMass .left) *
          (lengthReadout lengthUnit setup.barLength / 2) ^ 2
  totalInertiaIsSum :
    ∀ massUnit lengthUnit,
      momentOfInertiaReadout massUnit lengthUnit
          setup.totalMomentOfInertiaAboutAxle =
        momentOfInertiaReadout massUnit lengthUnit
            setup.barMomentOfInertiaAboutAxle +
          momentOfInertiaReadout massUnit lengthUnit
            setup.remainingBallMomentOfInertiaAboutAxle

/-!
Rotational kinetic energy is `I ω² / 2`.  Because the bar's center of mass
is at the axle, only the remaining endpoint ball loses gravitational
potential energy, by falling through the distance `L/2`.  The frictionless
axle implies conservation of mechanical energy between the two stages.
-/
structure SatisfiesDetachedBarEnergyLaws
    (setup : CenterAxleBarSetup) : Prop where
  rotationalKineticEnergyFormula :
    ∀ massUnit lengthUnit timeUnit stage,
      energyReadout massUnit lengthUnit timeUnit
          (setup.rotationalKineticEnergy stage) =
        (1 / 2 : ℝ) *
          momentOfInertiaReadout massUnit lengthUnit
            setup.totalMomentOfInertiaAboutAxle *
          (angularSpeedReadout timeUnit (setup.angularSpeed stage)) ^ 2
  remainingBallPotentialEnergyDrop :
    ∀ massUnit lengthUnit timeUnit,
      energyReadout massUnit lengthUnit timeUnit
          (setup.gravitationalPotentialEnergy
            .horizontalImmediatelyAfterDetachment) -
        energyReadout massUnit lengthUnit timeUnit
          (setup.gravitationalPotentialEnergy
            .verticalWithRemainingBallBelowAxle) =
        massReadout massUnit (setup.endpointBallMass .left) *
          accelerationReadout lengthUnit timeUnit
            setup.gravitationalAcceleration *
          (lengthReadout lengthUnit setup.barLength / 2)
  mechanicalEnergyConserved :
    ∀ massUnit lengthUnit timeUnit,
      energyReadout massUnit lengthUnit timeUnit
          (setup.rotationalKineticEnergy
            .horizontalImmediatelyAfterDetachment) +
        energyReadout massUnit lengthUnit timeUnit
          (setup.gravitationalPotentialEnergy
            .horizontalImmediatelyAfterDetachment) =
        energyReadout massUnit lengthUnit timeUnit
          (setup.rotationalKineticEnergy
            .verticalWithRemainingBallBelowAxle) +
        energyReadout massUnit lengthUnit timeUnit
          (setup.gravitationalPotentialEnergy
            .verticalWithRemainingBallBelowAxle)

/-! ## Displayed multiple-choice data -/

/-- Answer labels in the order shown in the exercise. -/
inductive AngularSpeedAnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The four displayed angular-speed values, in radians per second. -/
def displayedAngularSpeedRadiansPerSecond :
    AngularSpeedAnswerChoice → ℝ
  | .A => 23 / 5
  | .B => 57 / 10
  | .C => 31 / 5
  | .D => 31 / 10

/-- A displayed answer choice is at least as close as every other choice. -/
def IsClosestAngularSpeedChoice
    (exactSpeedRadiansPerSecond : ℝ)
    (choice : AngularSpeedAnswerChoice) : Prop :=
  ∀ other : AngularSpeedAnswerChoice,
    |exactSpeedRadiansPerSecond -
        displayedAngularSpeedRadiansPerSecond choice| ≤
      |exactSpeedRadiansPerSecond -
        displayedAngularSpeedRadiansPerSecond other|

/-- The selected displayed answer is the unique closest one. -/
def IsUniqueClosestAngularSpeedChoice
    (exactSpeedRadiansPerSecond : ℝ)
    (choice : AngularSpeedAnswerChoice) : Prop :=
  IsClosestAngularSpeedChoice exactSpeedRadiansPerSecond choice ∧
    ∀ other : AngularSpeedAnswerChoice,
      IsClosestAngularSpeedChoice exactSpeedRadiansPerSecond other →
        other = choice

/-!
The standard inertia and energy laws give

`ω² = (m g L) / (M L² / 12 + m (L/2)²) = 3675/113`.

This is a derived conclusion, not a premise.
-/
lemma vertical_angular_speed_squared
    (setup : CenterAxleBarSetup)
    (hScenario : MatchesCenteredBarReleaseScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGravity : UsesStandardTerrestrialGravity setup)
    (hPositive : HasPositivePhysicalParameters setup)
    (hInertia : SatisfiesCenteredBarInertiaLaws setup)
    (hEnergy : SatisfiesDetachedBarEnergyLaws setup) :
    (angularSpeedInRadiansPerSecond
      (setup.angularSpeed .verticalWithRemainingBallBelowAxle)) ^ 2 =
        (3675 : ℝ) / 113 := by
  have hBarMass :
      massReadout MassUnit.kilograms setup.barMass = (19 : ℝ) / 5 := by
    simpa only [massInKilograms] using hReadouts.barMassKilograms
  have hBarLength :
      lengthReadout LengthUnit.meters setup.barLength = (4 : ℝ) / 5 := by
    simpa only [lengthInMeters] using hReadouts.barLengthMeters
  have hBallMass :
      massReadout MassUnit.kilograms (setup.endpointBallMass .left) =
        (5 : ℝ) / 2 := by
    simpa only [massInKilograms] using hReadouts.eachBallMassKilograms .left
  have hGravitySI :
      accelerationReadout LengthUnit.meters TimeUnit.seconds
          setup.gravitationalAcceleration =
        (49 : ℝ) / 5 := by
    simpa only [accelerationInMetersPerSecondSquared] using
      hGravity.gravitationalAccelerationSI
  have hInitialSpeed :
      angularSpeedReadout TimeUnit.seconds
          (setup.angularSpeed .horizontalImmediatelyAfterDetachment) = 0 := by
    simpa only [angularSpeedInRadiansPerSecond] using hReadouts.releasedFromRest
  have hBarInertia :=
    hInertia.uniformBarInertia MassUnit.kilograms LengthUnit.meters
  have hBallInertia :=
    hInertia.remainingEndpointBallInertia
      MassUnit.kilograms LengthUnit.meters
  have hTotalInertia :=
    hInertia.totalInertiaIsSum MassUnit.kilograms LengthUnit.meters
  have hInitialKinetic :=
    hEnergy.rotationalKineticEnergyFormula
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
      SwingStage.horizontalImmediatelyAfterDetachment
  have hFinalKinetic :=
    hEnergy.rotationalKineticEnergyFormula
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
      SwingStage.verticalWithRemainingBallBelowAxle
  have hPotentialDrop :=
    hEnergy.remainingBallPotentialEnergyDrop
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hEnergyConservation :=
    hEnergy.mechanicalEnergyConserved
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  norm_num [hBarMass, hBarLength] at hBarInertia
  norm_num [hBallMass, hBarLength] at hBallInertia
  norm_num [hBarInertia, hBallInertia] at hTotalInertia
  norm_num [hInitialSpeed] at hInitialKinetic
  norm_num [hBallMass, hGravitySI, hBarLength] at hPotentialDrop
  rw [hTotalInertia] at hFinalKinetic
  change
    (angularSpeedReadout TimeUnit.seconds
      (setup.angularSpeed .verticalWithRemainingBallBelowAxle)) ^ 2 =
        (3675 : ℝ) / 113
  nlinarith

/-- Nonnegativity of angular speed selects the positive square root. -/
lemma vertical_angular_speed_exact
    (setup : CenterAxleBarSetup)
    (hScenario : MatchesCenteredBarReleaseScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGravity : UsesStandardTerrestrialGravity setup)
    (hPositive : HasPositivePhysicalParameters setup)
    (hInertia : SatisfiesCenteredBarInertiaLaws setup)
    (hEnergy : SatisfiesDetachedBarEnergyLaws setup) :
    angularSpeedInRadiansPerSecond
        (setup.angularSpeed .verticalWithRemainingBallBelowAxle) =
      Real.sqrt ((3675 : ℝ) / 113) := by
  have hNonnegative :
      0 ≤ angularSpeedInRadiansPerSecond
        (setup.angularSpeed .verticalWithRemainingBallBelowAxle) := by
    unfold angularSpeedInRadiansPerSecond angularSpeedReadout
    exact NNReal.coe_nonneg _
  have hSquared :=
    vertical_angular_speed_squared
      setup hScenario hReadouts hGravity hPositive hInertia hEnergy
  calc
    angularSpeedInRadiansPerSecond
        (setup.angularSpeed .verticalWithRemainingBallBelowAxle) =
        Real.sqrt
          ((angularSpeedInRadiansPerSecond
            (setup.angularSpeed .verticalWithRemainingBallBelowAxle)) ^ 2) :=
      (Real.sqrt_sq hNonnegative).symm
    _ = Real.sqrt ((3675 : ℝ) / 113) := congrArg Real.sqrt hSquared

/-!
The exact physical value is `sqrt (3675/113) rad/s`, within `0.01 rad/s` of
`5.70 rad/s`; B is the unique closest displayed option.

This formalizes `thm:physics:phyx_mini_0782:target`.
-/
theorem problem_phyx_mini_0782
    (setup : CenterAxleBarSetup)
    (hScenario : MatchesCenteredBarReleaseScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGravity : UsesStandardTerrestrialGravity setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hPositive : HasPositivePhysicalParameters setup)
    (hInertia : SatisfiesCenteredBarInertiaLaws setup)
    (hEnergy : SatisfiesDetachedBarEnergyLaws setup) :
    angularSpeedInRadiansPerSecond
        (setup.angularSpeed .verticalWithRemainingBallBelowAxle) =
        Real.sqrt ((3675 : ℝ) / 113) ∧
      |angularSpeedInRadiansPerSecond
          (setup.angularSpeed .verticalWithRemainingBallBelowAxle) -
          57 / 10| < 1 / 100 ∧
      IsUniqueClosestAngularSpeedChoice
        (angularSpeedInRadiansPerSecond
          (setup.angularSpeed .verticalWithRemainingBallBelowAxle)) .B := by
  have hExact :=
    vertical_angular_speed_exact
      setup hScenario hReadouts hGravity hPositive hInertia hEnergy
  have hLower :
      (57 / 10 : ℝ) < Real.sqrt ((3675 : ℝ) / 113) := by
    apply Real.lt_sqrt_of_sq_lt
    norm_num
  have hUpper :
      Real.sqrt ((3675 : ℝ) / 113) < (571 / 100 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 571 / 100)]
    norm_num
  refine ⟨hExact, ?_, ?_⟩
  · rw [hExact, abs_lt]
    constructor <;> linarith
  · rw [hExact]
    unfold IsUniqueClosestAngularSpeedChoice
    constructor
    · unfold IsClosestAngularSpeedChoice
      intro other
      cases other with
      | A =>
          change
            |Real.sqrt ((3675 : ℝ) / 113) - 57 / 10| ≤
              |Real.sqrt ((3675 : ℝ) / 113) - 23 / 5|
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          linarith
      | B => rfl
      | C =>
          change
            |Real.sqrt ((3675 : ℝ) / 113) - 57 / 10| ≤
              |Real.sqrt ((3675 : ℝ) / 113) - 31 / 5|
          rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
          linarith
      | D =>
          change
            |Real.sqrt ((3675 : ℝ) / 113) - 57 / 10| ≤
              |Real.sqrt ((3675 : ℝ) / 113) - 31 / 10|
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          linarith
    · intro other hOther
      unfold IsClosestAngularSpeedChoice at hOther
      cases other with
      | A =>
          have hAgainstB := hOther AngularSpeedAnswerChoice.B
          change
            |Real.sqrt ((3675 : ℝ) / 113) - 23 / 5| ≤
              |Real.sqrt ((3675 : ℝ) / 113) - 57 / 10| at hAgainstB
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
            at hAgainstB
          exfalso
          linarith
      | B => rfl
      | C =>
          have hAgainstB := hOther AngularSpeedAnswerChoice.B
          change
            |Real.sqrt ((3675 : ℝ) / 113) - 31 / 5| ≤
              |Real.sqrt ((3675 : ℝ) / 113) - 57 / 10| at hAgainstB
          rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
            at hAgainstB
          exfalso
          linarith
      | D =>
          have hAgainstB := hOther AngularSpeedAnswerChoice.B
          change
            |Real.sqrt ((3675 : ℝ) / 113) - 31 / 10| ≤
              |Real.sqrt ((3675 : ℝ) / 113) - 57 / 10| at hAgainstB
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
            at hAgainstB
          exfalso
          linarith

end PhyXMiniProblems.ProblemPhyXMini0782
