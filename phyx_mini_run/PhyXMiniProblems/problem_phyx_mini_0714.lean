import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0714

open Dimension

/-!
# Escape speed from the surface of a nonrotating Earth

A `1000 kg` rocket is launched radially outward from the Earth's surface and
then coasts without thrust.  The primary figure compares its initial state
`r₁ = Rₑ`, with speed `v₁`, to the marginal-escape state `r₂ = ∞`, `v₂ = 0`.

Masses, lengths, speeds, angular speeds, energies, and the gravitational
constant are represented by unit-independent Physlib quantities.  Real
numbers occur only as coherent SI readouts and displayed multiple-choice
values.

Assumption/target split:

* `MatchesPrimaryFigure` records the literal before/after labels, the surface
  and infinity locations, the outward arrow, and the zero final-speed readout;
* `MatchesProblemStatement` records the `1000 kg` mass, radial launch,
  nonrotating Earth, and unpowered coast;
* `MatchesStandardEarthCalibration` records standard SI values of `G`, the
  Earth's mass, and the Earth's mean radius;
* `SatisfiesNewtonianEscapeEnergyLaws` records kinetic energy, Newtonian
  gravitational potential energy, its zero limit at infinity, and conservation
  of mechanical energy; and
* only `problem_phyx_mini_0714` concludes the escape-speed formula and that the
  displayed `11200 m/s` value (choice C) is closest.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- The physical dimension `L³ M⁻¹ T⁻²` of Newton's gravitational constant. -/
def gravitationalConstantDimension : Dimension :=
  L𝓭 * L𝓭 * L𝓭 * M𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical radial length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative angular-speed magnitude; radians are dimensionless. -/
abbrev AngularSpeedMagnitudeQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A unit-independent value of Newton's gravitational constant. -/
abbrev GravitationalConstantQuantity : Type :=
  Dimensionful (WithDim gravitationalConstantDimension NNReal)

/-- A signed, unit-independent physical energy. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Metre-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Radian-per-second readout of an angular-speed magnitude. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedMagnitudeQuantity) : ℝ :=
  ((angularSpeed UnitChoices.SI).val : ℝ)

/-- SI readout of `G`, in `m³ kg⁻¹ s⁻²`. -/
def gravitationalConstantInSI
    (constant : GravitationalConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-- Joule readout of a signed physical energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Bodies, radial states, and primary-figure vocabulary -/

/-- The spherical Earth data relevant to the escape calculation. -/
structure EarthModel where
  mass : MassQuantity
  radius : LengthQuantity
  angularSpeedMagnitude : AngularSpeedMagnitudeQuantity

/-- The rocket's independent mass and before/after speed observables. -/
structure RocketModel where
  mass : MassQuantity
  launchSpeed : SpeedQuantity
  asymptoticSpeed : SpeedQuantity

/-- A radial location is either at a finite physical radius or at infinity. -/
inductive RadialLocation where
  | finite (radius : LengthQuantity)
  | atInfinity

/-- Radial direction of the rocket's initial velocity. -/
inductive RadialDirection where
  | inward
  | outward
  deriving DecidableEq, Repr

/-- Propulsion state after the initial firing. -/
inductive PostLaunchPropulsion where
  | coasting
  | powered
  deriving DecidableEq, Repr

/-- The two panels explicitly named in the supplied image. -/
inductive EscapePhase where
  | before
  | after
  deriving DecidableEq, Fintype, Repr

/-- Radius labels transcribed from the two panels. -/
inductive FigureRadiusLabel where
  | earthRadiusRₑ
  | infinity
  deriving DecidableEq, Repr

/-- Speed labels transcribed from the two panels. -/
inductive FigureSpeedLabel where
  | launchSpeedV₁
  | zeroFinalSpeedV₂
  deriving DecidableEq, Repr

/-- Literal qualitative and symbolic content shown in image `714.png`. -/
structure EscapeFigure where
  earthShown : Bool
  rocketShown : EscapePhase → Bool
  radiusLabel : EscapePhase → FigureRadiusLabel
  speedLabel : EscapePhase → FigureSpeedLabel
  outwardVelocityArrowShown : Bool
  thrustAfterLaunchShown : Bool

/-!
The independent physical observables for the marginal escape experiment.
None of the speed fields is defined from an answer choice or from the desired
escape-speed formula.
-/
structure SurfaceEscapeSetup where
  earth : EarthModel
  rocket : RocketModel
  gravitationalConstant : GravitationalConstantQuantity
  initialRadialLocation : RadialLocation
  asymptoticRadialLocation : RadialLocation
  initialDirection : RadialDirection
  postLaunchPropulsion : PostLaunchPropulsion
  surfaceKineticEnergy : EnergyQuantity
  surfaceGravitationalPotentialEnergy : EnergyQuantity
  asymptoticKineticEnergy : EnergyQuantity
  asymptoticGravitationalPotentialEnergy : EnergyQuantity
  figure : EscapeFigure

/-! ## Figure/data readouts and governing physical laws -/

/-!
Primary-image transcription.  The final zero-speed equality is a direct
figure readout for the marginal-escape state, not the requested launch speed.
-/
structure MatchesPrimaryFigure (setup : SurfaceEscapeSetup) : Prop where
  earthIsShown : setup.figure.earthShown = true
  rocketIsShownInBothPanels :
    ∀ phase, setup.figure.rocketShown phase = true
  beforeRadiusLabelIsEarthRadius :
    setup.figure.radiusLabel .before = .earthRadiusRₑ
  afterRadiusLabelIsInfinity :
    setup.figure.radiusLabel .after = .infinity
  beforeSpeedLabelIsV₁ :
    setup.figure.speedLabel .before = .launchSpeedV₁
  afterSpeedLabelIsZeroV₂ :
    setup.figure.speedLabel .after = .zeroFinalSpeedV₂
  startsAtEarthSurface :
    setup.initialRadialLocation = .finite setup.earth.radius
  endsAtInfinity :
    setup.asymptoticRadialLocation = .atInfinity
  finalSpeedIsZero :
    speedInMetersPerSecond setup.rocket.asymptoticSpeed = 0
  outwardArrowIsShown :
    setup.figure.outwardVelocityArrowShown = true
  noThrustIsShownAfterLaunch :
    setup.figure.thrustAfterLaunchShown = false

/-- Numerical and qualitative facts stated in the problem prose. -/
structure MatchesProblemStatement (setup : SurfaceEscapeSetup) : Prop where
  rocketMassIsOneThousandKilograms :
    massInKilograms setup.rocket.mass = 1000
  launchIsRadiallyOutward :
    setup.initialDirection = .outward
  earthIsNonrotating :
    angularSpeedInRadiansPerSecond setup.earth.angularSpeedMagnitude = 0
  rocketCoastsAfterLaunch :
    setup.postLaunchPropulsion = .coasting

/-!
Standard reference values needed to evaluate the recorded numerical choice.
These data do not mention the launch speed or any answer choice.
-/
structure MatchesStandardEarthCalibration
    (setup : SurfaceEscapeSetup) : Prop where
  gravitationalConstantSI :
    gravitationalConstantInSI setup.gravitationalConstant = 6.67430e-11
  earthMassKilograms :
    massInKilograms setup.earth.mass = 5.9722e24
  earthMeanRadiusMeters :
    lengthInMeters setup.earth.radius = 6.371e6

/-- Positivity conditions for the physical Newtonian branch. -/
structure HasPhysicalEscapeParameters
    (setup : SurfaceEscapeSetup) : Prop where
  gravitationalConstantPositive :
    0 < gravitationalConstantInSI setup.gravitationalConstant
  earthMassPositive :
    0 < massInKilograms setup.earth.mass
  earthRadiusPositive :
    0 < lengthInMeters setup.earth.radius
  rocketMassPositive :
    0 < massInKilograms setup.rocket.mass
  launchSpeedPositive :
    0 < speedInMetersPerSecond setup.rocket.launchSpeed

/-!
Newtonian work-energy model for unpowered radial flight.  The kinetic-energy
relations are `K = mv²/2`; the finite-radius potential is `U = -GMm/r`;
the potential tends to zero at infinity; and total mechanical energy is
conserved while coasting.  No field states `v₁ = sqrt (2GM/R)` or selects a
displayed answer.
-/
structure SatisfiesNewtonianEscapeEnergyLaws
    (setup : SurfaceEscapeSetup) : Prop where
  surfaceKineticEnergyLaw :
    energyInJoules setup.surfaceKineticEnergy =
      (1 / 2 : ℝ) * massInKilograms setup.rocket.mass *
        speedInMetersPerSecond setup.rocket.launchSpeed ^ 2
  surfacePotentialEnergyLaw :
    setup.initialRadialLocation = .finite setup.earth.radius →
      energyInJoules setup.surfaceGravitationalPotentialEnergy =
        -(gravitationalConstantInSI setup.gravitationalConstant *
            massInKilograms setup.earth.mass *
            massInKilograms setup.rocket.mass /
            lengthInMeters setup.earth.radius)
  asymptoticKineticEnergyLaw :
    energyInJoules setup.asymptoticKineticEnergy =
      (1 / 2 : ℝ) * massInKilograms setup.rocket.mass *
        speedInMetersPerSecond setup.rocket.asymptoticSpeed ^ 2
  potentialEnergyVanishesAtInfinity :
    setup.asymptoticRadialLocation = .atInfinity →
      energyInJoules setup.asymptoticGravitationalPotentialEnergy = 0
  mechanicalEnergyIsConservedWhileCoasting :
    setup.postLaunchPropulsion = .coasting →
      energyInJoules setup.surfaceKineticEnergy +
          energyInJoules setup.surfaceGravitationalPotentialEnergy =
        energyInJoules setup.asymptoticKineticEnergy +
          energyInJoules setup.asymptoticGravitationalPotentialEnergy

/-! ## Displayed answers and formalization target -/

/-- Labels of the four speed choices displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metre-per-second value printed beside each answer label. -/
def AnswerChoice.speedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 12200
  | .B => 13200
  | .C => 11200
  | .D => 14200

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
A choice is closest when its displayed speed has no greater absolute error
than any other displayed speed.  This avoids falsely identifying the rounded
`11200 m/s` choice with the exact speed from the calibrated constants.
-/
def IsClosestAnswerChoice (speed : ℝ) (selected : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |speed - selected.speedInMetersPerSecond| ≤
      |speed - other.speedInMetersPerSecond|

/-!
Conservation between `r₁ = Rₑ` and the marginal state `r₂ = ∞`, `v₂ = 0`
gives the exact launch speed `sqrt (2GMₑ/Rₑ)`.  For the calibrated terrestrial
values this is approximately `11186 m/s`, making `11200 m/s` (choice C) the
closest displayed answer.

Blueprint label: `thm:physics:phyx_mini_0714:target`.
-/
theorem problem_phyx_mini_0714
    (setup : SurfaceEscapeSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hProblem : MatchesProblemStatement setup)
    (hCalibration : MatchesStandardEarthCalibration setup)
    (hPhysical : HasPhysicalEscapeParameters setup)
    (hEnergy : SatisfiesNewtonianEscapeEnergyLaws setup) :
    speedInMetersPerSecond setup.rocket.launchSpeed =
        Real.sqrt
          (2 * gravitationalConstantInSI setup.gravitationalConstant *
            massInKilograms setup.earth.mass /
            lengthInMeters setup.earth.radius) ∧
      IsClosestAnswerChoice
        (speedInMetersPerSecond setup.rocket.launchSpeed)
        recordedAnswerChoice := by
  have hSurfacePotential :=
    hEnergy.surfacePotentialEnergyLaw hFigure.startsAtEarthSurface
  have hAsymptoticKineticZero :
      energyInJoules setup.asymptoticKineticEnergy = 0 := by
    simpa [hFigure.finalSpeedIsZero] using hEnergy.asymptoticKineticEnergyLaw
  have hAsymptoticPotentialZero :
      energyInJoules setup.asymptoticGravitationalPotentialEnergy = 0 :=
    hEnergy.potentialEnergyVanishesAtInfinity hFigure.endsAtInfinity
  have hConservation :=
    hEnergy.mechanicalEnergyIsConservedWhileCoasting
      hProblem.rocketCoastsAfterLaunch
  rw [hEnergy.surfaceKineticEnergyLaw, hSurfacePotential,
    hAsymptoticKineticZero, hAsymptoticPotentialZero] at hConservation
  have hSpeedSq :
      speedInMetersPerSecond setup.rocket.launchSpeed ^ 2 =
        2 * gravitationalConstantInSI setup.gravitationalConstant *
          massInKilograms setup.earth.mass /
          lengthInMeters setup.earth.radius := by
    rw [hProblem.rocketMassIsOneThousandKilograms] at hConservation
    have hRadiusNe :
        lengthInMeters setup.earth.radius ≠ 0 :=
      ne_of_gt hPhysical.earthRadiusPositive
    field_simp [hRadiusNe] at hConservation ⊢
    nlinarith [hConservation]
  have hRadicandNonnegative :
      0 ≤
        2 * gravitationalConstantInSI setup.gravitationalConstant *
          massInKilograms setup.earth.mass /
          lengthInMeters setup.earth.radius := by
    exact
      div_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (le_of_lt hPhysical.gravitationalConstantPositive))
          (le_of_lt hPhysical.earthMassPositive))
        (le_of_lt hPhysical.earthRadiusPositive)
  have hLaunchSpeed :
      speedInMetersPerSecond setup.rocket.launchSpeed =
        Real.sqrt
          (2 * gravitationalConstantInSI setup.gravitationalConstant *
            massInKilograms setup.earth.mass /
            lengthInMeters setup.earth.radius) := by
    nlinarith [Real.sq_sqrt hRadicandNonnegative,
      Real.sqrt_nonneg
        (2 * gravitationalConstantInSI setup.gravitationalConstant *
          massInKilograms setup.earth.mass /
          lengthInMeters setup.earth.radius),
      hPhysical.launchSpeedPositive]
  constructor
  · exact hLaunchSpeed
  · rw [hLaunchSpeed]
    unfold IsClosestAnswerChoice recordedAnswerChoice
    intro other
    have hSqrtNonnegative :
        0 ≤
          Real.sqrt
            (2 * gravitationalConstantInSI setup.gravitationalConstant *
              massInKilograms setup.earth.mass /
              lengthInMeters setup.earth.radius) :=
      Real.sqrt_nonneg _
    have hSqrtLe :
        Real.sqrt
            (2 * gravitationalConstantInSI setup.gravitationalConstant *
              massInKilograms setup.earth.mass /
              lengthInMeters setup.earth.radius) ≤ 11200 := by
      rw [Real.sqrt_le_iff]
      constructor
      · norm_num
      · rw [hCalibration.gravitationalConstantSI,
          hCalibration.earthMassKilograms,
          hCalibration.earthMeanRadiusMeters]
        norm_num
    have hOtherSpeed :
        (11200 : ℝ) ≤ other.speedInMetersPerSecond := by
      cases other <;> norm_num [AnswerChoice.speedInMetersPerSecond]
    simp only [AnswerChoice.speedInMetersPerSecond] at hOtherSpeed ⊢
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

end PhyXMiniProblems.ProblemPhyXMini0714
