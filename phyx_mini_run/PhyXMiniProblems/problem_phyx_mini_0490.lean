import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0490

open Dimension

/-!
# Temperature rise of a squash ball after one bounce

A soft rubber squash ball reaches a wall at `22 m/s` and rebounds at
`12 m/s`. The translational kinetic energy lost during the impact is assumed
to become sensible heat in the ball. Rubber's rounded mass-specific heat
capacity is `1200 J/(kg K)`.

Mass, speed, energy, specific heat capacity, and absolute temperature remain
physical quantities. Real numbers occur only as calibrated unit readouts,
affine Celsius coordinates, and displayed multiple-choice values. In
particular, the ball's final temperature is an independent observable and is
not defined from the recorded answer.
-/

/-! ## Physical quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-!
The dimension of mass-specific heat capacity,
`energy / (mass * temperature) = L² T⁻² Θ⁻¹`.
-/
def specificHeatCapacityDimension : Dimension :=
  L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹

/-- A nonnegative, unit-independent mass-specific heat capacity. -/
abbrev SpecificHeatCapacityQuantity : Type :=
  Dimensionful (WithDim specificHeatCapacityDimension NNReal)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.kilograms}).val : ℝ)

/-- Metre-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Joule readout of a signed physical energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- SI readout of mass-specific heat capacity in joules per kilogram-kelvin. -/
def specificHeatInJoulesPerKilogramKelvin
    (capacity : SpecificHeatCapacityQuantity) : ℝ :=
  ((capacity UnitChoices.SI).val : ℝ)

/-!
An affine Celsius coordinate attached to a Physlib absolute temperature.
Temperature differences have the same numerical size in Celsius and kelvin.
-/
structure CelsiusTemperatureReading where
  absoluteTemperature : Temperature
  degreesCelsius : ℝ
  kelvinCalibration :
    absoluteTemperature.toReal = degreesCelsius + (5463 / 20 : ℝ)

/-! ## Bounce states, physical roles, and primary-image vocabulary -/

/-- The instants immediately before and immediately after wall contact. -/
inductive BounceState where
  | incoming
  | outgoing
  deriving DecidableEq, Fintype, Repr

/-- Direction of the ball's motion relative to the court wall. -/
inductive WallRelativeDirection where
  | towardWall
  | awayFromWall
  deriving DecidableEq, Repr

/-- Material classification of the ball. -/
inductive BallMaterial where
  | softRubber
  | other
  deriving DecidableEq, Repr

/-- The object struck by the ball in the idealized bounce. -/
inductive CollisionPartner where
  | rigidCourtWall
  | other
  deriving DecidableEq, Repr

/-- Distinct objects plainly visible in the supplied squash photograph. -/
inductive FigureObject where
  | foregroundPlayer
  | backgroundPlayer
  | foregroundRacket
  | backgroundRacket
  | squashBall
  | frontWall
  | sideWall
  | woodenFloor
  deriving DecidableEq, Fintype, Repr

/-- Court features and visual encodings visible in the photograph. -/
inductive FigureFeature where
  | redBoundaryLines
  | yellowForegroundShirt
  | whiteBackgroundShirt
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative evidence extracted from the primary image. The photograph has no
printed labels or quantitative scale and therefore contributes no speed,
temperature, mass, or specific-heat readout.
-/
structure SquashGameFigure where
  showsObject : FigureObject → Bool
  showsFeature : FigureFeature → Bool
  foregroundPlayerSwingingRacket : Bool
  backgroundPlayerHoldingRacket : Bool
  bothPlayersFocusedOnBall : Bool
  ballNearCourtWall : Bool
  ballNearFloor : Bool
  floorMadeOfWood : Bool
  containsPrintedText : Bool
  containsQuantitativeScale : Bool

/-!
Independent physical quantities for one wall impact. Both kinetic energies,
the energy lost, and the heat absorbed by the ball are signed physical energy
quantities. The final temperature is not defined from any answer choice.
-/
structure SquashBallBounceSetup where
  material : BallMaterial
  collisionPartner : CollisionPartner
  ballMass : MassQuantity
  speedAt : BounceState → DimSpeed
  directionAt : BounceState → WallRelativeDirection
  kineticEnergyAt : BounceState → DimEnergy
  kineticEnergyLost : DimEnergy
  heatAbsorbedByBall : DimEnergy
  specificHeatCapacity : SpecificHeatCapacityQuantity
  initialTemperature : CelsiusTemperatureReading
  finalTemperature : CelsiusTemperatureReading
  exactlyOneWallBounce : Bool
  allLostKineticEnergyHeatsBall : Bool
  figure : SquashGameFigure

/-! ## Scenario, source data, primary-image facts, and governing laws -/

/-- Qualitative physical scenario stated in the problem. -/
structure MatchesSquashBallBounceScenario
    (setup : SquashBallBounceSetup) : Prop where
  ballIsSoftRubber : setup.material = .softRubber
  ballStrikesCourtWall : setup.collisionPartner = .rigidCourtWall
  incomingMotionIsTowardWall :
    setup.directionAt .incoming = .towardWall
  reboundMotionIsAwayFromWall :
    setup.directionAt .outgoing = .awayFromWall
  oneBounce : setup.exactlyOneWallBounce = true
  lostKineticEnergyBecomesBallHeat :
    setup.allLostKineticEnergyHeatsBall = true

/-!
The two speed magnitudes explicitly stated in the prose. The opposing motion
directions are recorded separately by `MatchesSquashBallBounceScenario`.
-/
structure MatchesProblemSpeedReadouts
    (setup : SquashBallBounceSetup) : Prop where
  incomingSpeedMetersPerSecond :
    speedInMetersPerSecond (setup.speedAt .incoming) = 22
  outgoingSpeedMetersPerSecond :
    speedInMetersPerSecond (setup.speedAt .outgoing) = 12

/-!
Rounded textbook reference data for rubber. The word "about" in the source is
represented by selecting `1200 J/(kg K)` as the calculation-model value; this
premise contains no temperature rise or answer choice.
-/
structure UsesRoundedRubberSpecificHeatData
    (setup : SquashBallBounceSetup) : Prop where
  rubberSpecificHeatJoulesPerKilogramKelvin :
    specificHeatInJoulesPerKilogramKelvin
      setup.specificHeatCapacity = 1200

/-- Qualitative facts visible in the supplied raster. -/
structure MatchesSuppliedSquashFigure
    (figure : SquashGameFigure) : Prop where
  everyNamedObjectShown : ∀ object, figure.showsObject object = true
  everyNamedFeatureShown : ∀ feature, figure.showsFeature feature = true
  foregroundPlayerIsSwinging :
    figure.foregroundPlayerSwingingRacket = true
  backgroundPlayerHasRacket :
    figure.backgroundPlayerHoldingRacket = true
  playersAttendToBall : figure.bothPlayersFocusedOnBall = true
  ballIsNearCourtWall : figure.ballNearCourtWall = true
  ballIsNearFloor : figure.ballNearFloor = true
  woodenCourtFloor : figure.floorMadeOfWood = true
  noPrintedLabels : figure.containsPrintedText = false
  noQuantitativeScale : figure.containsQuantitativeScale = false

/-- Positivity assumptions selecting a physically meaningful bounce. -/
structure HasPhysicalSquashBallParameters
    (setup : SquashBallBounceSetup) : Prop where
  positiveBallMass : 0 < massInKilograms setup.ballMass
  positiveSpecificHeat :
    0 < specificHeatInJoulesPerKilogramKelvin
      setup.specificHeatCapacity
  positiveInitialAbsoluteTemperature :
    0 < setup.initialTemperature.absoluteTemperature.toReal
  positiveFinalAbsoluteTemperature :
    0 < setup.finalTemperature.absoluteTemperature.toReal

/-!
Governing mechanics and calorimetry relations for the idealized impact:

* translational kinetic energy is `m v² / 2` at both bounce states;
* the lost kinetic energy is the incoming energy minus the outgoing energy;
* all of that loss is deposited as heat in the ball;
* sensible heat is `m c (T_f - T_i)`.

These general laws contain neither the calculated rise `17/120 °C` nor any
displayed answer value.
-/
structure SatisfiesBounceHeatingLaws
    (setup : SquashBallBounceSetup) : Prop where
  translationalKineticEnergy : ∀ state,
    energyInJoules (setup.kineticEnergyAt state) =
      (1 / 2 : ℝ) * massInKilograms setup.ballMass *
        (speedInMetersPerSecond (setup.speedAt state)) ^ 2
  kineticEnergyLossBalance :
    energyInJoules setup.kineticEnergyLost =
      energyInJoules (setup.kineticEnergyAt .incoming) -
        energyInJoules (setup.kineticEnergyAt .outgoing)
  conversionOfLostKineticEnergyToHeat :
    setup.allLostKineticEnergyHeatsBall = true →
      energyInJoules setup.heatAbsorbedByBall =
        energyInJoules setup.kineticEnergyLost
  sensibleHeatingLaw :
    energyInJoules setup.heatAbsorbedByBall =
      massInKilograms setup.ballMass *
        specificHeatInJoulesPerKilogramKelvin
          setup.specificHeatCapacity *
        (setup.finalTemperature.degreesCelsius -
          setup.initialTemperature.degreesCelsius)

/-! ## Displayed answers and current target -/

/-- The ball's measured Celsius temperature increase over the bounce. -/
def temperatureIncreaseInDegreesCelsius
    (setup : SquashBallBounceSetup) : ℝ :=
  setup.finalTemperature.degreesCelsius -
    setup.initialTemperature.degreesCelsius

/-- Labels of the four choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Temperature-increase value printed beside each answer label. -/
def displayedTemperatureIncreaseInDegreesCelsius : AnswerChoice → ℝ
  | .A => 9 / 50
  | .B => 4 / 25
  | .C => 1 / 5
  | .D => 7 / 50

/-- Dataset metadata recording the supplied answer label. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement with a two-decimal displayed answer under ordinary rounding. -/
def MatchesDisplayedTwoDecimalAnswer
    (setup : SquashBallBounceSetup) (choice : AnswerChoice) : Prop :=
  |temperatureIncreaseInDegreesCelsius setup -
      displayedTemperatureIncreaseInDegreesCelsius choice| <
    (1 / 200 : ℝ)

/-- The selected displayed rise is strictly closer than every alternative. -/
def IsUniqueClosestDisplayedTemperatureIncrease
    (setup : SquashBallBounceSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |temperatureIncreaseInDegreesCelsius setup -
        displayedTemperatureIncreaseInDegreesCelsius choice| <
      |temperatureIncreaseInDegreesCelsius setup -
        displayedTemperatureIncreaseInDegreesCelsius other|

/-!
The loss of translational kinetic energy per unit ball mass is
`(22² - 12²)/2 = 170 J/kg`. Dividing by the rounded rubber specific heat
gives the exact calculation-model temperature rise `17/120 °C`.
-/
lemma temperatureIncreaseInDegreesCelsius_exact
    (setup : SquashBallBounceSetup)
    (hScenario : MatchesSquashBallBounceScenario setup)
    (hSpeeds : MatchesProblemSpeedReadouts setup)
    (hRubberData : UsesRoundedRubberSpecificHeatData setup)
    (hPhysical : HasPhysicalSquashBallParameters setup)
    (hLaws : SatisfiesBounceHeatingLaws setup) :
    temperatureIncreaseInDegreesCelsius setup = (17 / 120 : ℝ) := by
  have hIncoming :=
    hLaws.translationalKineticEnergy BounceState.incoming
  have hOutgoing :=
    hLaws.translationalKineticEnergy BounceState.outgoing
  rw [hSpeeds.incomingSpeedMetersPerSecond] at hIncoming
  rw [hSpeeds.outgoingSpeedMetersPerSecond] at hOutgoing
  have hHeatConversion :=
    hLaws.conversionOfLostKineticEnergyToHeat
      hScenario.lostKineticEnergyBecomesBallHeat
  have hSensibleHeating := hLaws.sensibleHeatingLaw
  rw [hRubberData.rubberSpecificHeatJoulesPerKilogramKelvin] at hSensibleHeating
  unfold temperatureIncreaseInDegreesCelsius
  nlinarith [hLaws.kineticEnergyLossBalance,
    hPhysical.positiveBallMass]

/-!
The exact rise is approximately `0.1417 °C`; hence it rounds to `0.14 °C`
and is uniquely closest to choice D.

This formalizes blueprint label `thm:physics:phyx_mini_0490:target`.
-/
theorem problem_phyx_mini_0490
    (setup : SquashBallBounceSetup)
    (hScenario : MatchesSquashBallBounceScenario setup)
    (hSpeeds : MatchesProblemSpeedReadouts setup)
    (hRubberData : UsesRoundedRubberSpecificHeatData setup)
    (hFigure : MatchesSuppliedSquashFigure setup.figure)
    (hPhysical : HasPhysicalSquashBallParameters setup)
    (hLaws : SatisfiesBounceHeatingLaws setup) :
    temperatureIncreaseInDegreesCelsius setup = (17 / 120 : ℝ) ∧
      MatchesDisplayedTwoDecimalAnswer setup .D ∧
      IsUniqueClosestDisplayedTemperatureIncrease setup .D := by
  have hExact :=
    temperatureIncreaseInDegreesCelsius_exact setup hScenario hSpeeds
      hRubberData hPhysical hLaws
  refine ⟨hExact, ?_, ?_⟩
  · rw [MatchesDisplayedTwoDecimalAnswer, hExact]
    norm_num [displayedTemperatureIncreaseInDegreesCelsius, abs_of_nonneg,
      abs_of_neg]
  · intro other hOther
    fin_cases other
    · norm_num [hExact,
        displayedTemperatureIncreaseInDegreesCelsius, abs_of_nonneg,
        abs_of_neg]
    · norm_num [hExact,
        displayedTemperatureIncreaseInDegreesCelsius, abs_of_nonneg,
        abs_of_neg]
    · norm_num [hExact,
        displayedTemperatureIncreaseInDegreesCelsius, abs_of_nonneg,
        abs_of_neg]
    · exact (hOther rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0490
