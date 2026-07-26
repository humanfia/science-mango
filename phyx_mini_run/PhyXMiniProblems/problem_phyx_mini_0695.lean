import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/-!
# Instantaneous power supplied to a spring-coupled box

A `5.0 kg` box starts from rest at the equilibrium position of a horizontal
spring of stiffness `80 N/m`.  A rope then pulls it away from the wall with
constant tension `100 N` across a rough horizontal floor with kinetic-friction
coefficient `0.30`.  The requested quantity is the power supplied by the hand
or motor after the box has moved `0.50 m`.

The primary raster shows the same box at its initial and final positions.  It
labels the horizontal axis `x`, the initial coordinate `0`, the displacement
`Δr = 0.50 m`, a rightward tension arrow `T`, and a leftward kinetic-friction
arrow `f_k`.

Mass, position, length, acceleration, force, stiffness, speed, energy, and
power retain their physical dimensions through Physlib.  Real numbers occur
only at coherent-SI readout boundaries, for the dimensionless friction
coefficient, and for displayed answer values.

Assumption/target boundary:

* source and figure predicates record the measurements and visible geometry;
* standard terrestrial gravity is an independent calibration;
* the governing-law structure states horizontal force balance, Coulomb
  friction, Hooke energy, work--energy, and instantaneous power;
* the exact final power and its agreement with answer C are conclusions only.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0695

open Dimension

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A nonnegative physical mass, independent of the chosen unit system. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed coordinate on the horizontal `x` axis. -/
abbrev PositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical length, used for spring extension. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative acceleration magnitude of dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative force magnitude of dimension `M L T⁻²`. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative linear spring stiffness, with dimension `M T⁻²`. -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- The physical dimension `M L² T⁻³` of power. -/
def powerDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical power whose coherent-SI unit is the watt. -/
abbrev PowerQuantity : Type :=
  Dimensionful (WithDim powerDimension NNReal)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a signed horizontal coordinate in metres. -/
def positionInMeters (position : PositionQuantity) : ℝ :=
  (position UnitChoices.SI).val

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read an acceleration magnitude in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a force magnitude in newtons. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Read a spring stiffness in newtons per metre. -/
def springStiffnessInNewtonsPerMeter
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  ((stiffness UnitChoices.SI).val : ℝ)

/-- Read a Physlib speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read a Physlib energy in joules using its calibrated joule. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Read a physical power in watts. -/
def powerInWatts (power : PowerQuantity) : ℝ :=
  ((power UnitChoices.SI).val : ℝ)

/-! ## Apparatus, process states, and primary-figure vocabulary -/

/-- The two configurations of the box shown in the raster. -/
inductive MotionState where
  | initialEquilibrium
  | afterHalfMeter
  deriving DecidableEq, Fintype, Repr

/-- The stated constitutive model of the wall-mounted spring. -/
inductive SpringModel where
  | linearHookean
  deriving DecidableEq, Repr

/-- The pulling protocol used after release from rest. -/
inductive PullingProtocol where
  | constantRopeTension
  deriving DecidableEq, Repr

/-- The supporting surface and its role in the motion. -/
inductive SurfaceModel where
  | roughHorizontalFloor
  deriving DecidableEq, Repr

/-- The source of the power requested by the question. -/
inductive PowerSupplier where
  | handOrMotor
  deriving DecidableEq, Repr

/-- Horizontal directions distinguished by the force arrows. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- The two force arrows explicitly drawn in the primary image. -/
inductive FigureForceArrow where
  | tensionT
  | kineticFrictionFk
  deriving DecidableEq, Fintype, Repr

/-- Literal symbolic labels printed in the primary image. -/
inductive FigureTextLabel where
  | springConstantK
  | boxMassM
  | horizontalAxisX
  | originZero
  | displacementDeltaR
  deriving DecidableEq, Fintype, Repr

/--
Presentation data extracted from image `695.png`.  The two box drawings are
two states of one physical box, not two interacting blocks.
-/
structure PulledSpringBoxFigure where
  textLabelShown : FigureTextLabel → Bool
  boxShownAt : MotionState → Bool
  forceArrowShown : FigureForceArrow → Bool
  forceArrowDirection : FigureForceArrow → HorizontalDirection
  wallShownAtLeft : Bool
  springShownHorizontal : Bool
  springAnchoredToWall : Bool
  springAttachedToBox : Bool
  displacementArrowEndpoints : MotionState × MotionState
  printedMassKilograms : ℝ
  printedSpringStiffnessNewtonsPerMeter : ℝ
  printedInitialCoordinateMeters : ℝ
  printedDisplacementMeters : ℝ

/-!
Independent physical quantities for the apparatus and the two motion states.
The supplied power is an observable field and is not defined from an answer
choice or from the requested numerical value.
-/
structure PulledSpringBoxSetup where
  boxMass : MassQuantity
  springStiffness : SpringStiffnessQuantity
  ropeTensionMagnitude : ForceQuantity
  kineticFrictionCoefficient : ℝ
  gravitationalAccelerationMagnitude : AccelerationQuantity
  boxPosition : MotionState → PositionQuantity
  springExtension : MotionState → LengthQuantity
  boxSpeed : MotionState → DimSpeed
  normalForceMagnitude : ForceQuantity
  kineticFrictionMagnitude : ForceQuantity
  springForceMagnitude : MotionState → ForceQuantity
  ropeWork : MotionState → DimEnergy
  kineticFrictionWork : MotionState → DimEnergy
  springPotentialEnergy : MotionState → DimEnergy
  kineticEnergy : MotionState → DimEnergy
  powerSuppliedByPuller : MotionState → PowerQuantity
  springModel : SpringModel
  pullingProtocol : PullingProtocol
  surfaceModel : SurfaceModel
  powerSupplier : PowerSupplier
  figure : PulledSpringBoxFigure

/-! ## Source data, figure readouts, and physical branch -/

/--
The numerical data and initial/final conditions stated in the prose.  This
predicate contains no power value and no answer-choice assertion.
-/
structure MatchesProblemData (setup : PulledSpringBoxSetup) : Prop where
  boxMassReadout : massInKilograms setup.boxMass = 5
  springStiffnessReadout :
    springStiffnessInNewtonsPerMeter setup.springStiffness = 80
  constantTensionReadout :
    forceInNewtons setup.ropeTensionMagnitude = 100
  kineticFrictionCoefficientReadout :
    setup.kineticFrictionCoefficient = 3 / 10
  initialCoordinateIsZero :
    positionInMeters (setup.boxPosition .initialEquilibrium) = 0
  initialSpringAtEquilibrium :
    lengthInMeters (setup.springExtension .initialEquilibrium) = 0
  initiallyAtRest :
    speedInMetersPerSecond (setup.boxSpeed .initialEquilibrium) = 0
  movedHalfMeter :
    positionInMeters (setup.boxPosition .afterHalfMeter) -
        positionInMeters (setup.boxPosition .initialEquilibrium) = 1 / 2
  springIsLinear : setup.springModel = .linearHookean
  pullHasConstantTension : setup.pullingProtocol = .constantRopeTension
  floorIsRoughAndHorizontal : setup.surfaceModel = .roughHorizontalFloor
  requestedSupplierIsHandOrMotor : setup.powerSupplier = .handOrMotor

/-- Standard near-Earth gravitational calibration used by the numerical answer. -/
structure UsesStandardTerrestrialGravity
    (setup : PulledSpringBoxSetup) : Prop where
  gravitationalAccelerationReadout :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAccelerationMagnitude = 49 / 5

/--
Literal labels, numerical inscriptions, geometry, and arrow directions visible
in the supplied primary raster.
-/
structure MatchesPrimaryFigure (setup : PulledSpringBoxSetup) : Prop where
  everyTextLabelShown : ∀ label, setup.figure.textLabelShown label = true
  bothBoxStatesShown : ∀ state, setup.figure.boxShownAt state = true
  bothForceArrowsShown :
    ∀ arrow, setup.figure.forceArrowShown arrow = true
  tensionArrowPointsRight :
    setup.figure.forceArrowDirection .tensionT = .right
  kineticFrictionArrowPointsLeft :
    setup.figure.forceArrowDirection .kineticFrictionFk = .left
  wallVisibleOnLeft : setup.figure.wallShownAtLeft = true
  springDrawnHorizontally : setup.figure.springShownHorizontal = true
  springWallAnchored : setup.figure.springAnchoredToWall = true
  springAttachedToTheBox : setup.figure.springAttachedToBox = true
  displacementRunsFromInitialToFinal :
    setup.figure.displacementArrowEndpoints =
      (.initialEquilibrium, .afterHalfMeter)
  massInscriptionMatchesSetup :
    setup.figure.printedMassKilograms = massInKilograms setup.boxMass
  massInscriptionIsFive : setup.figure.printedMassKilograms = 5
  stiffnessInscriptionMatchesSetup :
    setup.figure.printedSpringStiffnessNewtonsPerMeter =
      springStiffnessInNewtonsPerMeter setup.springStiffness
  stiffnessInscriptionIsEighty :
    setup.figure.printedSpringStiffnessNewtonsPerMeter = 80
  originInscriptionIsZero :
    setup.figure.printedInitialCoordinateMeters = 0
  displacementInscriptionIsHalfMeter :
    setup.figure.printedDisplacementMeters = 1 / 2

/-- Positivity and nondegeneracy conditions selecting the physical branch. -/
structure HasPhysicalParameters (setup : PulledSpringBoxSetup) : Prop where
  boxMassPositive : 0 < massInKilograms setup.boxMass
  springStiffnessPositive :
    0 < springStiffnessInNewtonsPerMeter setup.springStiffness
  ropeTensionPositive : 0 < forceInNewtons setup.ropeTensionMagnitude
  kineticFrictionCoefficientNonnegative :
    0 ≤ setup.kineticFrictionCoefficient
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude
  finalDisplacementPositive :
    positionInMeters (setup.boxPosition .initialEquilibrium) <
      positionInMeters (setup.boxPosition .afterHalfMeter)
  speedNonnegative :
    ∀ state, 0 ≤ speedInMetersPerSecond (setup.boxSpeed state)
  springPotentialEnergyNonnegative :
    ∀ state, 0 ≤ energyInJoules (setup.springPotentialEnergy state)
  kineticEnergyNonnegative :
    ∀ state, 0 ≤ energyInJoules (setup.kineticEnergy state)

/-! ## Governing mechanics and power laws -/

/-!
The one-dimensional idealizations used in the work--energy calculation.

* extension equals rightward travel from the equilibrium position;
* vertical force balance gives `N = m g`;
* kinetic friction has magnitude `μ_k N` and does negative work;
* the spring obeys Hooke's law and stores `k x² / 2`;
* translational kinetic energy is `m v² / 2`;
* the change in kinetic energy is rope work plus friction work minus the
  increase in spring potential energy;
* the puller's instantaneous power is the collinear product `T v`.

Every field is a uniform physical law.  No field specifies a final speed,
final power, displayed wattage, or answer label.
-/
structure SatisfiesPulledSpringBoxLaws
    (setup : PulledSpringBoxSetup) : Prop where
  extensionTracksTravelFromEquilibrium :
    ∀ state,
      lengthInMeters (setup.springExtension state) =
        positionInMeters (setup.boxPosition state) -
          positionInMeters (setup.boxPosition .initialEquilibrium)
  verticalNormalForceBalance :
    forceInNewtons setup.normalForceMagnitude =
      massInKilograms setup.boxMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAccelerationMagnitude
  coulombKineticFrictionMagnitude :
    forceInNewtons setup.kineticFrictionMagnitude =
      setup.kineticFrictionCoefficient *
        forceInNewtons setup.normalForceMagnitude
  hookeForceMagnitude :
    ∀ state,
      forceInNewtons (setup.springForceMagnitude state) =
        springStiffnessInNewtonsPerMeter setup.springStiffness *
          lengthInMeters (setup.springExtension state)
  hookeSpringPotentialEnergy :
    ∀ state,
      energyInJoules (setup.springPotentialEnergy state) =
        (1 / 2 : ℝ) *
          springStiffnessInNewtonsPerMeter setup.springStiffness *
            lengthInMeters (setup.springExtension state) ^ 2
  translationalKineticEnergy :
    ∀ state,
      energyInJoules (setup.kineticEnergy state) =
        (1 / 2 : ℝ) * massInKilograms setup.boxMass *
          speedInMetersPerSecond (setup.boxSpeed state) ^ 2
  constantTensionWork :
    ∀ state,
      energyInJoules (setup.ropeWork state) =
        forceInNewtons setup.ropeTensionMagnitude *
          (positionInMeters (setup.boxPosition state) -
            positionInMeters (setup.boxPosition .initialEquilibrium))
  opposingKineticFrictionWork :
    ∀ state,
      energyInJoules (setup.kineticFrictionWork state) =
        -(forceInNewtons setup.kineticFrictionMagnitude) *
          (positionInMeters (setup.boxPosition state) -
            positionInMeters (setup.boxPosition .initialEquilibrium))
  workEnergyBalance :
    ∀ state,
      energyInJoules (setup.kineticEnergy state) -
          energyInJoules
            (setup.kineticEnergy .initialEquilibrium) =
        energyInJoules (setup.ropeWork state) +
            energyInJoules (setup.kineticFrictionWork state) -
          (energyInJoules (setup.springPotentialEnergy state) -
            energyInJoules
              (setup.springPotentialEnergy .initialEquilibrium))
  instantaneousPowerOfCollinearPull :
    ∀ state,
      powerInWatts (setup.powerSuppliedByPuller state) =
        forceInNewtons setup.ropeTensionMagnitude *
          speedInMetersPerSecond (setup.boxSpeed state)

/-! ## Derived work, speed, and power -/

/--
After `0.50 m`, the rope has done `50 J`, friction has removed `7.35 J`,
and the spring stores `10 J`, leaving `32.65 J` of kinetic energy.
-/
lemma finalKineticEnergyInJoules_eq_653_div_20
    (setup : PulledSpringBoxSetup)
    (_data : MatchesProblemData setup)
    (_gravity : UsesStandardTerrestrialGravity setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesPulledSpringBoxLaws setup) :
    energyInJoules (setup.kineticEnergy .afterHalfMeter) = 653 / 20 := by
  have hExtensionFinal :=
    _laws.extensionTracksTravelFromEquilibrium MotionState.afterHalfMeter
  have hNormal := _laws.verticalNormalForceBalance
  have hFriction := _laws.coulombKineticFrictionMagnitude
  have hSpringInitial :=
    _laws.hookeSpringPotentialEnergy MotionState.initialEquilibrium
  have hSpringFinal :=
    _laws.hookeSpringPotentialEnergy MotionState.afterHalfMeter
  have hKineticInitial :=
    _laws.translationalKineticEnergy MotionState.initialEquilibrium
  have hRopeFinal := _laws.constantTensionWork MotionState.afterHalfMeter
  have hFrictionWorkFinal :=
    _laws.opposingKineticFrictionWork MotionState.afterHalfMeter
  have hBalance := _laws.workEnergyBalance MotionState.afterHalfMeter
  rw [_data.boxMassReadout, _gravity.gravitationalAccelerationReadout] at hNormal
  norm_num at hNormal
  rw [_data.kineticFrictionCoefficientReadout, hNormal] at hFriction
  norm_num at hFriction
  rw [_data.springStiffnessReadout, _data.initialSpringAtEquilibrium] at hSpringInitial
  norm_num at hSpringInitial
  rw [_data.movedHalfMeter] at hExtensionFinal
  rw [_data.springStiffnessReadout, hExtensionFinal] at hSpringFinal
  norm_num at hSpringFinal
  rw [_data.boxMassReadout, _data.initiallyAtRest] at hKineticInitial
  norm_num at hKineticInitial
  rw [_data.constantTensionReadout, _data.movedHalfMeter] at hRopeFinal
  norm_num at hRopeFinal
  rw [hFriction, _data.movedHalfMeter] at hFrictionWorkFinal
  norm_num at hFrictionWorkFinal
  rw [hKineticInitial, hRopeFinal, hFrictionWorkFinal,
    hSpringFinal, hSpringInitial] at hBalance
  norm_num at hBalance ⊢
  exact hBalance

/-- The corresponding nonnegative final speed is `sqrt (653 / 50) m/s`. -/
lemma finalSpeedInMetersPerSecond_eq_sqrt_653_div_50
    (setup : PulledSpringBoxSetup)
    (_data : MatchesProblemData setup)
    (_gravity : UsesStandardTerrestrialGravity setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesPulledSpringBoxLaws setup) :
    speedInMetersPerSecond (setup.boxSpeed .afterHalfMeter) =
      Real.sqrt (653 / 50) := by
  have hKineticEnergy :=
    finalKineticEnergyInJoules_eq_653_div_20
      setup _data _gravity _physical _laws
  have hKineticFormula :=
    _laws.translationalKineticEnergy MotionState.afterHalfMeter
  rw [_data.boxMassReadout, hKineticEnergy] at hKineticFormula
  have hSpeedSquared :
      speedInMetersPerSecond (setup.boxSpeed MotionState.afterHalfMeter) ^ 2 =
        (653 / 50 : ℝ) := by
    nlinarith
  have hRadicandNonnegative : (0 : ℝ) ≤ 653 / 50 := by
    norm_num
  have hSqrtSquared := Real.sq_sqrt hRadicandNonnegative
  have hSpeedNonnegative :=
    _physical.speedNonnegative MotionState.afterHalfMeter
  have hSqrtNonnegative := Real.sqrt_nonneg (653 / 50 : ℝ)
  nlinarith

/-- The exact instantaneous puller power before numerical rounding. -/
lemma finalSuppliedPowerInWatts_eq
    (setup : PulledSpringBoxSetup)
    (_data : MatchesProblemData setup)
    (_gravity : UsesStandardTerrestrialGravity setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesPulledSpringBoxLaws setup) :
    powerInWatts (setup.powerSuppliedByPuller .afterHalfMeter) =
      100 * Real.sqrt (653 / 50) := by
  rw [_laws.instantaneousPowerOfCollinearPull,
    _data.constantTensionReadout,
    finalSpeedInMetersPerSecond_eq_sqrt_653_div_50
      setup _data _gravity _physical _laws]

/-! ## Displayed answers and formalization target -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Power in watts printed beside each answer label. -/
def AnswerChoice.displayedPowerWatts : AnswerChoice → ℝ
  | .A => 340
  | .B => 380
  | .C => 360
  | .D => 400

/-- The answer label recorded in the dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/--
A physical power rounds to a displayed multiple of `20 W`.  The strict
half-step tolerance avoids identifying either neighboring multiple at a tie.
-/
def RoundsToDisplayedPower
    (power : PowerQuantity) (choice : AnswerChoice) : Prop :=
  |powerInWatts power - choice.displayedPowerWatts| < 10

/-!
The exact instantaneous power is approximately `361 W`, hence it rounds to
`360 W` and matches recorded answer C.

This formalizes `thm:physics:phyx_mini_0695:target`.
-/
theorem suppliedPower_matches_recordedAnswerC
    (setup : PulledSpringBoxSetup)
    (_data : MatchesProblemData setup)
    (_figure : MatchesPrimaryFigure setup)
    (_gravity : UsesStandardTerrestrialGravity setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesPulledSpringBoxLaws setup) :
    powerInWatts (setup.powerSuppliedByPuller .afterHalfMeter) =
        100 * Real.sqrt (653 / 50) ∧
      RoundsToDisplayedPower
        (setup.powerSuppliedByPuller .afterHalfMeter)
        recordedDatasetAnswer := by
  have hPower :=
    finalSuppliedPowerInWatts_eq setup _data _gravity _physical _laws
  constructor
  · exact hPower
  · dsimp [RoundsToDisplayedPower, recordedDatasetAnswer,
      AnswerChoice.displayedPowerWatts]
    rw [hPower, abs_lt]
    have hRadicandNonnegative : (0 : ℝ) ≤ 653 / 50 := by
      norm_num
    have hSqrtSquared := Real.sq_sqrt hRadicandNonnegative
    have hSqrtNonnegative := Real.sqrt_nonneg (653 / 50 : ℝ)
    constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0695
