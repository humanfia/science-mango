import Mathlib
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
import Physlib.Units.WithDim.Basic

/-!
# Mine cars released from a stretched elastic cable

This file models problem `phyx_mini_0271`. Three equal ore cars are initially
held at rest on a `30°` incline by a cable parallel to the rails. The cable is
stretched by `15 cm`. When the lower coupling fails, the lowest car detaches
and the remaining two cars oscillate about a new equilibrium.

Mass, length, force, acceleration, speed, and cable stiffness are represented
by Physlib dimensionful quantities. Real numbers are used only for coherent SI
readouts, the dimensionless angle in degrees, and the scalar coordinate in
Physlib's one-dimensional harmonic-oscillator model.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0271

open Dimension
open scoped BigOperators

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, used for cable extensions and amplitude. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical force. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative speed. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) NNReal)

/-- A cable stiffness, with dimension force per length. -/
abbrev CableStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (quantity : MassQuantity) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (quantity : LengthQuantity) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Newton readout of a physical force. -/
def forceInNewtons (quantity : ForceQuantity) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Metres-per-second-squared readout of a physical acceleration. -/
def accelerationInMetersPerSecondSquared
    (quantity : AccelerationQuantity) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Metres-per-second readout of a physical speed. -/
def speedInMetersPerSecond (quantity : SpeedQuantity) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Newton-per-metre readout of the elastic cable's stiffness. -/
def cableStiffnessInNewtonsPerMeter
    (quantity : CableStiffnessQuantity) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Convert an angle stated in degrees to its dimensionless radian value. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-! ## Cars, stages, and primary-image geometry -/

/-- The three ore cars, ordered by position along the incline. -/
inductive OreCar where
  | lowest
  | middle
  | upper
  deriving DecidableEq, Fintype, Repr

/-- The load configurations relevant to the cable equilibrium. -/
inductive LoadStage where
  | beforeCouplingBreak
  | remainingTwoCars
  deriving DecidableEq, Fintype, Repr

/-- The two couplings between adjacent cars. -/
inductive CarCoupling where
  | lowestToMiddle
  | middleToUpper
  deriving DecidableEq, Repr

/-- Orientation of the cable relative to the mine railway. -/
inductive CableOrientation where
  | parallelToRails
  deriving DecidableEq, Repr

/-- Idealized model for the motion after the coupling failure. -/
inductive OscillationModel where
  | undampedLinearAlongRails
  deriving DecidableEq, Repr

/-- Qualitative components and annotations visible in the supplied figure. -/
structure SuppliedFigure where
  carVisible : OreCar → Bool
  inclinedRailVisible : Bool
  cableVisible : Bool
  pulleyVisible : Bool
  angleThetaMarked : Bool
  cableRunsToPulleyAlongRails : Bool
  cableAttachedToUpperCar : Bool
  breakFreeAnnotationRefersTo : OreCar

/-! ## Physical setup and supplied data -/

/--
The complete apparatus and the unknown post-break quantities.

The new equilibrium extension and the oscillation amplitude are independent
fields. In particular, neither is defined from the recorded answer.
-/
structure MineCarCableSetup where
  carMass : OreCar → MassQuantity
  gravitationalAcceleration : AccelerationQuantity
  inclineAngleDegrees : ℝ
  cableStiffness : CableStiffnessQuantity
  cableExtensionAtEquilibrium : LoadStage → LengthQuantity
  cableTensionAtEquilibrium : LoadStage → ForceQuantity
  attachedToCableLoad : LoadStage → OreCar → Bool
  failedCoupling : CarCoupling
  detachedCar : OreCar
  cableOrientation : CableOrientation
  postBreakMotionModel : OscillationModel
  releaseSpeed : SpeedQuantity
  oscillationAmplitude : LengthQuantity
  postBreakOscillator : ClassicalMechanics.HarmonicOscillator
  postBreakInitialConditions :
    ClassicalMechanics.HarmonicOscillator.InitialConditions
  figure : SuppliedFigure

/-- Total mass carried by the cable at a given stage, read in kilograms. -/
def attachedMassInKilograms
    (setup : MineCarCableSetup) (stage : LoadStage) : ℝ :=
  ∑ car : OreCar,
    if setup.attachedToCableLoad stage car then
      massInKilograms (setup.carMass car)
    else
      0

/--
Numerical and qualitative facts stated by the problem. The gravity and cable
stiffness are deliberately not assigned numerical values because both cancel
when the two static equilibria are compared.
-/
structure MatchesProblemData (setup : MineCarCableSetup) : Prop where
  equalCarMasses : ∀ car, massInKilograms (setup.carMass car) = 10000
  inclineAngle : setup.inclineAngleDegrees = 30
  initialCableExtensionMeters :
    lengthInMeters
        (setup.cableExtensionAtEquilibrium .beforeCouplingBreak) =
      15 / 100
  allThreeInitiallyLoadCable :
    ∀ car, setup.attachedToCableLoad .beforeCouplingBreak car = true
  upperCarRemainsAttached :
    setup.attachedToCableLoad .remainingTwoCars .upper = true
  middleCarRemainsAttached :
    setup.attachedToCableLoad .remainingTwoCars .middle = true
  lowestCarDetached :
    setup.attachedToCableLoad .remainingTwoCars .lowest = false
  lowerCouplingFails : setup.failedCoupling = .lowestToMiddle
  detachedCarIsLowest : setup.detachedCar = .lowest
  cableParallelToRails : setup.cableOrientation = .parallelToRails
  resultingMotionIsUndampedLinear :
    setup.postBreakMotionModel = .undampedLinearAlongRails
  instantaneousReleaseFromRest :
    speedInMetersPerSecond setup.releaseSpeed = 0

/--
Primary-image readout: three cars lie on an inclined rail, the cable from the
upper car runs along the rails toward a pulley, `θ` marks the incline, and the
break-free annotation identifies the lowest car.
-/
structure MatchesSuppliedFigure (setup : MineCarCableSetup) : Prop where
  allCarsVisible : ∀ car, setup.figure.carVisible car = true
  inclinedRailVisible : setup.figure.inclinedRailVisible = true
  cableVisible : setup.figure.cableVisible = true
  pulleyVisible : setup.figure.pulleyVisible = true
  thetaMarked : setup.figure.angleThetaMarked = true
  cableRunsAlongRails : setup.figure.cableRunsToPulleyAlongRails = true
  cableAttachedToUpperCar : setup.figure.cableAttachedToUpperCar = true
  breakFreeAnnotation :
    setup.figure.breakFreeAnnotationRefersTo = .lowest

/-! ## Governing mechanics -/

/-- Positivity and nondegeneracy of the physical inputs. -/
structure HasPhysicalParameters (setup : MineCarCableSetup) : Prop where
  eachCarMassPositive :
    ∀ car, 0 < massInKilograms (setup.carMass car)
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  cableStiffnessPositive :
    0 < cableStiffnessInNewtonsPerMeter setup.cableStiffness

/--
Hooke's law and force balance for the old and new static equilibria, followed
by the general Physlib harmonic-oscillator model for release about the new
equilibrium.

The amplitude field is linked only to Physlib's general amplitude computed
from initial position and velocity. No numerical post-break extension,
amplitude, or answer choice occurs in these laws.
-/
structure SatisfiesElasticCableOscillatorLaws
    (setup : MineCarCableSetup) : Prop where
  hookeLawAtEquilibrium :
    ∀ stage,
      forceInNewtons (setup.cableTensionAtEquilibrium stage) =
        cableStiffnessInNewtonsPerMeter setup.cableStiffness *
          lengthInMeters (setup.cableExtensionAtEquilibrium stage)
  staticForceBalanceAlongIncline :
    ∀ stage,
      forceInNewtons (setup.cableTensionAtEquilibrium stage) =
        attachedMassInKilograms setup stage *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          Real.sin (degreesToRadians setup.inclineAngleDegrees)
  postBreakOscillatorMassReadout :
    setup.postBreakOscillator.m =
      attachedMassInKilograms setup .remainingTwoCars
  postBreakOscillatorStiffnessReadout :
    setup.postBreakOscillator.k =
      cableStiffnessInNewtonsPerMeter setup.cableStiffness
  initialDisplacementFromNewEquilibrium :
    setup.postBreakInitialConditions.x₀ 0 =
      lengthInMeters
          (setup.cableExtensionAtEquilibrium .beforeCouplingBreak) -
        lengthInMeters
          (setup.cableExtensionAtEquilibrium .remainingTwoCars)
  initialVelocityReadout :
    setup.postBreakInitialConditions.v₀ 0 =
      speedInMetersPerSecond setup.releaseSpeed
  physicalAmplitudeReadout :
    lengthInMeters setup.oscillationAmplitude =
      (ClassicalMechanics.HarmonicOscillator.AmplitudePhase.fromInitialConditions
          setup.postBreakOscillator setup.postBreakInitialConditions).A

/--
Comparing Hooke equilibrium for three equal cars with that for the remaining
two cars gives a new cable extension of `10 cm`.
-/
lemma postBreakEquilibriumExtension_is_ten_centimeters
    (setup : MineCarCableSetup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesElasticCableOscillatorLaws setup) :
    lengthInMeters
        (setup.cableExtensionAtEquilibrium .remainingTwoCars) =
      10 / 100 := by
  classical
  have hOreUniv :
      (Finset.univ : Finset OreCar) = {.lowest, .middle, .upper} := by
    ext car
    fin_cases car <;> simp
  have hmassBefore :
      attachedMassInKilograms setup .beforeCouplingBreak = 30000 := by
    rw [attachedMassInKilograms, hOreUniv]
    simp [_data.allThreeInitiallyLoadCable, _data.equalCarMasses]
    norm_num
  have hmassAfter :
      attachedMassInKilograms setup .remainingTwoCars = 20000 := by
    rw [attachedMassInKilograms, hOreUniv]
    simp [_data.upperCarRemainsAttached, _data.middleCarRemainsAttached,
      _data.lowestCarDetached, _data.equalCarMasses]
    norm_num
  have hold := _laws.hookeLawAtEquilibrium .beforeCouplingBreak
  have hnew := _laws.hookeLawAtEquilibrium .remainingTwoCars
  have bold := _laws.staticForceBalanceAlongIncline .beforeCouplingBreak
  have bnew := _laws.staticForceBalanceAlongIncline .remainingTwoCars
  rw [hmassBefore] at bold
  rw [hmassAfter] at bnew
  rw [bold] at hold
  rw [bnew] at hnew
  rw [_data.initialCableExtensionMeters] at hold
  nlinarith [_physical.cableStiffnessPositive]

/--
For an undamped linear oscillator released from rest, Physlib's
amplitude--phase conversion makes the amplitude the magnitude of the initial
displacement from the new equilibrium.
-/
lemma oscillationAmplitude_eq_equilibriumShift
    (setup : MineCarCableSetup)
    (_data : MatchesProblemData setup)
    (_laws : SatisfiesElasticCableOscillatorLaws setup) :
    lengthInMeters setup.oscillationAmplitude =
      |lengthInMeters
          (setup.cableExtensionAtEquilibrium .beforeCouplingBreak) -
        lengthInMeters
          (setup.cableExtensionAtEquilibrium .remainingTwoCars)| := by
  rw [_laws.physicalAmplitudeReadout]
  simp [ClassicalMechanics.HarmonicOscillator.AmplitudePhase.fromInitialConditions,
    _laws.initialVelocityReadout, _data.instantaneousReleaseFromRest,
    _laws.initialDisplacementFromNewEquilibrium, Complex.norm_def, ← pow_two,
    Real.sqrt_sq_eq_abs]

/-! ## Displayed answers and formalization target -/

/-- Labels of the four displayed answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Oscillation amplitude in metres printed beside each answer label. -/
def AnswerChoice.meters : AnswerChoice → ℝ
  | .A => 30 / 1000
  | .B => 40 / 1000
  | .C => 50 / 1000
  | .D => 60 / 1000

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Exact agreement of a physical amplitude with a displayed answer. -/
def MatchesAnswerChoice
    (amplitude : LengthQuantity) (choice : AnswerChoice) : Prop :=
  lengthInMeters amplitude = choice.meters

/--
The equilibrium shifts from `0.150 m` to `0.100 m`. Since the remaining cars
are momentarily at rest at the old equilibrium when the coupling fails, their
oscillation amplitude about the new equilibrium is `0.050 m`, answer C.

This formalizes blueprint label `thm:physics:phyx_mini_0271:target`.
-/
theorem oscillationAmplitude_is_five_centimeters_and_matches_answerC
    (setup : MineCarCableSetup)
    (_data : MatchesProblemData setup)
    (_figure : MatchesSuppliedFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesElasticCableOscillatorLaws setup) :
    lengthInMeters setup.oscillationAmplitude = 50 / 1000 ∧
      MatchesAnswerChoice setup.oscillationAmplitude
        recordedAnswerChoice := by
  have hAmplitude :
      lengthInMeters setup.oscillationAmplitude = 50 / 1000 := by
    rw [oscillationAmplitude_eq_equilibriumShift setup _data _laws,
      _data.initialCableExtensionMeters,
      postBreakEquilibriumExtension_is_ten_centimeters setup _data _physical _laws]
    norm_num
  exact ⟨hAmplitude, by
    simpa [MatchesAnswerChoice, recordedAnswerChoice, AnswerChoice.meters] using hAmplitude⟩

end PhyXMiniProblems.ProblemPhyXMini0271
