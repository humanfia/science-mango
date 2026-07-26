import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Torsion constant for a disk physical pendulum

A `2.50 kg` uniform disk of diameter `D = 42.0 cm` is attached to the lower
end of a massless rod of length `L = 76.0 cm`.  A torsion spring at the upper
pivot reduces the small-angle oscillation period by `0.500 s`.

The primary image, contrary to its auxiliary caption, draws the lower endpoint
of the `L` arrow at the top rim of the disk.  Thus the disk center is a distance
`L + D / 2` below the pivot.  This distinction is recorded explicitly below.

Physical magnitudes use Physlib's unit-independent `Dimensionful` API.  Real
numbers occur only as coherent SI readouts and displayed answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0270

open Dimension

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative acceleration magnitude, with dimension `L T⁻²`. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A moment of inertia about the axis normal to the disk, with dimension `M L²`. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-- A signed torque, with dimension `M L² T⁻²`. -/
abbrev TorqueQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/--
The coefficient multiplying angular displacement in a linearized restoring
torque.  Radians are dimensionless, so its dimension is `M L² T⁻²`.
-/
abbrev RestoringTorqueCoefficientQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/--
The torsion constant of the pivot spring.  Although it has the same dimension
as a restoring-torque coefficient, it has a distinct physical role.
-/
abbrev TorsionConstantQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical length in meters. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical duration in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Read an acceleration magnitude in meters per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a moment of inertia in kilogram meter squared. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Read a signed torque in newton meters. -/
def torqueInNewtonMeters (torque : TorqueQuantity) : ℝ :=
  (torque UnitChoices.SI).val

/-- Read a linearized restoring coefficient in newton meters per radian. -/
def restoringCoefficientInNewtonMetersPerRadian
    (coefficient : RestoringTorqueCoefficientQuantity) : ℝ :=
  ((coefficient UnitChoices.SI).val : ℝ)

/-- Read a torsion constant in newton meters per radian. -/
def torsionConstantInNewtonMetersPerRadian
    (torsionConstant : TorsionConstantQuantity) : ℝ :=
  ((torsionConstant UnitChoices.SI).val : ℝ)

/-! ## Physical roles and primary-image geometry -/

/-- The idealized mass distribution of the disk. -/
inductive DiskMassDistribution where
  | uniformSolidDisk
  deriving DecidableEq, Repr

/-- The mass model specified for the supporting rod. -/
inductive RodMassModel where
  | negligibleMass
  deriving DecidableEq, Repr

/-- The equilibrium orientation stated in the problem. -/
inductive EquilibriumOrientation where
  | verticallyDownward
  deriving DecidableEq, Repr

/-- The connected restoring element visible around the pivot. -/
inductive PivotSpringKind where
  | connectedTorsionSpring
  deriving DecidableEq, Repr

/-- Components visible in the supplied primary image. -/
inductive FigureComponent where
  | fixedHorizontalSupport
  | pivot
  | torsionSpringCoil
  | verticalRod
  | disk
  deriving DecidableEq, Repr

/-- Distinguished points needed to state the primary-image geometry. -/
inductive FigurePoint where
  | pivot
  | diskTop
  | diskCenter
  | diskBottom
  deriving DecidableEq, Repr

/-- Mathematical labels printed in the supplied image. -/
inductive FigureLabel where
  | rodLengthL
  | diskDiameterD
  deriving DecidableEq, Repr

/-- Structured readout of the supplied physical diagram. -/
structure DiskPendulumFigure where
  shows : FigureComponent → Bool
  labelVisible : FigureLabel → Bool
  distanceBetween : FigurePoint → FigurePoint → LengthQuantity
  rodUpperEndpoint : FigurePoint
  rodLowerEndpoint : FigurePoint
  lengthArrowUpperEndpoint : FigurePoint
  lengthArrowLowerEndpoint : FigurePoint
  diameterArrowUpperEndpoint : FigurePoint
  diameterArrowLowerEndpoint : FigurePoint
  rodAxisPassesThroughDiskCenter : Bool

/-!
The physical system and its two periods.  The spring torsion constant is an
independent field: it is not defined from a displayed answer or from any other
measurement.  The signed torque functions describe the nonlinear system as a
function of angular displacement in radians.  The two Physlib oscillators and
their periods represent the tangent systems at the vertical equilibrium,
rather than asserting that the nonlinear finite-amplitude periods are exactly
those of harmonic oscillators.
-/
structure DiskTorsionPendulumSetup where
  figure : DiskPendulumFigure
  diskMass : MassQuantity
  diskDiameter_D : LengthQuantity
  diskRadius : LengthQuantity
  rodLength_L : LengthQuantity
  diskCenterDistanceBelowPivot : LengthQuantity
  gravitationalAccelerationMagnitude : AccelerationMagnitudeQuantity
  diskMomentOfInertiaAboutCenter : MomentOfInertiaQuantity
  diskMomentOfInertiaAboutPivot : MomentOfInertiaQuantity
  gravitationalRestoringCoefficient : RestoringTorqueCoefficientQuantity
  springTorsionConstant : TorsionConstantQuantity
  gravitationalTorqueAboutPivot : ℝ → TorqueQuantity
  torsionSpringTorqueAboutPivot : ℝ → TorqueQuantity
  combinedTorqueAboutPivot : ℝ → TorqueQuantity
  linearizedPeriodWithoutTorsionSpring : TimeQuantity
  linearizedPeriodWithTorsionSpring : TimeQuantity
  reportedPeriodReduction : TimeQuantity
  oscillatorWithoutTorsionSpring : ClassicalMechanics.HarmonicOscillator
  oscillatorWithTorsionSpring : ClassicalMechanics.HarmonicOscillator
  diskMassDistribution : DiskMassDistribution
  rodMassModel : RodMassModel
  equilibriumOrientation : EquilibriumOrientation
  pivotSpringKind : PivotSpringKind

/-! ## Figure/data readouts and physical laws -/

/-!
Primary-image evidence.  The `L` bracket runs from the pivot level to the top
rim, while the `D` bracket spans the disk.  Hence the center lever arm is
`L + D/2`; this is figure geometry, not the requested torsion constant.
-/
structure MatchesPrimaryDiskPendulumFigure
    (setup : DiskTorsionPendulumSetup) : Prop where
  everyComponentVisible : ∀ component, setup.figure.shows component = true
  bothLabelsVisible : ∀ label, setup.figure.labelVisible label = true
  rodStartsAtPivot : setup.figure.rodUpperEndpoint = .pivot
  rodEndsAtDiskTop : setup.figure.rodLowerEndpoint = .diskTop
  lengthArrowStartsAtPivot : setup.figure.lengthArrowUpperEndpoint = .pivot
  lengthArrowEndsAtDiskTop : setup.figure.lengthArrowLowerEndpoint = .diskTop
  diameterArrowStartsAtDiskTop :
    setup.figure.diameterArrowUpperEndpoint = .diskTop
  diameterArrowEndsAtDiskBottom :
    setup.figure.diameterArrowLowerEndpoint = .diskBottom
  rodAndDiskCentersAligned : setup.figure.rodAxisPassesThroughDiskCenter = true
  rodLengthReadout :
    setup.figure.distanceBetween .pivot .diskTop = setup.rodLength_L
  diskDiameterReadout :
    setup.figure.distanceBetween .diskTop .diskBottom = setup.diskDiameter_D
  diskRadiusReadout :
    setup.figure.distanceBetween .diskTop .diskCenter = setup.diskRadius
  centerLeverArmReadout :
    setup.figure.distanceBetween .pivot .diskCenter =
      setup.diskCenterDistanceBelowPivot
  centerLeverArmGeometry :
    lengthInMeters setup.diskCenterDistanceBelowPivot =
      lengthInMeters setup.rodLength_L + lengthInMeters setup.diskRadius

/-!
Numerical and qualitative problem data.  The gravity value is the conventional
near-Earth textbook calibration needed to distinguish the numerical choices.
The period-reduction relation is an observed comparison between two physical
states, interpreted by the textbook problem as a comparison of the two
small-angle tangent-model periods.  It does not assign a value to the spring
constant.
-/
structure MatchesDiskTorsionPendulumProblemData
    (setup : DiskTorsionPendulumSetup) : Prop where
  diskMassKilograms : massInKilograms setup.diskMass = 5 / 2
  diskDiameterMeters : lengthInMeters setup.diskDiameter_D = 21 / 50
  rodLengthMeters : lengthInMeters setup.rodLength_L = 19 / 25
  standardGravity :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAccelerationMagnitude = 49 / 5
  periodReductionSeconds : timeInSeconds setup.reportedPeriodReduction = 1 / 2
  measuredPeriodReduction :
    timeInSeconds setup.linearizedPeriodWithoutTorsionSpring -
        timeInSeconds setup.linearizedPeriodWithTorsionSpring =
      timeInSeconds setup.reportedPeriodReduction
  diskIsUniformAndSolid :
    setup.diskMassDistribution = .uniformSolidDisk
  rodHasNegligibleMass : setup.rodMassModel = .negligibleMass
  springIsConnected : setup.pivotSpringKind = .connectedTorsionSpring
  verticalEquilibrium :
    setup.equilibriumOrientation = .verticallyDownward

/-- Positivity and nondegeneracy conditions for the physical system. -/
structure HasPhysicalDiskTorsionPendulumParameters
    (setup : DiskTorsionPendulumSetup) : Prop where
  diskMassPositive : 0 < massInKilograms setup.diskMass
  diskDiameterPositive : 0 < lengthInMeters setup.diskDiameter_D
  diskRadiusPositive : 0 < lengthInMeters setup.diskRadius
  rodLengthPositive : 0 < lengthInMeters setup.rodLength_L
  centerDistancePositive :
    0 < lengthInMeters setup.diskCenterDistanceBelowPivot
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude
  pivotInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.diskMomentOfInertiaAboutPivot
  gravitationalCoefficientPositive :
    0 < restoringCoefficientInNewtonMetersPerRadian
      setup.gravitationalRestoringCoefficient
  torsionConstantPositive :
    0 < torsionConstantInNewtonMetersPerRadian
      setup.springTorsionConstant
  periodWithoutSpringPositive :
    0 < timeInSeconds setup.linearizedPeriodWithoutTorsionSpring
  periodWithSpringPositive :
    0 < timeInSeconds setup.linearizedPeriodWithTorsionSpring

/-!
Governing geometry, rigid-body, and small-oscillation laws:

* the radius is half the diameter;
* a uniform solid disk has central inertia `m r² / 2`;
* the parallel-axis contribution is `m d²`;
* the exact gravitational torque is `-m g d sin θ`;
* the ideal torsion spring obeys the exact Hooke law `-κ θ`;
* `HasDerivAt` contracts identify the tangent restoring coefficients at the
  vertical equilibrium, making the small-angle step local rather than a
  global equality; and
* each tangent-model period is the period of the corresponding generalized
  Physlib harmonic oscillator.

No field contains a displayed torsion-constant value or the conclusion that a
particular answer choice is correct.
-/
structure SatisfiesDiskTorsionPendulumLaws
    (setup : DiskTorsionPendulumSetup) : Prop where
  radiusDiameterRelation :
    lengthInMeters setup.diskRadius =
      lengthInMeters setup.diskDiameter_D / 2
  uniformDiskCentralInertia :
    momentOfInertiaInKilogramMetersSquared
        setup.diskMomentOfInertiaAboutCenter =
      massInKilograms setup.diskMass *
        lengthInMeters setup.diskRadius ^ 2 / 2
  scalarParallelAxisLaw :
    momentOfInertiaInKilogramMetersSquared
        setup.diskMomentOfInertiaAboutPivot =
      momentOfInertiaInKilogramMetersSquared
          setup.diskMomentOfInertiaAboutCenter +
        massInKilograms setup.diskMass *
          lengthInMeters setup.diskCenterDistanceBelowPivot ^ 2
  exactGravitationalTorqueLaw :
    ∀ angleRadians,
      torqueInNewtonMeters
          (setup.gravitationalTorqueAboutPivot angleRadians) =
        -(massInKilograms setup.diskMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude *
            lengthInMeters setup.diskCenterDistanceBelowPivot) *
          Real.sin angleRadians
  exactTorsionSpringTorqueLaw :
    ∀ angleRadians,
      torqueInNewtonMeters
          (setup.torsionSpringTorqueAboutPivot angleRadians) =
        -torsionConstantInNewtonMetersPerRadian
            setup.springTorsionConstant * angleRadians
  exactCombinedTorqueLaw :
    ∀ angleRadians,
      torqueInNewtonMeters (setup.combinedTorqueAboutPivot angleRadians) =
        torqueInNewtonMeters
            (setup.gravitationalTorqueAboutPivot angleRadians) +
          torqueInNewtonMeters
            (setup.torsionSpringTorqueAboutPivot angleRadians)
  gravitationalTorqueLinearizationAtEquilibrium :
    HasDerivAt
      (fun angleRadians ↦
        torqueInNewtonMeters
          (setup.gravitationalTorqueAboutPivot angleRadians))
      (-restoringCoefficientInNewtonMetersPerRadian
        setup.gravitationalRestoringCoefficient) 0
  torsionSpringTorqueLinearizationAtEquilibrium :
    HasDerivAt
      (fun angleRadians ↦
        torqueInNewtonMeters
          (setup.torsionSpringTorqueAboutPivot angleRadians))
      (-torsionConstantInNewtonMetersPerRadian
        setup.springTorsionConstant) 0
  combinedTorqueLinearizationAtEquilibrium :
    HasDerivAt
      (fun angleRadians ↦
        torqueInNewtonMeters
          (setup.combinedTorqueAboutPivot angleRadians))
      (-(restoringCoefficientInNewtonMetersPerRadian
            setup.gravitationalRestoringCoefficient +
          torsionConstantInNewtonMetersPerRadian
            setup.springTorsionConstant)) 0
  oscillatorWithoutSpringGeneralizedMass :
    setup.oscillatorWithoutTorsionSpring.m =
      momentOfInertiaInKilogramMetersSquared
        setup.diskMomentOfInertiaAboutPivot
  oscillatorWithoutSpringGeneralizedStiffness :
    setup.oscillatorWithoutTorsionSpring.k =
      restoringCoefficientInNewtonMetersPerRadian
        setup.gravitationalRestoringCoefficient
  periodWithoutSpringLaw :
    timeInSeconds setup.linearizedPeriodWithoutTorsionSpring =
      setup.oscillatorWithoutTorsionSpring.period
  oscillatorWithSpringGeneralizedMass :
    setup.oscillatorWithTorsionSpring.m =
      momentOfInertiaInKilogramMetersSquared
        setup.diskMomentOfInertiaAboutPivot
  additiveRestoringCoefficient :
    setup.oscillatorWithTorsionSpring.k =
      restoringCoefficientInNewtonMetersPerRadian
          setup.gravitationalRestoringCoefficient +
        torsionConstantInNewtonMetersPerRadian
          setup.springTorsionConstant
  periodWithSpringLaw :
    timeInSeconds setup.linearizedPeriodWithTorsionSpring =
      setup.oscillatorWithTorsionSpring.period

/-! ## Derived relation, displayed answers, and current target -/

/-!
Solving the spring-connected generalized-oscillator period law for the
torsion constant gives `κ = I (2π/T_with)² - m g d`.  This remains a derived
conclusion rather than a field of the governing-law interface.
-/
lemma springTorsionConstant_from_connectedPeriod
    (setup : DiskTorsionPendulumSetup)
    (_physical : HasPhysicalDiskTorsionPendulumParameters setup)
    (_laws : SatisfiesDiskTorsionPendulumLaws setup) :
    torsionConstantInNewtonMetersPerRadian setup.springTorsionConstant =
      momentOfInertiaInKilogramMetersSquared
          setup.diskMomentOfInertiaAboutPivot *
        (2 * Real.pi /
          timeInSeconds setup.linearizedPeriodWithTorsionSpring) ^ 2 -
      restoringCoefficientInNewtonMetersPerRadian
        setup.gravitationalRestoringCoefficient := by
  let oscillator := setup.oscillatorWithTorsionSpring
  have hfrequency :
      2 * Real.pi /
          timeInSeconds setup.linearizedPeriodWithTorsionSpring =
        setup.oscillatorWithTorsionSpring.ω := by
    rw [_laws.periodWithSpringLaw,
      ClassicalMechanics.HarmonicOscillator.period_eq]
    field_simp [setup.oscillatorWithTorsionSpring.ω_ne_zero,
      Real.pi_ne_zero]
  have hfrequency_sq := oscillator.ω_sq
  rw [hfrequency]
  change torsionConstantInNewtonMetersPerRadian
      setup.springTorsionConstant =
    momentOfInertiaInKilogramMetersSquared
        setup.diskMomentOfInertiaAboutPivot * oscillator.ω ^ 2 -
      restoringCoefficientInNewtonMetersPerRadian
        setup.gravitationalRestoringCoefficient
  rw [hfrequency_sq]
  rw [← _laws.oscillatorWithSpringGeneralizedMass,
    _laws.additiveRestoringCoefficient]
  dsimp [oscillator]
  field_simp [oscillator.m_ne_zero]
  ring

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed torsion constants, in newton meters per radian. -/
def AnswerChoice.newtonMetersPerRadian : AnswerChoice → ℝ
  | .A => 165 / 10
  | .B => 175 / 10
  | .C => 185 / 10
  | .D => 195 / 10

/-- The answer label recorded by the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with a torsion constant displayed to the nearest tenth. -/
def MatchesDisplayedTorsionConstant
    (torsionConstant : TorsionConstantQuantity)
    (choice : AnswerChoice) : Prop :=
  |torsionConstantInNewtonMetersPerRadian torsionConstant -
      choice.newtonMetersPerRadian| < 1 / 20

/-- The selected value is strictly closer than every distinct displayed value. -/
def IsUniqueClosestTorsionConstantChoice
    (torsionConstant : TorsionConstantQuantity)
    (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |torsionConstantInNewtonMetersPerRadian torsionConstant -
        choice.newtonMetersPerRadian| <
      |torsionConstantInNewtonMetersPerRadian torsionConstant -
        other.newtonMetersPerRadian|

/-!
For the image-grounded lever arm `d = L + D/2 = 0.970 m`, the disk's pivot
inertia and the two period laws determine a torsion constant of approximately
`18.49 N m/rad`.  It rounds to `18.5 N m/rad` and is uniquely closest to
recorded answer C.

This formalizes blueprint label `thm:physics:phyx_mini_0270:target`.
-/
theorem diskTorsionPendulumConstant_matches_recordedAnswerC
    (setup : DiskTorsionPendulumSetup)
    (_figure : MatchesPrimaryDiskPendulumFigure setup)
    (_data : MatchesDiskTorsionPendulumProblemData setup)
    (_physical : HasPhysicalDiskTorsionPendulumParameters setup)
    (_laws : SatisfiesDiskTorsionPendulumLaws setup) :
    MatchesDisplayedTorsionConstant
        setup.springTorsionConstant recordedAnswerChoice ∧
      IsUniqueClosestTorsionConstantChoice
        setup.springTorsionConstant recordedAnswerChoice := by
  have hRadius :
      lengthInMeters setup.diskRadius = 21 / 100 := by
    rw [_laws.radiusDiameterRelation, _data.diskDiameterMeters]
    norm_num
  have hCenterDistance :
      lengthInMeters setup.diskCenterDistanceBelowPivot = 97 / 100 := by
    rw [_figure.centerLeverArmGeometry, _data.rodLengthMeters, hRadius]
    norm_num
  have hCentralInertia :
      momentOfInertiaInKilogramMetersSquared
          setup.diskMomentOfInertiaAboutCenter =
        441 / 8000 := by
    rw [_laws.uniformDiskCentralInertia, _data.diskMassKilograms,
      hRadius]
    norm_num
  have hPivotInertia :
      momentOfInertiaInKilogramMetersSquared
          setup.diskMomentOfInertiaAboutPivot =
        19259 / 8000 := by
    rw [_laws.scalarParallelAxisLaw, hCentralInertia,
      _data.diskMassKilograms, hCenterDistance]
    norm_num
  have hGravitationalDerivative :
      HasDerivAt
        (fun angleRadians ↦
          torqueInNewtonMeters
            (setup.gravitationalTorqueAboutPivot angleRadians))
        (-(massInKilograms setup.diskMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude *
            lengthInMeters setup.diskCenterDistanceBelowPivot)) 0 := by
    have h :=
      (Real.hasDerivAt_sin 0).const_mul
        (-(massInKilograms setup.diskMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude *
            lengthInMeters setup.diskCenterDistanceBelowPivot))
    simpa only [Real.cos_zero, mul_one] using
      h.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun angleRadians ↦
          _laws.exactGravitationalTorqueLaw angleRadians)
  have hGravitationalCoefficient :
      restoringCoefficientInNewtonMetersPerRadian
          setup.gravitationalRestoringCoefficient =
        4753 / 200 := by
    have hDerivativeUniqueness :=
      hGravitationalDerivative.unique
        _laws.gravitationalTorqueLinearizationAtEquilibrium
    rw [_data.diskMassKilograms, _data.standardGravity,
      hCenterDistance] at hDerivativeUniqueness
    norm_num at hDerivativeUniqueness ⊢
    linarith only [hDerivativeUniqueness]
  have oscillatorPeriodIdentity
      (oscillator : ClassicalMechanics.HarmonicOscillator) :
      oscillator.period ^ 2 * oscillator.k =
        (2 * Real.pi) ^ 2 * oscillator.m := by
    rw [ClassicalMechanics.HarmonicOscillator.period_eq]
    field_simp [oscillator.ω_ne_zero]
    rw [oscillator.ω_sq]
    field_simp [oscillator.m_ne_zero]
  have hWithoutSpring :=
    oscillatorPeriodIdentity setup.oscillatorWithoutTorsionSpring
  rw [← _laws.periodWithoutSpringLaw,
    _laws.oscillatorWithoutSpringGeneralizedStiffness,
    _laws.oscillatorWithoutSpringGeneralizedMass,
    hGravitationalCoefficient, hPivotInertia] at hWithoutSpring
  have hWithSpring :=
    oscillatorPeriodIdentity setup.oscillatorWithTorsionSpring
  rw [← _laws.periodWithSpringLaw,
    _laws.additiveRestoringCoefficient,
    _laws.oscillatorWithSpringGeneralizedMass,
    hGravitationalCoefficient, hPivotInertia] at hWithSpring
  have hPeriodReduction :
      timeInSeconds setup.linearizedPeriodWithTorsionSpring =
        timeInSeconds setup.linearizedPeriodWithoutTorsionSpring -
          1 / 2 := by
    rw [← _data.periodReductionSeconds]
    linarith only [_data.measuredPeriodReduction]
  have hRestoringBalance :
      (timeInSeconds setup.linearizedPeriodWithoutTorsionSpring -
          1 / 2) ^ 2 *
          (4753 / 200 +
            torsionConstantInNewtonMetersPerRadian
              setup.springTorsionConstant) =
        timeInSeconds setup.linearizedPeriodWithoutTorsionSpring ^ 2 *
          (4753 / 200) := by
    rw [← hPeriodReduction]
    exact hWithSpring.trans hWithoutSpring.symm
  have arctanLower (x : ℝ) (hx : 0 ≤ x) :
      x - x ^ 3 / 3 + x ^ 5 / 5 - x ^ 7 / 7 ≤
        Real.arctan x := by
    let f : ℝ → ℝ := fun y ↦
      Real.arctan y - (y - y ^ 3 / 3 + y ^ 5 / 5 - y ^ 7 / 7)
    have hf (y : ℝ) :
        HasDerivAt f (y ^ 8 / (1 + y ^ 2)) y := by
      dsimp [f]
      convert (Real.hasDerivAt_arctan y).sub
        ((((hasDerivAt_id y).sub
          (((hasDerivAt_id y).pow 3).div_const 3)).add
            (((hasDerivAt_id y).pow 5).div_const 5)).sub
              (((hasDerivAt_id y).pow 7).div_const 7)) using 1
      all_goals first | rfl |
        (simp only [id_eq]; field_simp; ring)
    have hMonotone : Monotone f :=
      monotone_of_hasDerivAt_nonneg hf (fun y ↦ by positivity)
    have h := hMonotone hx
    simpa [f] using h
  have arctanUpper (x : ℝ) (hx : 0 ≤ x) :
      Real.arctan x ≤
        x - x ^ 3 / 3 + x ^ 5 / 5 - x ^ 7 / 7 + x ^ 9 / 9 := by
    let f : ℝ → ℝ := fun y ↦
      y - y ^ 3 / 3 + y ^ 5 / 5 - y ^ 7 / 7 + y ^ 9 / 9 -
        Real.arctan y
    have hf (y : ℝ) :
        HasDerivAt f (y ^ 10 / (1 + y ^ 2)) y := by
      dsimp [f]
      convert (((((hasDerivAt_id y).sub
        (((hasDerivAt_id y).pow 3).div_const 3)).add
          (((hasDerivAt_id y).pow 5).div_const 5)).sub
            (((hasDerivAt_id y).pow 7).div_const 7)).add
              (((hasDerivAt_id y).pow 9).div_const 9)).sub
                (Real.hasDerivAt_arctan y) using 1
      all_goals first | rfl |
        (simp only [id_eq]; field_simp; ring)
    have hMonotone : Monotone f :=
      monotone_of_hasDerivAt_nonneg hf (fun y ↦ by positivity)
    have h := hMonotone hx
    simpa [f] using h
  have hMachin := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have hLowerFive := arctanLower (1 / 5) (by norm_num)
  have hUpperFive := arctanUpper (1 / 5) (by norm_num)
  have hLowerTwoThirtyNine := arctanLower (1 / 239) (by norm_num)
  have hUpperTwoThirtyNine := arctanUpper (1 / 239) (by norm_num)
  have hPiLower : (3.1415 : ℝ) < Real.pi := by
    norm_num [inv_eq_one_div] at hMachin hLowerFive hUpperTwoThirtyNine ⊢
    linarith only [hMachin, hLowerFive, hUpperTwoThirtyNine]
  have hPiUpper : Real.pi < (3.1416 : ℝ) := by
    norm_num [inv_eq_one_div] at hMachin hUpperFive hLowerTwoThirtyNine ⊢
    linarith only [hMachin, hUpperFive, hLowerTwoThirtyNine]
  have hPiSquareLower : (3.1415 : ℝ) ^ 2 < Real.pi ^ 2 := by
    have hProduct :=
      mul_pos (sub_pos.mpr hPiLower)
        (by nlinarith only [Real.pi_pos] : 0 < Real.pi + 3.1415)
    nlinarith only [hProduct]
  have hPiSquareUpper : Real.pi ^ 2 < (3.1416 : ℝ) ^ 2 := by
    have hProduct :=
      mul_pos (sub_pos.mpr hPiUpper)
        (by nlinarith only [Real.pi_pos] : 0 < 3.1416 + Real.pi)
    nlinarith only [hProduct]
  have hPeriodBounds :
      1999 / 1000 <
          timeInSeconds setup.linearizedPeriodWithoutTorsionSpring ∧
        timeInSeconds setup.linearizedPeriodWithoutTorsionSpring < 2 := by
    constructor
    · by_contra hNot
      have hPeriodUpper :
          timeInSeconds setup.linearizedPeriodWithoutTorsionSpring ≤
            1999 / 1000 := le_of_not_gt hNot
      have hProduct :=
        mul_nonneg (sub_nonneg.mpr hPeriodUpper)
          (by
            nlinarith only [_physical.periodWithoutSpringPositive] :
              0 ≤ 1999 / 1000 +
                timeInSeconds
                  setup.linearizedPeriodWithoutTorsionSpring)
      nlinarith only [hWithoutSpring, hPiSquareLower, hProduct]
    · by_contra hNot
      have hPeriodLower :
          2 ≤ timeInSeconds
              setup.linearizedPeriodWithoutTorsionSpring :=
        le_of_not_gt hNot
      have hProduct :=
        mul_nonneg (sub_nonneg.mpr hPeriodLower)
          (by
            nlinarith only [_physical.periodWithoutSpringPositive] :
              0 ≤
                timeInSeconds
                    setup.linearizedPeriodWithoutTorsionSpring + 2)
      nlinarith only [hWithoutSpring, hPiSquareUpper, hProduct]
  have hSolvedBalance :
      torsionConstantInNewtonMetersPerRadian
          setup.springTorsionConstant *
          (timeInSeconds setup.linearizedPeriodWithoutTorsionSpring -
            1 / 2) ^ 2 =
        (4753 / 200) *
          (timeInSeconds setup.linearizedPeriodWithoutTorsionSpring -
            1 / 4) := by
    nlinarith only [hRestoringBalance]
  have hPeriodWithSquarePositive :
      0 <
        (timeInSeconds setup.linearizedPeriodWithoutTorsionSpring -
          1 / 2) ^ 2 :=
    sq_pos_of_pos (by nlinarith only [hPeriodBounds.1])
  have hUpperFactor :
      0 <
        (185 / 10 : ℝ) *
            (timeInSeconds setup.linearizedPeriodWithoutTorsionSpring +
              1999 / 1000 - 1) -
          4753 / 200 := by
    nlinarith only [hPeriodBounds.1]
  have hUpperProduct :
      0 <
        (timeInSeconds setup.linearizedPeriodWithoutTorsionSpring -
          1999 / 1000) *
          ((185 / 10 : ℝ) *
              (timeInSeconds setup.linearizedPeriodWithoutTorsionSpring +
                1999 / 1000 - 1) -
            4753 / 200) :=
    mul_pos (by linarith only [hPeriodBounds.1]) hUpperFactor
  have hUpperComparison :
      (4753 / 200 : ℝ) *
          (timeInSeconds setup.linearizedPeriodWithoutTorsionSpring -
            1 / 4) <
        185 / 10 *
          (timeInSeconds setup.linearizedPeriodWithoutTorsionSpring -
            1 / 2) ^ 2 := by
    nlinarith only [hUpperProduct]
  have hLowerFactor :
      0 <
        (1845 / 100 : ℝ) *
            (timeInSeconds setup.linearizedPeriodWithoutTorsionSpring + 1) -
          4753 / 200 := by
    nlinarith only [hPeriodBounds.1]
  have hLowerProduct :
      (timeInSeconds setup.linearizedPeriodWithoutTorsionSpring - 2) *
          ((1845 / 100 : ℝ) *
              (timeInSeconds setup.linearizedPeriodWithoutTorsionSpring + 1) -
            4753 / 200) <
        0 :=
    mul_neg_of_neg_of_pos (by linarith only [hPeriodBounds.2]) hLowerFactor
  have hLowerComparison :
      1845 / 100 *
          (timeInSeconds setup.linearizedPeriodWithoutTorsionSpring -
            1 / 2) ^ 2 <
        (4753 / 200 : ℝ) *
          (timeInSeconds setup.linearizedPeriodWithoutTorsionSpring -
            1 / 4) := by
    nlinarith only [hLowerProduct]
  have hTorsionBounds :
      1845 / 100 <
          torsionConstantInNewtonMetersPerRadian
            setup.springTorsionConstant ∧
        torsionConstantInNewtonMetersPerRadian
            setup.springTorsionConstant <
          185 / 10 := by
    constructor
    · by_contra hNot
      have hTorsionUpper :
          torsionConstantInNewtonMetersPerRadian
              setup.springTorsionConstant ≤
            1845 / 100 := le_of_not_gt hNot
      have hProduct :=
        mul_le_mul_of_nonneg_right hTorsionUpper
          hPeriodWithSquarePositive.le
      nlinarith only [hSolvedBalance, hLowerComparison, hProduct]
    · by_contra hNot
      have hTorsionLower :
          185 / 10 ≤
            torsionConstantInNewtonMetersPerRadian
              setup.springTorsionConstant :=
        le_of_not_gt hNot
      have hProduct :=
        mul_le_mul_of_nonneg_right hTorsionLower
          hPeriodWithSquarePositive.le
      nlinarith only [hSolvedBalance, hUpperComparison, hProduct]
  constructor
  · change
      |torsionConstantInNewtonMetersPerRadian
          setup.springTorsionConstant - 185 / 10| < 1 / 20
    rw [abs_of_nonpos (by linarith only [hTorsionBounds.2])]
    linarith only [hTorsionBounds.1]
  · change
      ∀ other, other ≠ AnswerChoice.C →
        |torsionConstantInNewtonMetersPerRadian
            setup.springTorsionConstant - 185 / 10| <
          |torsionConstantInNewtonMetersPerRadian
              setup.springTorsionConstant -
            other.newtonMetersPerRadian|
    intro other hOther
    rw [abs_of_nonpos (by linarith only [hTorsionBounds.2])]
    cases other with
    | A =>
        simp only [AnswerChoice.newtonMetersPerRadian, neg_sub]
        rw [abs_of_nonneg (by linarith only [hTorsionBounds.1])]
        linarith only [hTorsionBounds.1, hTorsionBounds.2]
    | B =>
        simp only [AnswerChoice.newtonMetersPerRadian, neg_sub]
        rw [abs_of_nonneg (by linarith only [hTorsionBounds.1])]
        linarith only [hTorsionBounds.1, hTorsionBounds.2]
    | C => exact (hOther rfl).elim
    | D =>
        simp only [AnswerChoice.newtonMetersPerRadian, neg_sub]
        rw [abs_of_nonpos (by linarith only [hTorsionBounds.2])]
        linarith only [hTorsionBounds.1, hTorsionBounds.2]

end PhyXMiniProblems.ProblemPhyXMini0270
