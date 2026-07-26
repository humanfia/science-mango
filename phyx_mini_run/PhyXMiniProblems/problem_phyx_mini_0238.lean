import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0238

open Dimension

/-!
# Period of a leaking cubical pendulum

A negligibly light cubical container is suspended from a light string.  It is
initially full of a uniform liquid, then drains at constant mass-flow rate
through its bottom.  The liquid level and hence the liquid's center of mass
move while it drains.  The stated scale separation `Lᵢ ≫ a` permits the
usual long-string, small-angle simple-pendulum approximation.

Physical lengths, volumes, masses, density, mass-flow rate, acceleration, and
time are represented by Physlib `Dimensionful` quantities.  Real numbers are
used only for coherent SI readouts, time coordinates in seconds, signed error
readouts, dimensionless scale ratios, and displayed formulas.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- The physical dimension of volume, `L³`. -/
def volumeDimension : Dimension := L𝓭 * L𝓭 * L𝓭

/-- The physical dimension of mass density, `M L⁻³`. -/
def massDensityDimension : Dimension :=
  M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The physical dimension of mass flow rate, `M T⁻¹`. -/
def massFlowRateDimension : Dimension := M𝓭 * T𝓭⁻¹

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical volume. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim volumeDimension NNReal)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical mass density. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim massDensityDimension NNReal)

/-- A nonnegative magnitude of mass discharged per unit time. -/
abbrev MassFlowRateQuantity : Type :=
  Dimensionful (WithDim massFlowRateDimension NNReal)

/-- A nonnegative physical acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def quantitySIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  quantitySIReadout length

/-- Cubic-meter readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  quantitySIReadout volume

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  quantitySIReadout mass

/-- Kilogram-per-cubic-meter readout of a mass density. -/
def densityInKilogramsPerCubicMeter (density : MassDensityQuantity) : ℝ :=
  quantitySIReadout density

/-- Kilogram-per-second readout of the positive outflow-rate magnitude. -/
def massFlowRateInKilogramsPerSecond (rate : MassFlowRateQuantity) : ℝ :=
  quantitySIReadout rate

/-- Meter-per-second-squared readout of a physical acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  quantitySIReadout acceleration

/-- Second readout of a physical duration. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  quantitySIReadout time

/-! ## Source figure and physical apparatus -/

/-- The two configurations displayed side by side in the source figure. -/
inductive FigurePanel where
  | initiallyFull
  | partiallyDrained
  deriving DecidableEq, Repr

/-- The four labels printed on the source figure. -/
inductive FigureLabel where
  | cubeSideA
  | initialPendulumLengthLi
  | liquidHeightH
  | instantaneousPendulumLengthL
  deriving DecidableEq, Repr

/-- Physical meaning of a length marker in the source figure. -/
inductive FigureLengthRole where
  | cubeSide
  | pivotToInitialCenterOfMass
  | bottomToLiquidSurface
  | pivotToInstantaneousCenterOfMass
  deriving DecidableEq, Repr

/-- Meaning assigned to each printed length label. -/
def FigureLabel.lengthRole : FigureLabel → FigureLengthRole
  | .cubeSideA => .cubeSide
  | .initialPendulumLengthLi => .pivotToInitialCenterOfMass
  | .liquidHeightH => .bottomToLiquidSurface
  | .instantaneousPendulumLengthL => .pivotToInstantaneousCenterOfMass

/-- Categorical evidence visible in the primary image. -/
structure PendulumFigure where
  showsPanel : FigurePanel → Bool
  showsLabel : FigureLabel → Bool
  cubeSuspendedFromCeiling : FigurePanel → Bool
  initialCubeShownFull : Bool
  laterCubeShownPartiallyFilled : Bool

/-- The outlet location stated in the prose. -/
inductive OutletLocation where
  | containerBottom
  deriving DecidableEq, Repr

/-- The idealized direction of the expelled liquid relative to the pendulum. -/
inductive OutflowDirection where
  | alongPendulumAxis
  deriving DecidableEq, Repr

/--
All physical quantities in the draining experiment.

The trajectory arguments are SI time coordinates in seconds.  The
`supportStringLength` runs from the fixed pivot to the top of the cube, whereas
both pendulum-length fields run from the pivot to the liquid's center of mass,
as specified by the problem statement.
-/
structure LeakingCubePendulumSetup where
  figure : PendulumFigure
  containerSide : LengthQuantity
  containerVolume : VolumeQuantity
  containerMass : MassQuantity
  supportStringLength : LengthQuantity
  supportStringMass : MassQuantity
  liquidDensity : MassDensityQuantity
  initialPendulumLength : LengthQuantity
  liquidHeightAtSeconds : ℝ → LengthQuantity
  instantaneousPendulumLengthAtSeconds : ℝ → LengthQuantity
  remainingLiquidVolumeAtSeconds : ℝ → VolumeQuantity
  remainingLiquidMassAtSeconds : ℝ → MassQuantity
  massOutflowRateMagnitude : MassFlowRateQuantity
  emptyingTime : TimeQuantity
  gravity : AccelerationQuantity
  oscillationAmplitudeRadians : NNReal
  smallAngleCutoffRadians : NNReal
  smallAngleRemainderCoefficient : NNReal
  localPeriodAtSeconds : ℝ → TimeQuantity
  smallAnglePeriodRemainderSecondsAt : ℝ → ℝ
  longStringRatioBound : ℝ
  outletLocation : OutletLocation
  outflowDirection : OutflowDirection

/-! ## Figure/data readouts and admissibility -/

/-- The primary image contains both configurations and all four source labels. -/
def MatchesPrimaryFigure (setup : LeakingCubePendulumSetup) : Prop :=
  setup.figure.showsPanel .initiallyFull = true ∧
    setup.figure.showsPanel .partiallyDrained = true ∧
    setup.figure.showsLabel .cubeSideA = true ∧
    setup.figure.showsLabel .initialPendulumLengthLi = true ∧
    setup.figure.showsLabel .liquidHeightH = true ∧
    setup.figure.showsLabel .instantaneousPendulumLengthL = true ∧
    setup.figure.cubeSuspendedFromCeiling .initiallyFull = true ∧
    setup.figure.cubeSuspendedFromCeiling .partiallyDrained = true ∧
    setup.figure.initialCubeShownFull = true ∧
    setup.figure.laterCubeShownPartiallyFilled = true

/--
Readouts stated in the prose: a cube of volume `a³`, initially full, with
`Lᵢ` measured to the initial liquid center of mass; a bottom outlet; and
complete emptying.  Zero container and string masses encode the word "light"
in the ideal model.  No period value or period approximation occurs here.
-/
def MatchesProblemData (setup : LeakingCubePendulumSetup) : Prop :=
  volumeInCubicMeters setup.containerVolume =
      lengthInMeters setup.containerSide ^ 3 ∧
    massInKilograms setup.containerMass = 0 ∧
    massInKilograms setup.supportStringMass = 0 ∧
    lengthInMeters (setup.liquidHeightAtSeconds 0) =
      lengthInMeters setup.containerSide ∧
    volumeInCubicMeters (setup.remainingLiquidVolumeAtSeconds 0) =
      volumeInCubicMeters setup.containerVolume ∧
    lengthInMeters (setup.instantaneousPendulumLengthAtSeconds 0) =
      lengthInMeters setup.initialPendulumLength ∧
    lengthInMeters
        (setup.liquidHeightAtSeconds (timeInSeconds setup.emptyingTime)) = 0 ∧
    volumeInCubicMeters
        (setup.remainingLiquidVolumeAtSeconds
          (timeInSeconds setup.emptyingTime)) = 0 ∧
    massInKilograms
        (setup.remainingLiquidMassAtSeconds
          (timeInSeconds setup.emptyingTime)) = 0 ∧
    setup.outletLocation = .containerBottom ∧
    setup.outflowDirection = .alongPendulumAxis

/-- SI times from release up to, but not including, the massless empty state. -/
def DuringEmptying (setup : LeakingCubePendulumSetup) (tSeconds : ℝ) : Prop :=
  tSeconds ∈ Set.Ico 0 (timeInSeconds setup.emptyingTime)

/--
Positivity and geometric bounds needed by the mechanical model.  The
dimensionless ratio bound witnesses the qualitative condition `Lᵢ ≫ a`.
-/
structure HasPhysicalParameters (setup : LeakingCubePendulumSetup) : Prop where
  containerSide_pos : 0 < lengthInMeters setup.containerSide
  containerVolume_pos : 0 < volumeInCubicMeters setup.containerVolume
  liquidDensity_pos :
    0 < densityInKilogramsPerCubicMeter setup.liquidDensity
  initialPendulumLength_pos :
    0 < lengthInMeters setup.initialPendulumLength
  massOutflowRate_pos :
    0 < massFlowRateInKilogramsPerSecond setup.massOutflowRateMagnitude
  emptyingTime_pos : 0 < timeInSeconds setup.emptyingTime
  gravity_pos : 0 < accelerationInMetersPerSecondSquared setup.gravity
  smallAngleCutoff_pos : 0 < (setup.smallAngleCutoffRadians : ℝ)
  smallAngleCutoff_lt_one : (setup.smallAngleCutoffRadians : ℝ) < 1
  oscillationAmplitude_within_cutoff :
    (setup.oscillationAmplitudeRadians : ℝ) ≤
      (setup.smallAngleCutoffRadians : ℝ)
  longStringRatioBound_pos : 0 < setup.longStringRatioBound
  longStringRatioBound_lt_one : setup.longStringRatioBound < 1
  longStringScaleSeparation :
    lengthInMeters setup.containerSide /
        lengthInMeters setup.initialPendulumLength ≤
      setup.longStringRatioBound
  liquidHeight_bounds : ∀ tSeconds : ℝ,
    DuringEmptying setup tSeconds →
      lengthInMeters (setup.liquidHeightAtSeconds tSeconds) ∈
        Set.Icc 0 (lengthInMeters setup.containerSide)
  instantaneousPendulumLength_pos : ∀ tSeconds : ℝ,
    DuringEmptying setup tSeconds →
      0 < lengthInMeters
        (setup.instantaneousPendulumLengthAtSeconds tSeconds)
  localPeriod_pos : ∀ tSeconds : ℝ,
    DuringEmptying setup tSeconds →
      0 < timeInSeconds (setup.localPeriodAtSeconds tSeconds)

/-! ## Governing geometry, draining, and pendulum laws -/

/--
The period in seconds of the linearized, frozen-length simple-pendulum model.
This is an approximating term, not the definition of the measured local
period stored in `LeakingCubePendulumSetup`.
-/
def linearizedSimplePendulumPeriodSeconds
    (length : LengthQuantity) (gravity : AccelerationQuantity) : ℝ :=
  2 * Real.pi *
    Real.sqrt
      (lengthInMeters length /
        accelerationInMetersPerSecondSquared gravity)

/--
The liquid is uniform and fills a square horizontal cross-section.  Its volume
is `a² h`, its mass is density times volume, and its positive constant
outflow-rate magnitude gives `M(t) = M(0) - q t` up to the emptying time.

The center-of-mass equations use that a uniform liquid column has its center
at half its fill height.  The last two fields give a local small-angle
contract: at each frozen time, the physical local period is the linearized
period at the instantaneous center-of-mass length plus a signed remainder,
and that remainder is explicitly `O(amplitude²)`.  In particular, they do not
identify the physical period with the answer-choice formula at `Lᵢ`.
-/
structure ObeysLeakingSimplePendulumLaws
    (setup : LeakingCubePendulumSetup) : Prop where
  liquidVolumeFromHeight : ∀ tSeconds : ℝ,
    DuringEmptying setup tSeconds →
      volumeInCubicMeters
          (setup.remainingLiquidVolumeAtSeconds tSeconds) =
        lengthInMeters setup.containerSide ^ 2 *
          lengthInMeters (setup.liquidHeightAtSeconds tSeconds)
  liquidMassFromDensity : ∀ tSeconds : ℝ,
    DuringEmptying setup tSeconds →
      massInKilograms (setup.remainingLiquidMassAtSeconds tSeconds) =
        densityInKilogramsPerCubicMeter setup.liquidDensity *
          volumeInCubicMeters
            (setup.remainingLiquidVolumeAtSeconds tSeconds)
  constantMassOutflow : ∀ tSeconds : ℝ,
    DuringEmptying setup tSeconds →
      massInKilograms (setup.remainingLiquidMassAtSeconds tSeconds) =
        massInKilograms (setup.remainingLiquidMassAtSeconds 0) -
          massFlowRateInKilogramsPerSecond
              setup.massOutflowRateMagnitude * tSeconds
  initialCenterOfMassGeometry :
    lengthInMeters setup.initialPendulumLength =
      lengthInMeters setup.supportStringLength +
        lengthInMeters setup.containerSide / 2
  instantaneousCenterOfMassGeometry : ∀ tSeconds : ℝ,
    DuringEmptying setup tSeconds →
      lengthInMeters
          (setup.instantaneousPendulumLengthAtSeconds tSeconds) =
        lengthInMeters setup.supportStringLength +
          lengthInMeters setup.containerSide -
            lengthInMeters (setup.liquidHeightAtSeconds tSeconds) / 2
  localPeriodExpansion : ∀ tSeconds : ℝ,
    DuringEmptying setup tSeconds →
      timeInSeconds (setup.localPeriodAtSeconds tSeconds) =
        linearizedSimplePendulumPeriodSeconds
            (setup.instantaneousPendulumLengthAtSeconds tSeconds)
            setup.gravity +
          setup.smallAnglePeriodRemainderSecondsAt tSeconds
  smallAngleRemainderBound : ∀ tSeconds : ℝ,
    DuringEmptying setup tSeconds →
      |setup.smallAnglePeriodRemainderSecondsAt tSeconds| ≤
        (setup.smallAngleRemainderCoefficient : ℝ) *
          (setup.oscillationAmplitudeRadians : ℝ) ^ 2 *
            linearizedSimplePendulumPeriodSeconds
              (setup.instantaneousPendulumLengthAtSeconds tSeconds)
              setup.gravity

/-! ## Displayed answer data and formalization target -/

/-- Labels of the four answer choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/--
The scalar expressions printed beside the four choices after substituting SI
readouts for `Lᵢ` and `g`.  This records the source display; in particular,
some distractors do not have the physical dimension of time.
-/
def AnswerChoice.displayedScalar
    (choice : AnswerChoice) (initialLength gravity : ℝ) : ℝ :=
  match choice with
  | .A => 2 * Real.pi * Real.sqrt (initialLength / gravity ^ 2)
  | .B => Real.pi * Real.sqrt (initialLength / gravity)
  | .C => 2 * Real.pi * Real.sqrt (gravity / initialLength)
  | .D => 2 * Real.pi * Real.sqrt (initialLength / gravity)

/-- The dataset records answer D. -/
def recordedAnswerChoice : AnswerChoice := .D

/--
The explicit small-angle contribution to the local-period error budget.  It
vanishes quadratically with the dimensionless oscillation amplitude.
-/
def smallAnglePeriodErrorBudgetSeconds
    (setup : LeakingCubePendulumSetup) (tSeconds : ℝ) : ℝ :=
  (setup.smallAngleRemainderCoefficient : ℝ) *
    (setup.oscillationAmplitudeRadians : ℝ) ^ 2 *
      linearizedSimplePendulumPeriodSeconds
        (setup.instantaneousPendulumLengthAtSeconds tSeconds) setup.gravity

/--
The long-string error budget obtained from the center-of-mass displacement
`0 ≤ L(t) - Lᵢ ≤ a/2` and concavity of the square root.  Relative to the
choice-D leading term it is first order in the dimensionless ratio `a/Lᵢ`.
-/
def longStringPeriodErrorBudgetSeconds
    (setup : LeakingCubePendulumSetup) : ℝ :=
  linearizedSimplePendulumPeriodSeconds
      setup.initialPendulumLength setup.gravity *
    (lengthInMeters setup.containerSide /
      (4 * lengthInMeters setup.initialPendulumLength))

/--
Answer D is the linearized frozen-length period at the initial center of mass.
For the physical local period during emptying, the theorem asserts an explicit
error bound instead of a global exact equality: the first term is the
small-angle remainder and the second is the long-string center-of-mass-drift
allowance.  Both vanish in their respective ideal limits.

This formalizes `thm:physics:phyx_mini_0238:target`.
-/
theorem period_of_leaking_cubical_pendulum
    (setup : LeakingCubePendulumSetup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_data : MatchesProblemData setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : ObeysLeakingSimplePendulumLaws setup) :
    AnswerChoice.displayedScalar recordedAnswerChoice
        (lengthInMeters setup.initialPendulumLength)
        (accelerationInMetersPerSecondSquared setup.gravity) =
      linearizedSimplePendulumPeriodSeconds
        setup.initialPendulumLength setup.gravity ∧
      ∀ tSeconds : ℝ, DuringEmptying setup tSeconds →
        |timeInSeconds (setup.localPeriodAtSeconds tSeconds) -
            AnswerChoice.displayedScalar recordedAnswerChoice
              (lengthInMeters setup.initialPendulumLength)
              (accelerationInMetersPerSecondSquared setup.gravity)| ≤
          smallAnglePeriodErrorBudgetSeconds setup tSeconds +
            longStringPeriodErrorBudgetSeconds setup := by
  have h_choice :
      AnswerChoice.displayedScalar recordedAnswerChoice
          (lengthInMeters setup.initialPendulumLength)
          (accelerationInMetersPerSecondSquared setup.gravity) =
        linearizedSimplePendulumPeriodSeconds
          setup.initialPendulumLength setup.gravity := by
    rfl
  refine ⟨h_choice, ?_⟩
  intro tSeconds h_during
  have h_height_bounds :=
    h_physical.liquidHeight_bounds tSeconds h_during
  have h_height_nonneg :
      0 ≤ lengthInMeters (setup.liquidHeightAtSeconds tSeconds) :=
    h_height_bounds.1
  have h_height_le_side :
      lengthInMeters (setup.liquidHeightAtSeconds tSeconds) ≤
        lengthInMeters setup.containerSide :=
    h_height_bounds.2
  have h_initial_length_pos :
      0 < lengthInMeters setup.initialPendulumLength :=
    h_physical.initialPendulumLength_pos
  have h_instantaneous_length_pos :
      0 <
        lengthInMeters
          (setup.instantaneousPendulumLengthAtSeconds tSeconds) :=
    h_physical.instantaneousPendulumLength_pos tSeconds h_during
  have h_gravity_pos :
      0 < accelerationInMetersPerSecondSquared setup.gravity :=
    h_physical.gravity_pos
  have h_initial_geometry := h_laws.initialCenterOfMassGeometry
  have h_instantaneous_geometry :=
    h_laws.instantaneousCenterOfMassGeometry tSeconds h_during
  have h_length_lower :
      lengthInMeters setup.initialPendulumLength ≤
        lengthInMeters
          (setup.instantaneousPendulumLengthAtSeconds tSeconds) := by
    rw [h_initial_geometry, h_instantaneous_geometry]
    linarith
  have h_length_upper :
      lengthInMeters
          (setup.instantaneousPendulumLengthAtSeconds tSeconds) ≤
        lengthInMeters setup.initialPendulumLength +
          lengthInMeters setup.containerSide / 2 := by
    rw [h_initial_geometry, h_instantaneous_geometry]
    linarith
  have h_initial_ratio_pos :
      0 <
        lengthInMeters setup.initialPendulumLength /
          accelerationInMetersPerSecondSquared setup.gravity :=
    div_pos h_initial_length_pos h_gravity_pos
  have h_instantaneous_ratio_pos :
      0 <
        lengthInMeters
            (setup.instantaneousPendulumLengthAtSeconds tSeconds) /
          accelerationInMetersPerSecondSquared setup.gravity :=
    div_pos h_instantaneous_length_pos h_gravity_pos
  have h_sqrt_order :
      Real.sqrt
          (lengthInMeters setup.initialPendulumLength /
            accelerationInMetersPerSecondSquared setup.gravity) ≤
        Real.sqrt
          (lengthInMeters
              (setup.instantaneousPendulumLengthAtSeconds tSeconds) /
            accelerationInMetersPerSecondSquared setup.gravity) := by
    apply Real.sqrt_le_sqrt
    exact
      (div_le_div_iff_of_pos_right h_gravity_pos).2 h_length_lower
  have h_ratio_difference :
      lengthInMeters
            (setup.instantaneousPendulumLengthAtSeconds tSeconds) /
          accelerationInMetersPerSecondSquared setup.gravity -
        lengthInMeters setup.initialPendulumLength /
          accelerationInMetersPerSecondSquared setup.gravity ≤
        lengthInMeters setup.containerSide /
          (2 * accelerationInMetersPerSecondSquared setup.gravity) := by
    rw [← sub_div]
    calc
      (lengthInMeters
              (setup.instantaneousPendulumLengthAtSeconds tSeconds) -
            lengthInMeters setup.initialPendulumLength) /
          accelerationInMetersPerSecondSquared setup.gravity ≤
          (lengthInMeters setup.containerSide / 2) /
            accelerationInMetersPerSecondSquared setup.gravity :=
        (div_le_div_iff_of_pos_right h_gravity_pos).2 (by linarith)
      _ =
          lengthInMeters setup.containerSide /
            (2 * accelerationInMetersPerSecondSquared setup.gravity) := by
        ring
  have h_initial_sqrt_sq :
      Real.sqrt
            (lengthInMeters setup.initialPendulumLength /
              accelerationInMetersPerSecondSquared setup.gravity) ^ 2 =
        lengthInMeters setup.initialPendulumLength /
          accelerationInMetersPerSecondSquared setup.gravity :=
    Real.sq_sqrt (le_of_lt h_initial_ratio_pos)
  have h_instantaneous_sqrt_sq :
      Real.sqrt
            (lengthInMeters
                (setup.instantaneousPendulumLengthAtSeconds tSeconds) /
              accelerationInMetersPerSecondSquared setup.gravity) ^ 2 =
        lengthInMeters
            (setup.instantaneousPendulumLengthAtSeconds tSeconds) /
          accelerationInMetersPerSecondSquared setup.gravity :=
    Real.sq_sqrt (le_of_lt h_instantaneous_ratio_pos)
  have h_scaled_sqrt_difference :
      (Real.sqrt
              (lengthInMeters
                  (setup.instantaneousPendulumLengthAtSeconds tSeconds) /
                accelerationInMetersPerSecondSquared setup.gravity) -
            Real.sqrt
              (lengthInMeters setup.initialPendulumLength /
                accelerationInMetersPerSecondSquared setup.gravity)) *
          (2 *
            Real.sqrt
              (lengthInMeters setup.initialPendulumLength /
                accelerationInMetersPerSecondSquared setup.gravity)) ≤
        lengthInMeters setup.containerSide /
          (2 * accelerationInMetersPerSecondSquared setup.gravity) := by
    nlinarith only [
      h_sqrt_order,
      h_ratio_difference,
      h_initial_sqrt_sq,
      h_instantaneous_sqrt_sq,
      sq_nonneg
        (Real.sqrt
            (lengthInMeters
                (setup.instantaneousPendulumLengthAtSeconds tSeconds) /
              accelerationInMetersPerSecondSquared setup.gravity) -
          Real.sqrt
            (lengthInMeters setup.initialPendulumLength /
              accelerationInMetersPerSecondSquared setup.gravity))]
  have h_scale_pos :
      0 <
        2 *
          Real.sqrt
            (lengthInMeters setup.initialPendulumLength /
              accelerationInMetersPerSecondSquared setup.gravity) := by
    positivity
  have h_scaled_budget :
      (Real.sqrt
              (lengthInMeters setup.initialPendulumLength /
                accelerationInMetersPerSecondSquared setup.gravity) *
            (lengthInMeters setup.containerSide /
              (4 * lengthInMeters setup.initialPendulumLength))) *
          (2 *
            Real.sqrt
              (lengthInMeters setup.initialPendulumLength /
                accelerationInMetersPerSecondSquared setup.gravity)) =
        lengthInMeters setup.containerSide /
          (2 * accelerationInMetersPerSecondSquared setup.gravity) := by
    calc
      (Real.sqrt
              (lengthInMeters setup.initialPendulumLength /
                accelerationInMetersPerSecondSquared setup.gravity) *
            (lengthInMeters setup.containerSide /
              (4 * lengthInMeters setup.initialPendulumLength))) *
          (2 *
            Real.sqrt
              (lengthInMeters setup.initialPendulumLength /
                accelerationInMetersPerSecondSquared setup.gravity)) =
          Real.sqrt
                (lengthInMeters setup.initialPendulumLength /
                  accelerationInMetersPerSecondSquared setup.gravity) ^ 2 *
            (lengthInMeters setup.containerSide /
              (2 * lengthInMeters setup.initialPendulumLength)) := by
        ring
      _ =
          (lengthInMeters setup.initialPendulumLength /
              accelerationInMetersPerSecondSquared setup.gravity) *
            (lengthInMeters setup.containerSide /
              (2 * lengthInMeters setup.initialPendulumLength)) := by
        rw [h_initial_sqrt_sq]
      _ =
          lengthInMeters setup.containerSide /
            (2 * accelerationInMetersPerSecondSquared setup.gravity) := by
        field_simp
  have h_sqrt_difference :
      Real.sqrt
            (lengthInMeters
                (setup.instantaneousPendulumLengthAtSeconds tSeconds) /
              accelerationInMetersPerSecondSquared setup.gravity) -
          Real.sqrt
            (lengthInMeters setup.initialPendulumLength /
              accelerationInMetersPerSecondSquared setup.gravity) ≤
        Real.sqrt
            (lengthInMeters setup.initialPendulumLength /
              accelerationInMetersPerSecondSquared setup.gravity) *
          (lengthInMeters setup.containerSide /
            (4 * lengthInMeters setup.initialPendulumLength)) := by
    apply le_of_mul_le_mul_right ?_ h_scale_pos
    rw [h_scaled_budget]
    exact h_scaled_sqrt_difference
  have h_period_drift_nonneg :
      0 ≤
        linearizedSimplePendulumPeriodSeconds
            (setup.instantaneousPendulumLengthAtSeconds tSeconds)
            setup.gravity -
          linearizedSimplePendulumPeriodSeconds
            setup.initialPendulumLength setup.gravity := by
    apply sub_nonneg.mpr
    unfold linearizedSimplePendulumPeriodSeconds
    exact
      mul_le_mul_of_nonneg_left h_sqrt_order (by positivity)
  have h_period_drift :
      |linearizedSimplePendulumPeriodSeconds
            (setup.instantaneousPendulumLengthAtSeconds tSeconds)
            setup.gravity -
          linearizedSimplePendulumPeriodSeconds
            setup.initialPendulumLength setup.gravity| ≤
        longStringPeriodErrorBudgetSeconds setup := by
    rw [abs_of_nonneg h_period_drift_nonneg]
    unfold linearizedSimplePendulumPeriodSeconds
    unfold longStringPeriodErrorBudgetSeconds
    calc
      2 * Real.pi *
              Real.sqrt
                (lengthInMeters
                    (setup.instantaneousPendulumLengthAtSeconds tSeconds) /
                  accelerationInMetersPerSecondSquared setup.gravity) -
            2 * Real.pi *
              Real.sqrt
                (lengthInMeters setup.initialPendulumLength /
                  accelerationInMetersPerSecondSquared setup.gravity) =
          (2 * Real.pi) *
            (Real.sqrt
                (lengthInMeters
                    (setup.instantaneousPendulumLengthAtSeconds tSeconds) /
                  accelerationInMetersPerSecondSquared setup.gravity) -
              Real.sqrt
                (lengthInMeters setup.initialPendulumLength /
                  accelerationInMetersPerSecondSquared setup.gravity)) := by
        ring
      _ ≤
          (2 * Real.pi) *
            (Real.sqrt
                (lengthInMeters setup.initialPendulumLength /
                  accelerationInMetersPerSecondSquared setup.gravity) *
              (lengthInMeters setup.containerSide /
                (4 * lengthInMeters setup.initialPendulumLength))) :=
        mul_le_mul_of_nonneg_left h_sqrt_difference (by positivity)
      _ =
          (2 * Real.pi *
              Real.sqrt
                (lengthInMeters setup.initialPendulumLength /
                  accelerationInMetersPerSecondSquared setup.gravity)) *
            (lengthInMeters setup.containerSide /
              (4 * lengthInMeters setup.initialPendulumLength)) := by
        ring
  have h_period_expansion :=
    h_laws.localPeriodExpansion tSeconds h_during
  have h_local_remainder :
      timeInSeconds (setup.localPeriodAtSeconds tSeconds) -
          linearizedSimplePendulumPeriodSeconds
            (setup.instantaneousPendulumLengthAtSeconds tSeconds)
            setup.gravity =
        setup.smallAnglePeriodRemainderSecondsAt tSeconds := by
    rw [h_period_expansion]
    ring
  have h_remainder_bound :
      |setup.smallAnglePeriodRemainderSecondsAt tSeconds| ≤
        smallAnglePeriodErrorBudgetSeconds setup tSeconds := by
    simpa [smallAnglePeriodErrorBudgetSeconds] using
      h_laws.smallAngleRemainderBound tSeconds h_during
  calc
    |timeInSeconds (setup.localPeriodAtSeconds tSeconds) -
          AnswerChoice.displayedScalar recordedAnswerChoice
            (lengthInMeters setup.initialPendulumLength)
            (accelerationInMetersPerSecondSquared setup.gravity)| =
        |timeInSeconds (setup.localPeriodAtSeconds tSeconds) -
          linearizedSimplePendulumPeriodSeconds
            setup.initialPendulumLength setup.gravity| := by
      rw [h_choice]
    _ ≤
        |timeInSeconds (setup.localPeriodAtSeconds tSeconds) -
            linearizedSimplePendulumPeriodSeconds
              (setup.instantaneousPendulumLengthAtSeconds tSeconds)
              setup.gravity| +
          |linearizedSimplePendulumPeriodSeconds
              (setup.instantaneousPendulumLengthAtSeconds tSeconds)
              setup.gravity -
            linearizedSimplePendulumPeriodSeconds
              setup.initialPendulumLength setup.gravity| :=
      abs_sub_le _ _ _
    _ =
        |setup.smallAnglePeriodRemainderSecondsAt tSeconds| +
          |linearizedSimplePendulumPeriodSeconds
              (setup.instantaneousPendulumLengthAtSeconds tSeconds)
              setup.gravity -
            linearizedSimplePendulumPeriodSeconds
              setup.initialPendulumLength setup.gravity| := by
      rw [h_local_remainder]
    _ ≤
        smallAnglePeriodErrorBudgetSeconds setup tSeconds +
          longStringPeriodErrorBudgetSeconds setup :=
      add_le_add h_remainder_bound h_period_drift

end PhyXMiniProblems.ProblemPhyXMini0238
