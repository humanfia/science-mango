import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
import Physlib.Units.WithDim.Basic

/-!
# Small-angle period of an off-center uniform disk pendulum

A uniform solid disk of radius `R = 2.35 cm` swings in a vertical plane about
a fixed pivot whose distance from the disk center is `d = 1.75 cm`.  The
primary image places the pivot vertically above the center, draws the radius
arrow from the center to the rim, and marks `d` between the pivot and center
levels.  The curved arrow has heads in both rotational directions.

The disk mass, geometric lengths, gravitational acceleration, moments of
inertia, restoring-torque coefficient, angular velocity, and period are
dimensionful Physlib quantities.  Real numbers are used only for coherent
unit readouts, the dimensionless release angle in radians, and the displayed
multiple-choice values.

The governing-law interface contains the uniform-disk inertia law, the
parallel-axis law, the exact nonlinear sine torque, the linearized
gravitational restoring coefficient, and the generic Physlib
harmonic-oscillator period law.  A separate derivative, little-o, and bounded
remainder contract says precisely in what local sense the nonlinear pendulum
is replaced by the linearized oscillator.  The target is the period of that
linearized model, not an exact finite-amplitude period.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0264

open Dimension Filter Asymptotics

/-! ## Dimensionful quantities and coherent readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical time interval. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative acceleration magnitude, with dimension `L T⁻²`. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A signed angular velocity; radians are dimensionless. -/
abbrev AngularVelocityQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A scalar moment of inertia about the axis normal to the disk plane. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-- A signed torque about the axis normal to the disk plane. -/
abbrev TorqueQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/--
The coefficient multiplying angular displacement in the linearized restoring
torque.  Its dimension is torque, `M L² T⁻²`, because radians are
dimensionless.
-/
abbrev RestoringTorqueCoefficientQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Unit choices in which lengths are read in centimeters. -/
def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical length in meters. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical length in centimeters. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  ((length centimeterUnitChoices).val : ℝ)

/-- Read a physical duration in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Read an acceleration magnitude in meters per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a signed angular velocity in radians per second. -/
def angularVelocityInRadiansPerSecond
    (velocity : AngularVelocityQuantity) : ℝ :=
  (velocity UnitChoices.SI).val

/-- Read a moment of inertia in kilogram meters squared. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Read a signed torque in newton meters. -/
def torqueInNewtonMeters (torque : TorqueQuantity) : ℝ :=
  (torque UnitChoices.SI).val

/-- Read a restoring-torque coefficient in newton meters per radian. -/
def restoringCoefficientInNewtonMeters
    (coefficient : RestoringTorqueCoefficientQuantity) : ℝ :=
  ((coefficient UnitChoices.SI).val : ℝ)

/-! ## Physical roles and primary-image geometry -/

/-- The mass distribution specified for the pendulum body. -/
inductive DiskMassDistribution where
  | uniformSolidDisk
  | unspecified
  deriving DecidableEq, Repr

/-- Plane in which the disk is supported and swings. -/
inductive MotionPlane where
  | vertical
  | other
  deriving DecidableEq, Repr

/-- Distinguished points present in the primary diagram. -/
inductive FigurePoint where
  | pivot
  | diskCenter
  | radiusEndpointOnRim
  deriving DecidableEq, Repr

/-- Text or mathematical labels visible in the primary diagram. -/
inductive FigureLabel where
  | pivotText
  | radiusR
  | pivotOffsetD
  deriving DecidableEq, Repr

/-- The two arrowheads on the curved oscillation arrow. -/
inductive RotationDirection where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Relative placement of the pivot and the center in the primary image. -/
inductive PivotPlacement where
  | verticallyAboveCenter
  | other
  deriving DecidableEq, Repr

/--
Readout of labels and geometric incidences in the supplied image.  Distances
are genuine physical lengths; the endpoint data distinguish the center-to-rim
radius arrow from the pivot-to-center offset bracket.
-/
structure DiskPendulumFigureReadout where
  distanceBetween : FigurePoint → FigurePoint → LengthQuantity
  radiusArrowStart : FigurePoint
  radiusArrowEnd : FigurePoint
  offsetBracketUpperLevel : FigurePoint
  offsetBracketLowerLevel : FigurePoint
  pivotPlacement : PivotPlacement
  labelVisible : FigureLabel → Bool
  rotationArrowheadVisible : RotationDirection → Bool

/--
All physical quantities used to model the disk pendulum.  The scalar Physlib
harmonic oscillator represents the linearized angular coordinate; its `m`
and `k` fields are connected to the dimensionful generalized inertia and
restoring coefficient only by the governing laws below.
-/
structure UniformDiskPendulumSetup where
  diskMassDistribution : DiskMassDistribution
  motionPlane : MotionPlane
  diskMass : MassQuantity
  diskRadius : LengthQuantity
  pivotOffsetFromCenter : LengthQuantity
  gravitationalAccelerationMagnitude : AccelerationMagnitudeQuantity
  releaseAngleRadians : ℝ
  releaseAngularVelocity : AngularVelocityQuantity
  smallAngleCutoffRadians : ℝ
  linearizationRelativeErrorTolerance : ℝ
  centerMomentOfInertia : MomentOfInertiaQuantity
  pivotMomentOfInertia : MomentOfInertiaQuantity
  nonlinearGravitationalTorqueAtAngle : ℝ → TorqueQuantity
  gravitationalRestoringCoefficient : RestoringTorqueCoefficientQuantity
  linearizedAngularOscillator : ClassicalMechanics.HarmonicOscillator
  linearizedMotionPeriod : TimeQuantity
  figure : DiskPendulumFigureReadout

/--
The primary-image incidences and labels.  In particular, the image—not its
auxiliary prose caption—shows `R` from the center to the rim and `d` from the
pivot level to the center level.
-/
structure MatchesPrimaryDiskPendulumFigure
    (setup : UniformDiskPendulumSetup) : Prop where
  radiusArrowStartsAtCenter :
    setup.figure.radiusArrowStart = .diskCenter
  radiusArrowEndsAtRim :
    setup.figure.radiusArrowEnd = .radiusEndpointOnRim
  radiusArrowHasDiskRadius :
    setup.figure.distanceBetween .diskCenter .radiusEndpointOnRim =
      setup.diskRadius
  offsetBracketStartsAtPivotLevel :
    setup.figure.offsetBracketUpperLevel = .pivot
  offsetBracketEndsAtCenterLevel :
    setup.figure.offsetBracketLowerLevel = .diskCenter
  offsetBracketHasPivotDistance :
    setup.figure.distanceBetween .pivot .diskCenter =
      setup.pivotOffsetFromCenter
  pivotIsVerticallyAboveCenter :
    setup.figure.pivotPlacement = .verticallyAboveCenter
  pivotTextVisible : setup.figure.labelVisible .pivotText = true
  radiusLabelVisible : setup.figure.labelVisible .radiusR = true
  offsetLabelVisible : setup.figure.labelVisible .pivotOffsetD = true
  clockwiseArrowheadVisible :
    setup.figure.rotationArrowheadVisible .clockwise = true
  counterclockwiseArrowheadVisible :
    setup.figure.rotationArrowheadVisible .counterclockwise = true

/--
Categorical apparatus and release information from the verbal problem.  The
release angle lies in a declared validity window for the local linearization;
the corresponding relative torque-error tolerance is nonnegative and less
than one.  A nonzero angle excludes the equilibrium trajectory, while zero
initial angular velocity formalizes “released.”
-/
structure MatchesUniformDiskPendulumScenario
    (setup : UniformDiskPendulumSetup) : Prop where
  diskIsUniformAndSolid :
    setup.diskMassDistribution = .uniformSolidDisk
  diskMovesInVerticalPlane : setup.motionPlane = .vertical
  smallAngleCutoffPositive : 0 < setup.smallAngleCutoffRadians
  relativeErrorToleranceNonnegative :
    0 ≤ setup.linearizationRelativeErrorTolerance
  relativeErrorToleranceBelowOne :
    setup.linearizationRelativeErrorTolerance < 1
  releaseWithinSmallAngleWindow :
    |setup.releaseAngleRadians| ≤ setup.smallAngleCutoffRadians
  releaseAngleNonzero : 0 < |setup.releaseAngleRadians|
  releasedFromRest :
    angularVelocityInRadiansPerSecond setup.releaseAngularVelocity = 0

/--
Numerical lengths printed in the problem and positivity of the physical
parameters.  The radius is `2.35 cm = 47/20 cm`; the pivot offset is
`1.75 cm = 7/4 cm`.
-/
structure HasUniformDiskPendulumProblemData
    (setup : UniformDiskPendulumSetup) : Prop where
  radiusCentimeters :
    lengthInCentimeters setup.diskRadius = 47 / 20
  pivotOffsetCentimeters :
    lengthInCentimeters setup.pivotOffsetFromCenter = 7 / 4
  diskMassPositive : 0 < massInKilograms setup.diskMass
  diskRadiusPositive : 0 < lengthInMeters setup.diskRadius
  pivotOffsetPositive :
    0 < lengthInMeters setup.pivotOffsetFromCenter
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude

/--
The conventional terrestrial value `g = 9.8 m/s²`, needed to distinguish the
four numerical answer choices.
-/
def UsesStandardGravity (setup : UniformDiskPendulumSetup) : Prop :=
  accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude = 49 / 5

/-! ## Governing rigid-body and small-oscillation laws -/

/--
The physical laws used for the small-angle calculation:

* a uniform solid disk has center-axis inertia `M R² / 2`;
* moving the parallel axis to the pivot adds `M d²`;
* the exact signed gravitational torque is `-M g d sin θ`;
* gravity supplies the positive linearized restoring coefficient `M g d`;
* the generalized oscillator mass and stiffness are the pivot inertia and
  restoring coefficient; and
* the physical duration has the generic Physlib harmonic-oscillator period.

No field states the mass-cancelled period formula or a displayed answer.
-/
structure SatisfiesUniformDiskPendulumLaws
    (setup : UniformDiskPendulumSetup) : Prop where
  uniformSolidDiskCenterInertia :
    momentOfInertiaInKilogramMetersSquared
        setup.centerMomentOfInertia =
      massInKilograms setup.diskMass *
        lengthInMeters setup.diskRadius ^ 2 / 2
  scalarParallelAxisLaw :
    momentOfInertiaInKilogramMetersSquared
        setup.pivotMomentOfInertia =
      momentOfInertiaInKilogramMetersSquared
          setup.centerMomentOfInertia +
        massInKilograms setup.diskMass *
          lengthInMeters setup.pivotOffsetFromCenter ^ 2
  exactNonlinearGravitationalTorqueLaw :
    ∀ angleRadians : ℝ,
      torqueInNewtonMeters
          (setup.nonlinearGravitationalTorqueAtAngle angleRadians) =
        -(massInKilograms setup.diskMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude *
            lengthInMeters setup.pivotOffsetFromCenter) *
          Real.sin angleRadians
  linearizedGravitationalRestoringCoefficient :
    restoringCoefficientInNewtonMeters
        setup.gravitationalRestoringCoefficient =
      massInKilograms setup.diskMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAccelerationMagnitude *
        lengthInMeters setup.pivotOffsetFromCenter
  oscillatorGeneralizedMass :
    setup.linearizedAngularOscillator.m =
      momentOfInertiaInKilogramMetersSquared
        setup.pivotMomentOfInertia
  oscillatorGeneralizedStiffness :
    setup.linearizedAngularOscillator.k =
      restoringCoefficientInNewtonMeters
        setup.gravitationalRestoringCoefficient
  genericSmallOscillationPeriodLaw :
    timeInSeconds setup.linearizedMotionPeriod =
      setup.linearizedAngularOscillator.period

/--
A mathematically local small-angle contract for the gravitational torque.
The derivative identifies the tangent restoring torque at equilibrium, the
little-o clause records first-order asymptotic validity, and the last field
controls the relative remainder throughout the declared release window.

This predicate does not assert a period or any displayed answer.
-/
structure HasControlledSmallAngleTorqueLinearization
    (setup : UniformDiskPendulumSetup) : Prop where
  torqueHasLinearizedDerivativeAtEquilibrium :
    HasDerivAt
      (fun angleRadians : ℝ =>
        torqueInNewtonMeters
          (setup.nonlinearGravitationalTorqueAtAngle angleRadians))
      (-restoringCoefficientInNewtonMeters
        setup.gravitationalRestoringCoefficient)
      0
  torqueLinearizationRemainderIsLittleO :
    (fun angleRadians : ℝ =>
      torqueInNewtonMeters
          (setup.nonlinearGravitationalTorqueAtAngle angleRadians) +
        restoringCoefficientInNewtonMeters
            setup.gravitationalRestoringCoefficient *
          angleRadians) =o[nhds 0]
      (fun angleRadians : ℝ => angleRadians)
  torqueRemainderControlledOnSmallAngleWindow :
    ∀ angleRadians : ℝ,
      |angleRadians| ≤ setup.smallAngleCutoffRadians →
        |torqueInNewtonMeters
              (setup.nonlinearGravitationalTorqueAtAngle angleRadians) +
            restoringCoefficientInNewtonMeters
                setup.gravitationalRestoringCoefficient *
              angleRadians| ≤
          setup.linearizationRelativeErrorTolerance *
            restoringCoefficientInNewtonMeters
                setup.gravitationalRestoringCoefficient *
            |angleRadians|

/-! ## Displayed choices and formalization target -/

/-- Labels of the four displayed period choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Period in seconds printed beside each answer label. -/
def AnswerChoice.seconds : AnswerChoice → ℝ
  | .A => 161 / 500
  | .B => 43 / 125
  | .C => 183 / 500
  | .D => 97 / 250

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with a displayed period after rounding to the nearest millisecond. -/
def RoundsToNearestMillisecond
    (periodSeconds displayedSeconds : ℝ) : Prop :=
  |periodSeconds - displayedSeconds| < 1 / 2000

/-- A displayed choice is at least as close as every listed alternative. -/
def IsClosestDisplayedPeriod
    (periodSeconds : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ alternative : AnswerChoice,
    |periodSeconds - choice.seconds| ≤
      |periodSeconds - alternative.seconds|

/--
For a uniform disk pivoted a distance `d` from its center, the period of the
linearized small-angle oscillator is

`T = 2π √((R²/2 + d²)/(g d))`.

With `R = 2.35 cm`, `d = 1.75 cm`, and `g = 9.8 m/s²`, this period rounds to
`0.366 s` and is closest to recorded answer C.

No equality with the exact finite-amplitude nonlinear pendulum period is
claimed.  This formalizes blueprint label
`thm:physics:phyx_mini_0264:target`.
-/
theorem linearizedUniformSolidDiskPendulumPeriod_is_recordedAnswerC
    (setup : UniformDiskPendulumSetup)
    (_figure : MatchesPrimaryDiskPendulumFigure setup)
    (_scenario : MatchesUniformDiskPendulumScenario setup)
    (_data : HasUniformDiskPendulumProblemData setup)
    (_gravity : UsesStandardGravity setup)
    (_laws : SatisfiesUniformDiskPendulumLaws setup)
    (_linearization : HasControlledSmallAngleTorqueLinearization setup) :
    timeInSeconds setup.linearizedMotionPeriod =
        2 * Real.pi *
          Real.sqrt
            ((lengthInMeters setup.diskRadius ^ 2 / 2 +
                lengthInMeters setup.pivotOffsetFromCenter ^ 2) /
              (accelerationInMetersPerSecondSquared
                  setup.gravitationalAccelerationMagnitude *
                lengthInMeters setup.pivotOffsetFromCenter)) ∧
      RoundsToNearestMillisecond
        (timeInSeconds setup.linearizedMotionPeriod)
        recordedAnswerChoice.seconds ∧
      IsClosestDisplayedPeriod
        (timeInSeconds setup.linearizedMotionPeriod)
        recordedAnswerChoice := by
  have length_centimeters_eq (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h_units := length.2
      UnitChoices.SI
      ({ UnitChoices.SI with length := LengthUnit.centimeters } :
        UnitChoices)
    have h_units_real := congrArg
      (fun reading : WithDim L𝓭 NNReal => (reading.val : ℝ)) h_units
    norm_num [lengthInCentimeters, lengthInMeters,
      centimeterUnitChoices, UnitChoices.dimScale,
      LengthUnit.centimeters, LengthUnit.meters, LengthUnit.scale,
      LengthUnit.div_eq_val] at h_units_real ⊢
    exact h_units_real
  have h_radius_meters :
      lengthInMeters setup.diskRadius = 47 / 2000 := by
    have h := _data.radiusCentimeters
    rw [length_centimeters_eq] at h
    norm_num at h ⊢
    linarith
  have h_offset_meters :
      lengthInMeters setup.pivotOffsetFromCenter = 7 / 400 := by
    have h := _data.pivotOffsetCentimeters
    rw [length_centimeters_eq] at h
    norm_num at h ⊢
    linarith
  have h_gravity :
      accelerationInMetersPerSecondSquared
          setup.gravitationalAccelerationMagnitude = 49 / 5 :=
    _gravity
  have h_mass_pos : 0 < massInKilograms setup.diskMass :=
    _data.diskMassPositive
  have h_geometric_factor_pos :
      0 <
        lengthInMeters setup.diskRadius ^ 2 / 2 +
          lengthInMeters setup.pivotOffsetFromCenter ^ 2 := by
    positivity
  have h_oscillator_mass :
      setup.linearizedAngularOscillator.m =
        massInKilograms setup.diskMass *
          (lengthInMeters setup.diskRadius ^ 2 / 2 +
            lengthInMeters setup.pivotOffsetFromCenter ^ 2) := by
    calc
      setup.linearizedAngularOscillator.m =
          momentOfInertiaInKilogramMetersSquared
            setup.pivotMomentOfInertia :=
        _laws.oscillatorGeneralizedMass
      _ =
          momentOfInertiaInKilogramMetersSquared
              setup.centerMomentOfInertia +
            massInKilograms setup.diskMass *
              lengthInMeters setup.pivotOffsetFromCenter ^ 2 :=
        _laws.scalarParallelAxisLaw
      _ =
          massInKilograms setup.diskMass *
              lengthInMeters setup.diskRadius ^ 2 / 2 +
            massInKilograms setup.diskMass *
              lengthInMeters setup.pivotOffsetFromCenter ^ 2 := by
        rw [_laws.uniformSolidDiskCenterInertia]
      _ =
          massInKilograms setup.diskMass *
            (lengthInMeters setup.diskRadius ^ 2 / 2 +
              lengthInMeters setup.pivotOffsetFromCenter ^ 2) := by
        ring
  have h_oscillator_stiffness :
      setup.linearizedAngularOscillator.k =
        massInKilograms setup.diskMass *
          (accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude *
            lengthInMeters setup.pivotOffsetFromCenter) := by
    calc
      setup.linearizedAngularOscillator.k =
          restoringCoefficientInNewtonMeters
            setup.gravitationalRestoringCoefficient :=
        _laws.oscillatorGeneralizedStiffness
      _ =
          massInKilograms setup.diskMass *
            accelerationInMetersPerSecondSquared
                setup.gravitationalAccelerationMagnitude *
              lengthInMeters setup.pivotOffsetFromCenter :=
        _laws.linearizedGravitationalRestoringCoefficient
      _ =
          massInKilograms setup.diskMass *
            (accelerationInMetersPerSecondSquared
                setup.gravitationalAccelerationMagnitude *
              lengthInMeters setup.pivotOffsetFromCenter) := by
        ring
  have h_oscillator_ratio :
      setup.linearizedAngularOscillator.k /
          setup.linearizedAngularOscillator.m =
        (accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude *
            lengthInMeters setup.pivotOffsetFromCenter) /
          (lengthInMeters setup.diskRadius ^ 2 / 2 +
            lengthInMeters setup.pivotOffsetFromCenter ^ 2) := by
    rw [h_oscillator_stiffness, h_oscillator_mass]
    field_simp [h_mass_pos.ne', h_geometric_factor_pos.ne']
  have h_period_formula :
      timeInSeconds setup.linearizedMotionPeriod =
        2 * Real.pi *
          Real.sqrt
            ((lengthInMeters setup.diskRadius ^ 2 / 2 +
                lengthInMeters setup.pivotOffsetFromCenter ^ 2) /
              (accelerationInMetersPerSecondSquared
                  setup.gravitationalAccelerationMagnitude *
                lengthInMeters setup.pivotOffsetFromCenter)) := by
    rw [_laws.genericSmallOscillationPeriodLaw,
      ClassicalMechanics.HarmonicOscillator.period_eq]
    change
      2 * Real.pi /
          Real.sqrt
            (setup.linearizedAngularOscillator.k /
              setup.linearizedAngularOscillator.m) =
        2 * Real.pi *
          Real.sqrt
            ((lengthInMeters setup.diskRadius ^ 2 / 2 +
                lengthInMeters setup.pivotOffsetFromCenter ^ 2) /
              (accelerationInMetersPerSecondSquared
                  setup.gravitationalAccelerationMagnitude *
                lengthInMeters setup.pivotOffsetFromCenter))
    rw [h_oscillator_ratio]
    calc
      2 * Real.pi /
          Real.sqrt
            ((accelerationInMetersPerSecondSquared
                  setup.gravitationalAccelerationMagnitude *
                lengthInMeters setup.pivotOffsetFromCenter) /
              (lengthInMeters setup.diskRadius ^ 2 / 2 +
                lengthInMeters setup.pivotOffsetFromCenter ^ 2)) =
          2 * Real.pi *
            (Real.sqrt
              ((accelerationInMetersPerSecondSquared
                    setup.gravitationalAccelerationMagnitude *
                  lengthInMeters setup.pivotOffsetFromCenter) /
                (lengthInMeters setup.diskRadius ^ 2 / 2 +
                  lengthInMeters setup.pivotOffsetFromCenter ^ 2)))⁻¹ := by
            rw [div_eq_mul_inv]
      _ =
          2 * Real.pi *
            Real.sqrt
              ((lengthInMeters setup.diskRadius ^ 2 / 2 +
                  lengthInMeters setup.pivotOffsetFromCenter ^ 2) /
                (accelerationInMetersPerSecondSquared
                    setup.gravitationalAccelerationMagnitude *
                  lengthInMeters setup.pivotOffsetFromCenter)) := by
            rw [← Real.sqrt_inv, inv_div]
  have h_radicand :
      (lengthInMeters setup.diskRadius ^ 2 / 2 +
          lengthInMeters setup.pivotOffsetFromCenter ^ 2) /
        (accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude *
          lengthInMeters setup.pivotOffsetFromCenter) =
      (4659 : ℝ) / 1372000 := by
    rw [h_radius_meters, h_offset_meters, h_gravity]
    norm_num
  have h_period_numeric :
      timeInSeconds setup.linearizedMotionPeriod =
        2 * Real.pi * Real.sqrt ((4659 : ℝ) / 1372000) := by
    rw [h_period_formula, h_radicand]
  have h_sqrt_sq :
      Real.sqrt ((4659 : ℝ) / 1372000) ^ 2 =
        (4659 : ℝ) / 1372000 :=
    Real.sq_sqrt (by norm_num)
  have h_lower_sq :
      ((5827 : ℝ) / 100000) ^ 2 <
        (4659 : ℝ) / 1372000 := by
    norm_num
  have h_upper_sq :
      (4659 : ℝ) / 1372000 <
        ((5828 : ℝ) / 100000) ^ 2 := by
    norm_num
  have h_sqrt_lower :
      (5827 : ℝ) / 100000 <
        Real.sqrt ((4659 : ℝ) / 1372000) := by
    nlinarith [Real.sqrt_nonneg ((4659 : ℝ) / 1372000)]
  have h_sqrt_upper :
      Real.sqrt ((4659 : ℝ) / 1372000) <
        (5828 : ℝ) / 100000 := by
    nlinarith [Real.sqrt_nonneg ((4659 : ℝ) / 1372000)]
  have h_sqrt_two_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have h_sqrt_two_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have h_sqrt_two_lower : (1.41421 : ℝ) < Real.sqrt 2 := by
    nlinarith only [h_sqrt_two_sq, h_sqrt_two_nonneg]
  have h_sqrt_two_upper : Real.sqrt 2 < (1.414214 : ℝ) := by
    nlinarith only [h_sqrt_two_sq, h_sqrt_two_nonneg]
  have h_nested_three_arg : 0 ≤ (2 : ℝ) + Real.sqrt 2 := by
    positivity
  have h_nested_three_sq :
      Real.sqrt (2 + Real.sqrt 2) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt h_nested_three_arg
  have h_nested_three_nonneg :
      0 ≤ Real.sqrt (2 + Real.sqrt 2) := Real.sqrt_nonneg _
  have h_nested_three_lower :
      (1.8477581 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
    nlinarith only [h_sqrt_two_lower, h_nested_three_sq,
      h_nested_three_nonneg]
  have h_nested_three_upper :
      Real.sqrt (2 + Real.sqrt 2) < (1.8477595 : ℝ) := by
    nlinarith only [h_sqrt_two_upper, h_nested_three_sq,
      h_nested_three_nonneg]
  have h_nested_four_arg :
      0 ≤ (2 : ℝ) + Real.sqrt (2 + Real.sqrt 2) := by
    positivity
  have h_nested_four_sq :
      Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) ^ 2 =
        2 + Real.sqrt (2 + Real.sqrt 2) :=
    Real.sq_sqrt h_nested_four_arg
  have h_nested_four_nonneg :
      0 ≤ Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) :=
    Real.sqrt_nonneg _
  have h_nested_four_lower :
      (1.961570 : ℝ) <
        Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
    nlinarith only [h_nested_three_lower, h_nested_four_sq,
      h_nested_four_nonneg]
  have h_nested_four_upper :
      Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) <
        (1.961571 : ℝ) := by
    nlinarith only [h_nested_three_upper, h_nested_four_sq,
      h_nested_four_nonneg]
  have h_sine_radical_arg :
      0 ≤ (2 : ℝ) - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
    linarith only [h_nested_four_upper]
  have h_sine_radical_sq :
      Real.sqrt
            (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) ^ 2 =
        2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) :=
    Real.sq_sqrt h_sine_radical_arg
  have h_sine_radical_nonneg :
      0 ≤
        Real.sqrt
          (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) :=
    Real.sqrt_nonneg _
  have h_sine_radical_lower :
      (0.196032 : ℝ) <
        Real.sqrt
          (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) := by
    nlinarith only [h_nested_four_upper, h_sine_radical_sq,
      h_sine_radical_nonneg]
  have h_sine_radical_upper :
      Real.sqrt
          (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) <
        (0.196036 : ℝ) := by
    nlinarith only [h_nested_four_lower, h_sine_radical_sq,
      h_sine_radical_nonneg]
  have h_sin_pi_over_thirty_two_lower :
      (0.098016 : ℝ) < Real.sin (Real.pi / 32) := by
    rw [Real.sin_pi_div_thirty_two]
    linarith only [h_sine_radical_lower]
  have h_sin_pi_over_thirty_two_upper :
      Real.sin (Real.pi / 32) < (0.098018 : ℝ) := by
    rw [Real.sin_pi_div_thirty_two]
    linarith only [h_sine_radical_upper]
  let piOverThirtyTwo : ℝ := Real.pi / 32
  have h_pi_over_thirty_two_nonneg : 0 ≤ piOverThirtyTwo := by
    dsimp [piOverThirtyTwo]
    positivity
  have h_pi_over_thirty_two_le_eighth :
      piOverThirtyTwo ≤ (1 / 8 : ℝ) := by
    dsimp [piOverThirtyTwo]
    nlinarith only [Real.pi_le_four]
  have h_pi_over_thirty_two_abs : |piOverThirtyTwo| ≤ 1 := by
    rw [abs_of_nonneg h_pi_over_thirty_two_nonneg]
    linarith only [h_pi_over_thirty_two_le_eighth]
  have h_pi_over_thirty_two_sin_bound :=
    Real.sin_bound h_pi_over_thirty_two_abs
  rw [abs_of_nonneg h_pi_over_thirty_two_nonneg] at h_pi_over_thirty_two_sin_bound
  have h_pi_over_thirty_two_approx_lower :=
    (abs_le.mp h_pi_over_thirty_two_sin_bound).1
  have h_pi_over_thirty_two_approx_upper :=
    (abs_le.mp h_pi_over_thirty_two_sin_bound).2
  have h_pi_gt_31 : (3.1 : ℝ) < Real.pi := by
    by_contra h
    have h_pi_le : Real.pi ≤ (3.1 : ℝ) := le_of_not_gt h
    have h_fourth :
        piOverThirtyTwo ^ 4 ≤ ((3.1 : ℝ) / 32) ^ 4 := by
      apply pow_le_pow_left₀ h_pi_over_thirty_two_nonneg _ 4
      dsimp [piOverThirtyTwo]
      nlinarith only [h_pi_le]
    have h_cube_nonneg : 0 ≤ piOverThirtyTwo ^ 3 :=
      pow_nonneg h_pi_over_thirty_two_nonneg _
    dsimp [piOverThirtyTwo] at h_pi_over_thirty_two_approx_upper h_fourth h_cube_nonneg
    nlinarith only [h_sin_pi_over_thirty_two_lower,
      h_pi_over_thirty_two_approx_upper, h_fourth, h_cube_nonneg,
      h_pi_le]
  have h_pi_over_thirty_two_ge_31 :
      (3.1 : ℝ) / 32 ≤ piOverThirtyTwo := by
    dsimp [piOverThirtyTwo]
    nlinarith only [h_pi_gt_31.le]
  have h_pi_gt_314 : (3.14 : ℝ) < Real.pi := by
    have h_cube :
        ((3.1 : ℝ) / 32) ^ 3 ≤ piOverThirtyTwo ^ 3 :=
      pow_le_pow_left₀ (by norm_num) h_pi_over_thirty_two_ge_31 3
    by_contra h
    have h_pi_le : Real.pi ≤ (3.14 : ℝ) := le_of_not_gt h
    have h_fourth :
        piOverThirtyTwo ^ 4 ≤ ((3.14 : ℝ) / 32) ^ 4 := by
      apply pow_le_pow_left₀ h_pi_over_thirty_two_nonneg _ 4
      dsimp [piOverThirtyTwo]
      nlinarith only [h_pi_le]
    dsimp [piOverThirtyTwo] at h_pi_over_thirty_two_approx_upper h_cube h_fourth
    nlinarith only [h_sin_pi_over_thirty_two_lower,
      h_pi_over_thirty_two_approx_upper, h_cube, h_fourth, h_pi_le]
  have h_pi_over_thirty_two_ge_314 :
      (3.14 : ℝ) / 32 ≤ piOverThirtyTwo := by
    dsimp [piOverThirtyTwo]
    nlinarith only [h_pi_gt_314.le]
  have h_pi_lower : (3141 : ℝ) / 1000 < Real.pi := by
    have h_cube :
        ((3.14 : ℝ) / 32) ^ 3 ≤ piOverThirtyTwo ^ 3 :=
      pow_le_pow_left₀ (by norm_num) h_pi_over_thirty_two_ge_314 3
    by_contra h
    have h_pi_le : Real.pi ≤ (3141 : ℝ) / 1000 :=
      le_of_not_gt h
    have h_fourth :
        piOverThirtyTwo ^ 4 ≤ (((3141 : ℝ) / 1000) / 32) ^ 4 := by
      apply pow_le_pow_left₀ h_pi_over_thirty_two_nonneg _ 4
      dsimp [piOverThirtyTwo]
      nlinarith only [h_pi_le]
    dsimp [piOverThirtyTwo] at h_pi_over_thirty_two_approx_upper h_cube h_fourth
    nlinarith only [h_sin_pi_over_thirty_two_lower,
      h_pi_over_thirty_two_approx_upper, h_cube, h_fourth, h_pi_le]
  have h_pi_lt_32 : Real.pi < (3.2 : ℝ) := by
    have h_cube :
        piOverThirtyTwo ^ 3 ≤ (1 / 8 : ℝ) ^ 3 :=
      pow_le_pow_left₀ h_pi_over_thirty_two_nonneg
        h_pi_over_thirty_two_le_eighth 3
    have h_fourth :
        piOverThirtyTwo ^ 4 ≤ (1 / 8 : ℝ) ^ 4 :=
      pow_le_pow_left₀ h_pi_over_thirty_two_nonneg
        h_pi_over_thirty_two_le_eighth 4
    by_contra h
    have h_pi_ge : (3.2 : ℝ) ≤ Real.pi := le_of_not_gt h
    dsimp [piOverThirtyTwo] at h_pi_over_thirty_two_approx_lower h_cube h_fourth
    nlinarith only [h_sin_pi_over_thirty_two_upper,
      h_pi_over_thirty_two_approx_lower, h_cube, h_fourth, h_pi_ge]
  have h_pi_over_thirty_two_le_32 :
      piOverThirtyTwo ≤ (3.2 : ℝ) / 32 := by
    dsimp [piOverThirtyTwo]
    nlinarith only [h_pi_lt_32.le]
  have h_pi_lt_315 : Real.pi < (3.15 : ℝ) := by
    have h_cube :
        piOverThirtyTwo ^ 3 ≤ ((3.2 : ℝ) / 32) ^ 3 :=
      pow_le_pow_left₀ h_pi_over_thirty_two_nonneg
        h_pi_over_thirty_two_le_32 3
    have h_fourth :
        piOverThirtyTwo ^ 4 ≤ ((3.2 : ℝ) / 32) ^ 4 :=
      pow_le_pow_left₀ h_pi_over_thirty_two_nonneg
        h_pi_over_thirty_two_le_32 4
    by_contra h
    have h_pi_ge : (3.15 : ℝ) ≤ Real.pi := le_of_not_gt h
    dsimp [piOverThirtyTwo] at h_pi_over_thirty_two_approx_lower h_cube h_fourth
    nlinarith only [h_sin_pi_over_thirty_two_upper,
      h_pi_over_thirty_two_approx_lower, h_cube, h_fourth, h_pi_ge]
  have h_pi_over_thirty_two_le_315 :
      piOverThirtyTwo ≤ (3.15 : ℝ) / 32 := by
    dsimp [piOverThirtyTwo]
    nlinarith only [h_pi_lt_315.le]
  have h_pi_lt_3145 : Real.pi < (3.145 : ℝ) := by
    have h_cube :
        piOverThirtyTwo ^ 3 ≤ ((3.15 : ℝ) / 32) ^ 3 :=
      pow_le_pow_left₀ h_pi_over_thirty_two_nonneg
        h_pi_over_thirty_two_le_315 3
    have h_fourth :
        piOverThirtyTwo ^ 4 ≤ ((3.15 : ℝ) / 32) ^ 4 :=
      pow_le_pow_left₀ h_pi_over_thirty_two_nonneg
        h_pi_over_thirty_two_le_315 4
    by_contra h
    have h_pi_ge : (3.145 : ℝ) ≤ Real.pi := le_of_not_gt h
    dsimp [piOverThirtyTwo] at h_pi_over_thirty_two_approx_lower h_cube h_fourth
    nlinarith only [h_sin_pi_over_thirty_two_upper,
      h_pi_over_thirty_two_approx_lower, h_cube, h_fourth, h_pi_ge]
  have h_pi_over_thirty_two_le_3145 :
      piOverThirtyTwo ≤ (3.145 : ℝ) / 32 := by
    dsimp [piOverThirtyTwo]
    nlinarith only [h_pi_lt_3145.le]
  have h_pi_upper : Real.pi < (3142 : ℝ) / 1000 := by
    have h_cube :
        piOverThirtyTwo ^ 3 ≤ ((3.145 : ℝ) / 32) ^ 3 :=
      pow_le_pow_left₀ h_pi_over_thirty_two_nonneg
        h_pi_over_thirty_two_le_3145 3
    have h_fourth :
        piOverThirtyTwo ^ 4 ≤ ((3.145 : ℝ) / 32) ^ 4 :=
      pow_le_pow_left₀ h_pi_over_thirty_two_nonneg
        h_pi_over_thirty_two_le_3145 4
    by_contra h
    have h_pi_ge : (3142 : ℝ) / 1000 ≤ Real.pi :=
      le_of_not_gt h
    dsimp [piOverThirtyTwo] at h_pi_over_thirty_two_approx_lower h_cube h_fourth
    nlinarith only [h_sin_pi_over_thirty_two_upper,
      h_pi_over_thirty_two_approx_lower, h_cube, h_fourth, h_pi_ge]
  have h_product_lower :
      ((3141 : ℝ) / 1000) * ((5827 : ℝ) / 100000) <
        Real.pi * Real.sqrt ((4659 : ℝ) / 1372000) := by
    calc
      ((3141 : ℝ) / 1000) * ((5827 : ℝ) / 100000) <
          Real.pi * ((5827 : ℝ) / 100000) :=
        mul_lt_mul_of_pos_right h_pi_lower (by norm_num)
      _ < Real.pi * Real.sqrt ((4659 : ℝ) / 1372000) :=
        mul_lt_mul_of_pos_left h_sqrt_lower Real.pi_pos
  have h_sqrt_pos :
      0 < Real.sqrt ((4659 : ℝ) / 1372000) := by
    linarith
  have h_product_upper :
      Real.pi * Real.sqrt ((4659 : ℝ) / 1372000) <
        ((3142 : ℝ) / 1000) * ((5828 : ℝ) / 100000) := by
    calc
      Real.pi * Real.sqrt ((4659 : ℝ) / 1372000) <
          ((3142 : ℝ) / 1000) *
            Real.sqrt ((4659 : ℝ) / 1372000) :=
        mul_lt_mul_of_pos_right h_pi_upper h_sqrt_pos
      _ < ((3142 : ℝ) / 1000) * ((5828 : ℝ) / 100000) :=
        mul_lt_mul_of_pos_left h_sqrt_upper (by norm_num)
  have h_period_above_display :
      (183 : ℝ) / 500 <
        timeInSeconds setup.linearizedMotionPeriod := by
    rw [h_period_numeric]
    norm_num at h_product_lower ⊢
    linarith only [h_product_lower]
  have h_period_upper :
      timeInSeconds setup.linearizedMotionPeriod <
        (733 : ℝ) / 2000 := by
    rw [h_period_numeric]
    norm_num at h_product_upper ⊢
    linarith only [h_product_upper]
  refine ⟨h_period_formula, ?_, ?_⟩
  · unfold RoundsToNearestMillisecond
    simp only [recordedAnswerChoice, AnswerChoice.seconds]
    rw [abs_of_pos (sub_pos.mpr h_period_above_display)]
    linarith only [h_period_upper]
  · unfold IsClosestDisplayedPeriod
    intro alternative
    cases alternative with
    | A =>
        change
          |timeInSeconds setup.linearizedMotionPeriod - 183 / 500| ≤
            |timeInSeconds setup.linearizedMotionPeriod - 161 / 500|
        rw [abs_of_pos (sub_pos.mpr h_period_above_display),
          abs_of_pos (by linarith only [h_period_above_display] : 0 <
            timeInSeconds setup.linearizedMotionPeriod - 161 / 500)]
        linarith only
    | B =>
        change
          |timeInSeconds setup.linearizedMotionPeriod - 183 / 500| ≤
            |timeInSeconds setup.linearizedMotionPeriod - 43 / 125|
        rw [abs_of_pos (sub_pos.mpr h_period_above_display),
          abs_of_pos (by linarith only [h_period_above_display] : 0 <
            timeInSeconds setup.linearizedMotionPeriod - 43 / 125)]
        linarith only
    | C =>
        exact le_rfl
    | D =>
        change
          |timeInSeconds setup.linearizedMotionPeriod - 183 / 500| ≤
            |timeInSeconds setup.linearizedMotionPeriod - 97 / 250|
        rw [abs_of_pos (sub_pos.mpr h_period_above_display),
          abs_of_neg (by linarith only [h_period_upper] : timeInSeconds
            setup.linearizedMotionPeriod - 97 / 250 < 0)]
        linarith only [h_period_upper]

end PhyXMiniProblems.ProblemPhyXMini0264
