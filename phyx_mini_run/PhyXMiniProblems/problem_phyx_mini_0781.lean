import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0781

open Dimension

/-!
# Grindstone stopping under axle friction

A `50.0 kg` uniform solid-disk grindstone has diameter `0.520 m`.  The full
scenario depicts an ax pressed against its rim with normal force `160 N` and
kinetic-friction coefficient `0.60`.  The question asks for a different time
interval, during which the blade is absent and the constant `6.50 N m` axle
friction torque is the only torque slowing the stone from `120 rev/min` to
rest.

Physical mass, length, force, torque, time, moment of inertia, angular
velocity, and angular acceleration are represented by unit-independent
Physlib quantities.  Real numbers occur only as coherent-SI readouts,
revolutions-per-minute readouts, schematic figure directions, and displayed
answer values.

Assumption/target split:

* governing laws: radius is half the diameter, the uniform-solid-disk moment
  of inertia, kinetic-friction magnitude and rim lever-arm laws for the full
  blade-contact scenario, opposition of axle friction to the initial spin,
  `tau = I * alpha`, and constant-angular-acceleration kinematics;
* previous-part results: none;
* figure/data readouts: the visible grindstone, tool, hands, axle, support,
  labels `m = 50.0 kg`, `F = 160 N`, and `omega`, the `0.520 m` diameter,
  coefficient `0.60`, axle torque magnitude `6.50 N m`, and initial speed
  `120 rev/min`; the asked interval has no blade contact and ends at rest;
* target conclusions: the exact stopping duration `338 * pi / 325` seconds
  and its unique agreement, to the displayed hundredth of a second, with
  recorded answer choice B (`3.27 s`).
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension of force, `M L T^-2`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of torque and energy, `M L^2 T^-2`. -/
def torqueDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of axial moment of inertia, `M L^2`. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative physical torque magnitude. -/
abbrev TorqueMagnitudeQuantity : Type :=
  Dimensionful (WithDim torqueDimension NNReal)

/-!
A signed axial torque.  Positive sign is chosen to agree with the initial
rotation arrow; axle friction therefore has negative signed readout.
-/
abbrev AxialTorqueQuantity : Type :=
  Dimensionful (WithDim torqueDimension ℝ)

/-- A nonnegative physical time interval. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative axial moment of inertia. -/
abbrev AxialMomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- A signed axial angular velocity; radians are dimensionless. -/
abbrev AxialAngularVelocityQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A signed axial angular acceleration. -/
abbrev AxialAngularAccelerationQuantity : Type :=
  Dimensionful (WithDim (T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a signed dimensionful quantity in coherent SI units. -/
def signedSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Newton readout of a force magnitude. -/
def forceInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout force

/-- Newton-meter readout of a torque magnitude. -/
def torqueMagnitudeInNewtonMeters (torque : TorqueMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout torque

/-- Signed newton-meter readout of an axial torque. -/
def axialTorqueInNewtonMeters (torque : AxialTorqueQuantity) : ℝ :=
  signedSIReadout torque

/-- Second readout of a physical duration. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  nonnegativeSIReadout time

/-- Kilogram-meter-squared readout of an axial moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : AxialMomentOfInertiaQuantity) : ℝ :=
  nonnegativeSIReadout inertia

/-- Radian-per-second readout of a signed angular velocity. -/
def angularVelocityInRadiansPerSecond
    (angularVelocity : AxialAngularVelocityQuantity) : ℝ :=
  signedSIReadout angularVelocity

/-!
Revolutions-per-minute readout.  One revolution is `2 * pi` radians and one
minute is `60` seconds, so the conversion factor is `30 / pi`.
-/
def angularVelocityInRevolutionsPerMinute
    (angularVelocity : AxialAngularVelocityQuantity) : ℝ :=
  angularVelocityInRadiansPerSecond angularVelocity * 30 / Real.pi

/-- Radian-per-second-squared readout of a signed angular acceleration. -/
def angularAccelerationInRadiansPerSecondSquared
    (angularAcceleration : AxialAngularAccelerationQuantity) : ℝ :=
  signedSIReadout angularAcceleration

/-- Real readout of the dimensionless kinetic-friction coefficient. -/
def kineticFrictionCoefficientReadout (coefficient : NNReal) : ℝ :=
  coefficient

/-! ## Physical roles and primary-image vocabulary -/

/-- The rigid-body idealization stated for the grindstone. -/
inductive GrindstoneShape where
  | uniformSolidDisk
  | other
  deriving DecidableEq, Repr

/-- Components visible in primary image `781.png`. -/
inductive GrindstoneFigureComponent where
  | circularGrindstone
  | axTool
  | hands
  | axle
  | supportFrame
  deriving DecidableEq, Fintype, Repr

/-- Text and symbol labels printed in primary image `781.png`. -/
inductive GrindstoneFigureLabel where
  | massMEqualsFiftyKilograms
  | appliedForceFEqualsOneHundredSixtyNewtons
  | angularVelocityOmega
  deriving DecidableEq, Fintype, Repr

/-- The contact location shown for the blade and grindstone. -/
inductive BladeContactLocation where
  | rim
  | awayFromRim
  deriving DecidableEq, Repr

/-- Drawing direction of the red applied-force arrow. -/
inductive AppliedForceArrowDirection where
  | rightwardIntoStone
  | other
  deriving DecidableEq, Repr

/-!
Drawing direction of the curved arrow at the top of the disk.  This records
the primary pixels without assigning an ambiguous front/back viewing
convention to the physical axle orientation.
-/
inductive RotationArrowTopDirection where
  | towardLeft
  | other
  deriving DecidableEq, Repr

/-- Qualitative and label evidence transcribed from primary image `781.png`. -/
structure GrindstoneFigure where
  componentIsVisible : GrindstoneFigureComponent → Bool
  labelIsVisible : GrindstoneFigureLabel → Bool
  bladeContactLocation : BladeContactLocation
  appliedForceArrowDirection : AppliedForceArrowDirection
  rotationArrowTopDirection : RotationArrowTopDirection

/-!
Physical quantities for the full illustrated scenario and for the axle-only
stopping interval.  The stopping duration and final angular velocity are
independent observables: neither is defined from a displayed answer.
-/
structure GrindstoneStoppingSetup where
  figure : GrindstoneFigure
  shape : GrindstoneShape
  mass : MassQuantity
  diameter : LengthQuantity
  radius : LengthQuantity
  referenceNormalForceAtRim : ForceMagnitudeQuantity
  kineticFrictionCoefficient : NNReal
  referenceBladeKineticFrictionForce : ForceMagnitudeQuantity
  referenceBladeFrictionTorque : TorqueMagnitudeQuantity
  axleFrictionTorqueMagnitude : TorqueMagnitudeQuantity
  axleFrictionTorque : AxialTorqueQuantity
  netTorqueDuringAskedInterval : AxialTorqueQuantity
  momentOfInertiaAboutAxle : AxialMomentOfInertiaQuantity
  initialAngularVelocity : AxialAngularVelocityQuantity
  finalAngularVelocity : AxialAngularVelocityQuantity
  angularAccelerationDuringAskedInterval :
    AxialAngularAccelerationQuantity
  stoppingDuration : TimeQuantity
  referenceFigureDepictsBladePressedAtRim : Bool
  rotatesAboutFixedAxle : Bool
  bladeContactsStoneDuringAskedInterval : Bool
  axleFrictionActsDuringAskedInterval : Bool
  axleFrictionTorqueIsConstantDuringAskedInterval : Bool

/-! ## Figure evidence, problem data, and physical admissibility -/

/-!
Facts visible in the primary image.  The image contains no diameter, friction
coefficient, axle-torque, initial-rpm, or stopping-time label; those enter
separately as verbal problem data.
-/
structure MatchesPrimaryGrindstoneFigure
    (setup : GrindstoneStoppingSetup) : Prop where
  everyComponentVisible :
    ∀ component, setup.figure.componentIsVisible component = true
  everyPrintedLabelVisible :
    ∀ label, setup.figure.labelIsVisible label = true
  bladeTouchesRim : setup.figure.bladeContactLocation = .rim
  forceArrowPointsIntoStone :
    setup.figure.appliedForceArrowDirection = .rightwardIntoStone
  rotationArrowPointsLeftAtTop :
    setup.figure.rotationArrowTopDirection = .towardLeft

/-!
Numerical and categorical data supplied by the prose.  The blade quantities
belong to the full illustrated scenario, while the asked stopping interval
explicitly removes blade contact and retains axle friction alone.
-/
structure MatchesGrindstoneProblemData
    (setup : GrindstoneStoppingSetup) : Prop where
  grindstoneIsUniformSolidDisk : setup.shape = .uniformSolidDisk
  massKilograms : massInKilograms setup.mass = 50
  diameterMeters : lengthInMeters setup.diameter = 13 / 25
  referenceNormalForceNewtons :
    forceInNewtons setup.referenceNormalForceAtRim = 160
  kineticFrictionCoefficientValue :
    kineticFrictionCoefficientReadout setup.kineticFrictionCoefficient = 3 / 5
  axleFrictionTorqueMagnitudeNewtonMeters :
    torqueMagnitudeInNewtonMeters setup.axleFrictionTorqueMagnitude = 13 / 2
  initialAngularVelocityRpm :
    angularVelocityInRevolutionsPerMinute setup.initialAngularVelocity = 120
  referenceBladePressedAtRim :
    setup.referenceFigureDepictsBladePressedAtRim = true
  fixedAxleRotation : setup.rotatesAboutFixedAxle = true
  bladeAbsentDuringAskedInterval :
    setup.bladeContactsStoneDuringAskedInterval = false
  axleFrictionActsDuringAskedInterval :
    setup.axleFrictionActsDuringAskedInterval = true
  axleFrictionTorqueConstantDuringAskedInterval :
    setup.axleFrictionTorqueIsConstantDuringAskedInterval = true
  finalStateIsRest :
    angularVelocityInRadiansPerSecond setup.finalAngularVelocity = 0

/-!
Positivity and sign conditions for the physical branch in which the stone
initially rotates in the chosen positive direction and axle friction slows it.
No numerical stopping duration occurs here.
-/
structure HasPhysicalGrindstoneParameters
    (setup : GrindstoneStoppingSetup) : Prop where
  massPositive : 0 < massInKilograms setup.mass
  diameterPositive : 0 < lengthInMeters setup.diameter
  radiusPositive : 0 < lengthInMeters setup.radius
  normalForcePositive : 0 < forceInNewtons setup.referenceNormalForceAtRim
  kineticFrictionCoefficientPositive :
    0 < kineticFrictionCoefficientReadout setup.kineticFrictionCoefficient
  axleFrictionTorqueMagnitudePositive :
    0 < torqueMagnitudeInNewtonMeters setup.axleFrictionTorqueMagnitude
  momentOfInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared setup.momentOfInertiaAboutAxle
  initiallyRotatingPositive :
    0 < angularVelocityInRadiansPerSecond setup.initialAngularVelocity
  axleOnlyAngularAccelerationNegative :
    angularAccelerationInRadiansPerSecondSquared
        setup.angularAccelerationDuringAskedInterval < 0
  stoppingDurationPositive : 0 < timeInSeconds setup.stoppingDuration

/-! ## Governing rigid-body and friction laws -/

/-!
The radius and uniform-disk inertia relations, the two unused reference blade
friction laws, and the axle-only rotational dynamics.  The last relation is
the constant-angular-acceleration kinematic law from the independent initial
and final angular velocities.  No field states the requested stopping time or
mentions an answer choice.
-/
structure SatisfiesGrindstoneRotationalLaws
    (setup : GrindstoneStoppingSetup) : Prop where
  radiusIsHalfDiameter :
    lengthInMeters setup.radius = lengthInMeters setup.diameter / 2
  uniformSolidDiskMomentOfInertia :
    momentOfInertiaInKilogramMetersSquared setup.momentOfInertiaAboutAxle =
      (1 / 2 : ℝ) * massInKilograms setup.mass *
        lengthInMeters setup.radius ^ 2
  referenceBladeKineticFrictionLaw :
    forceInNewtons setup.referenceBladeKineticFrictionForce =
      kineticFrictionCoefficientReadout setup.kineticFrictionCoefficient *
        forceInNewtons setup.referenceNormalForceAtRim
  referenceBladeRimTorqueLaw :
    torqueMagnitudeInNewtonMeters setup.referenceBladeFrictionTorque =
      lengthInMeters setup.radius *
        forceInNewtons setup.referenceBladeKineticFrictionForce
  axleFrictionOpposesPositiveRotation :
    axialTorqueInNewtonMeters setup.axleFrictionTorque =
      -torqueMagnitudeInNewtonMeters setup.axleFrictionTorqueMagnitude
  netTorqueIsAxleFrictionAlone :
    axialTorqueInNewtonMeters setup.netTorqueDuringAskedInterval =
      axialTorqueInNewtonMeters setup.axleFrictionTorque
  axialTorqueAngularAccelerationLaw :
    axialTorqueInNewtonMeters setup.netTorqueDuringAskedInterval =
      momentOfInertiaInKilogramMetersSquared setup.momentOfInertiaAboutAxle *
        angularAccelerationInRadiansPerSecondSquared
          setup.angularAccelerationDuringAskedInterval
  constantAngularAccelerationStoppingLaw :
    angularVelocityInRadiansPerSecond setup.finalAngularVelocity =
      angularVelocityInRadiansPerSecond setup.initialAngularVelocity +
        angularAccelerationInRadiansPerSecondSquared
            setup.angularAccelerationDuringAskedInterval *
          timeInSeconds setup.stoppingDuration

/-! ## Derived rotational quantities and displayed answers -/

/-- The stated uniform disk has axial moment of inertia `1.69 kg m^2`. -/
lemma momentOfInertiaAboutAxle_is_169_over_100
    (setup : GrindstoneStoppingSetup)
    (hData : MatchesGrindstoneProblemData setup)
    (hLaws : SatisfiesGrindstoneRotationalLaws setup) :
    momentOfInertiaInKilogramMetersSquared setup.momentOfInertiaAboutAxle =
      169 / 100 := by
  have hRadius := hLaws.radiusIsHalfDiameter
  calc
    momentOfInertiaInKilogramMetersSquared setup.momentOfInertiaAboutAxle =
        (1 / 2 : ℝ) * massInKilograms setup.mass *
          lengthInMeters setup.radius ^ 2 :=
      hLaws.uniformSolidDiskMomentOfInertia
    _ = 169 / 100 := by
      rw [hData.massKilograms]
      rw [hRadius, hData.diameterMeters]
      norm_num

/-- The initial `120 rev/min` equals `4 * pi rad/s`. -/
lemma initialAngularVelocity_is_four_pi
    (setup : GrindstoneStoppingSetup)
    (hData : MatchesGrindstoneProblemData setup) :
    angularVelocityInRadiansPerSecond setup.initialAngularVelocity =
      4 * Real.pi := by
  have hRpm := hData.initialAngularVelocityRpm
  change angularVelocityInRadiansPerSecond setup.initialAngularVelocity *
      30 / Real.pi = 120 at hRpm
  field_simp [Real.pi_ne_zero] at hRpm
  linarith

/-!
The axle-only angular acceleration is the negative torque magnitude divided
by the solid-disk inertia, namely `-650 / 169 rad/s^2`.
-/
lemma axleOnlyAngularAcceleration_is_neg_650_over_169
    (setup : GrindstoneStoppingSetup)
    (hData : MatchesGrindstoneProblemData setup)
    (hPhysical : HasPhysicalGrindstoneParameters setup)
    (hLaws : SatisfiesGrindstoneRotationalLaws setup) :
    angularAccelerationInRadiansPerSecondSquared
        setup.angularAccelerationDuringAskedInterval =
      -(650 / 169 : ℝ) := by
  have hInertia :=
    momentOfInertiaAboutAxle_is_169_over_100 setup hData hLaws
  have hDynamics := hLaws.axialTorqueAngularAccelerationLaw
  rw [hLaws.netTorqueIsAxleFrictionAlone,
    hLaws.axleFrictionOpposesPositiveRotation,
    hData.axleFrictionTorqueMagnitudeNewtonMeters,
    hInertia] at hDynamics
  norm_num at hDynamics ⊢
  linarith

/-- Labels of the four stopping-time choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Time in seconds printed beside each answer label. -/
def AnswerChoice.seconds : AnswerChoice → ℝ
  | .A => 243 / 50
  | .B => 327 / 100
  | .C => 523 / 100
  | .D => 343 / 50

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
A duration agrees with a displayed value to the nearest hundredth of a
second when the absolute error is strictly less than half a hundredth.
-/
def MatchesDisplayedStoppingTime
    (duration : TimeQuantity) (choice : AnswerChoice) : Prop :=
  |timeInSeconds duration - choice.seconds| < 1 / 200

/-!
Under axle friction alone, `I = 169/100 kg m^2`, the initial speed is
`4*pi rad/s`, and the opposing torque has magnitude `13/2 N m`.  The
constant-acceleration stopping duration is therefore
`338*pi/325 = 3.267... s`, which rounds to `3.27 s`; it uniquely matches
recorded choice B.

This formalizes `thm:physics:phyx_mini_0781:target`.
-/
theorem stoppingDuration_matches_recordedAnswerB
    (setup : GrindstoneStoppingSetup)
    (hFigure : MatchesPrimaryGrindstoneFigure setup)
    (hData : MatchesGrindstoneProblemData setup)
    (hPhysical : HasPhysicalGrindstoneParameters setup)
    (hLaws : SatisfiesGrindstoneRotationalLaws setup) :
    timeInSeconds setup.stoppingDuration = 338 * Real.pi / 325 ∧
      MatchesDisplayedStoppingTime setup.stoppingDuration
        recordedDatasetAnswer ∧
      ∀ choice,
        MatchesDisplayedStoppingTime setup.stoppingDuration choice →
          choice = recordedDatasetAnswer := by
  have hInitial := initialAngularVelocity_is_four_pi setup hData
  have hAcceleration :=
    axleOnlyAngularAcceleration_is_neg_650_over_169
      setup hData hPhysical hLaws
  have hKinematics := hLaws.constantAngularAccelerationStoppingLaw
  rw [hData.finalStateIsRest, hInitial, hAcceleration] at hKinematics
  have hExact :
      timeInSeconds setup.stoppingDuration = 338 * Real.pi / 325 := by
    linarith
  have hPiBounds : (3.14 : ℝ) < Real.pi ∧ Real.pi < 3.1416 := by
    have sin_lt_local {x : ℝ} (h : 0 < x) : Real.sin x < x := by
      rcases lt_or_ge 1 x with h' | h'
      · exact (Real.sin_le_one x).trans_lt h'
      have hx : |x| = x := abs_of_nonneg h.le
      have hbound :=
        le_of_abs_le (Real.sin_bound (show |x| ≤ 1 by rwa [hx]))
      rw [sub_le_iff_le_add', hx] at hbound
      apply hbound.trans_lt
      rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)]
      refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos h 3)
      apply pow_le_pow_of_le_one h.le h'
      simp
    have sin_gt_sub_cube_local {x : ℝ} (h : 0 < x) (h' : x ≤ 1) :
        x - x ^ 3 / 4 < Real.sin x := by
      have hx : |x| = x := abs_of_nonneg h.le
      have hbound :=
        neg_le_of_abs_le (Real.sin_bound (show |x| ≤ 1 by rwa [hx]))
      rw [le_sub_iff_add_le, hx] at hbound
      refine lt_of_lt_of_le ?_ hbound
      have hcalc :
          x ^ 3 / (4 : ℝ) - x ^ 3 / 6 = x ^ 3 * 12⁻¹ := by
        norm_num [div_eq_mul_inv, ← mul_sub]
      rw [add_comm, sub_add, sub_neg_eq_add, sub_lt_sub_iff_left,
        ← lt_sub_iff_add_lt', hcalc]
      refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos h 3)
      apply pow_le_pow_of_le_one h.le h'
      simp
    have pi_gt_sqrt_series (n : ℕ) :
        2 ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n) < Real.pi := by
      have hscaled :
          √(2 - Real.sqrtTwoAddSeries 0 n) / 2 * 2 ^ (n + 2) <
            Real.pi := by
        rw [← lt_div_iff₀, ← Real.sin_pi_over_two_pow_succ]
        focus
          apply sin_lt_local
          apply div_pos Real.pi_pos
        all_goals apply pow_pos <;> norm_num
      refine lt_of_le_of_lt (le_of_eq ?_) hscaled
      rw [pow_succ' _ (n + 1), ← mul_assoc, div_mul_cancel₀, mul_comm]
      simp
    have pi_lt_sqrt_series (n : ℕ) :
        Real.pi <
          2 ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n) + 1 / 4 ^ n := by
      have hscaled :
          Real.pi <
            (√(2 - Real.sqrtTwoAddSeries 0 n) / 2 +
                1 / (2 ^ n) ^ 3 / 4) *
              (2 : ℝ) ^ (n + 2) := by
        rw [← div_lt_iff₀ (by simp), ← Real.sin_pi_over_two_pow_succ,
          ← sub_lt_iff_lt_add']
        calc
          Real.pi / 2 ^ (n + 2) -
                Real.sin (Real.pi / 2 ^ (n + 2)) <
              (Real.pi / 2 ^ (n + 2)) ^ 3 / 4 :=
            sub_lt_comm.1 <|
              sin_gt_sub_cube_local (by positivity)
                (div_le_one_of_le₀ (by
                  calc
                    Real.pi ≤ 4 := Real.pi_le_four
                    _ = 2 ^ (0 + 2) := by norm_num
                    _ ≤ 2 ^ (n + 2) := by gcongr <;> norm_num)
                  (by positivity))
          _ ≤ (4 / 2 ^ (n + 2)) ^ 3 / 4 := by
            gcongr
            exact Real.pi_le_four
          _ = 1 / (2 ^ n) ^ 3 / 4 := by
            simp [add_comm n, pow_add, div_mul_eq_div_div]
            norm_num
      refine lt_of_lt_of_le hscaled (le_of_eq ?_)
      rw [add_mul]
      congr 1
      · ring
      simp only [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, div_div,
        ← pow_add]
      rw [one_div, one_div, inv_mul_eq_iff_eq_mul₀, eq_comm,
        mul_inv_eq_iff_eq_mul₀, ← pow_add]
      · rw [add_assoc, Nat.mul_succ, add_comm, add_comm n, add_assoc,
          mul_comm n]
      all_goals norm_num
    have pi_lower_bound_start (n : ℕ) {a : ℝ}
        (h : Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n ≤
          (2 : ℝ) - (a / (2 : ℝ) ^ (n + 1)) ^ 2) :
        a < Real.pi := by
      refine lt_of_le_of_lt ?_ (pi_gt_sqrt_series n)
      rw [mul_comm]
      refine
        (div_le_iff₀ (pow_pos (by simp) _)).mp
          (Real.le_sqrt_of_sq_le ?_)
      rwa [le_sub_comm, show (0 : ℝ) = (0 : ℕ) / (1 : ℕ) by
        rw [Nat.cast_zero, zero_div]]
    have sqrt_series_step_up (c d : ℕ) {a b n : ℕ} {z : ℝ}
        (hz : Real.sqrtTwoAddSeries (c / d) n ≤ z)
        (hb : 0 < b) (hd : 0 < d)
        (h : (2 * b + a) * d ^ 2 ≤ c ^ 2 * b) :
        Real.sqrtTwoAddSeries (a / b) (n + 1) ≤ z := by
      refine le_trans ?_ hz
      rw [Real.sqrtTwoAddSeries_succ]
      apply Real.sqrtTwoAddSeries_monotone_left
      have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
      have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
      rw [Real.sqrt_le_left (div_nonneg c.cast_nonneg d.cast_nonneg),
        div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hb'),
        div_le_div_iff₀ hb' (pow_pos hd' _)]
      exact_mod_cast h
    have pi_upper_bound_start (n : ℕ) {a : ℝ}
        (h : (2 : ℝ) -
            ((a - 1 / (4 : ℝ) ^ n) / (2 : ℝ) ^ (n + 1)) ^ 2 ≤
          Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n)
        (h₂ : (1 : ℝ) / (4 : ℝ) ^ n ≤ a) :
        Real.pi < a := by
      refine lt_of_lt_of_le (pi_lt_sqrt_series n) ?_
      rw [← le_sub_iff_add_le, ← le_div_iff₀', Real.sqrt_le_left,
        sub_le_comm]
      · rwa [Nat.cast_zero, zero_div] at h
      · exact
          div_nonneg (sub_nonneg.2 h₂)
            (pow_nonneg (le_of_lt zero_lt_two) _)
      · exact pow_pos zero_lt_two _
    have sqrt_series_step_down (a b : ℕ) {c d n : ℕ} {z : ℝ}
        (hz : z ≤ Real.sqrtTwoAddSeries (a / b) n)
        (hb : 0 < b) (hd : 0 < d)
        (h : a ^ 2 * d ≤ (2 * d + c) * b ^ 2) :
        z ≤ Real.sqrtTwoAddSeries (c / d) (n + 1) := by
      apply le_trans hz
      rw [Real.sqrtTwoAddSeries_succ]
      apply Real.sqrtTwoAddSeries_monotone_left
      apply Real.le_sqrt_of_sq_le
      have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
      have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
      rw [div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hd'),
        div_le_div_iff₀ (pow_pos hb' _) hd']
      exact_mod_cast h
    constructor
    · apply pi_lower_bound_start 4
      refine
        sqrt_series_step_up 338 239 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrt_series_step_up 704 381 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrt_series_step_up 1940 989 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrt_series_step_up 1447 727 ?_
          (by norm_num) (by norm_num) (by norm_num)
      norm_num [Real.sqrtTwoAddSeries]
    · apply pi_upper_bound_start 9
      · refine
          sqrt_series_step_down 4756 3363 ?_
            (by norm_num) (by norm_num) (by norm_num)
        refine
          sqrt_series_step_down 14965 8099 ?_
            (by norm_num) (by norm_num) (by norm_num)
        refine
          sqrt_series_step_down 21183 10799 ?_
            (by norm_num) (by norm_num) (by norm_num)
        refine
          sqrt_series_step_down 49188 24713 ?_
            (by norm_num) (by norm_num) (by norm_num)
        refine
          sqrt_series_step_down 43947 22000 ?_
            (by norm_num) (by norm_num) (by norm_num)
        refine
          sqrt_series_step_down 235667 117869 ?_
            (by norm_num) (by norm_num) (by norm_num)
        refine
          sqrt_series_step_down 624137 312092 ?_
            (by norm_num) (by norm_num) (by norm_num)
        refine
          sqrt_series_step_down 903049 451533 ?_
            (by norm_num) (by norm_num) (by norm_num)
        refine
          sqrt_series_step_down 849938 424971 ?_
            (by norm_num) (by norm_num) (by norm_num)
        norm_num [Real.sqrtTwoAddSeries]
      · norm_num
  refine ⟨hExact, ?_, ?_⟩
  · unfold MatchesDisplayedStoppingTime
    rw [hExact]
    change |338 * Real.pi / 325 - 327 / 100| < 1 / 200
    rw [abs_lt]
    constructor <;> nlinarith [hPiBounds.1, hPiBounds.2]
  · intro choice hChoice
    cases choice with
    | A =>
        exfalso
        unfold MatchesDisplayedStoppingTime at hChoice
        rw [hExact] at hChoice
        change |338 * Real.pi / 325 - 243 / 50| < 1 / 200 at hChoice
        rw [abs_lt] at hChoice
        nlinarith [hPiBounds.2]
    | B => rfl
    | C =>
        exfalso
        unfold MatchesDisplayedStoppingTime at hChoice
        rw [hExact] at hChoice
        change |338 * Real.pi / 325 - 523 / 100| < 1 / 200 at hChoice
        rw [abs_lt] at hChoice
        nlinarith [hPiBounds.2]
    | D =>
        exfalso
        unfold MatchesDisplayedStoppingTime at hChoice
        rw [hExact] at hChoice
        change |338 * Real.pi / 325 - 343 / 50| < 1 / 200 at hChoice
        rw [abs_lt] at hChoice
        nlinarith [hPiBounds.2]

end PhyXMiniProblems.ProblemPhyXMini0781
