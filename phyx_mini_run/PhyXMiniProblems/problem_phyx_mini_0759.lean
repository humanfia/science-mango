import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/-!
# Horizontal push on a crate on a frictionless ramp

This file models problem `phyx_mini_0759`. A crate of mass `100 kg` moves at
constant speed up a frictionless ramp inclined at `30°`. The supplied image
shows the applied force `F` pointing horizontally to the right, rather than
parallel to the ramp. The requested quantity is the magnitude of the contact
force exerted on the crate by the ramp.

Mass, force, acceleration, and speed are represented by Physlib dimensionful
quantities. Real numbers occur only as coherent SI readouts, dimensionless
angles, and displayed answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0759

open Dimension

/-! ## Dimensionful physical quantities and coherent SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical force magnitude. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A signed acceleration component in ramp-adapted coordinates. -/
abbrev SignedAccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A nonnegative physical speed. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) NNReal)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (quantity : MassQuantity) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Newton readout of a physical force magnitude. -/
def forceInNewtons (quantity : ForceQuantity) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Metres-per-second-squared readout of a nonnegative acceleration. -/
def accelerationInMetersPerSecondSquared
    (quantity : AccelerationQuantity) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Metres-per-second-squared readout of a signed acceleration component. -/
def signedAccelerationInMetersPerSecondSquared
    (quantity : SignedAccelerationQuantity) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Metres-per-second readout of a physical speed. -/
def speedInMetersPerSecond (quantity : SpeedQuantity) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Convert an angle stated in degrees to its dimensionless radian value. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-! ## Scenario roles and primary-image geometry -/

/-- Idealized contact between the crate and the ramp. -/
inductive ContactModel where
  | frictionless
  | withFriction
  deriving DecidableEq, Repr

/-- Direction of the crate's translational motion along the ramp. -/
inductive RampMotionDirection where
  | upRamp
  | downRamp
  deriving DecidableEq, Repr

/-- Whether the scalar speed changes during the depicted motion. -/
inductive SpeedRegime where
  | constant
  | varying
  deriving DecidableEq, Repr

/-- Distinguished force directions in the vertical cross-section. -/
inductive ForceDirection where
  | horizontalRight
  | upRamp
  | normalAwayFromRamp
  deriving DecidableEq, Repr

/-- Qualitative orientation of the ramp in the supplied image. -/
inductive RampOrientation where
  | risesToRight
  | risesToLeft
  deriving DecidableEq, Repr

/-- Physical elements explicitly visible in the supplied image. -/
inductive FigureComponent where
  | crate
  | inclinedRamp
  | appliedForceArrow
  deriving DecidableEq, Repr

/-- Symbols printed in the supplied image. -/
inductive FigureLabel where
  | massM
  | angleTheta
  | forceF
  deriving DecidableEq, Repr

/-- A structured readout of the primary image. -/
structure SuppliedFigure where
  visible : FigureComponent → Prop
  labelRefersTo : FigureLabel → FigureComponent
  rampOrientation : RampOrientation
  appliedForceArrowDirection : ForceDirection

/-! ## Physical setup, stated data, and figure readouts -/

/--
The crate-ramp apparatus and its unknown force magnitudes and acceleration
components. In particular, `rampForceMagnitude` is an independent physical
quantity; it is not defined from a displayed answer or from the desired
closed form.
-/
structure CrateOnRampSetup where
  crateMass : MassQuantity
  gravitationalAcceleration : AccelerationQuantity
  crateSpeed : SpeedQuantity
  appliedForceMagnitude : ForceQuantity
  rampForceMagnitude : ForceQuantity
  tangentialAcceleration : SignedAccelerationQuantity
  outwardNormalAcceleration : SignedAccelerationQuantity
  rampAngleDegrees : ℝ
  contactModel : ContactModel
  motionDirection : RampMotionDirection
  speedRegime : SpeedRegime
  appliedForceDirection : ForceDirection
  rampForceDirection : ForceDirection
  figure : SuppliedFigure

/--
Problem-statement data and the standard gravitational calibration used by the
displayed numerical choices. No value of the ramp force occurs here.
-/
structure MatchesProblemData (setup : CrateOnRampSetup) : Prop where
  crateMassKilograms : massInKilograms setup.crateMass = 100
  standardGravity :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      98 / 10
  inclineAngleDegrees : setup.rampAngleDegrees = 30
  frictionlessContact : setup.contactModel = .frictionless
  movesUpRamp : setup.motionDirection = .upRamp
  speedIsConstant : setup.speedRegime = .constant
  appliedForceIsHorizontal :
    setup.appliedForceDirection = .horizontalRight

/--
Primary-image readout: the ramp rises to the right, the crate is labelled
`m`, `θ` labels the incline, and the arrow labelled `F` is horizontal.
-/
structure MatchesSuppliedFigure (setup : CrateOnRampSetup) : Prop where
  crateVisible : setup.figure.visible .crate
  rampVisible : setup.figure.visible .inclinedRamp
  forceArrowVisible : setup.figure.visible .appliedForceArrow
  massLabelOnCrate : setup.figure.labelRefersTo .massM = .crate
  thetaLabelOnRamp : setup.figure.labelRefersTo .angleTheta = .inclinedRamp
  forceLabelOnArrow :
    setup.figure.labelRefersTo .forceF = .appliedForceArrow
  rampRisesToRight : setup.figure.rampOrientation = .risesToRight
  forceArrowIsHorizontal :
    setup.figure.appliedForceArrowDirection = .horizontalRight

/-! ## Kinematics and governing dynamics -/

/-- Positivity and acute-angle conditions selecting the physical branch. -/
structure HasPhysicalParameters (setup : CrateOnRampSetup) : Prop where
  massPositive : 0 < massInKilograms setup.crateMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  speedPositive : 0 < speedInMetersPerSecond setup.crateSpeed
  appliedForcePositive : 0 < forceInNewtons setup.appliedForceMagnitude
  rampForcePositive : 0 < forceInNewtons setup.rampForceMagnitude
  inclineAnglePositive : 0 < degreesToRadians setup.rampAngleDegrees
  inclineAngleLessThanRightAngle :
    degreesToRadians setup.rampAngleDegrees < Real.pi / 2
  inclineCosinePositive :
    0 < Real.cos (degreesToRadians setup.rampAngleDegrees)

/--
For straight-line motion up the ramp at constant speed, both ramp-adapted
components of the crate's acceleration vanish.
-/
structure SatisfiesConstantVelocityKinematics
    (setup : CrateOnRampSetup) : Prop where
  zeroTangentialAcceleration :
    signedAccelerationInMetersPerSecondSquared
        setup.tangentialAcceleration = 0
  zeroNormalAcceleration :
    signedAccelerationInMetersPerSecondSquared
        setup.outwardNormalAcceleration = 0

/-- Gravitational-force magnitude `m g`, read in newtons. -/
def weightInNewtons (setup : CrateOnRampSetup) : ℝ :=
  massInKilograms setup.crateMass *
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration

/--
Newton's second law resolved tangent to the ramp and along the outward ramp
normal. A horizontal push has tangential component `F cos θ` and inward-normal
component `F sin θ`; gravity contributes inward components `mg sin θ` and
`mg cos θ`. The frictionless contact force is normal to the ramp.

These are governing component balances. They do not state the requested
normal-force value or any displayed answer.
-/
structure SatisfiesFrictionlessRampDynamics
    (setup : CrateOnRampSetup) : Prop where
  contactForceIsNormal :
    setup.rampForceDirection = .normalAwayFromRamp
  newtonSecondLawTangential :
    forceInNewtons setup.appliedForceMagnitude *
          Real.cos (degreesToRadians setup.rampAngleDegrees) -
        weightInNewtons setup *
          Real.sin (degreesToRadians setup.rampAngleDegrees) =
      massInKilograms setup.crateMass *
        signedAccelerationInMetersPerSecondSquared
          setup.tangentialAcceleration
  newtonSecondLawNormal :
    forceInNewtons setup.rampForceMagnitude -
          forceInNewtons setup.appliedForceMagnitude *
            Real.sin (degreesToRadians setup.rampAngleDegrees) -
        weightInNewtons setup *
          Real.cos (degreesToRadians setup.rampAngleDegrees) =
      massInKilograms setup.crateMass *
        signedAccelerationInMetersPerSecondSquared
          setup.outwardNormalAcceleration

/-!
Eliminating the unknown horizontal push from the two zero-acceleration
component balances gives `N = mg / cos θ`.
-/
lemma rampForce_eq_weight_div_cosine
    (setup : CrateOnRampSetup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalParameters setup)
    (_kinematics : SatisfiesConstantVelocityKinematics setup)
    (_dynamics : SatisfiesFrictionlessRampDynamics setup) :
    forceInNewtons setup.rampForceMagnitude =
      weightInNewtons setup /
        Real.cos (degreesToRadians setup.rampAngleDegrees) := by
  have hcos : Real.cos (degreesToRadians setup.rampAngleDegrees) ≠ 0 :=
    ne_of_gt _physical.inclineCosinePositive
  apply (eq_div_iff hcos).2
  have ht := _dynamics.newtonSecondLawTangential
  have hn := _dynamics.newtonSecondLawNormal
  rw [_kinematics.zeroTangentialAcceleration, mul_zero] at ht
  rw [_kinematics.zeroNormalAcceleration, mul_zero] at hn
  have hnc :
      forceInNewtons setup.rampForceMagnitude *
          Real.cos (degreesToRadians setup.rampAngleDegrees) =
        weightInNewtons setup *
          (Real.sin (degreesToRadians setup.rampAngleDegrees) ^ 2 +
            Real.cos (degreesToRadians setup.rampAngleDegrees) ^ 2) := by
    linear_combination
      Real.sin (degreesToRadians setup.rampAngleDegrees) * ht +
      Real.cos (degreesToRadians setup.rampAngleDegrees) * hn
  simpa [Real.sin_sq_add_cos_sq] using hnc

/-! ## Displayed answers and formalization target -/

/-- Labels of the four displayed answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Force magnitudes in newtons printed beside the answer labels. -/
def AnswerChoice.forceInNewtons : AnswerChoice → ℝ
  | .A => 98 / 100 * 1000
  | .B => 102 / 100 * 1000
  | .C => 113 / 100 * 1000
  | .D => 126 / 100 * 1000

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- A displayed choice is uniquely closest to the derived ramp-force value. -/
def IsUniqueClosestAnswer
    (setup : CrateOnRampSetup) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice : AnswerChoice,
    otherChoice ≠ choice →
      |forceInNewtons setup.rampForceMagnitude - choice.forceInNewtons| <
        |forceInNewtons setup.rampForceMagnitude -
          otherChoice.forceInNewtons|

/-!
For `m = 100 kg`, `g = 9.8 m/s²`, and `θ = 30°`, the frictionless ramp's
force has exact magnitude `1960√3/3 N`, approximately `1.13 × 10³ N`.
Consequently choice C is uniquely closest among the displayed values.

This formalizes blueprint label `thm:physics:phyx_mini_0759:target`.
-/
theorem rampForceMagnitude_is_1960_sqrtThree_over_three_and_matches_C
    (setup : CrateOnRampSetup)
    (_data : MatchesProblemData setup)
    (_figure : MatchesSuppliedFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_kinematics : SatisfiesConstantVelocityKinematics setup)
    (_dynamics : SatisfiesFrictionlessRampDynamics setup) :
    forceInNewtons setup.rampForceMagnitude =
        1960 * Real.sqrt 3 / 3 ∧
      IsUniqueClosestAnswer setup recordedAnswerChoice ∧
      recordedAnswerChoice = .C := by
  have hangle :
      degreesToRadians setup.rampAngleDegrees = Real.pi / 6 := by
    rw [_data.inclineAngleDegrees]
    unfold degreesToRadians
    ring
  have hforce := rampForce_eq_weight_div_cosine
    setup _data _physical _kinematics _dynamics
  rw [hangle, Real.cos_pi_div_six] at hforce
  have hweight : weightInNewtons setup = 980 := by
    unfold weightInNewtons
    rw [_data.crateMassKilograms, _data.standardGravity]
    norm_num
  rw [hweight] at hforce
  have hsqrtpos : 0 < Real.sqrt 3 :=
    Real.sqrt_pos.2 (by norm_num)
  have hsqrtsq : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hradical :
      (980 : ℝ) / (Real.sqrt 3 / 2) =
        1960 * Real.sqrt 3 / 3 := by
    field_simp [ne_of_gt hsqrtpos]
    nlinarith
  have hforceExact :
      forceInNewtons setup.rampForceMagnitude =
        1960 * Real.sqrt 3 / 3 := hforce.trans hradical
  have hsqrtLower : (173 : ℝ) / 100 < Real.sqrt 3 := by
    nlinarith
  have hsqrtUpper : Real.sqrt 3 < (7 : ℝ) / 4 := by
    nlinarith
  have hforceLower : (1130 : ℝ) <
      1960 * Real.sqrt 3 / 3 := by
    nlinarith
  have hforceUpper :
      1960 * Real.sqrt 3 / 3 < (1195 : ℝ) := by
    nlinarith
  refine ⟨hforceExact, ?_, rfl⟩
  intro otherChoice hne
  rw [hforceExact]
  cases otherChoice with
  | A =>
      simp only [recordedAnswerChoice, AnswerChoice.forceInNewtons]
      rw [abs_of_nonneg (by linarith : 0 ≤
        1960 * Real.sqrt 3 / 3 - 113 / 100 * 1000)]
      rw [abs_of_nonneg (by linarith : 0 ≤
        1960 * Real.sqrt 3 / 3 - 98 / 100 * 1000)]
      norm_num
  | B =>
      simp only [recordedAnswerChoice, AnswerChoice.forceInNewtons]
      rw [abs_of_nonneg (by linarith : 0 ≤
        1960 * Real.sqrt 3 / 3 - 113 / 100 * 1000)]
      rw [abs_of_nonneg (by linarith : 0 ≤
        1960 * Real.sqrt 3 / 3 - 102 / 100 * 1000)]
      norm_num
  | C =>
      exact (hne rfl).elim
  | D =>
      simp only [recordedAnswerChoice, AnswerChoice.forceInNewtons]
      rw [abs_of_nonneg (by linarith : 0 ≤
        1960 * Real.sqrt 3 / 3 - 113 / 100 * 1000)]
      rw [abs_of_nonpos (by linarith : 1960 * Real.sqrt 3 / 3 -
        126 / 100 * 1000 ≤ 0)]
      norm_num
      linarith

end PhyXMiniProblems.ProblemPhyXMini0759
