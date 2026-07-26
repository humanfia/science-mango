import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0233

open Dimension

/-!
# Small oscillations of a pendulum coupled to a spring

A point mass `M` is carried by the end of a rigid massless rod of length `L`.
A horizontal spring of stiffness `k` is attached to the rod a distance `h`
below the pivot.  The angular coordinate `theta` is dimensionless.  The
physical parameters and frequencies below are unit-independent Physlib
quantities; real numbers are used only for readouts in coherent choices of
units and for the dimensionless angle and displayed answer formulas.
-/

/-! ## Dimensionful physical quantities and coherent-unit readouts -/

/-- Physical mass of the pendulum bob. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- Physical length, used for `L`, `h`, and a displacement per radian. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Gravitational acceleration, with dimension length per time squared. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Force, with dimension mass times length per time squared. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Spring force constant, with dimension force per length, or mass per time squared. -/
abbrev SpringConstantQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Moment of inertia about the pivot, with dimension mass times length squared. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) ℝ)

/-- Torque per radian, with dimension mass times length squared per time squared. -/
abbrev RotationalStiffnessQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Cyclic vibration frequency, in cycles per unit time. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- Angular frequency, in radians per unit time. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- Read a physical mass in a coherent choice of units. -/
def massReadout (units : UnitChoices) (mass : MassQuantity) : ℝ :=
  (mass units).val

/-- Read a physical length in a coherent choice of units. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  (length units).val

/-- Read a physical acceleration in a coherent choice of units. -/
def accelerationReadout
    (units : UnitChoices) (acceleration : AccelerationQuantity) : ℝ :=
  (acceleration units).val

/-- Read a physical force in a coherent choice of units. -/
def forceReadout (units : UnitChoices) (force : ForceQuantity) : ℝ :=
  (force units).val

/-- Read a spring constant in coherent mass and time units. -/
def springConstantReadout
    (units : UnitChoices) (springConstant : SpringConstantQuantity) : ℝ :=
  (springConstant units).val

/-- Read a moment of inertia in coherent mass and length units. -/
def momentOfInertiaReadout
    (units : UnitChoices) (momentOfInertia : MomentOfInertiaQuantity) : ℝ :=
  (momentOfInertia units).val

/-- Read a rotational stiffness in a coherent choice of units. -/
def rotationalStiffnessReadout
    (units : UnitChoices) (stiffness : RotationalStiffnessQuantity) : ℝ :=
  (stiffness units).val

/-- Read a cyclic frequency in inverse units of the selected time unit. -/
def frequencyReadout
    (units : UnitChoices) (frequency : FrequencyQuantity) : ℝ :=
  (frequency units).val

/-- Read an angular frequency in radians per selected time unit. -/
def angularFrequencyReadout
    (units : UnitChoices) (frequency : AngularFrequencyQuantity) : ℝ :=
  (frequency units).val

/-! ## Labels and qualitative information supplied by the diagram -/

/-- Symbolic labels printed in the primary figure. -/
inductive FigureLabel where
  | pendulumLength_L
  | attachmentDistance_h
  | bobMass_M
  | springConstant_k
  | angularDisplacement_theta
  deriving DecidableEq, Repr

/-- Orientations relevant to the pictured equilibrium configuration. -/
inductive Orientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The stated mechanical treatment of the suspension rod. -/
inductive RodRigidity where
  | rigid
  | flexible
  deriving DecidableEq, Repr

/-- Whether the rod's own inertia is included in the model. -/
inductive RodMassTreatment where
  | ignored
  | included
  deriving DecidableEq, Repr

/-- The amplitude regime in which the equation of motion is modeled. -/
inductive OscillationRegime where
  | smallAngleLinearized
  | finiteAmplitude
  deriving DecidableEq, Repr

/-- The spring state at the vertical equilibrium shown in the diagram. -/
inductive SpringEquilibriumState where
  | relaxed
  | prestretched
  deriving DecidableEq, Repr

/-!
Qualitative evidence read from the supplied image.  It contains no numerical
scale; it identifies the pivot, rod, bob, horizontal spring, attachment point,
fixed wall, and the labels `L`, `h`, `M`, `k`, and `theta`.
-/
structure SpringPendulumFigure where
  showsPivot : Bool
  showsRod : Bool
  showsBob : Bool
  showsSpring : Bool
  showsFixedWall : Bool
  rodLabel : FigureLabel
  attachmentDistanceLabel : FigureLabel
  bobLabel : FigureLabel
  springLabel : FigureLabel
  angleLabel : FigureLabel
  springAttachesToRod : Bool
  springAttachesToFixedWall : Bool
  equilibriumRodOrientation : Orientation
  equilibriumSpringOrientation : Orientation

/-! ## Physical setup, problem data, and governing laws -/

/-!
The independent physical inputs, intermediate generalized-coordinate
quantities, and the two requested frequency quantities.  In particular,
neither frequency is defined by an answer formula.
-/
structure SpringPendulumSetup where
  pendulumLength_L : LengthQuantity
  attachmentDistance_h : LengthQuantity
  bobMass_M : MassQuantity
  gravitationalAcceleration_g : AccelerationQuantity
  springConstant_k : SpringConstantQuantity
  attachmentHorizontalDisplacementPerRadian : LengthQuantity
  springForcePerRadian : ForceQuantity
  bobMomentOfInertia : MomentOfInertiaQuantity
  gravitationalRotationalStiffness : RotationalStiffnessQuantity
  springRotationalStiffness : RotationalStiffnessQuantity
  totalRotationalStiffness : RotationalStiffnessQuantity
  angularFrequency : AngularFrequencyQuantity
  vibrationFrequency : FrequencyQuantity
  rodRigidity : RodRigidity
  rodMassTreatment : RodMassTreatment
  oscillationRegime : OscillationRegime
  springEquilibriumState : SpringEquilibriumState
  figure : SpringPendulumFigure

/-!
Problem-statement data and primary-image readouts.  Relaxation of the spring
at the depicted vertical equilibrium is the standard ideal-spring condition
needed for that configuration to be torque-free.  No frequency relation or
answer choice is included here.
-/
structure MatchesProblemAndSuppliedFigure
    (setup : SpringPendulumSetup) : Prop where
  rigidRod : setup.rodRigidity = .rigid
  rodMassIgnored : setup.rodMassTreatment = .ignored
  smallAmplitude : setup.oscillationRegime = .smallAngleLinearized
  springRelaxedAtVerticalEquilibrium :
    setup.springEquilibriumState = .relaxed
  figureShowsPivot : setup.figure.showsPivot = true
  figureShowsRod : setup.figure.showsRod = true
  figureShowsBob : setup.figure.showsBob = true
  figureShowsSpring : setup.figure.showsSpring = true
  figureShowsFixedWall : setup.figure.showsFixedWall = true
  figureRodLabel : setup.figure.rodLabel = .pendulumLength_L
  figureAttachmentDistanceLabel :
    setup.figure.attachmentDistanceLabel = .attachmentDistance_h
  figureBobLabel : setup.figure.bobLabel = .bobMass_M
  figureSpringLabel : setup.figure.springLabel = .springConstant_k
  figureAngleLabel : setup.figure.angleLabel = .angularDisplacement_theta
  figureSpringRodAttachment : setup.figure.springAttachesToRod = true
  figureSpringWallAttachment : setup.figure.springAttachesToFixedWall = true
  figureVerticalEquilibriumRod :
    setup.figure.equilibriumRodOrientation = .vertical
  figureHorizontalEquilibriumSpring :
    setup.figure.equilibriumSpringOrientation = .horizontal

/-- Positivity and geometric nondegeneracy of the physical parameters. -/
structure HasPhysicalSpringPendulumParameters
    (setup : SpringPendulumSetup) : Prop where
  pendulumLengthPositive :
    ∀ units, 0 < lengthReadout units setup.pendulumLength_L
  attachmentDistancePositive :
    ∀ units, 0 < lengthReadout units setup.attachmentDistance_h
  attachmentNotBeyondBob :
    ∀ units,
      lengthReadout units setup.attachmentDistance_h ≤
        lengthReadout units setup.pendulumLength_L
  bobMassPositive : ∀ units, 0 < massReadout units setup.bobMass_M
  gravitationalAccelerationPositive :
    ∀ units, 0 < accelerationReadout units setup.gravitationalAcceleration_g
  springConstantPositive :
    ∀ units, 0 < springConstantReadout units setup.springConstant_k
  bobMomentOfInertiaPositive :
    ∀ units, 0 < momentOfInertiaReadout units setup.bobMomentOfInertia
  totalRotationalStiffnessPositive :
    ∀ units,
      0 < rotationalStiffnessReadout units setup.totalRotationalStiffness
  angularFrequencyPositive :
    ∀ units, 0 < angularFrequencyReadout units setup.angularFrequency
  vibrationFrequencyPositive :
    ∀ units, 0 < frequencyReadout units setup.vibrationFrequency

/-!
The governing rigid-body, small-angle geometry, Hooke-law, and torque laws:

* the point bob has moment of inertia `M L^2` about the pivot;
* the attachment moves horizontally by `h theta` to first order;
* Hooke's law turns that displacement into force coefficient `k h`;
* the lever arm `h` turns that force into spring torque coefficient `k h^2`;
* gravity contributes torque coefficient `M g L`;
* independent restoring torques add.

The intermediate quantities are kept explicit so that `k h^2` is derived
from geometry and Hooke's law rather than inserted as the requested answer.
-/
structure SatisfiesSmallAngleTorqueLaws
    (setup : SpringPendulumSetup) : Prop where
  pointBobMomentOfInertia :
    ∀ units,
      momentOfInertiaReadout units setup.bobMomentOfInertia =
        massReadout units setup.bobMass_M *
          lengthReadout units setup.pendulumLength_L ^ 2
  attachmentDisplacementGeometry :
    ∀ units,
      lengthReadout units setup.attachmentHorizontalDisplacementPerRadian =
        lengthReadout units setup.attachmentDistance_h
  hookeLawForLinearizedSpringForce :
    ∀ units,
      forceReadout units setup.springForcePerRadian =
        springConstantReadout units setup.springConstant_k *
          lengthReadout units setup.attachmentHorizontalDisplacementPerRadian
  springTorqueMomentArm :
    ∀ units,
      rotationalStiffnessReadout units setup.springRotationalStiffness =
        forceReadout units setup.springForcePerRadian *
          lengthReadout units setup.attachmentDistance_h
  linearizedGravityTorque :
    ∀ units,
      rotationalStiffnessReadout units
          setup.gravitationalRotationalStiffness =
        massReadout units setup.bobMass_M *
          accelerationReadout units setup.gravitationalAcceleration_g *
            lengthReadout units setup.pendulumLength_L
  restoringTorqueAddition :
    ∀ units,
      rotationalStiffnessReadout units setup.totalRotationalStiffness =
        rotationalStiffnessReadout units
            setup.gravitationalRotationalStiffness +
          rotationalStiffnessReadout units setup.springRotationalStiffness

/-!
In any coherent unit system, the generalized angular equation
`I theta'' + K theta = 0` has the same scalar form as Physlib's classical
harmonic oscillator.  Here the structure's generalized `m` readout is the
moment of inertia `I`, and its generalized `k` readout is the total rotational
stiffness `K`; their ratio still has dimension inverse time squared.
-/
def effectiveAngularOscillatorInUnits
    (setup : SpringPendulumSetup)
    (hPhysical : HasPhysicalSpringPendulumParameters setup)
    (units : UnitChoices) : ClassicalMechanics.HarmonicOscillator where
  m := momentOfInertiaReadout units setup.bobMomentOfInertia
  k := rotationalStiffnessReadout units setup.totalRotationalStiffness
  m_pos := hPhysical.bobMomentOfInertiaPositive units
  k_pos := hPhysical.totalRotationalStiffnessPositive units

/-!
The remaining small-oscillation laws: Physlib supplies
`omega = sqrt (K / I)` for the unitwise generalized oscillator, and ordinary
frequency is related by `omega = 2 pi f`.  These laws do not contain the
problem-specific closed form or an answer-choice label.
-/
structure SatisfiesSmallAngleFrequencyLaws
    (setup : SpringPendulumSetup)
    (hPhysical : HasPhysicalSpringPendulumParameters setup) : Prop where
  physlibGeneralizedAngularFrequency :
    ∀ units,
      angularFrequencyReadout units setup.angularFrequency =
        (effectiveAngularOscillatorInUnits setup hPhysical units).ω
  angularToCyclicFrequency :
    ∀ units,
      angularFrequencyReadout units setup.angularFrequency =
        2 * Real.pi * frequencyReadout units setup.vibrationFrequency

/-! ## Derived relations and displayed answer choices -/

/-- The small-angle spring geometry and Hooke's law yield torque coefficient `k h^2`. -/
lemma springRotationalStiffness_eq_k_mul_h_sq
    (setup : SpringPendulumSetup)
    (hTorque : SatisfiesSmallAngleTorqueLaws setup) :
    ∀ units,
      rotationalStiffnessReadout units setup.springRotationalStiffness =
        springConstantReadout units setup.springConstant_k *
          lengthReadout units setup.attachmentDistance_h ^ 2 := by
  intro units
  rw [hTorque.springTorqueMomentArm units,
    hTorque.hookeLawForLinearizedSpringForce units,
    hTorque.attachmentDisplacementGeometry units]
  ring

/-- The cyclic small-oscillation frequency in the closed form requested by the problem. -/
lemma smallAngle_vibrationFrequency_formula
    (setup : SpringPendulumSetup)
    (hPhysical : HasPhysicalSpringPendulumParameters setup)
    (hTorque : SatisfiesSmallAngleTorqueLaws setup)
    (hFrequency : SatisfiesSmallAngleFrequencyLaws setup hPhysical) :
    ∀ units,
      frequencyReadout units setup.vibrationFrequency =
        1 /
            (2 * Real.pi *
              lengthReadout units setup.pendulumLength_L) *
          Real.sqrt
            (accelerationReadout units setup.gravitationalAcceleration_g *
                lengthReadout units setup.pendulumLength_L +
              springConstantReadout units setup.springConstant_k *
                  lengthReadout units setup.attachmentDistance_h ^ 2 /
                massReadout units setup.bobMass_M) := by
  intro units
  have hL := hPhysical.pendulumLengthPositive units
  have hM := hPhysical.bobMassPositive units
  have hg := hPhysical.gravitationalAccelerationPositive units
  have hk := hPhysical.springConstantPositive units
  have hA :
      0 ≤
        accelerationReadout units setup.gravitationalAcceleration_g *
            lengthReadout units setup.pendulumLength_L +
          springConstantReadout units setup.springConstant_k *
              lengthReadout units setup.attachmentDistance_h ^ 2 /
            massReadout units setup.bobMass_M := by
    positivity
  have hRatio :
      rotationalStiffnessReadout units setup.totalRotationalStiffness /
          momentOfInertiaReadout units setup.bobMomentOfInertia =
        (accelerationReadout units setup.gravitationalAcceleration_g *
              lengthReadout units setup.pendulumLength_L +
            springConstantReadout units setup.springConstant_k *
                lengthReadout units setup.attachmentDistance_h ^ 2 /
              massReadout units setup.bobMass_M) /
          lengthReadout units setup.pendulumLength_L ^ 2 := by
    rw [hTorque.restoringTorqueAddition units,
      hTorque.linearizedGravityTorque units,
      springRotationalStiffness_eq_k_mul_h_sq setup hTorque units,
      hTorque.pointBobMomentOfInertia units]
    field_simp [ne_of_gt hM, ne_of_gt hL]
  rw [show
    frequencyReadout units setup.vibrationFrequency =
        angularFrequencyReadout units setup.angularFrequency /
          (2 * Real.pi) by
      apply (eq_div_iff (mul_ne_zero (by norm_num) Real.pi_ne_zero)).2
      simpa [mul_comm] using
        (hFrequency.angularToCyclicFrequency units).symm]
  rw [hFrequency.physlibGeneralizedAngularFrequency units]
  simp only [ClassicalMechanics.HarmonicOscillator.ω,
    effectiveAngularOscillatorInUnits]
  rw [hRatio, Real.sqrt_div hA, Real.sqrt_sq hL.le]
  field_simp [Real.pi_ne_zero, ne_of_gt hL]

/-- Labels of the four symbolic answer choices printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-!
The printed answer formulas interpreted as scalar coherent-unit readouts.
The three distractors are transcribed literally even though their displayed
summands are not dimensionally homogeneous.  This function is answer-list
metadata and does not constrain the independent physical frequency.
-/
def displayedAnswerFrequencyReadout
    (setup : SpringPendulumSetup) (units : UnitChoices) : AnswerChoice → ℝ
  | .A =>
      1 /
          (2 * Real.pi * lengthReadout units setup.pendulumLength_L) *
        Real.sqrt
          (accelerationReadout units setup.gravitationalAcceleration_g *
              lengthReadout units setup.pendulumLength_L +
            springConstantReadout units setup.springConstant_k *
                lengthReadout units setup.attachmentDistance_h /
              massReadout units setup.bobMass_M ^ 2)
  | .B =>
      1 /
          (2 * Real.pi * lengthReadout units setup.pendulumLength_L) *
        Real.sqrt
          (accelerationReadout units setup.gravitationalAcceleration_g *
              lengthReadout units setup.pendulumLength_L +
            springConstantReadout units setup.springConstant_k ^ 2 *
                lengthReadout units setup.attachmentDistance_h /
              massReadout units setup.bobMass_M)
  | .C =>
      1 /
          (2 * Real.pi * lengthReadout units setup.pendulumLength_L) *
        Real.sqrt
          (accelerationReadout units setup.gravitationalAcceleration_g *
              lengthReadout units setup.pendulumLength_L +
            springConstantReadout units setup.springConstant_k /
              (massReadout units setup.bobMass_M *
                lengthReadout units setup.attachmentDistance_h ^ 2))
  | .D =>
      1 /
          (2 * Real.pi * lengthReadout units setup.pendulumLength_L) *
        Real.sqrt
          (accelerationReadout units setup.gravitationalAcceleration_g *
              lengthReadout units setup.pendulumLength_L +
            springConstantReadout units setup.springConstant_k *
                lengthReadout units setup.attachmentDistance_h ^ 2 /
              massReadout units setup.bobMass_M)

/-- The answer label recorded by the dataset, retained only as metadata. -/
def recordedDatasetAnswerChoice : AnswerChoice := .D

/-- The modeled physical frequency agrees with the formula printed for a choice. -/
def MatchesAnswerChoice
    (setup : SpringPendulumSetup) (choice : AnswerChoice) : Prop :=
  ∀ units,
    frequencyReadout units setup.vibrationFrequency =
      displayedAnswerFrequencyReadout setup units choice

/-!
The small-angle torque equation is
`M L^2 theta'' + (M g L + k h^2) theta = 0`.  Hence

`f = (1 / (2 pi L)) sqrt (g L + k h^2 / M)`,

which is answer choice `D`.  This is the formal target corresponding to
blueprint label `thm:physics:phyx_mini_0233:target`.
-/
theorem problem_phyx_mini_0233
    (setup : SpringPendulumSetup)
    (hProblem : MatchesProblemAndSuppliedFigure setup)
    (hPhysical : HasPhysicalSpringPendulumParameters setup)
    (hTorque : SatisfiesSmallAngleTorqueLaws setup)
    (hFrequency : SatisfiesSmallAngleFrequencyLaws setup hPhysical) :
    MatchesAnswerChoice setup .D := by
  intro units
  simpa [displayedAnswerFrequencyReadout] using
    smallAngle_vibrationFrequency_formula setup hPhysical hTorque hFrequency units

end PhyXMiniProblems.ProblemPhyXMini0233
