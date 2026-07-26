import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.Units.WithDim.Basic

/-!
# Small angular oscillations of an end-pivoted plank supported by a spring

This file models problem `phyx_mini_0232`. A uniform plank of mass `5.00 kg`
and length `2.00 m` is pivoted at its left end. A vertical spring of force
constant `100 N/m`, anchored below the plank, supports the free end. The plank
is released from a small angular displacement about its horizontal static
equilibrium.

The requested quantity is explicitly the angular frequency of the *linearized*
motion. The finite-angle endpoint geometry and the first-order torque law are
kept separate: `HasDerivAt` records the local Hooke/lever-arm approximation at
the horizontal equilibrium instead of turning it into a global equality.

Physical quantities use Physlib's dimensionful values. Real numbers occur only
as coherent SI readouts, signed scalar components, dimensionless radian angles,
and displayed numerical answers.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0232

open Dimension

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative acceleration magnitude, with dimension length per time squared. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A spring force constant, with coherent SI unit newtons per metre. -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A moment of inertia, with coherent SI unit kilogram metre squared. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/--
The positive coefficient in the local law `tau(theta) = -kappa theta + o(theta)`.
Radians are dimensionless, so its dimension is that of torque.
-/
abbrev TorsionalStiffnessQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative angular frequency; radians are dimensionless. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A signed angular velocity; radians are dimensionless. -/
abbrev AngularVelocityQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Metres-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Newton-per-metre readout of a spring force constant. -/
def springStiffnessInNewtonsPerMeter
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  ((stiffness UnitChoices.SI).val : ℝ)

/-- Kilogram-metre-squared readout of a moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Newton-metre-per-radian readout of a local torsional stiffness. -/
def torsionalStiffnessInNewtonMetersPerRadian
    (stiffness : TorsionalStiffnessQuantity) : ℝ :=
  ((stiffness UnitChoices.SI).val : ℝ)

/-- Radians-per-second readout of a nonnegative angular frequency. -/
def angularFrequencyInRadiansPerSecond
    (frequency : AngularFrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Radians-per-second readout of a signed angular velocity. -/
def angularVelocityInRadiansPerSecond
    (velocity : AngularVelocityQuantity) : ℝ :=
  (velocity UnitChoices.SI).val

/-! ## Apparatus and figure-derived geometry -/

/-- The two distinguished ends of the plank. -/
inductive PlankEnd where
  | pivotEnd
  | freeEnd
  deriving DecidableEq, Repr

/-- Orientations used by the problem statement and primary image. -/
inductive Orientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The direction of rotation displayed by the curved arrow. -/
inductive RotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Whether the plank is modeled as having a uniform linear mass density. -/
inductive PlankMassDistribution where
  | uniform
  | unspecified
  deriving DecidableEq, Repr

/-- The approximation regime named in the source. -/
inductive OscillationRegime where
  | linearizedSmallOscillationAboutHorizontalEquilibrium
  | finiteAngleNonlinearMotion
  deriving DecidableEq, Repr

/-- Mathematical labels printed in the primary image. -/
inductive FigureLabel where
  | plankLength_L
  | angularDisplacement_theta
  | springConstant_k
  deriving DecidableEq, Repr

/-- Qualitative geometry read directly from the supplied image. -/
structure PivotedPlankSpringFigure where
  pivotLocation : PlankEnd
  springAttachmentLocation : PlankEnd
  equilibriumReferenceOrientation : Orientation
  springOrientationAtDisplayedPose : Orientation
  springAnchoredBelow : Bool
  displayedRotationSense : RotationSense
  lengthLabel : FigureLabel
  angleLabel : FigureLabel
  springLabel : FigureLabel

/-!
The apparatus and the scalar response functions used to describe its local
rotational behavior. Angles are in radians and are positive clockwise. Thus
`springEndDownwardDisplacementMetersAtAngle theta` is a signed SI component,
and `netClockwiseTorqueNewtonMetersAtAngle theta` is a signed torque component.

`linearizedAngularFrequency` is an unconstrained physical output at this
level. The governing laws below connect it to the local derivative of the
actual torque response; the structure itself does not contain the answer.
-/
structure PivotedPlankSpringSetup where
  plankMass : MassQuantity
  plankLength : LengthQuantity
  springForceConstant : SpringStiffnessQuantity
  gravitationalAccelerationMagnitude : AccelerationQuantity
  equilibriumSpringCompression : LengthQuantity
  momentOfInertiaAboutPivot : MomentOfInertiaQuantity
  effectiveTorsionalStiffness : TorsionalStiffnessQuantity
  linearizedAngularFrequency : AngularFrequencyQuantity
  springEndDownwardDisplacementMetersAtAngle : ℝ → ℝ
  springCompressionChangeMetersAtAngle : ℝ → ℝ
  netClockwiseTorqueNewtonMetersAtAngle : ℝ → ℝ
  initialAngularDisplacementRadians : ℝ
  initialAngularVelocity : AngularVelocityQuantity
  massDistribution : PlankMassDistribution
  oscillationRegime : OscillationRegime
  figure : PivotedPlankSpringFigure

/-!
The numerical givens, release condition, and image readouts. The uniform-plank
premise is made explicit because it is the mass model needed for the recorded
answer. No field constrains the requested frequency or chooses an answer.
-/
structure MatchesProblemAndFigure
    (setup : PivotedPlankSpringSetup) : Prop where
  plankMassReadout : massInKilograms setup.plankMass = 5
  plankLengthReadout : lengthInMeters setup.plankLength = 2
  springConstantReadout :
    springStiffnessInNewtonsPerMeter setup.springForceConstant = 100
  uniformPlank : setup.massDistribution = .uniform
  nonzeroInitialDisplacement : setup.initialAngularDisplacementRadians ≠ 0
  releasedFromRest :
    angularVelocityInRadiansPerSecond setup.initialAngularVelocity = 0
  smallOscillationModel :
    setup.oscillationRegime =
      .linearizedSmallOscillationAboutHorizontalEquilibrium
  pivotAtOneEnd : setup.figure.pivotLocation = .pivotEnd
  springAtOtherEnd : setup.figure.springAttachmentLocation = .freeEnd
  horizontalEquilibrium :
    setup.figure.equilibriumReferenceOrientation = .horizontal
  verticalSpringInImage :
    setup.figure.springOrientationAtDisplayedPose = .vertical
  springIsAnchoredBelow : setup.figure.springAnchoredBelow = true
  clockwiseArrow : setup.figure.displayedRotationSense = .clockwise
  figureLengthLabel : setup.figure.lengthLabel = .plankLength_L
  figureAngleLabel : setup.figure.angleLabel = .angularDisplacement_theta
  figureSpringLabel : setup.figure.springLabel = .springConstant_k

/-! ## Governing laws and local linearization -/

/-- Positivity and nondegeneracy conditions for the apparatus. -/
structure HasPhysicalPlankSpringParameters
    (setup : PivotedPlankSpringSetup) : Prop where
  plankMassPositive : 0 < massInKilograms setup.plankMass
  plankLengthPositive : 0 < lengthInMeters setup.plankLength
  springForceConstantPositive :
    0 < springStiffnessInNewtonsPerMeter setup.springForceConstant
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude
  equilibriumSpringCompressionPositive :
    0 < lengthInMeters setup.equilibriumSpringCompression
  momentOfInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.momentOfInertiaAboutPivot
  torsionalStiffnessPositive :
    0 < torsionalStiffnessInNewtonMetersPerRadian
      setup.effectiveTorsionalStiffness

/-!
Static torque balance about the pivot. The compressed spring supplies an
upward force at the free end, while the weight of the uniform plank acts at
its midpoint. This calibrates the preload but says nothing about the requested
angular frequency.
-/
structure SatisfiesHorizontalStaticEquilibrium
    (setup : PivotedPlankSpringSetup) : Prop where
  torqueBalance :
    springStiffnessInNewtonsPerMeter setup.springForceConstant *
          lengthInMeters setup.equilibriumSpringCompression *
          lengthInMeters setup.plankLength =
      massInKilograms setup.plankMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude *
          (lengthInMeters setup.plankLength / 2)

/-!
The generalized scalar harmonic oscillator in coherent SI readouts. Its
generalized mass is the moment of inertia and its generalized spring constant
is the local torsional stiffness.
-/
def rotationalOscillatorSI
    (setup : PivotedPlankSpringSetup)
    (hPhysical : HasPhysicalPlankSpringParameters setup) :
    ClassicalMechanics.HarmonicOscillator where
  m := momentOfInertiaInKilogramMetersSquared
    setup.momentOfInertiaAboutPivot
  k := torsionalStiffnessInNewtonMetersPerRadian
    setup.effectiveTorsionalStiffness
  m_pos := hPhysical.momentOfInertiaPositive
  k_pos := hPhysical.torsionalStiffnessPositive

/-!
Local mechanics at the horizontal equilibrium `theta = 0`.

* Rigid-plank geometry gives the exact signed endpoint displacement
  `L sin(theta)`.
* The two `HasDerivAt` fields state the corresponding first-order displacement
  and compression responses at the equilibrium.
* Static preload cancels gravity at zero angle. Gravity and the preloaded
  support torque have zero first derivative there, while Hooke's law and the
  free-end lever arm give torque derivative `-k L^2`.
* A uniform plank about an end has moment of inertia `m L^2 / 3`.

The torque statement is explicitly local. By Mathlib's meaning of
`HasDerivAt`, it says `tau(theta) = -k L^2 theta + o(theta)` as `theta → 0`;
it does not globalize the small-angle approximation.
-/
structure SatisfiesLocalPlankSpringMechanics
    (setup : PivotedPlankSpringSetup) : Prop where
  uniformPlankMomentOfInertia :
    momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutPivot =
      massInKilograms setup.plankMass *
        (lengthInMeters setup.plankLength) ^ 2 / 3
  zeroAngleEndDisplacement :
    setup.springEndDownwardDisplacementMetersAtAngle 0 = 0
  rigidPlankEndGeometry :
    ∀ theta : ℝ,
      setup.springEndDownwardDisplacementMetersAtAngle theta =
        lengthInMeters setup.plankLength * Real.sin theta
  endDisplacementDerivativeAtEquilibrium :
    HasDerivAt setup.springEndDownwardDisplacementMetersAtAngle
      (lengthInMeters setup.plankLength) 0
  zeroAngleCompressionChange :
    setup.springCompressionChangeMetersAtAngle 0 = 0
  compressionDerivativeAtEquilibrium :
    HasDerivAt setup.springCompressionChangeMetersAtAngle
      (lengthInMeters setup.plankLength) 0
  netTorqueAtEquilibrium :
    setup.netClockwiseTorqueNewtonMetersAtAngle 0 = 0
  hookeTorqueDerivativeAtEquilibrium :
    HasDerivAt setup.netClockwiseTorqueNewtonMetersAtAngle
      (-(springStiffnessInNewtonsPerMeter setup.springForceConstant *
        (lengthInMeters setup.plankLength) ^ 2)) 0

/-!
Definition of the linearized rotational model. The first field defines the
effective torsional stiffness as the negative derivative of the actual torque
response at equilibrium. The second applies Physlib's general harmonic-
oscillator frequency `sqrt (kappa / I)`. Neither field contains the numerical
data `5`, `2`, `100`, `sqrt 60`, `7.75`, or an answer label.
-/
structure SatisfiesLinearizedRotationalDynamics
    (setup : PivotedPlankSpringSetup)
    (hPhysical : HasPhysicalPlankSpringParameters setup) : Prop where
  torsionalStiffnessFromTorqueDerivative :
    HasDerivAt setup.netClockwiseTorqueNewtonMetersAtAngle
      (-torsionalStiffnessInNewtonMetersPerRadian
        setup.effectiveTorsionalStiffness) 0
  harmonicAngularFrequencyLaw :
    angularFrequencyInRadiansPerSecond setup.linearizedAngularFrequency =
      (rotationalOscillatorSI setup hPhysical).ω

/-! ## Displayed answers and formalization target -/

/-- Labels of the four angular-frequency answers printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Radians-per-second value displayed beside each answer label. -/
def AnswerChoice.radiansPerSecond : AnswerChoice → ℝ
  | .A => 7.25
  | .B => 8.75
  | .C => 6.75
  | .D => 7.75

/-- The answer label recorded by the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
Agreement with a two-decimal-place displayed answer. The half-unit in the last
decimal place makes this a rounding statement rather than the false exact
equality `sqrt 60 = 7.75`.
-/
def MatchesAnswerChoice
    (frequency : AngularFrequencyQuantity) (choice : AnswerChoice) : Prop :=
  |angularFrequencyInRadiansPerSecond frequency -
      choice.radiansPerSecond| ≤ 1 / 200

/-!
For the local rotational model, derivative uniqueness gives
`kappa = k L^2`. Together with `I = m L^2 / 3`, the Physlib oscillator law
therefore gives the exact linearized frequency `sqrt (3 k / m) = sqrt 60`
radians per second. It rounds to the displayed `7.75`, so the recorded choice
is D.

This formalizes `thm:physics:phyx_mini_0232:target`.
-/
theorem angularFrequency_matches_recordedAnswerD
    (setup : PivotedPlankSpringSetup)
    (hProblem : MatchesProblemAndFigure setup)
    (hPhysical : HasPhysicalPlankSpringParameters setup)
    (hEquilibrium : SatisfiesHorizontalStaticEquilibrium setup)
    (hLocalMechanics : SatisfiesLocalPlankSpringMechanics setup)
    (hLinearizedDynamics :
      SatisfiesLinearizedRotationalDynamics setup hPhysical) :
    angularFrequencyInRadiansPerSecond
          setup.linearizedAngularFrequency = Real.sqrt 60 ∧
      MatchesAnswerChoice setup.linearizedAngularFrequency
        recordedAnswerChoice := by
  have hStiffness :
      torsionalStiffnessInNewtonMetersPerRadian
          setup.effectiveTorsionalStiffness =
        springStiffnessInNewtonsPerMeter setup.springForceConstant *
          (lengthInMeters setup.plankLength) ^ 2 := by
    have hUnique :=
      hLocalMechanics.hookeTorqueDerivativeAtEquilibrium.unique
        hLinearizedDynamics.torsionalStiffnessFromTorqueDerivative
    linarith
  have hInertia :
      momentOfInertiaInKilogramMetersSquared
          setup.momentOfInertiaAboutPivot = 20 / 3 := by
    rw [hLocalMechanics.uniformPlankMomentOfInertia,
      hProblem.plankMassReadout, hProblem.plankLengthReadout]
    norm_num
  have hStiffnessNumeric :
      torsionalStiffnessInNewtonMetersPerRadian
          setup.effectiveTorsionalStiffness = 400 := by
    rw [hStiffness, hProblem.springConstantReadout,
      hProblem.plankLengthReadout]
    norm_num
  have hFrequency :
      angularFrequencyInRadiansPerSecond
          setup.linearizedAngularFrequency = Real.sqrt 60 := by
    rw [hLinearizedDynamics.harmonicAngularFrequencyLaw]
    simp only [ClassicalMechanics.HarmonicOscillator.ω,
      rotationalOscillatorSI]
    rw [hStiffnessNumeric, hInertia]
    congr 1
    norm_num
  refine ⟨hFrequency, ?_⟩
  rw [MatchesAnswerChoice, recordedAnswerChoice, hFrequency]
  simp only [AnswerChoice.radiansPerSecond]
  rw [abs_le]
  constructor <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 60),
      Real.sqrt_nonneg (60 : ℝ)]

end PhyXMiniProblems.ProblemPhyXMini0232
