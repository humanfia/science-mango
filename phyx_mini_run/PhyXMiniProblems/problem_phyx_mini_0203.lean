import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0203

open Dimension
open scoped ContDiff

/-!
# Vertical oscillation of a block on two parallel springs

The supplied figure shows one block, labeled `m`, attached to two identical
vertical springs, each labeled `k`.  Both springs join the same rigid support
to the same block, so they undergo the same displacement and their restoring
forces add in parallel.

The source uses the ideal linear-spring model.  That idealization is made
substantive below: each spring obeys Hooke's law for every signed displacement
from equilibrium, the two forces add, and a smooth displacement trajectory
satisfies Physlib's exact undamped harmonic-oscillator equation of motion.
Thus the requested equality is not obtained merely from a qualitative
"small-oscillation" regime label.

Mass, length, acceleration, force, stiffness, and frequency are represented by
unit-independent Physlib quantities.  Real numbers occur only as explicitly
named readouts in coherent selected units and in the source's symbolic answer
formulas.
-/

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, used for static spring extensions. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed vertical displacement from the block's static equilibrium. -/
abbrev DisplacementQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative acceleration, with dimension length divided by time squared. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A signed vertical force, with dimension mass times acceleration. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Spring stiffness, with dimension mass divided by time squared. -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Cyclic frequency, measured in cycles per unit time. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Angular frequency; radians are dimensionless, so this is inverse time. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a nonnegative length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed displacement in a selected length unit. -/
def displacementReadout
    (unit : LengthUnit) (displacement : DisplacementQuantity) : ℝ :=
  (displacement {UnitChoices.SI with length := unit}).val

/-- Read an acceleration in coherent selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a signed force in coherent selected mass, length, and time units. -/
def forceReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (force : ForceQuantity) : ℝ :=
  (force {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val

/-- Read spring stiffness in the selected mass unit per time unit squared. -/
def stiffnessReadout
    (massUnit : MassUnit) (timeUnit : TimeUnit)
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  ((stiffness {UnitChoices.SI with
    mass := massUnit, time := timeUnit}).val : ℝ)

/-- Read cyclic frequency in inverse units of the selected time unit. -/
def frequencyReadout
    (timeUnit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- Read angular frequency in radians per selected time unit. -/
def angularFrequencyReadout
    (timeUnit : TimeUnit) (frequency : AngularFrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- The two springs distinguished by their horizontal placement in the figure. -/
inductive SpringSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Mechanical arrangements relevant to combining two spring stiffnesses. -/
inductive SpringArrangement where
  | parallel
  | series
  deriving DecidableEq, Repr

/-- Orientations visible in the supplied diagram. -/
inductive Orientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Mathematical labels printed in the primary figure. -/
inductive FigureLabel where
  | springConstant_k
  | blockMass_m
  deriving DecidableEq, Repr

/-!
Qualitative facts readable from the primary image.  The image contains no
numerical scale; it identifies only the support, block, two springs, labels,
attachments, vertical orientation, and left/right placement.
-/
structure ParallelSpringFigure where
  showsTopSupport : Bool
  showsBlock : Bool
  showsSpring : SpringSide → Bool
  springLabel : SpringSide → FigureLabel
  blockLabel : FigureLabel
  springAttachesToTopSupport : SpringSide → Bool
  springAttachesToBlock : SpringSide → Bool
  springIsVertical : SpringSide → Bool
  leftSpringShownLeftOfRightSpring : Bool

/-!
Independent quantities and functions of the physical setup.  Restoring-force
functions and the two natural frequencies are unconstrained here.  In
particular, neither frequency is defined to equal an answer formula.

`displacementTrajectoryInUnits` is the one-dimensional displacement from
static equilibrium expressed in the selected length and time units, matching
the coordinate-level interface used by Physlib's classical oscillator.
-/
structure ParallelSpringOscillatorSetup where
  blockMass_m : MassQuantity
  springStiffness_k : SpringStiffnessQuantity
  springStiffness : SpringSide → SpringStiffnessQuantity
  effectiveSpringStiffness : SpringStiffnessQuantity
  gravitationalAcceleration : AccelerationQuantity
  equilibriumDrop : LengthQuantity
  springEquilibriumExtension : SpringSide → LengthQuantity
  springRestoringForce : SpringSide → DisplacementQuantity → ForceQuantity
  totalRestoringForce : DisplacementQuantity → ForceQuantity
  displacementTrajectoryInUnits :
    LengthUnit → TimeUnit → Time → EuclideanSpace ℝ (Fin 1)
  naturalFrequency : FrequencyQuantity
  naturalAngularFrequency : AngularFrequencyQuantity
  springArrangement : SpringArrangement
  springOrientation : Orientation
  blockMotionOrientation : Orientation
  figure : ParallelSpringFigure

/-!
Problem data and primary-image evidence.  The stiffness equalities say that
both pictured springs are identical and labeled `k`; they do not constrain the
requested natural frequency.
-/
structure MatchesProblemAndSuppliedFigure
    (setup : ParallelSpringOscillatorSetup) : Prop where
  identicalSpringStiffness :
    ∀ side, setup.springStiffness side = setup.springStiffness_k
  springsAreParallel : setup.springArrangement = .parallel
  springsAreVertical : setup.springOrientation = .vertical
  blockMovesVertically : setup.blockMotionOrientation = .vertical
  figureShowsTopSupport : setup.figure.showsTopSupport = true
  figureShowsBlock : setup.figure.showsBlock = true
  figureShowsBothSprings : ∀ side, setup.figure.showsSpring side = true
  figureSpringLabels :
    ∀ side, setup.figure.springLabel side = .springConstant_k
  figureBlockLabel : setup.figure.blockLabel = .blockMass_m
  figureSpringTopAttachments :
    ∀ side, setup.figure.springAttachesToTopSupport side = true
  figureSpringBlockAttachments :
    ∀ side, setup.figure.springAttachesToBlock side = true
  figureVerticalSprings :
    ∀ side, setup.figure.springIsVertical side = true
  figureLeftRightPlacement :
    setup.figure.leftSpringShownLeftOfRightSpring = true

/-- Positivity and nondegeneracy conditions for the physical oscillator. -/
structure HasPhysicalParallelSpringParameters
    (setup : ParallelSpringOscillatorSetup) : Prop where
  blockMassPositive :
    ∀ massUnit, 0 < massReadout massUnit setup.blockMass_m
  individualStiffnessPositive :
    ∀ side massUnit timeUnit,
      0 < stiffnessReadout massUnit timeUnit (setup.springStiffness side)
  effectiveStiffnessPositive :
    ∀ massUnit timeUnit,
      0 < stiffnessReadout massUnit timeUnit setup.effectiveSpringStiffness
  gravitationalAccelerationPositive :
    ∀ lengthUnit timeUnit,
      0 < accelerationReadout lengthUnit timeUnit setup.gravitationalAcceleration
  equilibriumDropPositive :
    ∀ lengthUnit, 0 < lengthReadout lengthUnit setup.equilibriumDrop
  naturalFrequencyPositive :
    ∀ timeUnit, 0 < frequencyReadout timeUnit setup.naturalFrequency
  naturalAngularFrequencyPositive :
    ∀ timeUnit,
      0 < angularFrequencyReadout timeUnit setup.naturalAngularFrequency

/-!
Exact constitutive, parallel-combination, and equilibrium laws:

* each ideal spring obeys Hooke's law for every signed displacement from
  equilibrium, not merely to first order near zero;
* the two actual restoring forces add because both springs attach to the same
  moving block;
* the effective stiffness is the sum of the individual stiffnesses;
* at static equilibrium the effective spring force balances the block's weight.

None of these fields states the requested frequency in terms of the individual
spring constant `k`.
-/
structure SatisfiesExactHookeParallelAndEquilibriumLaws
    (setup : ParallelSpringOscillatorSetup) : Prop where
  commonEquilibriumExtension :
    ∀ side lengthUnit,
      lengthReadout lengthUnit (setup.springEquilibriumExtension side) =
        lengthReadout lengthUnit setup.equilibriumDrop
  individualHookeLawForEveryDisplacement :
    ∀ side massUnit lengthUnit timeUnit displacement,
      forceReadout massUnit lengthUnit timeUnit
          (setup.springRestoringForce side displacement) =
        -stiffnessReadout massUnit timeUnit (setup.springStiffness side) *
          displacementReadout lengthUnit displacement
  parallelRestoringForcesAdd :
    ∀ massUnit lengthUnit timeUnit displacement,
      forceReadout massUnit lengthUnit timeUnit
          (setup.totalRestoringForce displacement) =
        forceReadout massUnit lengthUnit timeUnit
            (setup.springRestoringForce .left displacement) +
          forceReadout massUnit lengthUnit timeUnit
            (setup.springRestoringForce .right displacement)
  effectiveStiffnessAddition :
    ∀ massUnit timeUnit,
      stiffnessReadout massUnit timeUnit setup.effectiveSpringStiffness =
        stiffnessReadout massUnit timeUnit (setup.springStiffness .left) +
          stiffnessReadout massUnit timeUnit (setup.springStiffness .right)
  staticWeightBalance :
    ∀ massUnit lengthUnit timeUnit,
      stiffnessReadout massUnit timeUnit setup.effectiveSpringStiffness *
          lengthReadout lengthUnit setup.equilibriumDrop =
        massReadout massUnit setup.blockMass_m *
          accelerationReadout lengthUnit timeUnit
            setup.gravitationalAcceleration

/-!
Package the positive mass and effective-stiffness readouts as Physlib's exact
classical harmonic oscillator in any coherent mass and time units.
-/
def effectiveOscillatorInUnits
    (setup : ParallelSpringOscillatorSetup)
    (hPhysical : HasPhysicalParallelSpringParameters setup)
    (massUnit : MassUnit) (timeUnit : TimeUnit) :
    ClassicalMechanics.HarmonicOscillator where
  m := massReadout massUnit setup.blockMass_m
  k := stiffnessReadout massUnit timeUnit setup.effectiveSpringStiffness
  m_pos := hPhysical.blockMassPositive massUnit
  k_pos := hPhysical.effectiveStiffnessPositive massUnit timeUnit

/-!
Exact undamped dynamics of the ideal Hookean system.  The first two fields are
a genuine differentiability/equation-of-motion contract for the unitwise
trajectory.  The third identifies the system's independent natural angular
frequency with Physlib's characteristic frequency of that exact oscillator;
the final field is the standard conversion `ω = 2πf`.

The unknown effective stiffness has not been replaced by `2k` in this
interface, so the current answer remains a conclusion.
-/
structure SatisfiesExactIdealHookeanDynamics
    (setup : ParallelSpringOscillatorSetup)
    (hPhysical : HasPhysicalParallelSpringParameters setup) : Prop where
  trajectorySmooth :
    ∀ lengthUnit timeUnit,
      ContDiff ℝ ∞ (setup.displacementTrajectoryInUnits lengthUnit timeUnit)
  physlibEquationOfMotion :
    ∀ massUnit lengthUnit timeUnit,
      (effectiveOscillatorInUnits setup hPhysical massUnit timeUnit).EquationOfMotion
        (setup.displacementTrajectoryInUnits lengthUnit timeUnit)
  characteristicAngularFrequency :
    ∀ massUnit timeUnit,
      angularFrequencyReadout timeUnit setup.naturalAngularFrequency =
        (effectiveOscillatorInUnits setup hPhysical massUnit timeUnit).ω
  angularToCyclicFrequency :
    ∀ timeUnit,
      angularFrequencyReadout timeUnit setup.naturalAngularFrequency =
        2 * Real.pi * frequencyReadout timeUnit setup.naturalFrequency

/-!
The effective-stiffness conclusion is derived from the parallel combination
law and the source datum that each individual spring has stiffness `k`.
-/
lemma effectiveStiffnessReadout_eq_two_mul_k
    (setup : ParallelSpringOscillatorSetup)
    (hProblem : MatchesProblemAndSuppliedFigure setup)
    (hExactHooke : SatisfiesExactHookeParallelAndEquilibriumLaws setup) :
    ∀ massUnit timeUnit,
      stiffnessReadout massUnit timeUnit setup.effectiveSpringStiffness =
        2 * stiffnessReadout massUnit timeUnit setup.springStiffness_k := by
  intro massUnit timeUnit
  rw [hExactHooke.effectiveStiffnessAddition,
    hProblem.identicalSpringStiffness,
    hProblem.identicalSpringStiffness]
  ring

/-- Labels attached to the four symbolic answer formulas in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-!
The four printed formulas interpreted as cyclic-frequency readouts in coherent
selected units.  These are answer-list metadata and do not constrain the
independent natural frequency stored in the setup.
-/
def displayedAnswerFrequencyReadout
    (setup : ParallelSpringOscillatorSetup)
    (massUnit : MassUnit) (timeUnit : TimeUnit) : AnswerChoice → ℝ
  | .A =>
      (1 / (2 * Real.pi)) *
        Real.sqrt
          (stiffnessReadout massUnit timeUnit setup.springStiffness_k /
            (2 * massReadout massUnit setup.blockMass_m))
  | .B =>
      (1 / (2 * Real.pi)) *
        Real.sqrt
          ((2 * stiffnessReadout massUnit timeUnit setup.springStiffness_k) /
            massReadout massUnit setup.blockMass_m ^ 2)
  | .C =>
      (1 / (2 * Real.pi)) *
        Real.sqrt
          (stiffnessReadout massUnit timeUnit setup.springStiffness_k /
            massReadout massUnit setup.blockMass_m)
  | .D =>
      (1 / (2 * Real.pi)) *
        Real.sqrt
          ((2 * stiffnessReadout massUnit timeUnit setup.springStiffness_k) /
            massReadout massUnit setup.blockMass_m)

/-- The label recorded as correct in the dataset metadata; not a premise. -/
def recordedDatasetAnswerChoice : AnswerChoice := .D

/-- The modeled cyclic frequency agrees with one printed symbolic choice. -/
def MatchesAnswerChoice
    (setup : ParallelSpringOscillatorSetup) (choice : AnswerChoice) : Prop :=
  ∀ massUnit timeUnit,
    frequencyReadout timeUnit setup.naturalFrequency =
      displayedAnswerFrequencyReadout setup massUnit timeUnit choice

/-!
Two identical ideal Hookean springs attached in parallel have effective
stiffness `2k`.  Therefore the block's exact natural cyclic frequency in this
undamped model is `(1 / (2π)) * sqrt (2k / m)`, answer choice `D`.

This is the formal target corresponding to
`thm:physics:phyx_mini_0203:target`.
-/
theorem problem_phyx_mini_0203
    (setup : ParallelSpringOscillatorSetup)
    (hProblem : MatchesProblemAndSuppliedFigure setup)
    (hPhysical : HasPhysicalParallelSpringParameters setup)
    (hExactHooke : SatisfiesExactHookeParallelAndEquilibriumLaws setup)
    (hDynamics : SatisfiesExactIdealHookeanDynamics setup hPhysical) :
    (∀ massUnit timeUnit,
      frequencyReadout timeUnit setup.naturalFrequency =
        (1 / (2 * Real.pi)) *
          Real.sqrt
            ((2 * stiffnessReadout massUnit timeUnit
                setup.springStiffness_k) /
              massReadout massUnit setup.blockMass_m)) ∧
      MatchesAnswerChoice setup .D := by
  have hFrequency :
      ∀ massUnit timeUnit,
        frequencyReadout timeUnit setup.naturalFrequency =
          (1 / (2 * Real.pi)) *
            Real.sqrt
              ((2 * stiffnessReadout massUnit timeUnit
                  setup.springStiffness_k) /
                massReadout massUnit setup.blockMass_m) := by
    intro massUnit timeUnit
    have hCharacteristic :=
      hDynamics.characteristicAngularFrequency massUnit timeUnit
    have hConversion := hDynamics.angularToCyclicFrequency timeUnit
    rw [ClassicalMechanics.HarmonicOscillator.ω] at hCharacteristic
    change
      angularFrequencyReadout timeUnit setup.naturalAngularFrequency =
        Real.sqrt
          (stiffnessReadout massUnit timeUnit
              setup.effectiveSpringStiffness /
            massReadout massUnit setup.blockMass_m) at hCharacteristic
    rw [effectiveStiffnessReadout_eq_two_mul_k setup hProblem hExactHooke
      massUnit timeUnit] at hCharacteristic
    have hSqrt :
        Real.sqrt
            ((2 * stiffnessReadout massUnit timeUnit
                setup.springStiffness_k) /
              massReadout massUnit setup.blockMass_m) =
          2 * Real.pi *
            frequencyReadout timeUnit setup.naturalFrequency :=
      hCharacteristic.symm.trans hConversion
    rw [hSqrt]
    field_simp [Real.pi_ne_zero]
  exact ⟨hFrequency, by
    simpa [MatchesAnswerChoice, displayedAnswerFrequencyReadout] using hFrequency⟩

end PhyXMiniProblems.ProblemPhyXMini0203
