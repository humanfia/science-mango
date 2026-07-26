import Mathlib
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.Units.WithDim.Energy

/-!
# Elastic energy of a stretched spring-block system

This file formalizes problem `phyx_mini_0226`.  The primary image shows a
spring anchored to a wall on the left, a block on a horizontal support to the
right, and a horizontal force arrow labeled `F` pointing right.  The statement
adds that the block is initially at rest, the support is frictionless, and the
force stretches the spring from equilibrium.

Mass, length, velocity, stiffness, force, and energy are dimensionful physical
quantities.  Real numbers below occur only as named SI readouts or as the
one-dimensional SI-coordinate data required by Physlib's
`ClassicalMechanics.HarmonicOscillator` API.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0226

open Dimension

/-! ## Dimensionful physical quantities and SI readouts -/

/-- Physical mass, with dimension `M`. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- Physical displacement or length, with dimension `L`. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Physical velocity, with dimension `L T⁻¹`. -/
abbrev VelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/--
Physical spring stiffness, with dimension force per length, equivalently
`M T⁻²`.
-/
abbrev SpringConstantQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Physical force, with dimension `M L T⁻²`. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Physical energy, with dimension `M L² T⁻²`. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- SI kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  (mass UnitChoices.SI).val

/-- SI metre readout of a physical displacement. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- SI metre-per-second readout of a physical velocity. -/
def velocityInMetersPerSecond (velocity : VelocityQuantity) : ℝ :=
  (velocity UnitChoices.SI).val

/-- SI newton-per-metre readout of a physical spring stiffness. -/
def springConstantInNewtonsPerMeter
    (springConstant : SpringConstantQuantity) : ℝ :=
  (springConstant UnitChoices.SI).val

/-- SI newton readout of a physical force magnitude. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  (force UnitChoices.SI).val

/-- SI joule readout of a physical energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Labels and qualitative information read from the primary image -/

/-- Left and right sides of the supplied spring-block diagram. -/
inductive FigureSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Horizontal direction of the labeled force arrow. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- Orientation of the support surface drawn beneath the block. -/
inductive SurfaceOrientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The two physical objects joined by the spring in the figure. -/
inductive SpringEndpoint where
  | wallAnchor
  | block
  deriving DecidableEq, Repr

/-- Raw labels and geometry visible in the supplied image. -/
structure SpringBlockFigure where
  wallSide : FigureSide
  blockSide : FigureSide
  springEndpoints : SpringEndpoint × SpringEndpoint
  supportOrientation : SurfaceOrientation
  appliedForceLabel : String
  appliedForceDirection : HorizontalDirection

/--
Primary-image evidence: wall and spring to the left, block to the right, a
horizontal support, and the arrow `F` directed rightward away from the wall.
-/
def MatchesSuppliedFigure (figure : SpringBlockFigure) : Prop :=
  figure.wallSide = .left ∧
    figure.blockSide = .right ∧
    figure.springEndpoints = (.wallAnchor, .block) ∧
    figure.supportOrientation = .horizontal ∧
    figure.appliedForceLabel = "F" ∧
    figure.appliedForceDirection = .rightward

/-! ## Physical setup, given data, and governing law -/

/--
The physical spring-block system and the quantities named by the problem.

`extensionVectorInMeters` is the one-dimensional SI-coordinate readout used by
Physlib.  The physical extension and stored energy remain dimensionful fields,
and no numerical answer or answer-choice label is stored in this structure.
-/
structure SpringBlockSetup where
  figure : SpringBlockFigure
  blockMass : MassQuantity
  springConstant : SpringConstantQuantity
  extensionFromEquilibrium : LengthQuantity
  initialVelocity : VelocityQuantity
  appliedForceMagnitude : ForceQuantity
  surfaceFrictionForceMagnitude : ForceQuantity
  storedElasticEnergy : EnergyQuantity
  oscillatorSIReadout : ClassicalMechanics.HarmonicOscillator
  extensionVectorInMeters : EuclideanSpace ℝ (Fin 1)

/--
Numerical measurements and qualitative conditions stated in the problem.
The extension is converted from `5.46 cm` to metres.  Initial rest and zero
friction are properties of the setup, not assumptions about the requested
stored-energy value.
-/
def MatchesProblemData (setup : SpringBlockSetup) : Prop :=
  massInKilograms setup.blockMass = 250 / 1000 ∧
    springConstantInNewtonsPerMeter setup.springConstant = 838 / 10 ∧
    lengthInMeters setup.extensionFromEquilibrium = 546 / 10000 ∧
    velocityInMetersPerSecond setup.initialVelocity = 0 ∧
    forceInNewtons setup.surfaceFrictionForceMagnitude = 0

/-- Positivity conditions for the physical quantities supplied by the setup. -/
structure HasPhysicalParameters (setup : SpringBlockSetup) : Prop where
  blockMassPositive : 0 < massInKilograms setup.blockMass
  springConstantPositive :
    0 < springConstantInNewtonsPerMeter setup.springConstant
  extensionPositive : 0 < lengthInMeters setup.extensionFromEquilibrium
  appliedForcePositive : 0 < forceInNewtons setup.appliedForceMagnitude

/--
The one-dimensional Hooke-law energy model in coherent SI readouts.

Physlib's oscillator packages the positive mass and spring constant, while
`potentialEnergy` is its general law `U = (1/2) k x²`.  The last field says
that the physical energy stored by stretching the spring has that SI readout.
No problem-specific energy value or answer choice occurs in this interface.
-/
structure SatisfiesElasticSpringModel (setup : SpringBlockSetup) : Prop where
  oscillatorMassIsBlockMass :
    setup.oscillatorSIReadout.m = massInKilograms setup.blockMass
  oscillatorStiffnessIsSpringStiffness :
    setup.oscillatorSIReadout.k =
      springConstantInNewtonsPerMeter setup.springConstant
  oscillatorExtensionIsPhysicalExtension :
    setup.extensionVectorInMeters 0 =
      lengthInMeters setup.extensionFromEquilibrium
  storedEnergyIsSpringPotentialEnergy :
    energyInJoules setup.storedElasticEnergy =
      ClassicalMechanics.HarmonicOscillator.potentialEnergy
        setup.oscillatorSIReadout setup.extensionVectorInMeters

/-! ## Displayed answers and formalization target -/

/-- Labels printed beside the four candidate energies. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Energy in joules printed beside each answer label. -/
def AnswerChoice.energyInJoules : AnswerChoice → ℝ
  | .A => 325 / 1000
  | .B => 225 / 1000
  | .C => 425 / 1000
  | .D => 125 / 1000

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/--
Agreement with a displayed energy to the nearest millijoule.  The half-
millijoule tolerance avoids identifying the exact value from the supplied
three-significant-figure inputs with the rounded display `0.125 J`.
-/
def MatchesDisplayedEnergy
    (setup : SpringBlockSetup) (choice : AnswerChoice) : Prop :=
  |energyInJoules setup.storedElasticEnergy - choice.energyInJoules| ≤
    (1 / 2000 : ℝ)

/-- The selected energy is strictly closer than every other displayed choice. -/
def IsUniqueClosestDisplayedChoice
    (setup : SpringBlockSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |energyInJoules setup.storedElasticEnergy - choice.energyInJoules| <
      |energyInJoules setup.storedElasticEnergy - other.energyInJoules|

/--
For `k = 83.8 N/m` and extension `x = 5.46 cm`, the Hooke-law energy
`(1/2) k x²` is approximately `0.1249106 J`.  It therefore rounds to
`0.125 J`, answer D, and D is uniquely closest among the displayed choices.

This formalizes blueprint label `thm:physics:phyx_mini_0226:target`.
-/
theorem problem_phyx_mini_0226
    (setup : SpringBlockSetup)
    (hData : MatchesProblemData setup)
    (hFigure : MatchesSuppliedFigure setup.figure)
    (hPhysical : HasPhysicalParameters setup)
    (hModel : SatisfiesElasticSpringModel setup) :
    MatchesDisplayedEnergy setup recordedAnswerChoice ∧
      IsUniqueClosestDisplayedChoice setup recordedAnswerChoice := by
  rcases hData with ⟨hmass, hk, hx, hvel, hfric⟩
  rcases hModel with ⟨hoscMass, hoscK, hoscX, henergy⟩
  have hinner :
      inner ℝ setup.extensionVectorInMeters setup.extensionVectorInMeters =
        (lengthInMeters setup.extensionFromEquilibrium) ^ 2 := by
    rw [PiLp.inner_apply]
    simp [← hoscX]
  rw [ClassicalMechanics.HarmonicOscillator.potentialEnergy_eq, hinner,
    hoscK, hk, hx] at henergy
  norm_num at henergy
  constructor
  · norm_num [MatchesDisplayedEnergy, recordedAnswerChoice,
      AnswerChoice.energyInJoules, henergy]
  · intro other hother
    cases other with
    | A =>
        norm_num [recordedAnswerChoice, AnswerChoice.energyInJoules, henergy]
    | B =>
        norm_num [recordedAnswerChoice, AnswerChoice.energyInJoules, henergy]
    | C =>
        norm_num [recordedAnswerChoice, AnswerChoice.energyInJoules, henergy]
    | D =>
        exact (hother rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0226
