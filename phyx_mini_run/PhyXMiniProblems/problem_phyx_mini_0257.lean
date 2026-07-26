import Mathlib
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
import Physlib.Units.WithDim.Basic

/-!
# A block and spring on a frictionless incline

This file models problem `phyx_mini_0257`.  A block of weight `14.0 N` slides
without friction on a `40°` incline and is connected to the top of the incline
by a massless spring of natural length `0.450 m` and stiffness `120 N/m`.
After a slight downward displacement from equilibrium, the block is released
from rest.

The physical quantities below retain their dimensions through Physlib's
`Dimensionful` API.  Real numbers are used only for coherent SI readouts,
the dimensionless angle in degrees, and displayed answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0257

open Dimension

/-! ## Dimensionful physical quantities -/

/-- A physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A physical force, used for the block's weight. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A physical acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A spring stiffness, with dimension force per length. -/
abbrev SpringConstantQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A physical speed, used for the release speed. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) NNReal)

/-- A physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (quantity : MassQuantity) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Newton readout of a physical force. -/
def forceInNewtons (quantity : ForceQuantity) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (quantity : LengthQuantity) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Metres-per-second-squared readout of a physical acceleration. -/
def accelerationInMetersPerSecondSquared
    (quantity : AccelerationQuantity) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Newton-per-metre readout of a spring stiffness. -/
def springConstantInNewtonsPerMeter
    (quantity : SpringConstantQuantity) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Metres-per-second readout of a physical speed. -/
def speedInMetersPerSecond (quantity : SpeedQuantity) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Second readout of a physical duration. -/
def timeInSeconds (quantity : TimeQuantity) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Convert a dimensionless angle stated in degrees to radians. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-! ## Verbal and primary-image geometry -/

/-- Contact model between the block and the incline. -/
inductive BlockContactModel where
  | frictionlessSliding
  deriving DecidableEq, Repr

/-- Mass model for the connecting spring. -/
inductive SpringMassModel where
  | massless
  deriving DecidableEq, Repr

/-- Direction in which the block is initially pulled. -/
inductive InclineDirection where
  | upIncline
  | downIncline
  deriving DecidableEq, Repr

/-- Qualitative displacement regime expressed by the word "slightly". -/
inductive DisplacementRegime where
  | slight
  deriving DecidableEq, Repr

/-- Components visible in the supplied diagram. -/
inductive FigureComponent where
  | inclinedPlane
  | block
  | spring
  | topAnchor
  deriving DecidableEq, Repr

/-- Symbols printed in the supplied diagram. -/
inductive FigureLabel where
  | theta
  | springConstantK
  deriving DecidableEq, Repr

/-- Orientation of the spring relative to the incline. -/
inductive SpringOrientation where
  | alongIncline
  deriving DecidableEq, Repr

/-- Upper attachment shown for the spring. -/
inductive SpringUpperAttachment where
  | fixedAtTopOfIncline
  deriving DecidableEq, Repr

/-- Lower attachment shown for the spring. -/
inductive SpringLowerAttachment where
  | attachedToBlock
  deriving DecidableEq, Repr

/-- Structured readout of the primary image. -/
structure SuppliedFigure where
  visible : FigureComponent → Prop
  labelRefersTo : FigureLabel → FigureComponent
  springOrientation : SpringOrientation
  upperAttachment : SpringUpperAttachment
  lowerAttachment : SpringLowerAttachment

/-! ## Physical setup and supplied data -/

/--
The physical system and its unknown oscillation period.

The physical period is an independent field: it is neither defined to be a
displayed answer nor assigned a numerical value in this structure.
-/
structure InclinedSpringSetup where
  blockMass : MassQuantity
  blockWeight : ForceQuantity
  gravitationalAcceleration : AccelerationQuantity
  inclineAngleDegrees : ℝ
  springNaturalLength : LengthQuantity
  springConstant : SpringConstantQuantity
  equilibriumSpringLength : LengthQuantity
  equilibriumExtension : LengthQuantity
  releaseDisplacementFromEquilibrium : LengthQuantity
  releaseSpeed : SpeedQuantity
  oscillationPeriod : TimeQuantity
  oscillator : ClassicalMechanics.HarmonicOscillator
  contactModel : BlockContactModel
  springMassModel : SpringMassModel
  releaseDirection : InclineDirection
  displacementRegime : DisplacementRegime
  figure : SuppliedFigure

/--
Numerical and qualitative data stated in the problem.  The value `9.8 m/s²`
is the standard gravitational calibration needed to infer mass from the given
weight.  No period or answer-choice value occurs here.
-/
structure MatchesProblemData (setup : InclinedSpringSetup) : Prop where
  weightNewtons : forceInNewtons setup.blockWeight = 14
  standardGravity :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration = 98 / 10
  inclineAngle : setup.inclineAngleDegrees = 40
  naturalLengthMeters : lengthInMeters setup.springNaturalLength = 45 / 100
  springConstantNewtonsPerMeter :
    springConstantInNewtonsPerMeter setup.springConstant = 120
  frictionlessContact : setup.contactModel = .frictionlessSliding
  negligibleSpringMass : setup.springMassModel = .massless
  pulledDownIncline : setup.releaseDirection = .downIncline
  slightDisplacement : setup.displacementRegime = .slight
  nonzeroPull : 0 < lengthInMeters setup.releaseDisplacementFromEquilibrium
  releasedFromRest : speedInMetersPerSecond setup.releaseSpeed = 0

/--
Primary-image readout: an inclined plane, block, spring, and top anchor are
visible; `θ` labels the incline and `k` labels the spring; the spring runs
along the incline from the block to a fixed upper anchor.
-/
structure MatchesSuppliedFigure (setup : InclinedSpringSetup) : Prop where
  inclinedPlaneVisible : setup.figure.visible .inclinedPlane
  blockVisible : setup.figure.visible .block
  springVisible : setup.figure.visible .spring
  topAnchorVisible : setup.figure.visible .topAnchor
  thetaLabelsIncline : setup.figure.labelRefersTo .theta = .inclinedPlane
  kLabelsSpring : setup.figure.labelRefersTo .springConstantK = .spring
  springRunsAlongIncline : setup.figure.springOrientation = .alongIncline
  springFixedAtTop : setup.figure.upperAttachment = .fixedAtTopOfIncline
  springAttachedToBlock : setup.figure.lowerAttachment = .attachedToBlock

/-! ## Governing mechanics -/

/--
The governing laws for the frictionless, small-displacement motion.

The first two equations identify weight with `m g` and locate the statically
shifted equilibrium using the component of gravity along the incline.  The
last three fields connect the physical system to Physlib's positive-mass,
positive-stiffness harmonic oscillator and its general period.  None assumes
the requested numerical period or a displayed answer.
-/
structure SatisfiesInclinedSpringOscillatorLaws
    (setup : InclinedSpringSetup) : Prop where
  weightMassRelation :
    forceInNewtons setup.blockWeight =
      massInKilograms setup.blockMass *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  equilibriumLengthRelation :
    lengthInMeters setup.equilibriumSpringLength =
      lengthInMeters setup.springNaturalLength +
        lengthInMeters setup.equilibriumExtension
  equilibriumForceBalanceAlongIncline :
    springConstantInNewtonsPerMeter setup.springConstant *
        lengthInMeters setup.equilibriumExtension =
      forceInNewtons setup.blockWeight *
        Real.sin (degreesToRadians setup.inclineAngleDegrees)
  oscillatorMassReadout :
    setup.oscillator.m = massInKilograms setup.blockMass
  oscillatorSpringConstantReadout :
    setup.oscillator.k =
      springConstantInNewtonsPerMeter setup.springConstant
  physicalPeriodIsOscillatorPeriod :
    timeInSeconds setup.oscillationPeriod = setup.oscillator.period

/--
The Physlib oscillator laws give the standard mass--spring period formula.
Gravity and incline angle affect the equilibrium extension but not this
linearized period.
-/
lemma oscillationPeriod_formula
    (setup : InclinedSpringSetup)
    (h_laws : SatisfiesInclinedSpringOscillatorLaws setup) :
    timeInSeconds setup.oscillationPeriod =
      2 * Real.pi /
        Real.sqrt
          (springConstantInNewtonsPerMeter setup.springConstant /
            massInKilograms setup.blockMass) := by
  rw [h_laws.physicalPeriodIsOscillatorPeriod,
    ClassicalMechanics.HarmonicOscillator.period_eq]
  unfold ClassicalMechanics.HarmonicOscillator.ω
  rw [h_laws.oscillatorSpringConstantReadout, h_laws.oscillatorMassReadout]

/-! ## Displayed answers and target -/

/-- Labels of the four displayed answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Period in seconds printed beside each answer label. -/
def AnswerChoice.seconds : AnswerChoice → ℝ
  | .A => 619 / 1000
  | .B => 628 / 1000
  | .C => 686 / 1000
  | .D => 742 / 1000

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with a displayed period rounded to the nearest millisecond. -/
def MatchesDisplayedPeriod
    (period : TimeQuantity) (choice : AnswerChoice) : Prop :=
  |timeInSeconds period - choice.seconds| ≤ 1 / 2000

/-- The selected choice is strictly closer than every other displayed value. -/
def IsUniqueClosestAnswer
    (period : TimeQuantity) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |timeInSeconds period - choice.seconds| <
      |timeInSeconds period - other.seconds|

/--
For the stated `14.0 N` block and `120 N/m` spring, the small-oscillation
period rounds to `0.686 s`, the displayed answer C, and that choice is uniquely
closest.

This formalizes `thm:physics:phyx_mini_0257:target`.
-/
theorem oscillationPeriod_matches_recordedAnswerC
    (setup : InclinedSpringSetup)
    (h_data : MatchesProblemData setup)
    (h_figure : MatchesSuppliedFigure setup)
    (h_laws : SatisfiesInclinedSpringOscillatorLaws setup) :
    MatchesDisplayedPeriod setup.oscillationPeriod recordedAnswerChoice ∧
      IsUniqueClosestAnswer setup.oscillationPeriod recordedAnswerChoice := by
  have h_mass : massInKilograms setup.blockMass = (10 : ℝ) / 7 := by
    have h := h_laws.weightMassRelation
    rw [h_data.weightNewtons, h_data.standardGravity] at h
    norm_num at h ⊢
    linarith
  have h_period : timeInSeconds setup.oscillationPeriod =
      2 * Real.pi / Real.sqrt 84 := by
    rw [oscillationPeriod_formula setup h_laws,
      h_data.springConstantNewtonsPerMeter, h_mass]
    norm_num
  have h_sqrt_pos : 0 < Real.sqrt (84 : ℝ) :=
    Real.sqrt_pos.2 (by norm_num)
  have h_sqrt_lower : (9165 : ℝ) / 1000 < Real.sqrt 84 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h_sqrt_upper : Real.sqrt 84 < (22913 : ℝ) / 2500 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h_period_lower : (1371 : ℝ) / 2000 <
      timeInSeconds setup.oscillationPeriod := by
    rw [h_period, lt_div_iff₀ h_sqrt_pos]
    nlinarith [Real.pi_gt_d6]
  have h_period_upper : timeInSeconds setup.oscillationPeriod <
      (1373 : ℝ) / 2000 := by
    rw [h_period, div_lt_iff₀ h_sqrt_pos]
    nlinarith [Real.pi_lt_d6]
  have h_match :
      MatchesDisplayedPeriod setup.oscillationPeriod recordedAnswerChoice := by
    rw [MatchesDisplayedPeriod, recordedAnswerChoice, AnswerChoice.seconds, abs_le]
    constructor <;> norm_num <;> linarith
  refine ⟨h_match, ?_⟩
  intro other h_other
  change other ≠ AnswerChoice.C at h_other
  change |timeInSeconds setup.oscillationPeriod - (686 : ℝ) / 1000| <
    |timeInSeconds setup.oscillationPeriod - other.seconds|
  change |timeInSeconds setup.oscillationPeriod - (686 : ℝ) / 1000| ≤
    (1 : ℝ) / 2000 at h_match
  cases other with
  | A =>
      simp only [AnswerChoice.seconds]
      calc
        |timeInSeconds setup.oscillationPeriod - (686 : ℝ) / 1000| ≤
            (1 : ℝ) / 2000 := h_match
        _ < |timeInSeconds setup.oscillationPeriod - (619 : ℝ) / 1000| := by
          rw [abs_of_pos (by linarith)]
          norm_num
          linarith
  | B =>
      simp only [AnswerChoice.seconds]
      calc
        |timeInSeconds setup.oscillationPeriod - (686 : ℝ) / 1000| ≤
            (1 : ℝ) / 2000 := h_match
        _ < |timeInSeconds setup.oscillationPeriod - (628 : ℝ) / 1000| := by
          rw [abs_of_pos (by linarith)]
          norm_num
          linarith
  | C => exact (h_other rfl).elim
  | D =>
      simp only [AnswerChoice.seconds]
      calc
        |timeInSeconds setup.oscillationPeriod - (686 : ℝ) / 1000| ≤
            (1 : ℝ) / 2000 := h_match
        _ < |timeInSeconds setup.oscillationPeriod - (742 : ℝ) / 1000| := by
          rw [abs_of_neg (by linarith)]
          norm_num
          linarith

end PhyXMiniProblems.ProblemPhyXMini0257
