import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0709

open Dimension

/-!
# Minimum static-friction coefficient for a ladder

A uniform `3.0 m` ladder rests at `60°` above a horizontal floor against a
frictionless vertical wall.  The primary figure labels the weight `F_G`, the
ground normal `n₁`, the wall normal `n₂`, the static friction `f_s`, the
horizontal center-of-mass lever arm `d₁`, and the wall-contact height `d₂`.

Lengths and force magnitudes are genuine unit-covariant Physlib quantities.
Real numbers below are used only for coherent SI readouts, a dimensionless
angle or coefficient, and displayed multiple-choice values.
-/

/-! ## Dimensionful physical quantities and coherent SI readouts -/

/-- A nonnegative physical length. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative force magnitude, with dimension mass times acceleration. -/
abbrev ForceMagnitude : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical length in coherent SI metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical force magnitude in coherent SI newtons. -/
def forceInNewtons (force : ForceMagnitude) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Convert an angle readout in degrees to its dimensionless radian value. -/
def angleInRadiansFromDegrees (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/-! ## Figure labels and the physical setup -/

/-- The four force-vector labels printed in the supplied figure. -/
inductive ForceLabel where
  | gravityFG
  | groundNormalN1
  | wallNormalN2
  | staticFrictionFs
  deriving DecidableEq, Fintype, Repr

/-- Cardinal directions of the force arrows in the supplied figure. -/
inductive ForceDirection where
  | leftward
  | rightward
  | upward
  | downward
  deriving DecidableEq, Fintype, Repr

/-- Contact idealizations for the two supporting surfaces. -/
inductive SurfaceCondition where
  | frictionless
  | supportsStaticFriction
  deriving DecidableEq, Repr

/-- Named points on the ladder used by the force and torque annotations. -/
inductive LadderPoint where
  | base
  | centerOfMass
  | wallContact
  deriving DecidableEq, Fintype, Repr

/-!
Literal labels and qualitative information visible in the primary raster.
The figure does not print numerical values for `d₁` or `d₂`; it only names
them, so their geometry is imposed separately below.
-/
structure LadderStaticsFigure where
  ladderLengthLabelMeters : ℝ
  angleLabelDegrees : ℝ
  showsForce : ForceLabel → Bool
  shownForceDirection : ForceLabel → ForceDirection
  showsCenterOfMassMarker : Bool
  showsDistanceD1 : Bool
  showsDistanceD2 : Bool
  showsZeroNetTorqueAnnotation : Bool
  torqueReferencePoint : LadderPoint

/-!
The dimensionful quantities of the statics problem.  Each force field is a
magnitude; its direction is recorded independently by the primary-figure
data.  In particular, no coefficient value or answer choice is stored here.
-/
structure LadderStaticsSetup where
  figure : LadderStaticsFigure
  ladderLength : LengthMagnitude
  angleAboveHorizontal : ℝ
  centerOfMassHorizontalLeverArmD1 : LengthMagnitude
  wallContactHeightD2 : LengthMagnitude
  forceMagnitude : ForceLabel → ForceMagnitude
  wallCondition : SurfaceCondition
  groundCondition : SurfaceCondition

/-!
Problem and primary-image data: a `3.0 m` ladder at `60°`, the four force
arrows with the displayed orientations, a frictionless wall, static friction
at the ground, the two lever-arm labels, and the torque balance annotation at
the ladder base.  These data contain no proposed value of `μ_s`.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : LadderStaticsSetup) : Prop where
  lengthLabelIsThreeMeters :
    setup.figure.ladderLengthLabelMeters = 3
  physicalLengthMatchesLabel :
    lengthInMeters setup.ladderLength =
      setup.figure.ladderLengthLabelMeters
  angleLabelIsSixtyDegrees :
    setup.figure.angleLabelDegrees = 60
  physicalAngleMatchesLabel :
    setup.angleAboveHorizontal =
      angleInRadiansFromDegrees setup.figure.angleLabelDegrees
  everyForceIsShown :
    ∀ force, setup.figure.showsForce force = true
  gravityPointsDown :
    setup.figure.shownForceDirection .gravityFG = .downward
  groundNormalPointsUp :
    setup.figure.shownForceDirection .groundNormalN1 = .upward
  wallNormalPointsRight :
    setup.figure.shownForceDirection .wallNormalN2 = .rightward
  staticFrictionPointsLeft :
    setup.figure.shownForceDirection .staticFrictionFs = .leftward
  centerOfMassIsMarked :
    setup.figure.showsCenterOfMassMarker = true
  distanceD1IsShown :
    setup.figure.showsDistanceD1 = true
  distanceD2IsShown :
    setup.figure.showsDistanceD2 = true
  wallIsFrictionless :
    setup.wallCondition = .frictionless
  groundSuppliesStaticFriction :
    setup.groundCondition = .supportsStaticFriction
  zeroNetTorqueIsShown :
    setup.figure.showsZeroNetTorqueAnnotation = true
  torqueIsTakenAboutBase :
    setup.figure.torqueReferencePoint = .base

/-!
Geometry of the uniform ladder in the depicted branch.  The center of mass is
at the midpoint, so `d₁` is the horizontal moment arm `(L/2) cos θ`; `d₂` is
the vertical wall-contact height `L sin θ`.
-/
structure HasUniformLadderGeometry (setup : LadderStaticsSetup) : Prop where
  centerOfMassAtMidpoint :
    lengthInMeters setup.centerOfMassHorizontalLeverArmD1 =
      lengthInMeters setup.ladderLength / 2 *
        Real.cos setup.angleAboveHorizontal
  wallContactHeight :
    lengthInMeters setup.wallContactHeightD2 =
      lengthInMeters setup.ladderLength *
        Real.sin setup.angleAboveHorizontal

/-!
Positivity and angle conditions selecting the nondegenerate configuration
shown in the image.  They constrain only the physical branch, not the sought
coefficient.
-/
structure HasPhysicalLadderParameters (setup : LadderStaticsSetup) : Prop where
  ladderLengthPositive :
    0 < lengthInMeters setup.ladderLength
  centerLeverArmPositive :
    0 < lengthInMeters setup.centerOfMassHorizontalLeverArmD1
  wallContactHeightPositive :
    0 < lengthInMeters setup.wallContactHeightD2
  anglePositive :
    0 < setup.angleAboveHorizontal
  angleAcute :
    setup.angleAboveHorizontal < Real.pi / 2
  gravitationalForcePositive :
    0 < forceInNewtons (setup.forceMagnitude .gravityFG)
  groundNormalPositive :
    0 < forceInNewtons (setup.forceMagnitude .groundNormalN1)

/-! ## Governing laws -/

/-!
Static translational and rotational equilibrium in the force directions shown
by the figure.  The horizontal balance is `f_s = n₂`, the vertical balance is
`n₁ = F_G`, and zero torque about the base is `n₂ d₂ = F_G d₁`.
-/
structure SatisfiesStaticForceAndTorqueBalance
    (setup : LadderStaticsSetup) : Prop where
  horizontalForceBalance :
    forceInNewtons (setup.forceMagnitude .staticFrictionFs) =
      forceInNewtons (setup.forceMagnitude .wallNormalN2)
  verticalForceBalance :
    forceInNewtons (setup.forceMagnitude .groundNormalN1) =
      forceInNewtons (setup.forceMagnitude .gravityFG)
  torqueBalanceAboutBase :
    forceInNewtons (setup.forceMagnitude .wallNormalN2) *
        lengthInMeters setup.wallContactHeightD2 =
      forceInNewtons (setup.forceMagnitude .gravityFG) *
        lengthInMeters setup.centerOfMassHorizontalLeverArmD1

/-!
Coulomb's static-friction inequality for a proposed dimensionless coefficient
`μ`.  Such a coefficient can support the equilibrium when `μ ≥ 0` and the
required friction magnitude does not exceed `μ n₁`.
-/
def CoefficientPreventsSlip
    (setup : LadderStaticsSetup) (μ : ℝ) : Prop :=
  0 ≤ μ ∧
    forceInNewtons (setup.forceMagnitude .staticFrictionFs) ≤
      μ * forceInNewtons (setup.forceMagnitude .groundNormalN1)

/-! ## Multiple-choice readouts and formalization target -/

/-- Labels of the four answers supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless static-friction coefficient printed beside each choice. -/
def AnswerChoice.coefficient : AnswerChoice → ℝ
  | .A => 35 / 100
  | .B => 23 / 100
  | .C => 29 / 100
  | .D => 41 / 100

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
A displayed option is closest to an exact coefficient when its absolute error
is no greater than that of any other displayed option.
-/
def IsClosestAnswerChoice (coefficient : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |coefficient - choice.coefficient| ≤
      |coefficient - other.coefficient|

/-!
For a uniform ladder at `60°`, force and torque balance give
`μ_min = (1/2) cot 60° = 1/(2√3)`.  This is approximately `0.288675`, so the
closest displayed coefficient is `0.29`, recorded answer C.

The minimum is expressed as an `IsLeast` conclusion over every coefficient
that satisfies the generic Coulomb bound; it is not included in any premise.

Blueprint label: `thm:physics:phyx_mini_0709:target`.
-/
theorem minimumStaticFrictionCoefficient_is_answerChoiceC
    (setup : LadderStaticsSetup)
    (hFigure : MatchesProblemAndPrimaryFigure setup)
    (hGeometry : HasUniformLadderGeometry setup)
    (hPhysical : HasPhysicalLadderParameters setup)
    (hEquilibrium : SatisfiesStaticForceAndTorqueBalance setup) :
    IsLeast {μ : ℝ | CoefficientPreventsSlip setup μ}
        (1 / (2 * Real.sqrt 3)) ∧
      IsClosestAnswerChoice (1 / (2 * Real.sqrt 3))
        recordedAnswerChoice := by
  have hLength : lengthInMeters setup.ladderLength = 3 := by
    rw [hFigure.physicalLengthMatchesLabel,
      hFigure.lengthLabelIsThreeMeters]
  have hAngle : setup.angleAboveHorizontal = Real.pi / 3 := by
    rw [hFigure.physicalAngleMatchesLabel,
      hFigure.angleLabelIsSixtyDegrees]
    unfold angleInRadiansFromDegrees
    ring
  have hCenterArm :
      lengthInMeters setup.centerOfMassHorizontalLeverArmD1 = 3 / 4 := by
    rw [hGeometry.centerOfMassAtMidpoint, hLength, hAngle,
      Real.cos_pi_div_three]
    norm_num
  have hWallHeight :
      lengthInMeters setup.wallContactHeightD2 =
        3 * Real.sqrt 3 / 2 := by
    rw [hGeometry.wallContactHeight, hLength, hAngle,
      Real.sin_pi_div_three]
    ring
  have hsqrtPos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtNe : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt hsqrtPos
  have hRequiredFriction :
      forceInNewtons (setup.forceMagnitude .staticFrictionFs) =
        (1 / (2 * Real.sqrt 3)) *
          forceInNewtons (setup.forceMagnitude .groundNormalN1) := by
    rw [hEquilibrium.horizontalForceBalance,
      hEquilibrium.verticalForceBalance]
    have hTorque := hEquilibrium.torqueBalanceAboutBase
    rw [hWallHeight, hCenterArm] at hTorque
    field_simp [hsqrtNe]
    nlinarith
  have hCoefficientNonnegative : 0 ≤ (1 / (2 * Real.sqrt 3) : ℝ) := by
    positivity
  constructor
  · constructor
    · exact ⟨hCoefficientNonnegative, hRequiredFriction.le⟩
    · intro μ hμ
      rcases hμ with ⟨_, hFrictionBound⟩
      rw [hRequiredFriction] at hFrictionBound
      exact le_of_mul_le_mul_right hFrictionBound
        hPhysical.groundNormalPositive
  · have hDenominatorPositive : 0 < (2 * Real.sqrt 3 : ℝ) := by
      positivity
    have hsqrtUpper : Real.sqrt (3 : ℝ) ≤ 25 / 13 := by
      rw [Real.sqrt_le_iff]
      constructor <;> norm_num
    have hsqrtLower : (50 / 29 : ℝ) ≤ Real.sqrt 3 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    have hLower :
        (13 / 50 : ℝ) ≤ 1 / (2 * Real.sqrt 3) := by
      rw [le_div_iff₀ hDenominatorPositive]
      nlinarith
    have hUpper :
        1 / (2 * Real.sqrt 3) ≤ (29 / 100 : ℝ) := by
      rw [div_le_iff₀ hDenominatorPositive]
      nlinarith
    intro other
    cases other with
    | A =>
        change
          |1 / (2 * Real.sqrt 3) - 29 / 100| ≤
            |1 / (2 * Real.sqrt 3) - 35 / 100|
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        norm_num
    | B =>
        change
          |1 / (2 * Real.sqrt 3) - 29 / 100| ≤
            |1 / (2 * Real.sqrt 3) - 23 / 100|
        rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
        linarith
    | C =>
        exact le_rfl
    | D =>
        change
          |1 / (2 * Real.sqrt 3) - 29 / 100| ≤
            |1 / (2 * Real.sqrt 3) - 41 / 100|
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        norm_num

end PhyXMiniProblems.ProblemPhyXMini0709
