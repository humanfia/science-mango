import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0733

open Dimension

/-!
# Vertical displacement of machinery moved along an inclined plank

A heavy piece of machinery is moved a distance `d = 12.5 m` up a straight
plank whose angle to the horizontal is `theta = 20 degrees`.  The primary
figure shows the machinery on the rising plank, a dimension line parallel to
the plank labelled `d`, and the angle between the plank and horizontal ground
labelled `theta`.

Distances below are nonnegative, unit-independent Physlib quantities.  Real
numbers occur only as named-unit readouts and dimensionless answer values;
the incline itself is represented by Mathlib's angle type.

Assumption/target boundary:

* scenario and figure predicates identify the machinery, plank, motion
  direction, and the meanings of the labels `d` and `theta`;
* the numerical readouts state only the supplied `12.5 m` and `20 degrees`;
* the governing law states the generic vertical projection relation
  `vertical = path length * sin(theta)` in every length unit;
* neither the vertical distance, the displayed value `4.28 m`, nor choice C
  occurs in any premise structure.
-/

/-! ## Dimensionful distances and angle conversion -/

/-- A nonnegative physical distance, represented coherently in every unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Read a physical distance in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Metre readout of a physical distance. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Convert a numerical degree readout to Mathlib's angle type. -/
def angleFromDegrees (degreeValue : ℝ) : Real.Angle :=
  ((degreeValue * Real.pi / 180 : ℝ) : Real.Angle)

/-! ## Physical roles and primary-figure labels -/

/-- Kind of body being translated along the support surface. -/
inductive MovingBodyKind where
  | heavyMachinery
  | other
  deriving DecidableEq, Repr

/-- Kind of surface that constrains the body's straight-line motion. -/
inductive SupportSurfaceKind where
  | straightInclinedPlank
  | other
  deriving DecidableEq, Repr

/-- Direction of translation along the plank. -/
inductive AlongPlankDirection where
  | upPlank
  | downPlank
  deriving DecidableEq, Repr

/-- Physical objects visible in the supplied raster. -/
inductive FigureObject where
  | heavyMachinery
  | inclinedPlank
  | horizontalGround
  | verticalPlankSupport
  deriving DecidableEq, Fintype, Repr

/-- The two symbolic annotations visible in the supplied raster. -/
inductive FigureLabel where
  | alongPlankDistanceD
  | inclineAngleTheta
  deriving DecidableEq, Fintype, Repr

/-!
Data transcribed from image 733.  The bitmap supplies incidences,
orientations, and the meanings of `d` and `theta`; the numerical values come
from the prose.  It does not display a numerical vertical displacement.
-/
structure SuppliedInclinedPlankFigure where
  showsObject : FigureObject -> Bool
  showsLabel : FigureLabel -> Bool
  distanceLabelD : LengthQuantity
  inclineAngleLabelTheta : Real.Angle
  distanceDimensionLineParallelToPlank : Bool
  thetaIsBetweenPlankAndHorizontal : Bool
  machineryIsSupportedByPlank : Bool
  plankRisesAboveHorizontalGround : Bool
  containsNumericalVerticalAnswer : Bool

/-!
Independent quantities of the motion.  In particular,
`verticalDisplacement` is not defined from the requested answer; it is related
to the path displacement by the projection law below.
-/
structure MachineryInclineSetup where
  bodyKind : MovingBodyKind
  supportSurface : SupportSurfaceKind
  motionDirection : AlongPlankDirection
  alongPlankDisplacementD : LengthQuantity
  verticalDisplacement : LengthQuantity
  plankAngleTheta : Real.Angle
  figure : SuppliedInclinedPlankFigure

/-! ## Scenario, data, figure, and governing-law assumptions -/

/-- Qualitative assignments stated by the problem scenario. -/
structure MatchesMachineryInclineScenario
    (setup : MachineryInclineSetup) : Prop where
  bodyIsHeavyMachinery : setup.bodyKind = .heavyMachinery
  surfaceIsStraightInclinedPlank :
    setup.supportSurface = .straightInclinedPlank
  machineryMovesUpPlank : setup.motionDirection = .upPlank

/-!
The two numerical inputs from the prose.  No vertical distance or answer
choice is included here.
-/
structure MatchesMachineryInclineReadouts
    (setup : MachineryInclineSetup) : Prop where
  alongPlankDistanceMeters :
    lengthInMeters setup.alongPlankDisplacementD = 25 / 2
  inclineAngleTwentyDegrees :
    setup.plankAngleTheta = angleFromDegrees 20

/-!
Objects, labels, and relations read from the primary image.  The label fields
denote setup quantities without assigning the unknown vertical displacement.
-/
structure MatchesSuppliedInclinedPlankFigure
    (setup : MachineryInclineSetup) : Prop where
  everyObjectShown : forall object, setup.figure.showsObject object = true
  everyLabelShown : forall label, setup.figure.showsLabel label = true
  distanceLabelDenotesAlongPlankDisplacement :
    setup.figure.distanceLabelD = setup.alongPlankDisplacementD
  angleLabelDenotesPlankAngle :
    setup.figure.inclineAngleLabelTheta = setup.plankAngleTheta
  distanceLineRunsAlongPlank :
    setup.figure.distanceDimensionLineParallelToPlank = true
  thetaMeasuredFromHorizontal :
    setup.figure.thetaIsBetweenPlankAndHorizontal = true
  machineryRestsOnPlank :
    setup.figure.machineryIsSupportedByPlank = true
  plankRisesAboveGround :
    setup.figure.plankRisesAboveHorizontalGround = true
  figureDoesNotContainNumericalAnswer :
    setup.figure.containsNumericalVerticalAnswer = false

/-- Positivity and first-quadrant conditions selecting the pictured branch. -/
structure HasPhysicalMachineryInclineParameters
    (setup : MachineryInclineSetup) : Prop where
  alongPlankDistancePositive :
    0 < lengthInMeters setup.alongPlankDisplacementD
  inclineHasPositiveVerticalComponent :
    0 < Real.Angle.sin setup.plankAngleTheta
  inclineHasPositiveHorizontalComponent :
    0 < Real.Angle.cos setup.plankAngleTheta

/-!
The governing right-triangle projection law.  For motion a distance `d` up a
straight plank at angle `theta` above horizontal, the vertical component is
`d * sin(theta)`.  The relation is required in every length unit and contains
neither the supplied numerical inputs nor the requested answer.
-/
structure SatisfiesInclinedPlankProjectionLaw
    (setup : MachineryInclineSetup) : Prop where
  verticalProjection : forall unit : LengthUnit,
    lengthReadout unit setup.verticalDisplacement =
      lengthReadout unit setup.alongPlankDisplacementD *
        Real.Angle.sin setup.plankAngleTheta

/-! ## Derived vertical distance and displayed choices -/

/-- Labels of the four metre-valued answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metre value printed beside each answer label. -/
def displayedVerticalDistanceMeters : AnswerChoice -> ℝ
  | .A => 2.42
  | .B => 3.81
  | .C => 4.28
  | .D => 5.63

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
A physical distance agrees with a value displayed to the nearest hundredth
of a metre when its metre readout differs by less than half a hundredth.
-/
def RoundsToDisplayedHundredth
    (distance : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInMeters distance - displayedVerticalDistanceMeters choice| < 1 / 200

/-- A choice is the unique answer matching the vertical distance to 0.01 m. -/
def IsUniqueRoundedAnswer
    (distance : LengthQuantity) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedHundredth distance choice ∧
    ∀ other : AnswerChoice,
      RoundsToDisplayedHundredth distance other -> other = choice

/-!
The projection law first gives the exact trigonometric expression for the
vertical displacement.  This conclusion specializes only the governing law
and the two supplied readouts; it is not a premise of the model.
-/
lemma verticalDisplacementInMeters_eq_sineProjection
    (setup : MachineryInclineSetup)
    (h_readouts : MatchesMachineryInclineReadouts setup)
    (h_projection : SatisfiesInclinedPlankProjectionLaw setup) :
    lengthInMeters setup.verticalDisplacement =
      (25 / 2 : ℝ) * Real.Angle.sin (angleFromDegrees 20) := by
  have hd :
      lengthReadout LengthUnit.meters setup.alongPlankDisplacementD =
        (25 / 2 : ℝ) := by
    simpa [lengthInMeters] using h_readouts.alongPlankDistanceMeters
  rw [lengthInMeters, h_projection.verticalProjection LengthUnit.meters, hd,
    h_readouts.inclineAngleTwentyDegrees]

/-!
Moving `12.5 m` up a plank inclined at `20 degrees` raises the machinery by
`12.5 * sin(20 degrees)` metres, approximately `4.28 m`.  Thus C is the
unique choice agreeing with the physical vertical displacement to the
precision printed in the options.

This formalizes blueprint label `thm:physics:phyx_mini_0733:target`.
Neither the exact projection result, the rounded distance, nor the selection
of C occurs in a scenario, readout, figure, physical-branch, or governing-law
premise.
-/
theorem problem_phyx_mini_0733
    (setup : MachineryInclineSetup)
    (h_scenario : MatchesMachineryInclineScenario setup)
    (h_readouts : MatchesMachineryInclineReadouts setup)
    (h_figure : MatchesSuppliedInclinedPlankFigure setup)
    (h_physical : HasPhysicalMachineryInclineParameters setup)
    (h_projection : SatisfiesInclinedPlankProjectionLaw setup) :
    lengthInMeters setup.verticalDisplacement =
        (25 / 2 : ℝ) * Real.Angle.sin (angleFromDegrees 20) ∧
      IsUniqueRoundedAnswer setup.verticalDisplacement .C := by
  have h_exact :=
    verticalDisplacementInMeters_eq_sineProjection setup h_readouts h_projection
  have h_angle_sin : Real.Angle.sin (angleFromDegrees 20) =
      Real.sin (Real.pi / 9) := by
    rw [angleFromDegrees, Real.Angle.sin_coe]
    congr 1
    ring
  let x : ℝ := Real.pi / 9
  let s : ℝ := Real.sin x
  have hs_pos : 0 < s := by
    dsimp [s, x]
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hs_lt_half : s < (1 / 2 : ℝ) := by
    dsimp [s, x]
    rw [← Real.sin_pi_div_six]
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have htriple : Real.sin (3 * x) = 3 * s - 4 * s ^ 3 := by
    dsimp [s]
    rw [show 3 * x = 2 * x + x by ring, Real.sin_add, Real.sin_two_mul,
      Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hcubic : 3 * s - 4 * s ^ 3 = Real.sqrt 3 / 2 := by
    calc
      3 * s - 4 * s ^ 3 = Real.sin (3 * x) := htriple.symm
      _ = Real.sin (Real.pi / 3) := by
        congr 1
        dsimp [x]
        ring
      _ = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  have hsqrt_lower : (433 / 250 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 433 / 250)]
    norm_num
  have hsqrt_upper : Real.sqrt 3 < (1733 / 1000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1733 / 1000)]
    norm_num
  have hs_lower : (171 / 500 : ℝ) < s := by
    by_contra h
    have hs_le : s ≤ (171 / 500 : ℝ) := le_of_not_gt h
    have hs_sq_le : s ^ 2 ≤ (171 / 500 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hs_pos.le hs_le 2
    have hqs_le : (171 / 500 : ℝ) * s ≤ (171 / 500 : ℝ) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hs_le
        (by norm_num : (0 : ℝ) ≤ 171 / 500)
      nlinarith
    have hcoef : 0 ≤ 3 - 4 * ((171 / 500 : ℝ) ^ 2 +
        (171 / 500 : ℝ) * s + s ^ 2) := by
      nlinarith
    have hprod := mul_nonneg (sub_nonneg.mpr hs_le) hcoef
    nlinarith
  have hs_upper : s < (857 / 2500 : ℝ) := by
    by_contra h
    have hr_le : (857 / 2500 : ℝ) ≤ s := le_of_not_gt h
    have hs_half : s ≤ (1 / 2 : ℝ) := hs_lt_half.le
    have hs_sq_le : s ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hs_pos.le hs_half 2
    have hsr_le : s * (857 / 2500 : ℝ) ≤
        (1 / 2 : ℝ) * (857 / 2500 : ℝ) :=
      mul_le_mul_of_nonneg_right hs_half (by norm_num)
    have hcoef : 0 ≤ 3 - 4 * (s ^ 2 +
        s * (857 / 2500 : ℝ) + (857 / 2500 : ℝ) ^ 2) := by
      nlinarith
    have hprod := mul_nonneg (sub_nonneg.mpr hr_le) hcoef
    nlinarith
  have h_sin_bounds : (171 / 500 : ℝ) < Real.sin (Real.pi / 9) ∧
      Real.sin (Real.pi / 9) < (857 / 2500 : ℝ) := by
    simpa [s, x] using And.intro hs_lower hs_upper
  refine ⟨h_exact, ?_⟩
  unfold IsUniqueRoundedAnswer
  constructor
  · unfold RoundsToDisplayedHundredth
    rw [h_exact, h_angle_sin, abs_lt]
    norm_num [displayedVerticalDistanceMeters]
    constructor <;> nlinarith [h_sin_bounds.1, h_sin_bounds.2]
  · intro other hother
    cases other with
    | A =>
        exfalso
        unfold RoundsToDisplayedHundredth at hother
        rw [h_exact, h_angle_sin, abs_lt] at hother
        norm_num [displayedVerticalDistanceMeters] at hother
        nlinarith [h_sin_bounds.1]
    | B =>
        exfalso
        unfold RoundsToDisplayedHundredth at hother
        rw [h_exact, h_angle_sin, abs_lt] at hother
        norm_num [displayedVerticalDistanceMeters] at hother
        nlinarith [h_sin_bounds.1]
    | C => rfl
    | D =>
        exfalso
        unfold RoundsToDisplayedHundredth at hother
        rw [h_exact, h_angle_sin, abs_lt] at hother
        norm_num [displayedVerticalDistanceMeters] at hother
        nlinarith [h_sin_bounds.2]

end PhyXMiniProblems.ProblemPhyXMini0733
