import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0710

open Dimension

/-!
# Tallest cylindrical can that remains upright on an incline

A right circular food can has diameter `7.5 cm` and rests with its circular
base on a rigid plane inclined by `30°`. In the axial cross-section shown by
the source image, the base is labelled `b`, the limiting height is labelled
`h_max`, and the gravitational-force arrow `F_G` acts vertically downward
through the center of mass. At the limiting configuration the gravity line
of action passes through the downhill edge of the base, the tipping pivot.

Lengths and the gravity-force magnitude are unit-independent Physlib
quantities. Real numbers are used only for named-unit readouts, radian-angle
readouts, and dimensionless trigonometric factors. The exact limiting height
is `7.5 * sqrt 3 cm`; the displayed `13 cm` is its closest multiple-choice
approximation, not an exact replacement for the physical value.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- The physical dimension of force, `M L T⁻²`. -/
def forceDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Centimeter readout of a physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- SI readout of a force magnitude, in newtons. -/
def forceMagnitudeInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Convert a dimensionless degree readout to a dimensionless radian readout. -/
def degreesToRadians (degrees : ℝ) : ℝ := degrees * Real.pi / 180

/-! ## Physical setup and primary-image vocabulary -/

/-- Three-dimensional shape of the food container. -/
inductive CanShape where
  | rightCircularCylinder
  | other
  deriving DecidableEq, Repr

/-- Mass-distribution idealization represented by the central mass mark. -/
inductive CanMassDistribution where
  | centered
  | other
  deriving DecidableEq, Repr

/-- Orientation of the can axis relative to the support plane. -/
inductive CanOrientation where
  | axisNormalToIncline
  | other
  deriving DecidableEq, Repr

/-- Kind of support surface used in the statics model. -/
inductive SupportSurfaceKind where
  | rigidPlanarIncline
  | other
  deriving DecidableEq, Repr

/-- Distinguished points in the axial cross-section of the can. -/
inductive CanPoint where
  | centerOfMass
  | downhillPivot
  | uphillBaseEdge
  deriving DecidableEq, Repr

/-- Vertical direction of the gravitational-force arrow. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Physical objects visible in the supplied raster. -/
inductive FigureObject where
  | canCrossSection
  | inclinedPlane
  | centerOfMassMark
  | gravityArrow
  | gravityLineOfAction
  | downhillPivotPoint
  deriving DecidableEq, Fintype, Repr

/-- Literal and numerical annotations visible in the supplied raster. -/
inductive FigureLabel where
  | baseB
  | maximumHeightHMax
  | gravitationalForceFG
  | lineOfAction
  | inclineThirtyDegrees
  | canRotationThirtyDegrees
  deriving DecidableEq, Fintype, Repr

/--
The gravitational load pictured on the can. Its dimensional magnitude,
point of application, and spatial direction are retained separately.
-/
structure GravitationalForce where
  magnitude : ForceMagnitudeQuantity
  applicationPoint : CanPoint
  direction : VerticalDirection

/-!
Data transcribed from image 710. The two Boolean incidence fields record
which distinguished points lie on the dashed gravity line; their analytic
coordinate meaning is supplied separately by the limiting-line geometry law.
The image itself contains no numerical height answer.
-/
structure SuppliedCanFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  baseLabelB : LengthQuantity
  heightLabelHMax : LengthQuantity
  inclineAngleLabelRadians : ℝ
  canRotationLabelRadians : ℝ
  gravityArrowApplicationPoint : CanPoint
  gravityArrowDirection : VerticalDirection
  lineOfActionPassesThroughCenterOfMass : Bool
  lineOfActionPassesThroughDownhillPivot : Bool
  containsNumericalHeightAnswer : Bool

/-!
The independent physical quantities of the can-on-incline experiment.

`centerOfMassAlongBaseFromDownhillPivot` and
`centerOfMassAboveBaseNormal` are the two components of the center-of-mass
position in coordinates tangent and normal to the incline. The predicate
`restsWithoutFallingAtHeight` describes the family of otherwise identical,
centered cylindrical cans with varying height. It is constrained by the
general statics law below rather than being defined from the desired answer.
-/
structure CanOnInclineSetup where
  shape : CanShape
  massDistribution : CanMassDistribution
  orientation : CanOrientation
  supportSurface : SupportSurfaceKind
  diameter : LengthQuantity
  baseWidthB : LengthQuantity
  heightHMax : LengthQuantity
  centerOfMassAlongBaseFromDownhillPivot : LengthQuantity
  centerOfMassAboveBaseNormal : LengthQuantity
  inclineAngleRadians : ℝ
  gravitationalForce : GravitationalForce
  restsWithoutFallingAtHeight : LengthQuantity → Prop
  figure : SuppliedCanFigure

/-! ## Assumptions: scenario, readouts, figure, geometry, and statics -/

/-- Qualitative physical assignments stated by the prose and picture. -/
structure MatchesCanOnInclineScenario (setup : CanOnInclineSetup) : Prop where
  canIsRightCircularCylinder : setup.shape = .rightCircularCylinder
  massDistributionIsCentered : setup.massDistribution = .centered
  canAxisIsNormalToIncline : setup.orientation = .axisNormalToIncline
  supportIsRigidPlanarIncline : setup.supportSurface = .rigidPlanarIncline
  gravityActsAtCenterOfMass :
    setup.gravitationalForce.applicationPoint = .centerOfMass
  gravityPointsVerticallyDownward :
    setup.gravitationalForce.direction = .downward

/--
The numerical input from the problem statement: diameter `7.5 cm` and slope
angle `30° = π/6` radians. No height value occurs in these readouts.
-/
structure MatchesCanProblemReadouts (setup : CanOnInclineSetup) : Prop where
  diameterCentimeters : lengthInCentimeters setup.diameter = 15 / 2
  inclineAngleThirtyDegrees :
    setup.inclineAngleRadians = degreesToRadians 30

/--
Objects, labels, arrow direction, and incidences read from the primary image.
The symbols `b` and `h_max` denote setup fields but do not assign the unknown
height a numerical value.
-/
structure MatchesSuppliedCanFigure (setup : CanOnInclineSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  everyLabelShown : ∀ label, setup.figure.showsLabel label = true
  baseLabelDenotesBaseWidth : setup.figure.baseLabelB = setup.baseWidthB
  heightLabelDenotesUnknownHeight :
    setup.figure.heightLabelHMax = setup.heightHMax
  inclineAngleLabel :
    setup.figure.inclineAngleLabelRadians = degreesToRadians 30
  canRotationAngleLabel :
    setup.figure.canRotationLabelRadians = degreesToRadians 30
  gravityArrowApplicationPoint :
    setup.figure.gravityArrowApplicationPoint = .centerOfMass
  gravityArrowDirection : setup.figure.gravityArrowDirection = .downward
  linePassesThroughCenterOfMass :
    setup.figure.lineOfActionPassesThroughCenterOfMass = true
  linePassesThroughDownhillPivot :
    setup.figure.lineOfActionPassesThroughDownhillPivot = true
  figureDoesNotContainAnswer :
    setup.figure.containsNumericalHeightAnswer = false

/-- Positivity and acute-angle conditions selecting the physical branch. -/
structure HasPhysicalCanParameters (setup : CanOnInclineSetup) : Prop where
  diameterPositive : 0 < lengthInCentimeters setup.diameter
  baseWidthPositive : 0 < lengthInCentimeters setup.baseWidthB
  heightPositive : 0 < lengthInCentimeters setup.heightHMax
  centerOfMassAlongPositive :
    0 < lengthInCentimeters setup.centerOfMassAlongBaseFromDownhillPivot
  centerOfMassNormalPositive :
    0 < lengthInCentimeters setup.centerOfMassAboveBaseNormal
  gravityMagnitudePositive :
    0 < forceMagnitudeInNewtons setup.gravitationalForce.magnitude
  inclineAngleAcute :
    setup.inclineAngleRadians ∈ Set.Ioo 0 (Real.pi / 2)

/-!
Axial cross-section geometry for a centered right circular cylinder. The
base chord `b` equals the cylinder diameter, and the center of mass lies
halfway across the base and halfway up the can. The equations are stated in
every length unit and contain no solved value of `h_max`.
-/
structure SatisfiesCenteredCanGeometry (setup : CanOnInclineSetup) : Prop where
  baseWidthEqualsDiameter : ∀ unit : LengthUnit,
    lengthReadout unit setup.baseWidthB =
      lengthReadout unit setup.diameter
  centerOfMassHalfwayAcrossBase : ∀ unit : LengthUnit,
    2 * lengthReadout unit setup.centerOfMassAlongBaseFromDownhillPivot =
      lengthReadout unit setup.baseWidthB
  centerOfMassHalfwayUpCan : ∀ unit : LengthUnit,
    2 * lengthReadout unit setup.centerOfMassAboveBaseNormal =
      lengthReadout unit setup.heightHMax

/-!
Analytic meaning of the figure statement that the vertical gravity line
through the center of mass passes through the downhill pivot. In coordinates
tangent and normal to the incline, the two horizontal projections cancel.
This is the limiting tipping geometry, not the requested solved height.
-/
structure SatisfiesLimitingLineOfActionGeometry
    (setup : CanOnInclineSetup) : Prop where
  centerOfMassDirectlyOverPivot : ∀ unit : LengthUnit,
    lengthReadout unit setup.centerOfMassAlongBaseFromDownhillPivot *
        Real.cos setup.inclineAngleRadians =
      lengthReadout unit setup.centerOfMassAboveBaseNormal *
        Real.sin setup.inclineAngleRadians

/-!
The governing static-stability law for otherwise identical centered cans of
varying height. A can remains upright exactly while the vertical gravity line
meets the base footprint. In the chosen incline coordinates this is
`height * sin θ ≤ b * cos θ`; equality is the downhill tipping threshold.
No numerical height or answer label occurs in the law.
-/
structure SatisfiesStaticStabilityLaw (setup : CanOnInclineSetup) : Prop where
  stableIffGravityLineWithinBase : ∀ candidateHeight : LengthQuantity,
    setup.restsWithoutFallingAtHeight candidateHeight ↔
      lengthInCentimeters candidateHeight *
          Real.sin setup.inclineAngleRadians ≤
        lengthInCentimeters setup.baseWidthB *
          Real.cos setup.inclineAngleRadians

/-! ## Derived maximum-height criterion and answer choices -/

/-- A physical height is stable and is at least as tall as every stable one. -/
def IsTallestStableHeight
    (setup : CanOnInclineSetup) (height : LengthQuantity) : Prop :=
  setup.restsWithoutFallingAtHeight height ∧
    ∀ candidateHeight : LengthQuantity,
      setup.restsWithoutFallingAtHeight candidateHeight →
        lengthInCentimeters candidateHeight ≤
          lengthInCentimeters height

/-- Labels of the four centimeter-valued answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Centimeter value printed beside each answer label. -/
def displayedHeightCentimeters : AnswerChoice → ℝ
  | .A => 8
  | .B => 10
  | .C => 13
  | .D => 15

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A choice is at least as close to the exact limiting height as every choice. -/
def IsClosestDisplayedHeight
    (setup : CanOnInclineSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |lengthInCentimeters setup.heightHMax -
        displayedHeightCentimeters choice| ≤
      |lengthInCentimeters setup.heightHMax -
        displayedHeightCentimeters other|

/-- A choice is the unique closest displayed height. -/
def IsUniqueClosestDisplayedHeight
    (setup : CanOnInclineSetup) (choice : AnswerChoice) : Prop :=
  IsClosestDisplayedHeight setup choice ∧
    ∀ other : AnswerChoice,
      IsClosestDisplayedHeight setup other → other = choice

/-!
The centered-mass and limiting-line geometry give the general threshold
formula `h_max = b / tan θ`. This is a derived relation, not a premise.
-/
lemma limitingHeightInCentimeters_eq_base_div_tan
    (setup : CanOnInclineSetup)
    (h_physical : HasPhysicalCanParameters setup)
    (h_geometry : SatisfiesCenteredCanGeometry setup)
    (h_lineOfAction : SatisfiesLimitingLineOfActionGeometry setup) :
    lengthInCentimeters setup.heightHMax =
      lengthInCentimeters setup.baseWidthB /
        Real.tan setup.inclineAngleRadians := by
  have h_sin_pos : 0 < Real.sin setup.inclineAngleRadians :=
    Real.sin_pos_of_pos_of_lt_pi h_physical.inclineAngleAcute.1
      (by linarith [h_physical.inclineAngleAcute.2, Real.pi_pos])
  have h_cos_pos : 0 < Real.cos setup.inclineAngleRadians :=
    Real.cos_pos_of_mem_Ioo
      ⟨(neg_lt_zero.mpr (div_pos Real.pi_pos (by norm_num))).trans
          h_physical.inclineAngleAcute.1,
        h_physical.inclineAngleAcute.2⟩
  have h_half_up :
      2 * lengthInCentimeters setup.centerOfMassAboveBaseNormal =
        lengthInCentimeters setup.heightHMax := by
    simpa only [lengthInCentimeters] using
      h_geometry.centerOfMassHalfwayUpCan LengthUnit.centimeters
  have h_half_across :
      2 * lengthInCentimeters
          setup.centerOfMassAlongBaseFromDownhillPivot =
        lengthInCentimeters setup.baseWidthB := by
    simpa only [lengthInCentimeters] using
      h_geometry.centerOfMassHalfwayAcrossBase LengthUnit.centimeters
  have h_directly_over :
      lengthInCentimeters setup.centerOfMassAlongBaseFromDownhillPivot *
          Real.cos setup.inclineAngleRadians =
        lengthInCentimeters setup.centerOfMassAboveBaseNormal *
          Real.sin setup.inclineAngleRadians := by
    simpa only [lengthInCentimeters] using
      h_lineOfAction.centerOfMassDirectlyOverPivot LengthUnit.centimeters
  have h_threshold :
      lengthInCentimeters setup.heightHMax *
          Real.sin setup.inclineAngleRadians =
        lengthInCentimeters setup.baseWidthB *
          Real.cos setup.inclineAngleRadians := by
    calc
      lengthInCentimeters setup.heightHMax *
            Real.sin setup.inclineAngleRadians =
          (2 * lengthInCentimeters setup.centerOfMassAboveBaseNormal) *
            Real.sin setup.inclineAngleRadians := by
              rw [h_half_up]
      _ = 2 *
          (lengthInCentimeters setup.centerOfMassAboveBaseNormal *
            Real.sin setup.inclineAngleRadians) := by ring
      _ = 2 *
          (lengthInCentimeters setup.centerOfMassAlongBaseFromDownhillPivot *
            Real.cos setup.inclineAngleRadians) := by
              rw [h_directly_over]
      _ = (2 *
          lengthInCentimeters setup.centerOfMassAlongBaseFromDownhillPivot) *
            Real.cos setup.inclineAngleRadians := by ring
      _ = lengthInCentimeters setup.baseWidthB *
          Real.cos setup.inclineAngleRadians := by
            rw [h_half_across]
  rw [Real.tan_eq_sin_div_cos]
  apply (eq_div_iff (div_ne_zero h_sin_pos.ne' h_cos_pos.ne')).2
  field_simp
  simpa only [mul_comm] using h_threshold

/-!
For a centered cylindrical can of diameter `7.5 cm` on a `30°` incline, the
limiting gravity line passes through the downhill base edge. Consequently
`h_max = b / tan(30°) = 7.5 * sqrt 3 cm`.

This exact height is the largest one satisfying the static-stability
criterion. It is approximately `12.99 cm`, making `13 cm` the unique closest
displayed choice, namely answer C.

This formalizes blueprint label `thm:physics:phyx_mini_0710:target`.
Neither the exact height, maximality, nor the selection of C occurs in any
scenario, readout, figure, geometry, or governing-law premise.
-/
theorem problem_phyx_mini_0710
    (setup : CanOnInclineSetup)
    (h_scenario : MatchesCanOnInclineScenario setup)
    (h_readouts : MatchesCanProblemReadouts setup)
    (h_figure : MatchesSuppliedCanFigure setup)
    (h_physical : HasPhysicalCanParameters setup)
    (h_geometry : SatisfiesCenteredCanGeometry setup)
    (h_lineOfAction : SatisfiesLimitingLineOfActionGeometry setup)
    (h_statics : SatisfiesStaticStabilityLaw setup) :
    lengthInCentimeters setup.heightHMax =
        (15 / 2 : ℝ) * Real.sqrt 3 ∧
      IsTallestStableHeight setup setup.heightHMax ∧
      IsUniqueClosestDisplayedHeight setup .C := by
  have h_angle : setup.inclineAngleRadians = Real.pi / 6 := by
    calc
      setup.inclineAngleRadians = degreesToRadians 30 :=
        h_readouts.inclineAngleThirtyDegrees
      _ = Real.pi / 6 := by
        unfold degreesToRadians
        ring
  have h_base :
      lengthInCentimeters setup.baseWidthB = (15 / 2 : ℝ) := by
    calc
      lengthInCentimeters setup.baseWidthB =
          lengthInCentimeters setup.diameter := by
        simpa only [lengthInCentimeters] using
          h_geometry.baseWidthEqualsDiameter LengthUnit.centimeters
      _ = (15 / 2 : ℝ) := h_readouts.diameterCentimeters
  have h_sqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have h_sqrt_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by norm_num
  have h_exact :
      lengthInCentimeters setup.heightHMax =
        (15 / 2 : ℝ) * Real.sqrt 3 := by
    rw [limitingHeightInCentimeters_eq_base_div_tan setup h_physical
      h_geometry h_lineOfAction, h_base, h_angle, Real.tan_pi_div_six]
    field_simp
  refine ⟨h_exact, ?_, ?_⟩
  · constructor
    · apply
        (h_statics.stableIffGravityLineWithinBase setup.heightHMax).2
      rw [h_exact, h_base, h_angle, Real.sin_pi_div_six,
        Real.cos_pi_div_six]
      ring_nf
      exact le_rfl
    · intro candidateHeight h_stable
      have h_candidate :=
        (h_statics.stableIffGravityLineWithinBase candidateHeight).1
          h_stable
      rw [h_base, h_angle, Real.sin_pi_div_six,
        Real.cos_pi_div_six] at h_candidate
      rw [h_exact]
      nlinarith
  · have h_height_gt :
        (23 / 2 : ℝ) < (15 / 2 : ℝ) * Real.sqrt 3 := by
      nlinarith
    have h_height_lt :
        (15 / 2 : ℝ) * Real.sqrt 3 < (13 : ℝ) := by
      nlinarith
    have h_closest : IsClosestDisplayedHeight setup .C := by
      intro other
      rw [h_exact]
      cases other with
      | A =>
          simp only [displayedHeightCentimeters]
          rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
          linarith
      | B =>
          simp only [displayedHeightCentimeters]
          rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
          linarith
      | C => exact le_rfl
      | D =>
          simp only [displayedHeightCentimeters]
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          linarith
    refine ⟨h_closest, ?_⟩
    intro other h_other
    cases other with
    | A =>
        have h_to_C := h_other .C
        rw [h_exact] at h_to_C
        simp only [displayedHeightCentimeters] at h_to_C
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
          at h_to_C
        exfalso
        linarith
    | B =>
        have h_to_C := h_other .C
        rw [h_exact] at h_to_C
        simp only [displayedHeightCentimeters] at h_to_C
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
          at h_to_C
        exfalso
        linarith
    | C => rfl
    | D =>
        have h_to_C := h_other .C
        rw [h_exact] at h_to_C
        simp only [displayedHeightCentimeters] at h_to_C
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          at h_to_C
        exfalso
        linarith

end PhyXMiniProblems.ProblemPhyXMini0710
