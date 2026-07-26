import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0681

open Dimension

/-!
# Tension at a perpendicular two-strand spider-web junction

A spider pulls downward on the common junction of three silk strands.  The two
upper strands are perpendicular, and the diagram chooses the `x` and `y` axes
along those strands.  Their tensions are labelled `Tₓ` and `Tᵧ` respectively.

Forces are unit-independent Physlib quantities with physical dimension
`M L T⁻²`.  Real numbers occur only in coherent-SI vector readouts, in
dimensionless diagram coordinates and directions, and in the numerical values
printed by the problem and its answer choices.
-/

/-! ## Physical forces and diagram directions -/

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A unit-independent planar physical force quantity. -/
abbrev PlanarForceQuantity : Type :=
  Dimensionful
    (WithDim forceDimension (EuclideanSpace ℝ (Fin 2)))

/-- A dimensionless vector used for directions and locations in the diagram. -/
abbrev DiagramVector : Type := EuclideanSpace ℝ (Fin 2)

/-- Downward in diagram coordinates: coordinate `0` is right and `1` is up. -/
def downwardDiagramDirection : DiagramVector :=
  !₂[0, -1]

/-- Read a planar force vector in coherent SI units, i.e. newtons. -/
def forceVectorInNewtons
    (force : PlanarForceQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (force UnitChoices.SI).val

/-- The Euclidean magnitude of a coherent-SI force readout, in newtons. -/
def forceMagnitudeInNewtons (force : PlanarForceQuantity) : ℝ :=
  ‖forceVectorInNewtons force‖

/-- The two sloping strands, simultaneously used as the labelled coordinate axes. -/
inductive SlopingAxis where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- Qualitative directions of lines and arrows in the supplied raster. -/
inductive FigureDirection where
  | upperRight
  | upperLeft
  | downward
  deriving DecidableEq, Fintype, Repr

/-- The direction in which each upper strand leaves the junction in the figure. -/
def expectedUpperStrandDirection : SlopingAxis → FigureDirection
  | .x => .upperRight
  | .y => .upperLeft

/-- Named physical objects and silk segments visible in image `681.png`. -/
inductive FigureFeature where
  | ceilingBeams
  | spider
  | junction
  | xUpperStrand
  | yUpperStrand
  | verticalSpiderStrand
  deriving DecidableEq, Fintype, Repr

/-- Literal labels printed in the supplied raster. -/
inductive FigureLabel where
  | xAxis
  | yAxis
  | tensionTx
  | tensionTy
  deriving DecidableEq, Fintype, Repr

/--
Typed qualitative content of the primary figure.  The bitmap supplies the
strand geometry and the `x`, `y`, `Tₓ`, and `Tᵧ` labels, but it contains no
numerical force readout.
-/
structure SpiderWebFigure where
  showsFeature : FigureFeature → Bool
  showsLabel : FigureLabel → Bool
  upperStrandDirection : SlopingAxis → FigureDirection
  loadStrandDirection : FigureDirection
  axesOriginateAtJunction : Bool
  tensionLabelsFollowUpperStrands : SlopingAxis → Bool
  upperStrandsMeetAtJunction : Bool
  verticalStrandJoinsJunctionToSpider : Bool
  containsNumericalForceReadout : Bool

/--
Independent physical quantities and geometry for the web junction.  In
particular, the `y`-strand tension and resultant are fields to be constrained
by the governing laws, not definitions made from the recorded answer.
-/
structure SpiderWebStaticsSetup where
  junctionDiagramCoordinate : DiagramVector
  axisOriginDiagramCoordinate : DiagramVector
  strandDirection : SlopingAxis → DiagramVector
  tensionApplicationDiagramCoordinate : SlopingAxis → DiagramVector
  spiderLoadApplicationDiagramCoordinate : DiagramVector
  resultantApplicationDiagramCoordinate : DiagramVector
  tensionForce : SlopingAxis → PlanarForceQuantity
  spiderLoadForce : PlanarForceQuantity
  resultantForce : PlanarForceQuantity
  figure : SpiderWebFigure

/-! ## Figure evidence, source data, and governing laws -/

/--
Literal evidence transcribed from the primary raster: two differently sloped
upper strands meet the vertical spider strand at the labelled axis origin.
-/
structure MatchesSuppliedSpiderWebFigure
    (setup : SpiderWebStaticsSetup) : Prop where
  everyFeatureShown : ∀ feature, setup.figure.showsFeature feature = true
  everyLiteralLabelShown : ∀ label, setup.figure.showsLabel label = true
  displayedUpperStrandDirections : ∀ axis,
    setup.figure.upperStrandDirection axis = expectedUpperStrandDirection axis
  spiderStrandPointsDownward :
    setup.figure.loadStrandDirection = .downward
  axisOriginIsJunction :
    setup.axisOriginDiagramCoordinate = setup.junctionDiagramCoordinate
  axesShownAtJunction : setup.figure.axesOriginateAtJunction = true
  tensionLabelsFollowStrands : ∀ axis,
    setup.figure.tensionLabelsFollowUpperStrands axis = true
  upperStrandsMeet : setup.figure.upperStrandsMeetAtJunction = true
  verticalStrandReachesSpider :
    setup.figure.verticalStrandJoinsJunctionToSpider = true
  noNumericalReadoutInRaster :
    setup.figure.containsNumericalForceReadout = false

/--
All three strand forces are concurrent at the junction, and the vertical
spider strand transmits a downward force to that junction.
-/
structure MatchesProblemScenario
    (setup : SpiderWebStaticsSetup) : Prop where
  eachTensionActsAtJunction : ∀ axis,
    setup.tensionApplicationDiagramCoordinate axis =
      setup.junctionDiagramCoordinate
  spiderLoadActsAtJunction :
    setup.spiderLoadApplicationDiagramCoordinate =
      setup.junctionDiagramCoordinate
  resultantLocatedAtJunction :
    setup.resultantApplicationDiagramCoordinate =
      setup.junctionDiagramCoordinate
  spiderLoadPointsDownward :
    forceVectorInNewtons setup.spiderLoadForce =
      forceMagnitudeInNewtons setup.spiderLoadForce •
        downwardDiagramDirection

/--
The two numerical force magnitudes stated in the prose.  The downward load is
`0.150 N` and the supplied `x`-strand tension is `0.127 N`; no `Tᵧ` value or
answer label occurs in these data.
-/
structure MatchesProblemForceReadouts
    (setup : SpiderWebStaticsSetup) : Prop where
  spiderLoadMagnitudeNewtons :
    forceMagnitudeInNewtons setup.spiderLoadForce = 3 / 20
  xTensionMagnitudeNewtons :
    forceMagnitudeInNewtons (setup.tensionForce .x) = 127 / 1000

/-- The two diagram axes are unit directions along perpendicular silk strands. -/
structure HasPerpendicularSlopingStrandAxes
    (setup : SpiderWebStaticsSetup) : Prop where
  eachStrandDirectionIsUnit : ∀ axis, ‖setup.strandDirection axis‖ = 1
  strandDirectionsArePerpendicular :
    inner ℝ (setup.strandDirection .x) (setup.strandDirection .y) = 0

/--
Ideal silk tension pulls away from the junction along its strand.  This is a
general tension-direction law and does not prescribe either tension magnitude.
-/
structure ObeysIdealSilkTensionDirectionLaw
    (setup : SpiderWebStaticsSetup) : Prop where
  tensionActsAlongItsStrand : ∀ axis,
    forceVectorInNewtons (setup.tensionForce axis) =
      forceMagnitudeInNewtons (setup.tensionForce axis) •
        setup.strandDirection axis

/--
Vector superposition at the junction and static equilibrium.  The spider load
is the force transmitted downward through the third strand.  Neither field
states the requested `Tᵧ` magnitude or a displayed answer.
-/
structure ObeysJunctionForceBalance
    (setup : SpiderWebStaticsSetup) : Prop where
  resultantIsVectorSum :
    forceVectorInNewtons setup.resultantForce =
      forceVectorInNewtons (setup.tensionForce .x) +
        forceVectorInNewtons (setup.tensionForce .y) +
          forceVectorInNewtons setup.spiderLoadForce
  junctionIsInStaticEquilibrium :
    forceVectorInNewtons setup.resultantForce = 0

/-! ## Pythagorean consequence and multiple-choice target -/

/--
Perpendicular tension directions and zero resultant make the squared spider
load equal to the sum of the squared upper-strand tensions.
-/
lemma perpendicularTensionMagnitudeRelation
    (setup : SpiderWebStaticsSetup)
    (_axes : HasPerpendicularSlopingStrandAxes setup)
    (_tensionLaw : ObeysIdealSilkTensionDirectionLaw setup)
    (_balance : ObeysJunctionForceBalance setup) :
    forceMagnitudeInNewtons setup.spiderLoadForce ^ 2 =
      forceMagnitudeInNewtons (setup.tensionForce .x) ^ 2 +
        forceMagnitudeInNewtons (setup.tensionForce .y) ^ 2 := by
  have hsum :
      forceVectorInNewtons (setup.tensionForce .x) +
          forceVectorInNewtons (setup.tensionForce .y) +
        forceVectorInNewtons setup.spiderLoadForce = 0 := by
    rw [← _balance.resultantIsVectorSum,
      _balance.junctionIsInStaticEquilibrium]
  have hload :
      forceVectorInNewtons setup.spiderLoadForce =
        -(forceVectorInNewtons (setup.tensionForce .x) +
          forceVectorInNewtons (setup.tensionForce .y)) :=
    eq_neg_of_add_eq_zero_right hsum
  have horth :
      inner ℝ (forceVectorInNewtons (setup.tensionForce .x))
          (forceVectorInNewtons (setup.tensionForce .y)) = 0 := by
    rw [_tensionLaw.tensionActsAlongItsStrand,
      _tensionLaw.tensionActsAlongItsStrand,
      real_inner_smul_left, real_inner_smul_right,
      _axes.strandDirectionsArePerpendicular]
    simp
  change ‖forceVectorInNewtons setup.spiderLoadForce‖ ^ 2 =
    ‖forceVectorInNewtons (setup.tensionForce .x)‖ ^ 2 +
      ‖forceVectorInNewtons (setup.tensionForce .y)‖ ^ 2
  rw [hload, norm_neg]
  simpa [pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (forceVectorInNewtons (setup.tensionForce .x))
      (forceVectorInNewtons (setup.tensionForce .y)) horth

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The `Tᵧ` magnitude in newtons printed beside each answer label. -/
def displayedAnswerTensionInNewtons : AnswerChoice → ℝ
  | .A => 39 / 1000
  | .B => 29 / 1000
  | .C => 78 / 1000
  | .D => 156 / 1000

/--
A choice is closest to an exact tension when no displayed magnitude has a
smaller absolute error.  This records multiple-choice selection without
identifying the exact physical value with a rounded or inconsistent display.
-/
def IsClosestDisplayedAnswer
    (choice : AnswerChoice) (exactTensionNewtons : ℝ) : Prop :=
  ∀ other,
    |exactTensionNewtons - displayedAnswerTensionInNewtons choice| ≤
      |exactTensionNewtons - displayedAnswerTensionInNewtons other|

/--
The perpendicular equilibrium data determine
`Tᵧ = √6371 / 1000 N ≈ 0.0798 N`.  Among the supplied alternatives, the
recorded choice `C`, displaying `0.078 N`, is the closest.

This formalizes `thm:physics:phyx_mini_0681:target`.  The closest-choice
conclusion is used because the printed `0.078 N` is not exactly the
Pythagorean consequence of the stated `0.150 N` and `0.127 N` readouts.
-/
theorem problem_phyx_mini_0681
    (setup : SpiderWebStaticsSetup)
    (_figure : MatchesSuppliedSpiderWebFigure setup)
    (_scenario : MatchesProblemScenario setup)
    (_readouts : MatchesProblemForceReadouts setup)
    (_axes : HasPerpendicularSlopingStrandAxes setup)
    (_tensionLaw : ObeysIdealSilkTensionDirectionLaw setup)
    (_balance : ObeysJunctionForceBalance setup) :
    forceMagnitudeInNewtons (setup.tensionForce .y) =
        Real.sqrt 6371 / 1000 ∧
      IsClosestDisplayedAnswer .C
        (forceMagnitudeInNewtons (setup.tensionForce .y)) := by
  have hy_nonneg :
      0 ≤ forceMagnitudeInNewtons (setup.tensionForce .y) := norm_nonneg _
  have hy_sq :
      forceMagnitudeInNewtons (setup.tensionForce .y) ^ 2 =
        6371 / 1000000 := by
    have h :=
      perpendicularTensionMagnitudeRelation setup _axes _tensionLaw _balance
    rw [_readouts.spiderLoadMagnitudeNewtons,
      _readouts.xTensionMagnitudeNewtons] at h
    norm_num at h ⊢
    linarith
  have hsqrt_sq : Real.sqrt (6371 : ℝ) ^ 2 = 6371 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (6371 : ℝ) :=
    Real.sqrt_nonneg _
  have hy :
      forceMagnitudeInNewtons (setup.tensionForce .y) =
        Real.sqrt 6371 / 1000 := by
    nlinarith
  refine ⟨hy, ?_⟩
  rw [hy]
  intro other
  have hsqrt_ge : 78 ≤ Real.sqrt (6371 : ℝ) := by
    nlinarith
  have hsqrt_le : Real.sqrt (6371 : ℝ) ≤ 117 := by
    nlinarith
  fin_cases other
  · simp only [displayedAnswerTensionInNewtons]
    rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith)]
    linarith
  · simp only [displayedAnswerTensionInNewtons]
    rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith)]
    linarith
  · exact le_rfl
  · simp only [displayedAnswerTensionInNewtons]
    rw [abs_of_nonneg (by nlinarith), abs_of_nonpos (by nlinarith)]
    linarith

end PhyXMiniProblems.ProblemPhyXMini0681
