import FamilyStickyGrounding.FamilyStickyHierarchyWZ2TranslatedSharedHundredHullVolumeV1
import FamilyStickyGrounding.FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1
import FamilyStickyCinematicL32PyzActualUnitBallVerticalCoefficientCeilingV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyHierarchyWZ2TranslatedSharedHundredHullBaseZNormalizationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowScaleFloorV1
open FamilyStickyWZ2SharedHundredSourceConstantEndpointV1
open FamilyStickyHierarchyWZ2TranslatedSharedHundredHullVolumeV1
open FamilyStickyCinematicL32PyzActualUnitBallVerticalCoefficientCeilingV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

/-!
# Honest normalization of the explicit WZ2 hull source height

The selected hierarchy collision container is obtained from one source tube
by two motion-ball translations, one forward and one backward.  The hierarchy
controls both vector norms by the next effective radius, but it contains no
absolute-position field for the unshifted tube.  Consequently its automatic
conclusion is the relative bound

`containerBaseZ <= sourceBaseZ + 2 * parentRadius`.

If the underlying source tube is additionally contained in the unit ball,
the existing coordinate lemma bounds its base height by one and the hierarchy
bound `parentRadius <= 1` gives the constant three.  The corresponding
height-capped hull-volume endpoint is proved below.  The final theorem shows
that the bare shared-container interface permits arbitrary absolute height,
so some source-position normalization is genuinely necessary.
-/

/-- Translating a tube by a vector of norm at most `bound` increases the
absolute vertical coordinate of its axis base by at most `bound`. -/
theorem sourceBaseZAbs_translateTube_le
    {radius : NNReal} (T : Tube radius) (v : Space) (bound : NNReal)
    (hv : ‖v‖ ≤ (bound : Real)) :
    sourceBaseZAbs (translateTube T v) ≤ sourceBaseZAbs T + bound := by
  have hv2 : |v 2| ≤ (bound : Real) := by
    have hcoord := (PiLp.norm_apply_le v (2 : Fin 3)).trans hv
    simpa only [Real.norm_eq_abs] using hcoord
  change |(v + T.axis.base) 2| ≤ |T.axis.base 2| + (bound : Real)
  rw [PiLp.add_apply]
  calc
    |v 2 + T.axis.base 2| ≤ |v 2| + |T.axis.base 2| := abs_add_le _ _
    _ ≤ (bound : Real) + |T.axis.base 2| := add_le_add hv2 le_rfl
    _ = |T.axis.base 2| + (bound : Real) := by ring

/-- Two motion vectors of the same radius cost at most twice that radius.
The outer `hundredTube` changes only the radius and leaves the axis fixed. -/
theorem sourceBaseZAbs_hundredTube_two_translates_le
    {radius : NNReal} (T : Tube radius) (v w : Space) (bound : NNReal)
    (hv : ‖v‖ ≤ (bound : Real)) (hw : ‖w‖ ≤ (bound : Real)) :
    sourceBaseZAbs
        (hundredTube (translateTube (translateTube T v) (-w))) ≤
      sourceBaseZAbs T + 2 * bound := by
  have hneg : ‖-w‖ ≤ (bound : Real) := by simpa using hw
  change sourceBaseZAbs (translateTube (translateTube T v) (-w)) ≤ _
  calc
    sourceBaseZAbs (translateTube (translateTube T v) (-w)) ≤
        sourceBaseZAbs (translateTube T v) + bound :=
      sourceBaseZAbs_translateTube_le _ _ _ hneg
    _ ≤ (sourceBaseZAbs T + bound) + bound :=
      add_le_add (sourceBaseZAbs_translateTube_le T v bound hv) le_rfl
    _ = sourceBaseZAbs T + 2 * bound := by
      simp [two_mul, add_assoc]

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type*}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}

/-- Exact relative height bound supplied by the hierarchy collision data.
No absolute position assumption is used. -/
theorem selectedHierarchyCollisionCell_sourceBaseZAbs_le_source_add_two_parentRadius
    (C : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G C k p))
    (r : Fin
      (FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.repetitions
        G.toDependentSource k)) :
    sourceBaseZAbs
        (hundredTube
          (selectedHierarchyCollisionCell_sharedHundredSourceContainer
            H G C k p a r).container) ≤
      sourceBaseZAbs ((hierarchyCollisionGrid H G C k p).tube a.1.1) +
        2 * H.effectiveRadius (k.1 + 1) := by
  let PG := hierarchyCollisionGrid H G C k p
  let g := (C.output.layerOutput k).omega r
  have ha : ‖PG.gridVector a.2‖ ≤
      (H.effectiveRadius (k.1 + 1) : Real) := by
    change ‖(a.2.1 : Space)‖ ≤
      (H.effectiveRadius (k.1 + 1) : Real)
    have haMem := (C.output.layerOutput k).certificate.centers_subset a.2.2
    simpa [Metric.mem_closedBall, dist_zero_right,
      HierarchyRandomMotionGeometry.toDependentSource] using haMem
  have hg : ‖PG.gridVector g‖ ≤
      (H.effectiveRadius (k.1 + 1) : Real) := by
    change ‖(g.1 : Space)‖ ≤
      (H.effectiveRadius (k.1 + 1) : Real)
    exact (C.output.layerOutput k).vector_norm_le r
  change sourceBaseZAbs
      (hundredTube
        (translateTube
          (translateTube (PG.tube a.1.1) (PG.gridVector a.2))
          (-(PG.gridVector g)))) ≤ _
  exact sourceBaseZAbs_hundredTube_two_translates_le
    (PG.tube a.1.1) (PG.gridVector a.2) (PG.gridVector g)
      (H.effectiveRadius (k.1 + 1)) ha hg

/-- Unit-ball containment of a source tube gives the missing absolute base
height normalization. -/
theorem sourceBaseZAbs_le_one_of_carrier_subset_unitBall
    {radius : NNReal} (T : Tube radius)
    (hunit : T.carrier ⊆ Metric.closedBall (0 : Space) 1) :
    sourceBaseZAbs T ≤ 1 := by
  change |T.axis.base 2| ≤ (1 : Real)
  exact abs_axis_base_apply_le_one_of_carrier_subset_unitBall T hunit 2

/-- Under a unit-ball assumption on the unshifted candidate tube, the actual
selected shared container has absolute source height at most three. -/
theorem selectedHierarchyCollisionCell_sourceBaseZAbs_le_three_of_source_unitBall
    (C : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G C k p))
    (r : Fin
      (FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.repetitions
        G.toDependentSource k))
    (hunit : ((hierarchyCollisionGrid H G C k p).tube a.1.1).carrier ⊆
      Metric.closedBall (0 : Space) 1) :
    sourceBaseZAbs
        (hundredTube
          (selectedHierarchyCollisionCell_sharedHundredSourceContainer
            H G C k p a r).container) ≤ 3 := by
  calc
    sourceBaseZAbs
        (hundredTube
          (selectedHierarchyCollisionCell_sharedHundredSourceContainer
            H G C k p a r).container) ≤
        sourceBaseZAbs ((hierarchyCollisionGrid H G C k p).tube a.1.1) +
          2 * H.effectiveRadius (k.1 + 1) :=
      selectedHierarchyCollisionCell_sourceBaseZAbs_le_source_add_two_parentRadius
        C k p a r
    _ ≤ 1 + 2 * 1 := by
      gcongr
      · exact sourceBaseZAbs_le_one_of_carrier_subset_unitBall _ hunit
      · exact G.parentRadius_le_one k
    _ = 3 := by norm_num

/-- The explicit shear-grid volume formula with an externally certified
upper bound for the source base height substituted into it. -/
def shearGridTubeVolumeBoundAtBaseZCap
    (radius : NNReal) (spacing : Real) (siteCount : Nat)
    (baseZCap : NNReal) : ENNReal :=
  8 * (tubeReach radius : ENNReal) ^ 2 *
    ((tubeReach radius + shearGridMagnitude spacing siteCount *
      (baseZCap + tubeReach radius) : NNReal) : ENNReal)

/-- Monotonic substitution of a genuine base-height bound into the exact
coordinate-box volume formula. -/
theorem shearGridTubeVolumeBound_le_atBaseZCap
    {radius : NNReal} (T : Tube radius)
    (spacing : Real) (siteCount : Nat) (baseZCap : NNReal)
    (hbase : sourceBaseZAbs T ≤ baseZCap) :
    shearGridTubeVolumeBound T spacing siteCount ≤
      shearGridTubeVolumeBoundAtBaseZCap
        radius spacing siteCount baseZCap := by
  unfold shearGridTubeVolumeBound shearGridTubeVolumeBoundAtBaseZCap
  gcongr

/-- A unit-ball-normalized common source gives a height-independent explicit
hull-volume bound.  The hundred-fold radius change does not move the axis. -/
theorem volume_translatedSharedHundredHullContainer_le_unitBallBaseZCap
    {kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    {siteCount : Nat} (hsiteCount : 0 < siteCount) (spacing : Real)
    (fine : UniformTubeFamily delta kappa)
    (shared : SharedHundredSourceContainer fine)
    (hunit : shared.container.carrier ⊆
      Metric.closedBall (0 : Space) 1) :
    volume
        (translatedSharedHundredHullContainer
          (FamilyStickyWZ2ShearParameterPackingV1.shearReducedShift spacing
            (siteCount := siteCount)) fine shared : Set Space) ≤
      shearGridTubeVolumeBoundAtBaseZCap
        (hundredRadius delta) spacing siteCount 1 := by
  apply (volume_translatedSharedHundredHullContainer_le_explicit
    hsiteCount spacing fine shared).trans
  apply shearGridTubeVolumeBound_le_atBaseZCap
  change sourceBaseZAbs shared.container ≤ 1
  exact sourceBaseZAbs_le_one_of_carrier_subset_unitBall _ hunit

/-- Selected-hierarchy hull-volume endpoint after adding only the missing
local source unit-ball normalization. -/
theorem volume_selectedHierarchyCollisionCell_translatedSharedHundredHull_le_threeBaseZCap
    (C : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G C k p))
    (r : Fin
      (FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.repetitions
        G.toDependentSource k))
    {siteCount : Nat} (hsiteCount : 0 < siteCount) (spacing : Real)
    (hunit : ((hierarchyCollisionGrid H G C k p).tube a.1.1).carrier ⊆
      Metric.closedBall (0 : Space) 1) :
    volume
        (translatedSharedHundredHullContainer
          (FamilyStickyWZ2ShearParameterPackingV1.shearReducedShift spacing
            (siteCount := siteCount))
          (selectedHierarchyCollisionCellFamily H G C k p a r)
          (selectedHierarchyCollisionCell_sharedHundredSourceContainer
            H G C k p a r) : Set Space) ≤
      shearGridTubeVolumeBoundAtBaseZCap
        (hundredRadius (H.effectiveRadius k.1)) spacing siteCount 3 := by
  apply (volume_translatedSharedHundredHullContainer_le_explicit
    hsiteCount spacing
      (selectedHierarchyCollisionCellFamily H G C k p a r)
      (selectedHierarchyCollisionCell_sharedHundredSourceContainer
        H G C k p a r)).trans
  apply shearGridTubeVolumeBound_le_atBaseZCap
  exact selectedHierarchyCollisionCell_sourceBaseZAbs_le_three_of_source_unitBall
    C k p a r hunit

/-- The bare shared-container interface permits arbitrary absolute source
height.  Translation preserves all carrier-in-hundred-container data, so no
uniform base-height constant follows from that interface alone. -/
theorem exists_sharedHundredSourceContainer_with_sourceBaseZAbs_gt
    {radius : NNReal} (T : Tube radius) (height : NNReal) :
    ∃ fine : UniformTubeFamily radius Unit,
      ∃ shared : SharedHundredSourceContainer fine,
        height < sourceBaseZAbs (hundredTube shared.container) := by
  let v : Space :=
    point3 0 0 ((height : Real) + 1 - T.axis.base 2)
  let U : Tube radius := translateTube T v
  let fine : UniformTubeFamily radius Unit :=
    { tubes := fun _ => U
      refinement := UniformRefinement.ofFinset Finset.univ }
  let shared : SharedHundredSourceContainer fine :=
    { container := U
      carrier_subset := fun _ => carrier_subset_hundredTube U }
  refine ⟨fine, shared, ?_⟩
  change (height : Real) < |(v + T.axis.base) 2|
  have hcoord : (v + T.axis.base) 2 = (height : Real) + 1 := by
    simp [v, point3]
  rw [hcoord, abs_of_nonneg (by positivity)]
  linarith

#print axioms sourceBaseZAbs_translateTube_le
#print axioms sourceBaseZAbs_hundredTube_two_translates_le
#print axioms selectedHierarchyCollisionCell_sourceBaseZAbs_le_source_add_two_parentRadius
#print axioms selectedHierarchyCollisionCell_sourceBaseZAbs_le_three_of_source_unitBall
#print axioms shearGridTubeVolumeBound_le_atBaseZCap
#print axioms volume_translatedSharedHundredHullContainer_le_unitBallBaseZCap
#print axioms volume_selectedHierarchyCollisionCell_translatedSharedHundredHull_le_threeBaseZCap
#print axioms exists_sharedHundredSourceContainer_with_sourceBaseZAbs_gt

end
end FamilyStickyHierarchyWZ2TranslatedSharedHundredHullBaseZNormalizationV1
