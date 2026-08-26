import FamilyStickyGrounding.FamilyStickyHierarchySelectedLevelZeroDescendantProducerV1
import Family4GlobalExtremalUpstream
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyHierarchySelectedLevelZeroExtremalNormalizationProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyTerminalSourceChartBucketProducerV1
open FamilyStickyHierarchySelectedSourceNestedRestrictionV1
open FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowScaleFloorV1
open FamilyStickyHierarchyWZ2TranslatedSharedHundredHullVolumeV1
open FamilyStickyHierarchyWZ2TranslatedSharedHundredHullBaseZNormalizationV1
open FamilyStickyHierarchySelectedLevelZeroDescendantProducerV1

noncomputable section

universe u

/-!
# Extremal normalization of selected level-zero descendants

`SelectedTerminalSourceChartBucketGeometry` records only the selected index
set, its inclusion in the level-zero source, the fixed vertical chart, and
the graph-`c` bucket diameter.  Neither that structure nor
`MultiscaleTubeHierarchy` contains an absolute-position field, so unit-ball
containment cannot be recovered from those records alone.

The nearest genuine upstream datum is the defining extremal-family
certificate: `EpsilonExtremalTubeFamily.contained_in_unit_ball` places every
active source carrier in the unit ball.  This module transports that field
from the selected source family to the rebuilt selected hierarchy and then
feeds the level-zero descendant producer.  The collision-cell endpoints no
longer take a free `hunit` premise.
-/

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type u}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  (S : SelectedTerminalSourceChartBucketGeometry (H := H))

variable {Y : Shading S.family.bodyFamily}
  {parallelLoss : Nat} {epsilon sigma : Real}

/-- The selected extremal source's existing unit-ball field is exactly the
normalization required by the selected hierarchy at level zero. -/
theorem selectedLevelZeroUnitBallNormalized_of_extremal
    (E : EpsilonExtremalTubeFamily S.family Y Finset.univ
      parallelLoss epsilon sigma) :
    SelectedLevelZeroUnitBallNormalized S := by
  apply selectedLevelZeroUnitBallNormalized_of_original S
  intro i hi
  let j : {i // i ∈ S.selected} := ⟨i, hi⟩
  have hj := E.contained_in_unit_ball j (Finset.mem_univ j)
  simpa only [SelectedTerminalSourceChartBucketGeometry.family_tubes, j]
    using hj

/-- Every actual selected collision candidate receives its normalized
level-zero descendant directly from the extremal source certificate. -/
theorem exists_unitBall_selectedLevelZero_descendant_of_extremal
    (E : EpsilonExtremalTubeFamily S.family Y Finset.univ
      parallelLoss epsilon sigma)
    {G : HierarchyRandomMotionGeometry (selectedHierarchy S)}
    (C : HierarchyJointRandomMotionCertificate (selectedHierarchy S) G)
    (k : Fin depth) (p : SelectedHierarchyIndex S (k.1 + 1))
    (a : ModelCandidate
      (hierarchyCollisionGrid (selectedHierarchy S) G C k p)) :
    ∃ i : SelectedHierarchyIndex S 0,
      (((selectedHierarchy S).effectiveFamily 0).tubes i).carrier ⊆
          Metric.closedBall (0 : Space) 1 ∧
        (((selectedHierarchy S).effectiveFamily 0).tubes i).carrier ⊆
          ((hierarchyCollisionGrid
            (selectedHierarchy S) G C k p).tube a.1.1).carrier := by
  exact
    exists_unitBall_selectedLevelZero_descendant_of_collisionCandidate
      S C (selectedLevelZeroUnitBallNormalized_of_extremal S E) k p a

/-- The selected collision source-height cap with no caller-supplied
unit-ball premise. -/
theorem selectedHierarchyCollisionCell_sourceBaseZAbs_le_nine_halves_of_extremal
    (E : EpsilonExtremalTubeFamily S.family Y Finset.univ
      parallelLoss epsilon sigma)
    {G : HierarchyRandomMotionGeometry (selectedHierarchy S)}
    (C : HierarchyJointRandomMotionCertificate (selectedHierarchy S) G)
    (k : Fin depth) (p : SelectedHierarchyIndex S (k.1 + 1))
    (a : ModelCandidate
      (hierarchyCollisionGrid (selectedHierarchy S) G C k p))
    (r : Fin
      (FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.repetitions
        G.toDependentSource k)) :
    sourceBaseZAbs
        (hundredTube
          (selectedHierarchyCollisionCell_sharedHundredSourceContainer
            (selectedHierarchy S) G C k p a r).container) ≤
      (9 / 2 : NNReal) := by
  exact
    selectedHierarchyCollisionCell_sourceBaseZAbs_le_nine_halves
      S C (selectedLevelZeroUnitBallNormalized_of_extremal S E) k p a r

/-- End-to-end explicit hull-volume bound whose only normalization input is
the actual selected extremal-family certificate. -/
theorem volume_selectedHierarchyCollisionCell_translatedSharedHundredHull_le_nineHalves_of_extremal
    (E : EpsilonExtremalTubeFamily S.family Y Finset.univ
      parallelLoss epsilon sigma)
    {G : HierarchyRandomMotionGeometry (selectedHierarchy S)}
    (C : HierarchyJointRandomMotionCertificate (selectedHierarchy S) G)
    (k : Fin depth) (p : SelectedHierarchyIndex S (k.1 + 1))
    (a : ModelCandidate
      (hierarchyCollisionGrid (selectedHierarchy S) G C k p))
    (r : Fin
      (FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.repetitions
        G.toDependentSource k))
    {siteCount : Nat} (hsiteCount : 0 < siteCount) (spacing : Real) :
    volume
        (translatedSharedHundredHullContainer
          (FamilyStickyWZ2ShearParameterPackingV1.shearReducedShift spacing
            (siteCount := siteCount))
          (selectedHierarchyCollisionCellFamily
            (selectedHierarchy S) G C k p a r)
          (selectedHierarchyCollisionCell_sharedHundredSourceContainer
            (selectedHierarchy S) G C k p a r) : Set Space) ≤
      shearGridTubeVolumeBoundAtBaseZCap
        (hundredRadius ((selectedHierarchy S).effectiveRadius k.1))
          spacing siteCount (9 / 2) := by
  exact
    volume_selectedHierarchyCollisionCell_translatedSharedHundredHull_le_nineHalves
      S C (selectedLevelZeroUnitBallNormalized_of_extremal S E)
        k p a r hsiteCount spacing

#print axioms selectedLevelZeroUnitBallNormalized_of_extremal
#print axioms exists_unitBall_selectedLevelZero_descendant_of_extremal
#print axioms selectedHierarchyCollisionCell_sourceBaseZAbs_le_nine_halves_of_extremal
#print axioms volume_selectedHierarchyCollisionCell_translatedSharedHundredHull_le_nineHalves_of_extremal

end
end FamilyStickyHierarchySelectedLevelZeroExtremalNormalizationProducerV1
