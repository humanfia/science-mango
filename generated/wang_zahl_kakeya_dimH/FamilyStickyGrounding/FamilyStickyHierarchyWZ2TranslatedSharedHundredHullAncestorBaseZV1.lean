import FamilyStickyGrounding.FamilyStickyHierarchyWZ2TranslatedSharedHundredHullBaseZNormalizationV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyHierarchyWZ2TranslatedSharedHundredHullAncestorBaseZV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowScaleFloorV1
open FamilyStickyHierarchyWZ2TranslatedSharedHundredHullVolumeV1
open FamilyStickyCinematicL32PyzActualUnitBallVerticalCoefficientCeilingV1
open FamilyStickyHierarchyWZ2TranslatedSharedHundredHullBaseZNormalizationV1

noncomputable section

/-!
# Ancestor-ready source-height normalization

An arbitrary hierarchy-level source tube need not itself lie in the unit
ball.  It is enough that its carrier contain one finer tube which does.  The
base of that finer tube is a unit-ball point in the coarse carrier, so the
explicit tube-reach estimate bounds the coarse axis base.  This is the
geometric bridge needed once the still-missing selected-descendant index
transport has produced the finer tube.
-/

/-- If a source carrier contains the carrier of a unit-ball-normalized finer
tube, then its axis base height is at most `1 + tubeReach sourceRadius`. -/
theorem sourceBaseZAbs_le_one_add_tubeReach_of_unitBall_carrier_subset
    {sourceRadius unitRadius : NNReal}
    (source : Tube sourceRadius) (unitTube : Tube unitRadius)
    (hunit : unitTube.carrier ⊆ Metric.closedBall (0 : Space) 1)
    (hsubset : unitTube.carrier ⊆ source.carrier) :
    sourceBaseZAbs source ≤ 1 + tubeReach sourceRadius := by
  have hp : unitTube.axis.base ∈ source.carrier :=
    hsubset (unitTube.axis_subset_carrier unitTube.axis.base_mem_carrier)
  have hnear :=
    abs_tube_coord_sub_base_le_tubeReach source hp (2 : Fin 3)
  have hunitBase :=
    abs_axis_base_apply_le_one_of_carrier_subset_unitBall
      unitTube hunit (2 : Fin 3)
  change |source.axis.base 2| ≤
    (1 : Real) + (tubeReach sourceRadius : Real)
  calc
    |source.axis.base 2| =
        |(source.axis.base 2 - unitTube.axis.base 2) +
          unitTube.axis.base 2| := by ring_nf
    _ ≤ |source.axis.base 2 - unitTube.axis.base 2| +
        |unitTube.axis.base 2| := abs_add_le _ _
    _ = |unitTube.axis.base 2 - source.axis.base 2| +
        |unitTube.axis.base 2| := by rw [abs_sub_comm]
    _ ≤ (tubeReach sourceRadius : Real) + 1 :=
      add_le_add hnear hunitBase
    _ = (1 : Real) + (tubeReach sourceRadius : Real) := by ring

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type*}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}

/-- Once a unit-ball finer descendant is known to lie in the selected
candidate carrier, the existing hierarchy radius bounds give the absolute
selected-container height `9/2`. -/
theorem selectedHierarchyCollisionCell_sourceBaseZAbs_le_nine_halves_of_unitBall_descendant
    (C : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G C k p))
    (r : Fin
      (FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.repetitions
        G.toDependentSource k))
    {unitRadius : NNReal} (unitTube : Tube unitRadius)
    (hunit : unitTube.carrier ⊆ Metric.closedBall (0 : Space) 1)
    (hsubset : unitTube.carrier ⊆
      ((hierarchyCollisionGrid H G C k p).tube a.1.1).carrier) :
    sourceBaseZAbs
        (hundredTube
          (selectedHierarchyCollisionCell_sharedHundredSourceContainer
            H G C k p a r).container) ≤
      (9 / 2 : NNReal) := by
  calc
    sourceBaseZAbs
        (hundredTube
          (selectedHierarchyCollisionCell_sharedHundredSourceContainer
            H G C k p a r).container) ≤
        sourceBaseZAbs ((hierarchyCollisionGrid H G C k p).tube a.1.1) +
          2 * H.effectiveRadius (k.1 + 1) :=
      selectedHierarchyCollisionCell_sourceBaseZAbs_le_source_add_two_parentRadius
        C k p a r
    _ ≤ (1 + tubeReach (H.effectiveRadius k.1)) +
        2 * H.effectiveRadius (k.1 + 1) :=
      add_le_add
        (sourceBaseZAbs_le_one_add_tubeReach_of_unitBall_carrier_subset
          _ unitTube hunit hsubset) le_rfl
    _ ≤ (9 / 2 : NNReal) := by
      unfold tubeReach
      apply NNReal.coe_le_coe.mp
      push_cast
      have hchild : (H.effectiveRadius k.1 : Real) ≤ 1 / 2 := by
        have h := NNReal.coe_le_coe.mpr (G.childRadius_le_half k)
        norm_num at h
        exact h
      have hparent :
          (H.effectiveRadius (k.1 + 1) : Real) ≤ 1 := by
        exact_mod_cast G.parentRadius_le_one k
      nlinarith

/-- Ancestor-ready selected-hierarchy hull-volume endpoint.  Its only new
geometric input is the literal carrier containment of one unit-ball finer
tube in the selected source candidate. -/
theorem volume_selectedHierarchyCollisionCell_translatedSharedHundredHull_le_nineHalvesBaseZCap
    (C : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G C k p))
    (r : Fin
      (FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.repetitions
        G.toDependentSource k))
    {unitRadius : NNReal} (unitTube : Tube unitRadius)
    (hunit : unitTube.carrier ⊆ Metric.closedBall (0 : Space) 1)
    (hsubset : unitTube.carrier ⊆
      ((hierarchyCollisionGrid H G C k p).tube a.1.1).carrier)
    {siteCount : Nat} (hsiteCount : 0 < siteCount) (spacing : Real) :
    volume
        (translatedSharedHundredHullContainer
          (FamilyStickyWZ2ShearParameterPackingV1.shearReducedShift spacing
            (siteCount := siteCount))
          (selectedHierarchyCollisionCellFamily H G C k p a r)
          (selectedHierarchyCollisionCell_sharedHundredSourceContainer
            H G C k p a r) : Set Space) ≤
      shearGridTubeVolumeBoundAtBaseZCap
        (hundredRadius (H.effectiveRadius k.1)) spacing siteCount
          (9 / 2) := by
  apply (volume_translatedSharedHundredHullContainer_le_explicit
    hsiteCount spacing
      (selectedHierarchyCollisionCellFamily H G C k p a r)
      (selectedHierarchyCollisionCell_sharedHundredSourceContainer
        H G C k p a r)).trans
  apply shearGridTubeVolumeBound_le_atBaseZCap
  exact
    selectedHierarchyCollisionCell_sourceBaseZAbs_le_nine_halves_of_unitBall_descendant
      C k p a r unitTube hunit hsubset

#print axioms sourceBaseZAbs_le_one_add_tubeReach_of_unitBall_carrier_subset
#print axioms selectedHierarchyCollisionCell_sourceBaseZAbs_le_nine_halves_of_unitBall_descendant
#print axioms volume_selectedHierarchyCollisionCell_translatedSharedHundredHull_le_nineHalvesBaseZCap

end
end FamilyStickyHierarchyWZ2TranslatedSharedHundredHullAncestorBaseZV1
