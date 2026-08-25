import FamilyStickyGrounding.FamilyStickyHierarchyCollisionTestGeometryProducerV1
import FamilyStickyGrounding.FamilyStickyHierarchyJointRandomMotionCertificateV1

set_option autoImplicit false

open Set
open scoped NNReal

namespace FamilyStickyHierarchyJointRandomMotionEndToEndV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexGeometry
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyCollisionTestGeometryProducerV1
open FamilyStickyHierarchyCollisionTestGeometryProducerV1.HierarchyCollisionTestSourceGeometry
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

/-!
# End-to-end hierarchy joint random motion

The caller supplies the actual hierarchy, the minimal collision-test source
geometry, levelwise WZ endpoint separation, and one transparent collision
mean inequality.  The collision-test catalogue, its box sides and
certificates, all hierarchy layer data, analytic repetition counts, joint
tail parameter, random vectors, prefix loads, and collision loads are then
constructed internally.

In particular, no `HierarchyRandomMotionGeometry`, test family, side function,
load conclusion, probability estimate, or target certificate is an input.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]

/-- Collision expectation smallness stated only with hierarchy source data.
The certified branching factor replaces every actual parent-fibre card. -/
def HierarchyJointCollisionUnitNumerics
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) : Prop :=
  forall k : Fin depth,
    (297 * ((H.step k.1 k.2).combinatorics.branchingFactor : Real) *
        (200 * (H.effectiveRadius k.1 : Real)) *
        (200 * (H.effectiveRadius k.1 : Real))) /
      (H.effectiveRadius (k.1 + 1) : Real) ^ 2 <=
    (FamilyStickyRandomWZCommonNeighbourPackingV1.commonHundredNeighbourPackingConstant : Real)

variable (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (S : HierarchyCollisionTestSourceGeometry H)

include S
/-- The generated geometry satisfies the small-radius premise of the joint
selector directly from the source record. -/
theorem hierarchyJointHundredRadiusSmall :
    HierarchyJointHundredRadiusSmall H := by
  intro k
  exact S.hundredRadius_le_half k

/-- The hierarchy-only numerical condition implies the exact per-parent
collision-unit condition for the generated layer data. -/
theorem hierarchyParentCollisionUnitScale
    (hunit : HierarchyJointCollisionUnitNumerics H) :
    HierarchyParentCollisionUnitScale H
      (S.toHierarchyRandomMotionGeometry H) := by
  intro k p hp
  let C := (H.step k.1 k.2).combinatorics
  have hcardNat : (C.index.fiber p).card <= C.branchingFactor := by
    exact C.fiber_card_le_loss_mul_branching p hp
  have hcard : ((C.index.fiber p).card : Real) <=
      (C.branchingFactor : Real) := by
    exact_mod_cast hcardNat
  have hside0 :
      (Tube.frameBoxSides
          (FamilyStickyRandomModelTubeCollisionGridV1.hundredRadius
            (H.effectiveRadius k.1)) 0 : Real) =
        200 * (H.effectiveRadius k.1 : Real) := by
    norm_num [Tube.frameBoxSides,
      FamilyStickyRandomModelTubeCollisionGridV1.hundredRadius,
      NNReal.coe_mul]
    ring
  have hside1 :
      (Tube.frameBoxSides
          (FamilyStickyRandomModelTubeCollisionGridV1.hundredRadius
            (H.effectiveRadius k.1)) 1 : Real) =
        200 * (H.effectiveRadius k.1 : Real) := by
    norm_num [Tube.frameBoxSides,
      FamilyStickyRandomModelTubeCollisionGridV1.hundredRadius,
      NNReal.coe_mul]
    ring
  unfold parentCollisionMean
  change
    (297 * ((C.index.fiber p).card : Real) *
        (Tube.frameBoxSides
          (FamilyStickyRandomModelTubeCollisionGridV1.hundredRadius
            (H.effectiveRadius k.1)) 0 : Real) *
        (Tube.frameBoxSides
          (FamilyStickyRandomModelTubeCollisionGridV1.hundredRadius
            (H.effectiveRadius k.1)) 1 : Real)) /
      (H.effectiveRadius (k.1 + 1) : Real) ^ 2 <= _
  calc
    _ <=
        (297 * (C.branchingFactor : Real) *
            (200 * (H.effectiveRadius k.1 : Real)) *
            (200 * (H.effectiveRadius k.1 : Real))) /
          (H.effectiveRadius (k.1 + 1) : Real) ^ 2 := by
      rw [hside0, hside1]
      gcongr
    _ <= _ := hunit k

/-- End-to-end source theorem: construct the generated hierarchy geometry
and then invoke the faithful joint analytic/collision selector. -/
theorem exists_joint_certificate
    (W : HierarchyLevelWZSeparationData H)
    (hunit : HierarchyJointCollisionUnitNumerics H) :
    Nonempty
      (HierarchyJointRandomMotionCertificate H
        (S.toHierarchyRandomMotionGeometry H)) := by
  exact FamilyStickyHierarchyJointRandomMotionCertificateV1.exists_certificate
    H (S.toHierarchyRandomMotionGeometry H)
    (hierarchyJointHundredRadiusSmall H S) W
    (hierarchyParentCollisionUnitScale H S hunit)

#print axioms hierarchyJointHundredRadiusSmall
#print axioms hierarchyParentCollisionUnitScale
#print axioms exists_joint_certificate

end
end FamilyStickyHierarchyJointRandomMotionEndToEndV1
