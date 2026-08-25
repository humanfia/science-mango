import FamilyStickyGrounding.FamilyStickyHierarchyRadiusBranchingScalarClosureV1
import FamilyStickyGrounding.FamilyStickyHierarchySelectedSourceDirectTerminalWZConsumerV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open Set
open scoped NNReal

namespace FamilyStickyHierarchySelectedParentCollisionUnitScaleProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyJointRandomMotionEndToEndV1
open FamilyStickyHierarchyJointRandomMotionNumericThresholdV1
open FamilyStickyHierarchyJointRandomMotionPackingThresholdClosureV1
open FamilyStickyHierarchyCollisionTestGeometryProducerV1
open FamilyStickyHierarchyCollisionTestGeometryProducerV1.HierarchyCollisionTestSourceGeometry
open FamilyStickyHierarchyRadiusBranchingScalarClosureV1
open FamilyStickyHierarchyRadiusBranchingScalarClosureV1.ScalarCertificate
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyTerminalSourceChartBucketProducerV1
open FamilyStickyHierarchySelectedSourceNestedRestrictionV1
open FamilyStickyHierarchySelectedSourceJointOutputBindingV1
open FamilyStickyHierarchySelectedSourceDirectTerminalWZConsumerV1

noncomputable section

/-!
# Selected-parent collision unit-scale producer

The collision mean used by the joint selector depends only on a hierarchy
parent fibre and its two consecutive effective radii.  It is independent of
the auxiliary analytic test catalogue stored in `HierarchyRandomMotionGeometry`.
Consequently the hierarchy-only numerical bound from the EndToEnd module
produces a collision-unit certificate for every geometry over the hierarchy.

The recursively selected hierarchy preserves both effective radii and the
certified branching factor exactly.  We transport the numerical bound without
loss, apply the geometry-independent producer to `SelectedGeometry`, and then
close the scalar-certificate route using the unconditional explicit-grid
`20000` packing threshold.
-/

universe u

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]

/-! ## Geometry-independent collision scale -/

/-- The EndToEnd numerical hypothesis controls the collision mean for an
arbitrary random-motion geometry over the hierarchy.  No field of `G.tests`
is used: the layer's parent tubes are definitionally the hierarchy fibre. -/
theorem hierarchyParentCollisionUnitScale_of_jointNumerics
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (hunit : HierarchyJointCollisionUnitNumerics H) :
    HierarchyParentCollisionUnitScale H G := by
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

/-! ## Lossless restriction to the selected hierarchy -/

variable {H : MultiscaleTubeHierarchy depth nominalRadius Index}

/-- Selection changes index proofs but preserves every scalar in the joint
collision numerical inequality. -/
theorem selectedHierarchy_jointCollisionUnitNumerics
    (R : SelectedTerminalSourceChartBucketGeometry (H := H))
    (hunit : HierarchyJointCollisionUnitNumerics H) :
    HierarchyJointCollisionUnitNumerics (selectedHierarchy R) := by
  intro k
  simpa only [selectedHierarchy_effectiveRadius_eq,
    selectedHierarchy_step_branchingFactor] using hunit k

/-- The actual restricted test geometry therefore has the selected-parent
collision-unit scale with no cardinal or radius loss. -/
theorem selectedGeometry_parentCollisionUnitScale
    (G : HierarchyRandomMotionGeometry H)
    (R : SelectedTerminalSourceChartBucketGeometry (H := H))
    (hunit : HierarchyJointCollisionUnitNumerics H) :
    HierarchyParentCollisionUnitScale
      (selectedHierarchy R) (SelectedGeometry G R) := by
  exact hierarchyParentCollisionUnitScale_of_jointNumerics
    (selectedHierarchy R) (SelectedGeometry G R)
      (selectedHierarchy_jointCollisionUnitNumerics R hunit)

/-! ## Scalar-certificate and intrinsic-selector wrappers -/

/-- The most upstream unit-scale wrapper.  The scalar certificate builds the
source geometry; its `20000` estimate, together with the already proved
explicit-grid packing threshold, supplies the hierarchy numerics.  Selection
then transports those numerics definitionally. -/
theorem selectedGeometry_parentCollisionUnitScale_of_scalarCertificate
    (C : ScalarCertificate H)
    (R : SelectedTerminalSourceChartBucketGeometry (H := H)) :
    HierarchyParentCollisionUnitScale
      (selectedHierarchy R)
      (SelectedGeometry ((toSourceGeometry H C).toHierarchyRandomMotionGeometry H) R) := by
  have hunit : HierarchyJointCollisionUnitNumerics H :=
    hierarchyJointCollisionUnitNumerics_of_threshold H
      (toSourceGeometry H C)
      commonHundredNeighbourTwentyThousandThreshold
  exact selectedGeometry_parentCollisionUnitScale
    ((toSourceGeometry H C).toHierarchyRandomMotionGeometry H) R hunit

/-- The existing intrinsic selected-hierarchy selector now needs no numeric
or collision-scale premise.  Its WZ-separation input is the selector's
independent geometric premise and is inherited losslessly by the selected
hierarchy in the DirectTerminal consumer. -/
theorem exists_intrinsicSelectedCertificate_of_scalarCertificate
    (C : ScalarCertificate H)
    (R : SelectedTerminalSourceChartBucketGeometry (H := H))
    (W : HierarchyLevelWZSeparationData H) :
    Nonempty (HierarchyJointRandomMotionCertificate
      (selectedHierarchy R)
      (SelectedGeometry ((toSourceGeometry H C).toHierarchyRandomMotionGeometry H) R)) := by
  exact exists_selectedCertificate_without_hundred_small
    (S := R) W
      (selectedGeometry_parentCollisionUnitScale_of_scalarCertificate C R)

/-- Concrete intrinsic selector wrapper.  No old output, coupling field, or
additional numerical hypothesis is present. -/
noncomputable def selectIntrinsicSelectedCertificate_of_scalarCertificate
    (C : ScalarCertificate H)
    (R : SelectedTerminalSourceChartBucketGeometry (H := H))
    (W : HierarchyLevelWZSeparationData H) :
    HierarchyJointRandomMotionCertificate
      (selectedHierarchy R)
      (SelectedGeometry ((toSourceGeometry H C).toHierarchyRandomMotionGeometry H) R) :=
  Classical.choice
    (exists_intrinsicSelectedCertificate_of_scalarCertificate C R W)

#print axioms hierarchyParentCollisionUnitScale_of_jointNumerics
#print axioms selectedHierarchy_jointCollisionUnitNumerics
#print axioms selectedGeometry_parentCollisionUnitScale
#print axioms selectedGeometry_parentCollisionUnitScale_of_scalarCertificate
#print axioms exists_intrinsicSelectedCertificate_of_scalarCertificate
#print axioms selectIntrinsicSelectedCertificate_of_scalarCertificate

end
end FamilyStickyHierarchySelectedParentCollisionUnitScaleProducerV1
