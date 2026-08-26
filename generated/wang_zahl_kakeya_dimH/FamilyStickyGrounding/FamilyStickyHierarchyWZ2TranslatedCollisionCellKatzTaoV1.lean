import FamilyStickyGrounding.FamilyStickyHierarchyWZ2FixedGridConstantEndpointV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyHierarchyWZ2TranslatedCollisionCellKatzTaoV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1
open FamilyStickyWZ2SharedHundredSourceConstantEndpointV1
open FamilyStickyHierarchyWZ2FixedGridConstantEndpointV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Unconditional Katz--Tao endpoint for a translated hierarchy collision cell

The fixed-grid collision-cell endpoint controls the contained mass of the
whole product-indexed translated family whenever the test body contains one
of its members.  For an arbitrary convex test body there are exactly two
cases.  If `containedIndices` is empty, its contained mass is zero.  Otherwise
one contained product index supplies the endpoint's distinguished copy and
source index.  Thus the local endpoint upgrades to the literal global
`IsKatzTao` predicate without a Katz--Tao callback or a union-volume premise.
-/

/-- A contained-member endpoint for the full family suffices for Katz--Tao:
the only missing test bodies are those with empty `containedIndices`, where
the contained mass vanishes definitionally. -/
theorem isKatzTao_of_containedMember_endpoint
    {iota : Type*} [Fintype iota]
    (coefficient : ENNReal) (family : ConvexFamily iota)
    (hendpoint : forall (K : ConvexBody Space) (i : iota),
      (family i : Set Space) <= (K : Set Space) ->
        containedMass family K <=
          coefficient * volume (K : Set Space)) :
    IsKatzTao coefficient family := by
  classical
  intro K
  unfold IsKatzTaoAt
  by_cases hcontained : (containedIndices family K).Nonempty
  · obtain ⟨i, hi⟩ := hcontained
    exact hendpoint K i ((mem_containedIndices family K i).1 hi)
  · have hempty : containedIndices family K = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hcontained
    unfold containedMass
    rw [hempty]
    simp

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  {spacing : Real} {siteCount gridConstant : Nat}

/-- The complete product-indexed family of all fixed-shear translated copies
of one selected hierarchy collision cell is Katz--Tao with the certified
fixed-grid coefficient.  All geometric inputs are the produced hypotheses of
the collision-cell endpoint; no Katz--Tao or union lower bound is assumed. -/
theorem selectedHierarchyCollisionCell_fullTranslatedFamily_isKatzTao
    (grid : FixedShearCopyGridCertificate siteCount gridConstant)
    (joint : HierarchyJointRandomMotionCertificate H G)
    (wz : HierarchyLevelWZSeparationData H)
    (k : Fin depth) (p : Index (k.1 + 1))
    (hp : p ∈ (G.toDependentSource.layer k).activeParents)
    (a : ModelCandidate (hierarchyCollisionGrid H G joint k p))
    (r : Fin (repetitions G.toDependentSource k))
    (baseD rho : Real) (hspacing : 0 < spacing) (hrho : 0 <= rho)
    (source : Finset
      (SelectedHierarchyCollisionCellIndex H G joint k p a r))
    (hselected :
      (Finset.univ : Finset
        (SelectedHierarchyCollisionCellIndex H G joint k p a r)) <=
      fixedVerticalChartIndices
        (selectedHierarchyCollisionCellFamily H G joint k p a r) source)
    (hcluster : forall l,
      |tubeGraphD
          ((selectedHierarchyCollisionCellFamily H G joint k p a r).tubes l) -
        baseD| <= rho) :
    IsKatzTao
      (16 *
        ((gridConstant * commonHundredNeighbourPackingConstant : Nat) :
          ENNReal))
      (indexedTranslatedBodyFamily
        (shearReducedShift spacing (siteCount := siteCount))
        (tubeBodyFamily
          (selectedHierarchyCollisionCellFamily H G joint k p a r).tubes)) := by
  apply isKatzTao_of_containedMember_endpoint
  intro K qi hcontained
  obtain ⟨_side, _cert, _hside, _hlong, hmass⟩ :=
    exists_selectedHierarchyCollisionCell_distortedJohnCertificate_and_containedMass_le_fixedGridConstant_mul_WZConstant
      grid joint wz k p hp a r K qi.1 qi.2 hcontained baseD rho hspacing
      hrho source hselected hcluster
  exact hmass

#print axioms isKatzTao_of_containedMember_endpoint
#print axioms selectedHierarchyCollisionCell_fullTranslatedFamily_isKatzTao

end
end FamilyStickyHierarchyWZ2TranslatedCollisionCellKatzTaoV1
