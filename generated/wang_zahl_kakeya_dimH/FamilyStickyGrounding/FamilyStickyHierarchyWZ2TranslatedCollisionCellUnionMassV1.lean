import FamilyStickyGrounding.FamilyStickyHierarchyWZ2TranslatedCollisionCellKatzTaoV1
import FamilyStickyGrounding.FamilyStickyKatzTaoAtEveryScaleOverlapMultiplicityConsumerV1
import FamilyStickyGrounding.FamilyStickyWZ2TranslatedShadingUnionCopyLossV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyHierarchyWZ2TranslatedCollisionCellUnionMassV1

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
open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyWZ2TranslatedActualShadingInstantiationV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2TranslatedShadingUnionCopyLossV1
open FamilyStickyKatzTaoAtEveryScaleOverlapMultiplicityConsumerV1
open FamilyStickyKatzTaoAtEveryScaleOverlapMultiplicityConsumerV1.KatzTaoOverlapRowGeometry
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1
open FamilyStickyWZ2SharedHundredSourceConstantEndpointV1
open FamilyStickyHierarchyWZ2FixedGridConstantEndpointV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellKatzTaoV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# From translated collision-cell Katz--Tao to copy-averaged union mass

The unconditional collision-cell endpoint supplies Katz--Tao for the full
product-indexed family of translated copies.  The analytic overlap consumer
then controls the mass of that literal translated shading once its genuine
row geometry has been constructed.  Translation preserves each copy's mass,
so cancelling the positive finite copy count returns the estimate to the
source shading with the translated union divided by that count.

No mass bound, union lower bound, second-moment estimate, or average-
multiplicity estimate is assumed below.  The remaining input
`KatzTaoOverlapRowGeometry` consists only of a pairwise-overlap majorant, its
support in active contained bodies, convex row containers, and their volume
comparison.  Producing that incidence/containment geometry for a hierarchy
collision cell is therefore the precise residual geometric task.
-/

/-- The shaded union of the actual product-indexed translated shading is the
literal translated-carrier union used by the WZ2 copy-loss module. -/
@[simp]
theorem indexedTranslatedActualShading_shadedUnion_eq
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes)) :
    (indexedTranslatedActualShading shift fine Y).shadedUnion =
      indexedTranslatedActualShadingUnion shift fine Y := by
  rfl

/-- Katz--Tao plus honest overlap-row geometry for all translated copies
controls the source mass by the average volume of their literal union.  The
nonempty-copy hypothesis is exactly what permits cancellation of the copy
cardinality. -/
theorem source_shadingMass_le_katzTaoRowFactor_mul_copyAverage
    {tau kappa : Type*} {delta : NNReal}
    [Fintype tau] [Fintype kappa] [DecidableEq kappa]
    (htau : Nonempty tau)
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes))
    {C : ENNReal}
    (hKT : IsKatzTao C
      (indexedTranslatedBodyFamily shift (tubeBodyFamily fine.tubes)))
    (R : KatzTaoOverlapRowGeometry
      (indexedTranslatedActualShading shift fine Y)) :
    Y.shadingMass <=
      (C * R.scaleFactor) *
        (volume (indexedTranslatedActualShadingUnion shift fine Y) /
          (Fintype.card tau : ENNReal)) := by
  have htranslated := R.shadingMass_le_of_isKatzTao hKT
  rw [indexedTranslatedActualShading_shadingMass,
    indexedTranslatedActualShading_shadedUnion_eq] at htranslated
  have hcard0 : (Fintype.card tau : ENNReal) ≠ 0 := by
    exact_mod_cast
      (Fintype.card_pos_iff.mpr htau).ne'
  have hcardTop : (Fintype.card tau : ENNReal) ≠ ∞ :=
    ENNReal.coe_ne_top
  apply (ENNReal.mul_le_mul_iff_left hcard0 hcardTop).mp
  calc
    Y.shadingMass * (Fintype.card tau : ENNReal) =
        (Fintype.card tau : ENNReal) * Y.shadingMass := mul_comm _ _
    _ <= (C * R.scaleFactor) *
        volume (indexedTranslatedActualShadingUnion shift fine Y) :=
      htranslated
    _ = (C * R.scaleFactor) *
          ((volume (indexedTranslatedActualShadingUnion shift fine Y) /
              (Fintype.card tau : ENNReal)) *
            (Fintype.card tau : ENNReal)) := by
      rw [ENNReal.div_mul_cancel hcard0 hcardTop]
    _ = ((C * R.scaleFactor) *
          (volume (indexedTranslatedActualShadingUnion shift fine Y) /
            (Fintype.card tau : ENNReal))) *
        (Fintype.card tau : ENNReal) := by
      ac_rfl

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  {spacing : Real} {siteCount gridConstant : Nat}

/-- For a selected hierarchy collision cell, the fixed-grid certificate and
the collision/source hypotheses automatically supply the Katz--Tao input.
Thus its only downstream geometric premise is the literal translated
overlap-row geometry; the conclusion has the certified constant and divides
the actual translated union by the declared positive number of copies. -/
theorem selectedHierarchyCollisionCell_shadingMass_le_fixedGridKatzTao_mul_rowScale_mul_copyAverage
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
        baseD| <= rho)
    (hsiteCount : 0 < siteCount)
    (Y : Shading
      (tubeBodyFamily
        (selectedHierarchyCollisionCellFamily H G joint k p a r).tubes))
    (R : KatzTaoOverlapRowGeometry
      (indexedTranslatedActualShading
        (shearReducedShift spacing (siteCount := siteCount))
        (selectedHierarchyCollisionCellFamily H G joint k p a r) Y)) :
    Y.shadingMass <=
      ((16 *
          ((gridConstant * commonHundredNeighbourPackingConstant : Nat) :
            ENNReal)) * R.scaleFactor) *
        (volume
            (indexedTranslatedActualShadingUnion
              (shearReducedShift spacing (siteCount := siteCount))
              (selectedHierarchyCollisionCellFamily H G joint k p a r) Y) /
          (siteCount : ENNReal)) := by
  have hKT :=
    selectedHierarchyCollisionCell_fullTranslatedFamily_isKatzTao
      grid joint wz k p hp a r baseD rho hspacing hrho source hselected
        hcluster
  simpa using
    (source_shadingMass_le_katzTaoRowFactor_mul_copyAverage
      (htau := ⟨⟨0, hsiteCount⟩⟩)
      (shift := shearReducedShift spacing (siteCount := siteCount))
      (fine := selectedHierarchyCollisionCellFamily H G joint k p a r)
      (Y := Y) hKT R)

#print axioms indexedTranslatedActualShading_shadedUnion_eq
#print axioms source_shadingMass_le_katzTaoRowFactor_mul_copyAverage
#print axioms selectedHierarchyCollisionCell_shadingMass_le_fixedGridKatzTao_mul_rowScale_mul_copyAverage

end
end FamilyStickyHierarchyWZ2TranslatedCollisionCellUnionMassV1
