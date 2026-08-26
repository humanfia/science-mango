import FamilyStickyGrounding.FamilyStickyWZ2ProjectedShadedUnionMassV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyWZ2ProjectedShadedUnionPopularFloorConsumerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedActualShadingInstantiationV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2TranslatedShadingUnionCopyLossV1
open FamilyStickyWZ2SharedHundredSourceConstantEndpointV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowScaleFloorV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellPopularFloorUnionV1
open FamilyStickyWZ2ProjectedShadedUnionMassV1

noncomputable section

/-!
# The projected full-shading union feeds the generic WZ2 endpoint

The projected slice is the literal projection of the full shaded union and
the active set is the full finite index family.  Hence the only mass input is
the transparent scalar lower bound on `Y.shadingMass.toReal`.
-/

/-- The full projected shaded union discharges the restricted-integral
premise of the generic shared-`100T` endpoint without a callback. -/
theorem projectedShadedUnion_halfMass_le_sharedHundredHull_originalUnion
    {tau kappa : Type*} [Fintype tau] [Fintype kappa]
    {delta : NNReal} [DecidableEq kappa]
    (htau : Nonempty tau)
    (shift : tau → ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (shared : SharedHundredSourceContainer fine)
    (Y : Shading (tubeBodyFamily fine.tubes))
    (f : Real → Real) (hf : Measurable f)
    (alpha cap : Real) (halphaPos : 0 < alpha) (hcapPos : 0 < cap)
    (hmass : alpha * Fintype.card kappa * cap ≤ Y.shadingMass.toReal)
    {C : ENNReal}
    (hKT : IsKatzTao C
      (indexedTranslatedBodyFamily shift (tubeBodyFamily fine.tubes))) :
    ENNReal.ofReal (alpha / 2 * Fintype.card kappa * cap) ≤
      (C *
        (volume (translatedSharedHundredHullContainer shift fine shared :
          Set Space) / popularCarrierFloor alpha cap)) *
        (volume (indexedTranslatedActualShadingUnion shift fine Y) /
          (Fintype.card tau : ENNReal)) := by
  simpa only [Finset.card_univ] using
    (projectedSlice_halfMass_le_sharedHundredHull_originalUnion
      htau shift fine shared Y (Finset.univ : Finset kappa) f hf
      (twistedProjection f '' Y.shadedUnion) alpha cap halphaPos hcapPos
      (projectedShadedUnion_massLower Y f hf alpha cap hmass) hKT)

#print axioms projectedShadedUnion_halfMass_le_sharedHundredHull_originalUnion

end

end FamilyStickyWZ2ProjectedShadedUnionPopularFloorConsumerV1
