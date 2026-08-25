import FamilyStickyGrounding.FamilyStickyWZ2AmbientShearLocalCountV1
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace FamilyStickyWZ2AmbientShearContainedMassV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2ReducedParameterClusterWindowV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyWZ2AmbientCinematicTranslationVolumeV1
open FamilyStickyWZ2AmbientShearWindowBridgeV1
open FamilyStickyWZ2AmbientShearLocalCountV1

noncomputable section

/-!
# From local ambient shear counts to contained mass

The ambient shear window modules bound the number of product-indexed tube
bodies contained in a convex test.  Here that cardinality estimate is turned
into an `ENNReal` contained-mass estimate using the actual tube-volume bound
and volume preservation of the ambient cinematic translation.

This is a card-to-mass normalization bridge.  It deliberately stops before a
uniform Katz--Tao assertion: obtaining one still requires an internally
derived comparison between the explicit local count cap times `delta^2` and
the volume of the arbitrary convex test.
-/

/-- The explicitly filtered shear-product indices are exactly the standard
contained indices of the corresponding translated convex family. -/
theorem containedShearProductIndices_eq_containedIndices
    {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
    {delta : NNReal} (spacing : Real) {siteCount : Nat}
    (fine : UniformTubeFamily delta kappa) (K : ConvexBody Space) :
    containedShearProductIndices spacing (siteCount := siteCount) fine K =
      containedIndices
        (indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes)) K := by
  classical
  rfl

/-- Every contained translated tube has the same volume as its source tube,
so the contained mass is at most the contained-index count times the uniform
upper volume cap. -/
theorem containedMass_indexedShear_le_card_mul_tubeVolumeCap
    {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
    {delta : NNReal} (spacing : Real) {siteCount : Nat}
    (fine : UniformTubeFamily delta kappa) (K : ConvexBody Space)
    (hdelta : delta <= (2 : NNReal)⁻¹) :
    containedMass
        (indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes)) K <=
      ((containedShearProductIndices
          spacing (siteCount := siteCount) fine K).card : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) := by
  classical
  unfold containedMass
  rw [← containedShearProductIndices_eq_containedIndices
    spacing fine K]
  calc
    (∑ ji ∈ containedShearProductIndices
        spacing (siteCount := siteCount) fine K,
        volume
          (indexedTranslatedBodyFamily
            (shearReducedShift spacing (siteCount := siteCount))
            (tubeBodyFamily fine.tubes) ji : Set Space)) <=
        ∑ _ji ∈ containedShearProductIndices
          spacing (siteCount := siteCount) fine K,
          8 * (delta : ENNReal) ^ 2 := by
      apply Finset.sum_le_sum
      intro ji _hji
      rw [coe_indexedTranslatedBodyFamily,
        volume_ambientCinematicTranslation_image]
      exact (fine.tubes ji.2).volume_le_eight_mul_sq_of_le_half hdelta
    _ = ((containedShearProductIndices
          spacing (siteCount := siteCount) fine K).card : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) := by
      simp [nsmul_eq_mul]

/-- Combining the genuine ambient window count with the actual tube-volume
bound gives a fully internal local contained-mass cap. -/
theorem containedMass_indexedShear_le_local_sourceBudget_mul_tubeVolumeCap
    {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
    {delta : NNReal}
    {spacing : Real} {siteCount : Nat}
    (fine : UniformTubeFamily delta kappa)
    (K : ConvexBody Space) (center radius baseD rho : Real)
    (hdelta : delta <= (2 : NNReal)⁻¹)
    (hspacing : 0 < spacing) (hradius : 0 <= radius) (hrho : 0 <= rho)
    (hwindow : CoordinateOneWindow K center radius)
    (hvertical : forall i,
      (1 / 2 : Real) <= |(fine.tubes i).axis.direction 2|)
    (hcluster : forall i, |tubeGraphD (fine.tubes i) - baseD| <= rho)
    (sourceBudget : Nat)
    (hsource : forall q,
      (parameterWindowIndices
        (fun i => tubeShearReducedParameter (fine.tubes i))
        q (4 * radius)).card <= sourceBudget) :
    containedMass
        (indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes)) K <=
      ((min siteCount (shearShiftHitBudget spacing (4 * radius + rho)) *
          sourceBudget : Nat) : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) := by
  calc
    containedMass
        (indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes)) K <=
      ((containedShearProductIndices
          spacing (siteCount := siteCount) fine K).card : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) :=
      containedMass_indexedShear_le_card_mul_tubeVolumeCap
        spacing fine K hdelta
    _ <= ((min siteCount
          (shearShiftHitBudget spacing (4 * radius + rho)) *
          sourceBudget : Nat) : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) := by
      gcongr
      exact_mod_cast
        card_containedShearProductIndices_le_local_sourceBudget
          fine K center radius baseD rho hspacing hradius hrho
          hwindow hvertical hcluster sourceBudget hsource

#print axioms containedShearProductIndices_eq_containedIndices
#print axioms containedMass_indexedShear_le_card_mul_tubeVolumeCap
#print axioms containedMass_indexedShear_le_local_sourceBudget_mul_tubeVolumeCap

end
end FamilyStickyWZ2AmbientShearContainedMassV1
