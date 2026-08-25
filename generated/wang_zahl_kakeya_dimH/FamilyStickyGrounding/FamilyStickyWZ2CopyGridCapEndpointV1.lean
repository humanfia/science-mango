import FamilyStickyGrounding.FamilyStickyWZ2SharedHundredSourceConstantEndpointV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyWZ2CopyGridCapEndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyRandomWZLineParameterGeometryV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2AmbientShearContainedMassV1
open FamilyStickyWZ2AmbientShearDistortedTubeAdapterV1
open FamilyStickyWZ2DistortedJohnRadiusNormalizationV1
open FamilyStickyWZ2SharedHundredSourceConstantEndpointV1

noncomputable section

/-!
# Removing the convex-test-dependent WZ2 copy ceiling

The previous endpoint retains the sharp local copy count
`min siteCount (Nat.ceil (...) + 1)`.  This is always at most the declared
finite copy-grid size.  Consequently the final Katz--Tao coefficient can be
made independent of the John radius, convex-test volume, shear parameter,
and source cluster radius: it is simply
`16 * siteCount * commonHundredNeighbourPackingConstant`.

The result is unconditional for a fixed finite grid.  Obtaining a fully
dimension-only constant now has the precise upstream requirement of bounding
`siteCount`; no convex-body-dependent ceiling remains in the conclusion.
-/

variable {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
  {delta : NNReal} {spacing : Real} {siteCount : Nat}

/-- The sharp local copy budget from the distorted-John endpoint is bounded
by the total declared copy-grid cardinality. -/
theorem localCopyBudget_mul_WZConstant_le_siteCount_mul_WZConstant
    (K : ConvexBody Space) (j : Fin siteCount) (rho : Real) :
    min siteCount
          (Nat.ceil
            ((2 *
              (4 * johnRadiusVolumeCap K delta
                (shearSiteD spacing j) + rho)) / spacing) + 1) *
        commonHundredNeighbourPackingConstant <=
      siteCount * commonHundredNeighbourPackingConstant := by
  exact Nat.mul_le_mul_right _ (Nat.min_le_left _ _)

/-- Fixed-source-constant WZ2 endpoint with every convex-test-dependent copy
ceiling removed from the output coefficient. -/
theorem exists_distortedJohnCertificate_and_containedMass_le_siteCount_mul_WZConstant
    (fine : UniformTubeFamily delta kappa) (K : ConvexBody Space)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (j : Fin siteCount) (i : kappa)
    (hcontained :
      ((indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes) (j, i) : ConvexBody Space) : Set Space) <=
        (K : Set Space))
    (baseD rho : Real) (hspacing : 0 < spacing) (hrho : 0 <= rho)
    (hpair : Set.Pairwise (Set.univ : Set kappa) fun a b =>
      WZEndpointParameterSeparated (fine.tubes a) (fine.tubes b))
    (shared : SharedHundredSourceContainer fine)
    (hvertical : forall l,
      (1 / 2 : Real) <= |(fine.tubes l).axis.direction 2|)
    (hcluster : forall l, |tubeGraphD (fine.tubes l) - baseD| <= rho) :
    ∃ side : Fin 3 -> NNReal,
      ∃ _cert : BoxDimensionsCertificate 288 side K,
        (forall l,
          2 * distortedTubeRadius delta (shearSiteD spacing j) <= side l) ∧
        (∃ l : Fin 3,
          distortedAxisLength (shearSiteD spacing j) <= 6 * side l) ∧
        containedMass
            (indexedTranslatedBodyFamily
              (shearReducedShift spacing (siteCount := siteCount))
              (tubeBodyFamily fine.tubes)) K <=
          (16 *
            ((siteCount * commonHundredNeighbourPackingConstant : Nat) :
              ENNReal)) *
            volume (K : Set Space) := by
  obtain ⟨side, cert, hside, hlong, hmass⟩ :=
    exists_distortedJohnCertificate_and_containedMass_le_WZConstant_mul_volume
      fine K hdelta hdeltaHalf j i hcontained baseD rho hspacing hrho
      hpair shared hvertical hcluster
  refine ⟨side, cert, hside, hlong, hmass.trans ?_⟩
  have hnat := localCopyBudget_mul_WZConstant_le_siteCount_mul_WZConstant
    (delta := delta) (spacing := spacing) K j rho
  have hcast :
      ((min siteCount
          (Nat.ceil
            ((2 *
              (4 * johnRadiusVolumeCap K delta
                (shearSiteD spacing j) + rho)) / spacing) + 1) *
          commonHundredNeighbourPackingConstant : Nat) : ENNReal) <=
        ((siteCount * commonHundredNeighbourPackingConstant : Nat) :
          ENNReal) := by
    exact_mod_cast hnat
  gcongr

/-- Literal fixed-chart version of the copy-grid-cardinality endpoint. -/
theorem exists_distortedJohnCertificate_and_containedMass_le_siteCount_mul_WZConstant_of_fixedVerticalChart
    (fine : UniformTubeFamily delta kappa) (K : ConvexBody Space)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (j : Fin siteCount) (i : kappa)
    (hcontained :
      ((indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes) (j, i) : ConvexBody Space) : Set Space) <=
        (K : Set Space))
    (baseD rho : Real) (hspacing : 0 < spacing) (hrho : 0 <= rho)
    (hpair : Set.Pairwise (Set.univ : Set kappa) fun a b =>
      WZEndpointParameterSeparated (fine.tubes a) (fine.tubes b))
    (shared : SharedHundredSourceContainer fine)
    (source : Finset kappa)
    (hselected : (Finset.univ : Finset kappa) <=
      fixedVerticalChartIndices fine source)
    (hcluster : forall l, |tubeGraphD (fine.tubes l) - baseD| <= rho) :
    ∃ side : Fin 3 -> NNReal,
      ∃ _cert : BoxDimensionsCertificate 288 side K,
        (forall l,
          2 * distortedTubeRadius delta (shearSiteD spacing j) <= side l) ∧
        (∃ l : Fin 3,
          distortedAxisLength (shearSiteD spacing j) <= 6 * side l) ∧
        containedMass
            (indexedTranslatedBodyFamily
              (shearReducedShift spacing (siteCount := siteCount))
              (tubeBodyFamily fine.tubes)) K <=
          (16 *
            ((siteCount * commonHundredNeighbourPackingConstant : Nat) :
              ENNReal)) *
            volume (K : Set Space) := by
  exact exists_distortedJohnCertificate_and_containedMass_le_siteCount_mul_WZConstant
    fine K hdelta hdeltaHalf j i hcontained baseD rho hspacing hrho hpair shared
      (vertical_half_of_univ_subset_fixedVerticalChart fine source hselected)
      hcluster

#print axioms localCopyBudget_mul_WZConstant_le_siteCount_mul_WZConstant
#print axioms exists_distortedJohnCertificate_and_containedMass_le_siteCount_mul_WZConstant
#print axioms exists_distortedJohnCertificate_and_containedMass_le_siteCount_mul_WZConstant_of_fixedVerticalChart

end
end FamilyStickyWZ2CopyGridCapEndpointV1
