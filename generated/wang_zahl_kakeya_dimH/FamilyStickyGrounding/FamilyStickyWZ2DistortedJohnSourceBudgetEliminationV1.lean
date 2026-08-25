import FamilyStickyGrounding.FamilyStickyWZ2DistortedJohnRadiusNormalizationV1
import FamilyStickyGrounding.FamilyStickyWZ2JohnBoxSourceBudgetProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyWZ2DistortedJohnSourceBudgetEliminationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2ReducedParameterClusterWindowV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyWZ2AmbientShearWindowBridgeV1
open FamilyStickyWZ2AmbientShearLocalCountV1
open FamilyStickyWZ2AmbientShearContainedMassV1
open FamilyStickyWZ2JohnBoxVolumeNormalizationV1
open FamilyStickyWZ2AmbientShearDistortedTubeAdapterV1
open FamilyStickyWZ2DistortedJohnRadiusNormalizationV1
open FamilyStickyWZ2JohnBoxSourceBudgetProducerV1

noncomputable section

/-!
# Internal source budgets for the distorted WZ2 John endpoint

The volume-normalized John-radius cap makes both the copy-grid window and
the source window independent of the chosen certificate.  Consequently the
finite source cardinality, or the sharper separated source-shear packing
bound, can be inserted internally.  Neither endpoint asks the caller for a
window-cardinality function.
-/

variable {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
  {delta : NNReal} {spacing : Real} {siteCount : Nat}

/-- No source separation is needed: the whole finite source family is an
honest uniform budget for every explicit cap window. -/
theorem exists_distortedJohnCertificate_and_containedMass_le_cardBudget_mul_volume
    (fine : UniformTubeFamily delta kappa) (K : ConvexBody Space)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (j : Fin siteCount) (i : kappa)
    (hcontained :
      ((indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes) (j, i) : ConvexBody Space) : Set Space) <=
        (K : Set Space))
    (baseD rho : Real) (hspacing : 0 < spacing) (hrho : 0 <= rho)
    (hvertical : forall l,
      (1 / 2 : Real) <= |(fine.tubes l).axis.direction 2|)
    (hcluster : forall l, |tubeGraphD (fine.tubes l) - baseD| <= rho) :
    ∃ side : Fin 3 -> NNReal,
      ∃ _cert : BoxDimensionsCertificate 288 side K,
        (∀ l,
          2 * distortedTubeRadius delta (shearSiteD spacing j) <= side l) ∧
        (∃ l : Fin 3,
          distortedAxisLength (shearSiteD spacing j) <= 6 * side l) ∧
        containedMass
            (indexedTranslatedBodyFamily
              (shearReducedShift spacing (siteCount := siteCount))
              (tubeBodyFamily fine.tubes)) K <=
          (16 *
            ((min siteCount
              (Nat.ceil
                ((2 *
                  (4 * johnRadiusVolumeCap K delta
                    (shearSiteD spacing j) + rho)) / spacing) + 1) *
                Fintype.card kappa : Nat) : ENNReal)) *
            volume (K : Set Space) := by
  obtain ⟨side, cert, hside, hlong, _hwindow, _hRcap, hendpoint⟩ :=
    exists_distortedJohnWindow_and_containedMass_le_expandedBudget_mul_volume
      fine K hdelta hdeltaHalf j i hcontained baseD rho hspacing hrho
      hvertical hcluster
  refine ⟨side, cert, hside, hlong, ?_⟩
  exact hendpoint (Fintype.card kappa)
    (fun q => card_tubeShearReducedParameter_window_le_card fine q
      (4 * johnRadiusVolumeCap K delta (shearSiteD spacing j)))

/-- Under projected source-shear separation, the internal source factor is
the minimum of the actual source cardinality, the cap-window packing count,
and the whole-cluster packing count.  All three grid budgets are displayed
as literal natural ceilings. -/
theorem exists_distortedJohnCertificate_and_containedMass_le_separatedBudget_mul_volume
    (fine : UniformTubeFamily delta kappa) (K : ConvexBody Space)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (j : Fin siteCount) (i : kappa)
    (hcontained :
      ((indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes) (j, i) : ConvexBody Space) : Set Space) <=
        (K : Set Space))
    (baseD rho sourceSpacing : Real)
    (hspacing : 0 < spacing) (hrho : 0 <= rho)
    (hsourceSpacing : 0 < sourceSpacing)
    (hvertical : forall l,
      (1 / 2 : Real) <= |(fine.tubes l).axis.direction 2|)
    (hcluster : forall l, |tubeGraphD (fine.tubes l) - baseD| <= rho)
    (hsourceSeparated : SourceShearSeparated fine sourceSpacing) :
    ∃ side : Fin 3 -> NNReal,
      ∃ _cert : BoxDimensionsCertificate 288 side K,
        (∀ l,
          2 * distortedTubeRadius delta (shearSiteD spacing j) <= side l) ∧
        (∃ l : Fin 3,
          distortedAxisLength (shearSiteD spacing j) <= 6 * side l) ∧
        containedMass
            (indexedTranslatedBodyFamily
              (shearReducedShift spacing (siteCount := siteCount))
              (tubeBodyFamily fine.tubes)) K <=
          (16 *
            ((min siteCount
                (Nat.ceil
                  ((2 *
                    (4 * johnRadiusVolumeCap K delta
                      (shearSiteD spacing j) + rho)) / spacing) + 1) *
              min (Fintype.card kappa)
                (min
                  (Nat.ceil
                    ((2 *
                      (4 * johnRadiusVolumeCap K delta
                        (shearSiteD spacing j))) / sourceSpacing) + 1)
                  (Nat.ceil ((2 * rho) / sourceSpacing) + 1)) : Nat) :
                ENNReal)) *
            volume (K : Set Space) := by
  obtain ⟨side, cert, hside, hlong, _hwindow, _hRcap, hendpoint⟩ :=
    exists_distortedJohnWindow_and_containedMass_le_expandedBudget_mul_volume
      fine K hdelta hdeltaHalf j i hcontained baseD rho hspacing hrho
      hvertical hcluster
  refine ⟨side, cert, hside, hlong, ?_⟩
  let cap : Real :=
    johnRadiusVolumeCap K delta (shearSiteD spacing j)
  let sourceBudget : Nat :=
    min (Fintype.card kappa)
      (min
        (Nat.ceil ((2 * (4 * cap)) / sourceSpacing) + 1)
        (Nat.ceil ((2 * rho) / sourceSpacing) + 1))
  have hsource : forall q,
      (parameterWindowIndices
        (fun l => tubeShearReducedParameter (fine.tubes l)) q
        (4 * cap)).card <= sourceBudget := by
    intro q
    simpa [cap, sourceBudget, shearShiftHitBudget] using
      card_tubeShearReducedParameter_window_le_min_hitBudget
        fine baseD hsourceSpacing hrho
        (mul_nonneg (by norm_num) (johnRadiusVolumeCap_nonneg
          K delta (shearSiteD spacing j)))
        hcluster hsourceSeparated q
  have hresult := hendpoint sourceBudget hsource
  simpa only [cap, sourceBudget] using hresult

#print axioms exists_distortedJohnCertificate_and_containedMass_le_cardBudget_mul_volume
#print axioms exists_distortedJohnCertificate_and_containedMass_le_separatedBudget_mul_volume

end
end FamilyStickyWZ2DistortedJohnSourceBudgetEliminationV1
