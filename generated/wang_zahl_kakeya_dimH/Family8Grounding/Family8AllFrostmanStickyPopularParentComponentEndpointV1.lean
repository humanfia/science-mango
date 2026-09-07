import Family8Grounding.Family8AllFrostmanStickyPopularParentPowerV4

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8AllFrostmanStickyPopularParentComponentEndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8AllFrostmanStickyPopularComponentPowerV2
open Family8AllFrostmanStickyPopularParentPowerV4
open Family8StickyParentPopularCanonicalUnionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

/-!
# Popular-row all-Frostman endpoint with the parent count produced

The active-parent power premise of the componentwise endpoint is absent.
It is supplied by the actual Sticky Katz--Tao estimate from
`Family8AllFrostmanStickyPopularParentPowerV4`.  The two remaining genuine
component inputs are the fine-fibre cardinal power and the source
Katz--Tao-error power.
-/

theorem allFrostman_unionLower_of_stickyPopularParentAndComponentPowers
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {eta gamma fiberExponent scaleExponent katzTaoExponent
      parentAbsorbExponent factorAbsorbExponent : Real}
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hF : FrostmanHypotheses D eta)
    (cover : StickyMultiscaleCover D.family)
    {frostmanError katzTaoError : ENNReal}
    (hsticky : cover.IsStickyAtEveryScale frostmanError katzTaoError)
    (rho : NNReal) (hdeltaRho : delta <= rho) (hrhoOne : rho <= 1)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hactive :
      (cover.cover rho hdeltaRho hrhoOne).activeFine = Finset.univ)
    (fiberCap : Nat)
    (hfiberCard : forall k :
      {k // k ∈ (cover.cover rho hdeltaRho hrhoOne).activeCoarse},
      ((activeIndexFactorization
        (cover.cover rho hdeltaRho hrhoOne)).fiber k).card <= fiberCap)
    (hparentAbsorb : 0 < parentAbsorbExponent)
    (hparentThreshold :
      delta <= stickyPopularParentPowerThreshold parentAbsorbExponent)
    (hscale :
      (delta : ENNReal) ^ scaleExponent <= (rho : ENNReal))
    (hfiberPower : (fiberCap : ENNReal) <=
      (delta : ENNReal) ^ (-fiberExponent))
    (hKatzTaoPower : katzTaoError <=
      (delta : ENNReal) ^ (-katzTaoExponent))
    (hfactorAbsorb : 0 < factorAbsorbExponent)
    (hfactorThreshold :
      delta <= stickyPopularComponentPowerThreshold factorAbsorbExponent)
    (hexponent :
      4 * eta +
        (2 * fiberExponent +
          (katzTaoExponent + 2 * scaleExponent + parentAbsorbExponent) +
          katzTaoExponent + factorAbsorbExponent) <= gamma / 2) :
    (delta : ENNReal) ^ (gamma / 2) <=
      volume D.shading.shadedUnion := by
  apply allFrostman_unionLower_of_stickyPopularComponentPowers
    D hD hF cover hsticky rho hdeltaRho hrhoOne hactive fiberCap
      hfiberCard hfactorAbsorb hfactorThreshold hfiberPower
  · exact activeCoarse_card_le_delta_negativePower_of_stickyAtEveryScale
      D hD cover hsticky rho hdeltaRho hrhoOne hrhoHalf hparentAbsorb
        hparentThreshold hscale hKatzTaoPower
  · exact hKatzTaoPower
  · exact hexponent

#print axioms
  allFrostman_unionLower_of_stickyPopularParentAndComponentPowers

end

end Family8AllFrostmanStickyPopularParentComponentEndpointV1
