import Family8Grounding.Family8AllFrostmanStickyPopularParentComponentEndpointV1
import Family8Grounding.Family8AllFrostmanStickyPopularFiberPowerV3

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8AllFrostmanStickyPopularAutomaticFiberEndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8AllFrostmanStickyPopularComponentPowerV2
open Family8AllFrostmanStickyPopularParentPowerV4
open Family8AllFrostmanStickyPopularParentComponentEndpointV1
open Family8AllFrostmanStickyPopularFiberPowerV3
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

/-!
# Popular-row all-Frostman endpoint with the fibre cap produced

The parent-count endpoint and the actual source-Katz--Tao fibre-cap producer
previously ended in separate files.  This module applies them to the same
literal scale cover.  Both the cardinal bound for every active fibre and its
small-power envelope are now constructed internally from `KatzTaoHypotheses`.

The remaining inputs are scalar scale comparisons and the final explicit
exponent budget; no fibre-cardinality or union-volume conclusion is supplied
as a premise.
-/

theorem allFrostman_unionLower_of_stickyPopularAutomaticFiber
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {eta gamma etaKT scaleLoss fiberAbsorbExponent scaleExponent
      katzTaoExponent parentAbsorbExponent factorAbsorbExponent : Real}
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hF : FrostmanHypotheses D eta)
    (cover : StickyMultiscaleCover D.family)
    {frostmanError katzTaoError : ENNReal}
    (hsticky : cover.IsStickyAtEveryScale frostmanError katzTaoError)
    (rho : NNReal) (hdeltaRho : delta <= rho) (hrhoOne : rho <= 1)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hactive :
      (cover.cover rho hdeltaRho hrhoOne).activeFine = Finset.univ)
    (hEtaKT : 0 < etaKT)
    (hKT : KatzTaoHypotheses D etaKT)
    (hscaleRatio :
      (rho : ENNReal) ^ 2 / ((delta : ENNReal) ^ 2 / 2) <=
        2 * (delta : ENNReal) ^ (-2 * scaleLoss))
    (hfiberAbsorb : 0 < fiberAbsorbExponent)
    (hfiberThreshold :
      delta <= ordinaryFiberNatCapSmallDeltaThreshold fiberAbsorbExponent)
    (hparentAbsorb : 0 < parentAbsorbExponent)
    (hparentThreshold :
      delta <= stickyPopularParentPowerThreshold parentAbsorbExponent)
    (hscaleLower :
      (delta : ENNReal) ^ scaleExponent <= (rho : ENNReal))
    (hKatzTaoPower : katzTaoError <=
      (delta : ENNReal) ^ (-katzTaoExponent))
    (hfactorAbsorb : 0 < factorAbsorbExponent)
    (hfactorThreshold :
      delta <= stickyPopularComponentPowerThreshold factorAbsorbExponent)
    (hexponent :
      4 * eta +
        (2 * ordinaryFiberPowerEnvelope scaleLoss etaKT fiberAbsorbExponent +
          (katzTaoExponent + 2 * scaleExponent + parentAbsorbExponent) +
          katzTaoExponent + factorAbsorbExponent) <= gamma / 2) :
    (delta : ENNReal) ^ (gamma / 2) <=
      volume D.shading.shadedUnion := by
  let M := katzTaoDoubledFiberNatCap delta rho
    ((delta : ENNReal) ^ (-etaKT))
  have hM :
      (forall k : {k // k ∈
          (cover.cover rho hdeltaRho hrhoOne).activeCoarse},
        ((activeIndexFactorization
          (cover.cover rho hdeltaRho hrhoOne)).fiber k).card <= M) /\
      (M : ENNReal) <= (delta : ENNReal) ^
        (-ordinaryFiberPowerEnvelope
          scaleLoss etaKT fiberAbsorbExponent) := by
    exact activeIndexFiber_card_and_power_le_of_katzTaoHypotheses
      D hD (cover.cover rho hdeltaRho hrhoOne)
        hdeltaRho hrhoOne hEtaKT hKT hscaleRatio
          hfiberAbsorb hfiberThreshold
  exact allFrostman_unionLower_of_stickyPopularParentAndComponentPowers
    D hD hF cover hsticky rho hdeltaRho hrhoOne hrhoHalf hactive
      M hM.1 hparentAbsorb hparentThreshold hscaleLower hM.2
        hKatzTaoPower hfactorAbsorb hfactorThreshold hexponent

#print axioms allFrostman_unionLower_of_stickyPopularAutomaticFiber

end

end Family8AllFrostmanStickyPopularAutomaticFiberEndpointV1
