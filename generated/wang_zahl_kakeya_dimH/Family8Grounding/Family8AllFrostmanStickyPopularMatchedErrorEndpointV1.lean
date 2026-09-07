import Family8Grounding.Family8AllFrostmanStickyPopularAutomaticFiberEndpointV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8AllFrostmanStickyPopularMatchedErrorEndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8AllFrostmanStickyPopularComponentPowerV2
open Family8AllFrostmanStickyPopularParentPowerV4
open Family8AllFrostmanStickyPopularAutomaticFiberEndpointV1
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Popular-row all-Frostman endpoint at the source Katz--Tao error

When the Sticky cover carries the same literal Katz--Tao error
`delta ^ (-etaKT)` as `KatzTaoHypotheses D etaKT`, its error-power premise is
definitionally discharged.  Combined with the automatic fibre endpoint,
neither finite component cardinalities nor a separate Katz--Tao scalar bound
remain among the inputs.
-/

theorem allFrostman_unionLower_of_stickyPopularMatchedKatzTaoError
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {eta gamma etaKT scaleLoss fiberAbsorbExponent scaleExponent
      parentAbsorbExponent factorAbsorbExponent : Real}
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hF : FrostmanHypotheses D eta)
    (cover : StickyMultiscaleCover D.family)
    {frostmanError : ENNReal}
    (hsticky : cover.IsStickyAtEveryScale frostmanError
      ((delta : ENNReal) ^ (-etaKT)))
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
    (hfactorAbsorb : 0 < factorAbsorbExponent)
    (hfactorThreshold :
      delta <= stickyPopularComponentPowerThreshold factorAbsorbExponent)
    (hexponent :
      4 * eta +
        (2 * ordinaryFiberPowerEnvelope scaleLoss etaKT fiberAbsorbExponent +
          (etaKT + 2 * scaleExponent + parentAbsorbExponent) +
          etaKT + factorAbsorbExponent) <= gamma / 2) :
    (delta : ENNReal) ^ (gamma / 2) <=
      volume D.shading.shadedUnion := by
  exact allFrostman_unionLower_of_stickyPopularAutomaticFiber
    D hD hF cover hsticky rho hdeltaRho hrhoOne hrhoHalf hactive
      hEtaKT hKT hscaleRatio hfiberAbsorb hfiberThreshold
        hparentAbsorb hparentThreshold hscaleLower le_rfl
          hfactorAbsorb hfactorThreshold hexponent

#print axioms allFrostman_unionLower_of_stickyPopularMatchedKatzTaoError

end

end Family8AllFrostmanStickyPopularMatchedErrorEndpointV1
