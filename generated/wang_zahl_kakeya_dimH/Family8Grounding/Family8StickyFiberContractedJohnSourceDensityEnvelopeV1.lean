import Family8Grounding.Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
import Family8Grounding.Family8StickyFiberContractedJohnDensityTransportV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyFiberContractedJohnSourceDensityEnvelopeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8ContractedJohnActualTubeProxyV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickyFiberContractedJohnDensityTransportV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Source-density envelope for the contracted-John first factor

The genuine density transport removes the final normalized-proxy density
premise from the source-constant Frostman connector.  Both remaining scalar
budgets now mention only the original source fibre, source Katz--Tao constant,
cardinality, and explicit scales.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The source density retained after John proxy volume transport, eighth
normalization, and the fresh-greedy source loss.  The divisions are kept in
the order in which the three genuine estimates are applied, so the statement
does not need any nonzero/finite side conditions for `ENNReal` division. -/
def stickyFiberContractedJohnRetainedSourceDensity
    (C density : ENNReal) : ENNReal :=
  density / 93312 / 128 / stickyFiberContractedJohnSourceClosedLoss C

/-- A literal source-fibre density budget and the source-only base budget
produce the genuine selected Frostman endpoint. -/
theorem exists_stickyFiberContractedJohn_global_average_le_sourceDensityEnvelope_frostmanRHS
    {beta epsilon eta : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho) (k : {k // k ∈ S.activeCoarse})
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C fine.bodyFamily)
    (hdelta0 : contractedJohnProxyRadius delta rho / 8 <= delta0)
    (hsourceDensityBudget :
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^ eta) <=
        stickyFiberContractedJohnRetainedSourceDensity C
          (stickyFiberSourceShading S Y k.1).shadingDensity)
    (hbaseBudget :
      stickyFiberContractedJohnSourceClosedLoss C *
          ((128 * (93312 * C)) * volume (unitBallBody : Set Space)) <=
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-eta)) *
          ((Fintype.card {i // i ∈ S.fiber k.1} : ENNReal) *
            (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
                2 / 2))) :
    exists selected : Finset {i // i ∈ S.fiber k.1},
      selected.Nonempty ∧
      (stickyFiberSourceShading S Y k.1).averageMultiplicity <=
        stickyFiberContractedJohnSourceClosedLoss C *
          frostmanMultiplicityRHS
            (contractedJohnProxyRadius delta rho / 8)
            (restrictActualTubeDatum
              (eighthNormalizedDatum
                (stickyFiberContractedJohnProxyDatum
                  S Y hrho hrhoOne k)) selected).actualFamilyVolume
            epsilon beta := by
  have htransport :=
    stickyFiberSource_shadingDensity_div_93312_div_128_le_normalizedProxy
      S Y hdelta hdeltaHalf hrho hrhoOne hdeltaRho k
  have hdensityBudget :
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^ eta) <=
        (eighthNormalizedDatum
          (stickyFiberContractedJohnProxyDatum
            S Y hrho hrhoOne k)).shading.shadingDensity /
          stickyFiberContractedJohnSourceClosedLoss C := by
    apply hsourceDensityBudget.trans
    unfold stickyFiberContractedJohnRetainedSourceDensity
    exact ENNReal.div_le_div_right htransport
      (stickyFiberContractedJohnSourceClosedLoss C)
  exact
    exists_stickyFiberContractedJohn_global_average_le_sourceEnvelope_frostmanRHS
      hF S Y hdelta hdeltaHalf hrho hrhoOne hdeltaRho k hCfinite hKT
        hdelta0 hdensityBudget hbaseBudget

#print axioms stickyFiberContractedJohnRetainedSourceDensity
#print axioms
  exists_stickyFiberContractedJohn_global_average_le_sourceDensityEnvelope_frostmanRHS

end
end Family8StickyFiberContractedJohnSourceDensityEnvelopeV1
