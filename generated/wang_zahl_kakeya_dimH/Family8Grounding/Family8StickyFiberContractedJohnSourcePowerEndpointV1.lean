import Family8Grounding.Family8StickyFiberContractedJohnSourceDensityEnvelopeV1
import Family8Grounding.Family8StickyFiberContractedJohnSourcePowerEnvelopeV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyFiberContractedJohnSourcePowerEndpointV1

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
open Family8StickyFiberContractedJohnSourceDensityEnvelopeV1
open Family8StickyFiberContractedJohnSourcePowerEnvelopeV4
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Source-power endpoint for the contracted-John first factor

The two uniform power envelopes are applied on the actual normalized proxy
scale.  Thus the selected Frostman endpoint no longer asks for either the
fresh-greedy loss or the unit-ball base scalar: only two explicit power
comparisons involving the literal source density and source fibre cardinality
remain.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- One datum-independent scale threshold suffices for both the source loss
and the complete source base scalar. -/
def contractedJohnSourcePowerEndpointThreshold (a : Real) : NNReal :=
  min (contractedJohnSourceClosedLossThreshold a)
    (contractedJohnSourceBaseThreshold a)

theorem contractedJohnSourcePowerEndpointThreshold_pos (a : Real) :
    0 < contractedJohnSourcePowerEndpointThreshold a := by
  exact lt_min
    (contractedJohnSourceClosedLossThreshold_pos a)
    (contractedJohnSourceBaseThreshold_pos a)

/-- Source Katz--Tao power control, one retained-density power comparison,
and one fibre-cardinality power comparison produce the genuine selected
Frostman endpoint.  Both constant-loss budgets are constructed internally. -/
theorem exists_stickyFiberContractedJohn_global_average_le_sourcePower_frostmanRHS
    {beta epsilon eta p a : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho) (k : {k // k ∈ S.activeCoarse})
    {C : ENNReal} (hKT : IsKatzTao C fine.bodyFamily)
    (hp : 0 < p) (ha : 0 < a)
    (hdelta0 : contractedJohnProxyRadius delta rho / 8 <= delta0)
    (hsmall : contractedJohnProxyRadius delta rho / 8 <=
      contractedJohnSourcePowerEndpointThreshold a)
    (hCpower : C <=
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^ (-p)))
    (hsourceDensityPower :
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^ eta) <=
        ((stickyFiberSourceShading S Y k.1).shadingDensity / 93312 / 128) /
          (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-(p + a))))
    (hbasePower :
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          (-(2 * p + a))) <=
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
  let scale : NNReal := contractedJohnProxyRadius delta rho / 8
  have hproxyPos : 0 < contractedJohnProxyRadius delta rho :=
    stickyFiberContractedJohnProxyDatum_delta_pos hdelta hrho
  have hscalePos : 0 < scale := by
    dsimp only [scale]
    positivity
  have hproxyHalf : contractedJohnProxyRadius delta rho <= (2 : NNReal)⁻¹ :=
    stickyFiberContractedJohnProxyDatum_delta_le_half hdeltaRho hrho
  have hscaleOne : scale <= 1 := by
    dsimp only [scale]
    calc
      contractedJohnProxyRadius delta rho / 8 <= (2 : NNReal)⁻¹ / 8 := by
        gcongr
      _ <= 1 := by
        rw [← NNReal.coe_le_coe]
        norm_num
  have hsmallClosed : scale <= contractedJohnSourceClosedLossThreshold a :=
    hsmall.trans (min_le_left _ _)
  have hsmallBase : scale <= contractedJohnSourceBaseThreshold a :=
    hsmall.trans (min_le_right _ _)
  have hCscale : C <= (scale : ENNReal) ^ (-p) := by
    simpa only [scale] using hCpower
  have hloss : stickyFiberContractedJohnSourceClosedLoss C <=
      (scale : ENNReal) ^ (-(p + a)) :=
    stickyFiberContractedJohnSourceClosedLoss_le_negativePower
      hscalePos hscaleOne hp ha hsmallClosed hCscale
  have hbase :
      stickyFiberContractedJohnSourceClosedLoss C *
          ((128 * (93312 * C)) * volume (unitBallBody : Set Space)) <=
        (scale : ENNReal) ^ (-eta) *
          ((Fintype.card {i // i ∈ S.fiber k.1} : ENNReal) *
            ((scale : ENNReal) ^ 2 / 2)) := by
    apply (stickyFiberContractedJohnSourceBase_le_negativePower
      hscalePos hscaleOne hp ha hsmallBase hCscale).trans
    simpa only [scale] using hbasePower
  have hdensity :
      (scale : ENNReal) ^ eta <=
        stickyFiberContractedJohnRetainedSourceDensity C
          (stickyFiberSourceShading S Y k.1).shadingDensity := by
    apply (show (scale : ENNReal) ^ eta <=
        ((stickyFiberSourceShading S Y k.1).shadingDensity / 93312 / 128) /
          (scale : ENNReal) ^ (-(p + a)) by
      simpa only [scale] using hsourceDensityPower).trans
    unfold stickyFiberContractedJohnRetainedSourceDensity
    exact ENNReal.div_le_div_left hloss _
  have hscaleTop : (scale : ENNReal) ^ (-p) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.coe_ne_zero.mpr hscalePos.ne') ENNReal.coe_ne_top
  have hCfinite : C ≠ ∞ := ne_top_of_le_ne_top hscaleTop hCscale
  exact
    exists_stickyFiberContractedJohn_global_average_le_sourceDensityEnvelope_frostmanRHS
      hF S Y hdelta hdeltaHalf hrho hrhoOne hdeltaRho k hCfinite hKT
        hdelta0 (by simpa only [scale] using hdensity)
        (by simpa only [scale] using hbase)

#print axioms contractedJohnSourcePowerEndpointThreshold
#print axioms contractedJohnSourcePowerEndpointThreshold_pos
#print axioms
  exists_stickyFiberContractedJohn_global_average_le_sourcePower_frostmanRHS

end
end Family8StickyFiberContractedJohnSourcePowerEndpointV1
