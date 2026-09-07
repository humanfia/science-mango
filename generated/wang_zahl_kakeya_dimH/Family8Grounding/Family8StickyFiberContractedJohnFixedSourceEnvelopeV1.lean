import Family8Grounding.Family8StickyFiberContractedJohnGlobalFrostmanConnectorV1
import Family8Grounding.Family8ContractedJohnAffineJacobianLowerV3
import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV6
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyFiberContractedJohnFixedSourceEnvelopeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8ContractedJohnActualTubeProxyV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnProxyKatzTaoV2
open Family8StickyFiberContractedJohnGlobalNormalizedFreshV1
open Family8StickyFiberContractedJohnGlobalFrostmanConnectorV1
open Family8ContractedJohnAffineJacobianLowerV3
open Family8B2NormalizedConflictKatzTaoCapV6
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# A source-constant envelope for the contracted-John first factor

The geometric Jacobian estimate gives `Cproxy <= 93312*C`.  This file pushes
that bound through the fixed conflict ceiling and the Frostman connector.
Downstream callers only see the original global Katz--Tao constant `C`; the
chosen John witness, affine Jacobian, proxy constant, and natural ceiling no
longer occur in their scalar premises or conclusion.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Ceiling-free loss expressed solely in the original global KT constant. -/
def stickyFiberContractedJohnSourceClosedLoss (C : ENNReal) : ENNReal :=
  480000 * (128 * (93312 * C)) + 2

/-- The proxy ceiling-free loss is bounded by the source-only loss. -/
theorem stickyFiberContractedJohnProxyClosedLoss_le_sourceClosedLoss
    (S : StickyScaleCover fine rho) (hdelta : 0 < delta)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (k : {k // k ∈ S.activeCoarse}) (C : ENNReal) :
    480000 *
          (128 * stickyFiberContractedJohnProxyKatzTaoConstant
            S hrho hrhoOne k C) + 2 <=
      stickyFiberContractedJohnSourceClosedLoss C := by
  unfold stickyFiberContractedJohnSourceClosedLoss
  gcongr
  exact stickyFiberContractedJohnProxyKatzTaoConstant_le_fixed
    S hdelta hrho hrhoOne k C

/-- The literal natural greedy loss is also bounded by the source-only
ceiling-free loss. -/
theorem stickyFiberContractedJohnNatLoss_coe_le_sourceClosedLoss
    (S : StickyScaleCover fine rho) (hdelta : 0 < delta)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (k : {k // k ∈ S.activeCoarse}) {C : ENNReal}
    (hCfinite : C ≠ ∞) :
    ((Nat.ceil ((480000 *
          (128 * stickyFiberContractedJohnProxyKatzTaoConstant
            S hrho hrhoOne k C) : ENNReal).toReal) + 1 : Nat) : ENNReal) <=
      stickyFiberContractedJohnSourceClosedLoss C := by
  let Cproxy := stickyFiberContractedJohnProxyKatzTaoConstant
    S hrho hrhoOne k C
  have hCproxyfinite : Cproxy ≠ ∞ :=
    stickyFiberContractedJohnProxyKatzTaoConstant_ne_top
      S hrho hrhoOne hdelta k hCfinite
  have hscaledFinite : (128 : ENNReal) * Cproxy ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCproxyfinite
  calc
    ((Nat.ceil ((480000 * (128 * Cproxy) : ENNReal).toReal) + 1 : Nat) :
        ENNReal) <= 480000 * (128 * Cproxy) + 2 :=
      fixedKatzTaoClosedLoss_coe_le_add_two hscaledFinite
    _ <= stickyFiberContractedJohnSourceClosedLoss C :=
      stickyFiberContractedJohnProxyClosedLoss_le_sourceClosedLoss
        S hdelta hrho hrhoOne k C

/-- Source-only scalar budgets imply the original literal proxy/ceiling
budgets and hence the selected Frostman endpoint. -/
theorem exists_stickyFiberContractedJohn_global_average_le_sourceEnvelope_frostmanRHS
    {beta epsilon eta : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho) (k : {k // k ∈ S.activeCoarse})
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C fine.bodyFamily)
    (hdelta0 : contractedJohnProxyRadius delta rho / 8 <= delta0)
    (hdensityBudget :
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^ eta) <=
        (eighthNormalizedDatum
          (stickyFiberContractedJohnProxyDatum
            S Y hrho hrhoOne k)).shading.shadingDensity /
          stickyFiberContractedJohnSourceClosedLoss C)
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
  let Cproxy := stickyFiberContractedJohnProxyKatzTaoConstant
    S hrho hrhoOne k C
  let lossNat := Nat.ceil ((480000 * (128 * Cproxy) : ENNReal).toReal) + 1
  let sourceLoss := stickyFiberContractedJohnSourceClosedLoss C
  have hloss : (lossNat : ENNReal) <= sourceLoss := by
    simpa only [lossNat, Cproxy, sourceLoss] using
      (stickyFiberContractedJohnNatLoss_coe_le_sourceClosedLoss
        S hdelta hrho hrhoOne k hCfinite)
  have hCproxy : Cproxy <= 93312 * C := by
    exact stickyFiberContractedJohnProxyKatzTaoConstant_le_fixed
      S hdelta hrho hrhoOne k C
  have hdensityOriginal :
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^ eta) <=
        (eighthNormalizedDatum
          (stickyFiberContractedJohnProxyDatum
            S Y hrho hrhoOne k)).shading.shadingDensity /
          (lossNat : ENNReal) := by
    apply hdensityBudget.trans
    exact ENNReal.div_le_div_left hloss _
  have hbaseOriginal :
      (lossNat : ENNReal) * ((128 * Cproxy) *
          volume (unitBallBody : Set Space)) <=
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-eta)) *
          ((Fintype.card {i // i ∈ S.fiber k.1} : ENNReal) *
            (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
                2 / 2)) := by
    apply le_trans ?_ hbaseBudget
    gcongr
  obtain ⟨selected, hselected, havg⟩ :=
    exists_stickyFiberContractedJohn_global_average_le_frostmanRHS
      hF S Y hdelta hdeltaHalf hrho hrhoOne hdeltaRho k hCfinite hKT
        hdelta0
        (by simpa only [lossNat, Cproxy] using hdensityOriginal)
        (by simpa only [lossNat, Cproxy] using hbaseOriginal)
  refine ⟨selected, hselected, havg.trans ?_⟩
  gcongr

#print axioms stickyFiberContractedJohnProxyClosedLoss_le_sourceClosedLoss
#print axioms stickyFiberContractedJohnNatLoss_coe_le_sourceClosedLoss
#print axioms
  exists_stickyFiberContractedJohn_global_average_le_sourceEnvelope_frostmanRHS

end
end Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
