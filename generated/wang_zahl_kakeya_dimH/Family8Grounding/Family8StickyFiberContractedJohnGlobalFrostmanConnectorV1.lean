import Family8Grounding.Family8StickyFiberContractedJohnGlobalNormalizedFreshV1
import Family8Grounding.Family8FiniteRandomRigidMotionB2FrostmanConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyFiberContractedJohnGlobalFrostmanConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FrostmanConnectorV1
open Family8ContractedJohnActualTubeProxyV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnProxyKatzTaoV2
open Family8StickyFiberContractedJohnNormalizedFreshV1
open Family8StickyFiberContractedJohnGlobalNormalizedFreshV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Global Katz--Tao contracted-John fibre to the Frostman endpoint

This composition eliminates the proxy Katz--Tao and conflict inputs and then
applies the deterministic normalized Frostman connector.  Exactly two honest
scalar premises remain: density after the fixed greedy loss and the ambient
unit-ball base normalization.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The selected normalized proxy reaches the Frostman multiplicity RHS from
global source Katz--Tao control and the two literal scalar budgets. -/
theorem exists_stickyFiberContractedJohn_global_average_le_frostmanRHS
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
          (Nat.ceil ((480000 *
            (128 * stickyFiberContractedJohnProxyKatzTaoConstant
              S hrho hrhoOne k C) : ENNReal).toReal) + 1 : Nat))
    (hbaseBudget :
      (Nat.ceil ((480000 *
          (128 * stickyFiberContractedJohnProxyKatzTaoConstant
            S hrho hrhoOne k C) : ENNReal).toReal) + 1 : Nat) *
          ((128 * stickyFiberContractedJohnProxyKatzTaoConstant
            S hrho hrhoOne k C) *
              volume (unitBallBody : Set Space)) <=
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-eta)) *
          ((Fintype.card {i // i ∈ S.fiber k.1} : ENNReal) *
            (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
                2 / 2))) :
    exists selected : Finset {i // i ∈ S.fiber k.1},
      selected.Nonempty ∧
      (stickyFiberSourceShading S Y k.1).averageMultiplicity <=
        (Nat.ceil ((480000 *
          (128 * stickyFiberContractedJohnProxyKatzTaoConstant
            S hrho hrhoOne k C) : ENNReal).toReal) + 1 : Nat) *
          frostmanMultiplicityRHS
            (contractedJohnProxyRadius delta rho / 8)
            (restrictActualTubeDatum
              (eighthNormalizedDatum
                (stickyFiberContractedJohnProxyDatum
                  S Y hrho hrhoOne k)) selected).actualFamilyVolume
            epsilon beta := by
  let Cproxy := stickyFiberContractedJohnProxyKatzTaoConstant
    S hrho hrhoOne k C
  let D := stickyFiberContractedJohnProxyDatum S Y hrho hrhoOne k
  let threshold := Nat.ceil ((480000 * (128 * Cproxy) : ENNReal).toReal)
  let loss := threshold + 1
  have hCproxyfinite : Cproxy ≠ ∞ :=
    stickyFiberContractedJohnProxyKatzTaoConstant_ne_top
      S hrho hrhoOne hdelta k hCfinite
  have hproxyKT : IsKatzTao Cproxy D.family.bodyFamily := by
    change IsKatzTao Cproxy
      (stickyFiberContractedJohnProxyFamily
        S hrho hrhoOne k).bodyFamily
    exact stickyFiberContractedJohnProxyFamily_isKatzTao_of_global
      S Y hrho hrhoOne hdelta hdeltaHalf hdeltaRho k hKT
  obtain ⟨selected, hselected, hadmissible, hcard, hmass,
      hselectedKT, _havg⟩ :=
    exists_stickyFiberContractedJohn_normalizedFresh_of_isKatzTao
      S Y hdelta hrho hrhoOne hdeltaRho k hCproxyfinite hproxyKT
  let _ : NeZero loss :=
    ⟨Nat.ne_of_gt (by dsimp only [loss]; omega)⟩
  have hcard' : (Fintype.card {i // i ∈ S.fiber k.1} : ENNReal) <=
      (loss : ENNReal) * (selected.card : ENNReal) := by
    simpa only [loss, threshold, Cproxy] using hcard
  have hmass' : (eighthNormalizedDatum D).shading.shadingMass <=
      (loss : ENNReal) *
        (restrictActualTubeDatum
          (eighthNormalizedDatum D) selected).shading.shadingMass := by
    simpa only [loss, threshold, Cproxy, D] using hmass
  have hbound : D.shading.averageMultiplicity <=
      (loss : ENNReal) *
        frostmanMultiplicityRHS
          (contractedJohnProxyRadius delta rho / 8)
          (restrictActualTubeDatum
            (eighthNormalizedDatum D) selected).actualFamilyVolume
          epsilon beta := by
    apply source_averageMultiplicity_le_normalized_loss_mul_frostmanRHS_of_refinement
      hF D selected loss (128 * Cproxy) hdelta0 hadmissible hcard' hmass'
        hselectedKT
    · simpa only [loss, threshold, Cproxy, D] using hdensityBudget
    · simpa only [loss, threshold, Cproxy, D] using hbaseBudget
  have hproxyAvg : D.shading.averageMultiplicity =
      (stickyFiberSourceShading S Y k.1).averageMultiplicity := by
    change (stickyFiberContractedJohnProxyShading
      S Y hrho hrhoOne k).averageMultiplicity =
        (stickyFiberSourceShading S Y k.1).averageMultiplicity
    exact stickyFiberContractedJohnProxyShading_averageMultiplicity
      S Y hrho hrhoOne k
  rw [hproxyAvg] at hbound
  refine ⟨selected, hselected, ?_⟩
  simpa only [loss, threshold, Cproxy, D] using hbound

#print axioms
  exists_stickyFiberContractedJohn_global_average_le_frostmanRHS

end

end Family8StickyFiberContractedJohnGlobalFrostmanConnectorV1
