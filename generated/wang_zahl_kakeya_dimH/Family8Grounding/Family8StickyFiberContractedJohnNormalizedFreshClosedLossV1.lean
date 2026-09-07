import Family8Grounding.Family8StickyFiberContractedJohnNormalizedFreshV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyFiberContractedJohnNormalizedFreshClosedLossV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8ContractedJohnActualTubeProxyV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnNormalizedFreshV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Closed-loss automatic normalized fresh selection

This successor replaces the natural ceiling in the canonical proxy fresh
selection by the finite ENNReal envelope `480000 * (128 * C) + 2`.  Thus
downstream scalar budgets no longer need to mention a natural ceiling.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The automatic canonical proxy selection with a ceiling-free common loss. -/
theorem exists_stickyFiberContractedJohn_normalizedFresh_closedLoss_of_isKatzTao
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho) (k : {k // k ∈ S.activeCoarse})
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C
      (stickyFiberContractedJohnProxyDatum
        S Y hrho hrhoOne k).family.bodyFamily) :
    let D := stickyFiberContractedJohnProxyDatum S Y hrho hrhoOne k
    let closedLoss : ENNReal := 480000 * (128 * C) + 2
    exists selected : Finset {i // i ∈ S.fiber k.1},
      selected.Nonempty ∧
      (restrictActualTubeDatum (eighthNormalizedDatum D) selected).IsAdmissible ∧
      (Fintype.card {i // i ∈ S.fiber k.1} : ENNReal) <=
        closedLoss * (selected.card : ENNReal) ∧
      (eighthNormalizedDatum D).shading.shadingMass <=
        closedLoss *
          (restrictActualTubeDatum
            (eighthNormalizedDatum D) selected).shading.shadingMass ∧
      IsKatzTao (128 * C)
        (restrictActualTubeDatum
          (eighthNormalizedDatum D) selected).family.bodyFamily ∧
      (stickyFiberSourceShading S Y k.1).averageMultiplicity <=
        closedLoss *
          (restrictActualTubeDatum
            (eighthNormalizedDatum D) selected).shading.averageMultiplicity := by
  dsimp only
  let D := stickyFiberContractedJohnProxyDatum S Y hrho hrhoOne k
  let threshold := Nat.ceil ((480000 * (128 * C) : ENNReal).toReal)
  let closedLoss : ENNReal := 480000 * (128 * C) + 2
  obtain ⟨selected, hselected, hadmissible, hcard, hmass,
      hselectedKT, havg⟩ :=
    exists_stickyFiberContractedJohn_normalizedFresh_of_isKatzTao
      S Y hdelta hrho hrhoOne hdeltaRho k hCfinite hKT
  have hscaledFinite : (128 : ENNReal) * C ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCfinite
  have hloss : ((threshold + 1 : Nat) : ENNReal) <= closedLoss := by
    exact fixedKatzTaoClosedLoss_coe_le_add_two hscaledFinite
  refine ⟨selected, hselected, hadmissible, ?_, ?_, hselectedKT, ?_⟩
  · apply hcard.trans
    gcongr
  · apply hmass.trans
    gcongr
  · apply havg.trans
    gcongr

#print axioms
  exists_stickyFiberContractedJohn_normalizedFresh_closedLoss_of_isKatzTao

end

end Family8StickyFiberContractedJohnNormalizedFreshClosedLossV1
