import Family8Grounding.Family8StickyShadingAwareSelectedFiberDensityCrossV1
import Mathlib.Tactic

/-!
# Explicit density floor on a shading-aware selected Sticky fibre

The parent tube has volume at least `rho^2 / 2`. Combining that geometric
lower bound with the same-fibre density cross inequality gives an explicit
quotient lower bound for the actual source-fibre shading density.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyShadingAwareSelectedFiberDensityFloorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open Family8StickyShadingAwareSelectedFiberDensityCrossV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The literal selected-fibre density is bounded below by the parent scale
and source coefficient, divided only by the honest shading-aware cover loss,
dyadic branching cap, and fine-tube volume constant. -/
theorem shadingAwareSelectedParent_density_floor
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (k : Fin S.coarseCard)
    (hk : k ∈ shadingAwareSelectedParents
      S Y A hA0 hAtop hrho hactive hmass) :
    let L := stickyShadingAwareCoverLoss S Y A
    let B := logBucketBranching
      (shadingAwareLogBucketLevel
        S Y A hA0 hAtop hrho hactive hmass)
    (A * ((rho : ENNReal) ^ 2 / 2)) /
        ((2 * L) * (((2 * B : Nat) : ENNReal) *
          (8 * (delta : ENNReal) ^ 2))) ≤
      (stickyFiberSourceShading S Y k).shadingDensity := by
  let L := stickyShadingAwareCoverLoss S Y A
  let B := logBucketBranching
    (shadingAwareLogBucketLevel
      S Y A hA0 hAtop hrho hactive hmass)
  have hparent : (rho : ENNReal) ^ 2 / 2 ≤
      volume (S.coarse.tubes k).carrier :=
    (S.coarse.tubes k).half_sq_le_volume_of_le_half hrhoHalf
  have hcross : A * volume (S.coarse.tubes k).carrier ≤
      ((2 * L) * (((2 * B : Nat) : ENNReal) *
        (8 * (delta : ENNReal) ^ 2))) *
          (stickyFiberSourceShading S Y k).shadingDensity := by
    simpa only [L, B] using
      shadingAwareSelectedParent_cost_le_cappedFiberVolume_mul_density
        S Y A hA0 hAtop hrho hactive hmass hdeltaHalf k hk
  have hscaled : A * ((rho : ENNReal) ^ 2 / 2) ≤
      ((2 * L) * (((2 * B : Nat) : ENNReal) *
        (8 * (delta : ENNReal) ^ 2))) *
          (stickyFiberSourceShading S Y k).shadingDensity :=
    (mul_le_mul' le_rfl hparent).trans hcross
  simpa only [L, B] using ENNReal.div_le_of_le_mul' hscaled

#print axioms shadingAwareSelectedParent_density_floor

end
end Family8StickyShadingAwareSelectedFiberDensityFloorV1
