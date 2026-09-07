import Family8Grounding.Family8StickyShadingAwareCanonicalLogPartitionV1
import Family8Grounding.Family8StickySelectedFineMassPopularScalarTransportV1
import Mathlib.Tactic

/-!
# Density cross inequality on the shading-aware logarithmic fibre

For every parent in the actual shading-aware dyadic bucket, the selected
shading mass is exactly the mass of its literal Sticky fibre. Parent
efficiency, the tube-volume bound, and the dyadic fibre-cardinality cap then
give a denominator-free lower-density inequality on that same fibre.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyShadingAwareSelectedFiberDensityCrossV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickySelectedFineMassPopularScalarTransportV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The mass assigned by the logarithmic selector is literally the shading
mass of the corresponding full Sticky fibre. -/
theorem assignedShadingMass_eq_stickyFiberSourceShading_shadingMass
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (k : Fin S.coarseCard) :
    assignedShadingMass S Y k =
      (stickyFiberSourceShading S Y k).shadingMass := by
  have hraw :
      (rawIndexFactorization S.activeFine S.parent).fiber k = S.fiber k := by
    ext i
    simp only [IndexFactorization.mem_fiber, rawIndexFactorization,
      StickyScaleCover.mem_fiber]
  unfold assignedShadingMass Shading.shadingMass
  rw [hraw]
  calc
    (∑ i ∈ S.fiber k, volume (Y.carrier i)) =
        ∑ i : {i // i ∈ S.fiber k}, volume (Y.carrier i.1) := by
      rw [← Finset.attach_eq_univ]
      exact (Finset.sum_attach (S.fiber k)
        (fun i => volume (Y.carrier i))).symm
    _ = ∑ i : {i // i ∈ S.fiber k},
        volume ((stickyFiberSourceShading S Y k).carrier i) := rfl

/-- Every parent in the actual shading-aware logarithmic bucket satisfies a
single same-fibre density cross inequality. The right side records only the
literal cover loss, the common dyadic branching cap, the exact fine scale,
and the actual source-fibre shading density. -/
theorem shadingAwareSelectedParent_cost_le_cappedFiberVolume_mul_density
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (k : Fin S.coarseCard)
    (hk : k ∈ shadingAwareSelectedParents
      S Y A hA0 hAtop hrho hactive hmass) :
    let L := stickyShadingAwareCoverLoss S Y A
    let B := logBucketBranching
      (shadingAwareLogBucketLevel
        S Y A hA0 hAtop hrho hactive hmass)
    A * volume (S.coarse.tubes k).carrier ≤
      ((2 * L) * (((2 * B : Nat) : ENNReal) *
        (8 * (delta : ENNReal) ^ 2))) *
          (stickyFiberSourceShading S Y k).shadingDensity := by
  dsimp only
  let L := stickyShadingAwareCoverLoss S Y A
  let B := logBucketBranching
    (shadingAwareLogBucketLevel
      S Y A hA0 hAtop hrho hactive hmass)
  have hkBucket : k ∈ shadingEfficientLogCardBucket S Y A L
      (shadingAwareLogBucketLevel
        S Y A hA0 hAtop hrho hactive hmass) := by
    simpa only [shadingAwareSelectedParents, L] using hk
  have hkEff : k ∈ shadingEfficientParents S Y A L :=
    ((mem_dyadicFiber
      (shadingEfficientParents S Y A L)
      (fiberLogCardLabel S.activeFine S.parent)
      (shadingAwareLogBucketLevel
        S Y A hA0 hAtop hrho hactive hmass) k).1 hkBucket).1
  have hcost : A * volume (S.coarse.tubes k).carrier ≤
      (2 * L) * assignedShadingMass S Y k :=
    (Finset.mem_filter.mp hkEff).2
  have hvolume : familyVolume (S.fiberFamily k) ≤
      (Fintype.card {i // i ∈ S.fiber k} : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) :=
    stickyFiber_familyVolume_le_card_mul_eight_sq S hdeltaHalf k
  have hbounds := shadingAwareSelected_fiber_bounds
    S Y A hA0 hAtop hrho hactive hmass k hk
  have hcard : (Fintype.card {i // i ∈ S.fiber k} : ENNReal) ≤
      ((2 * B : Nat) : ENNReal) := by
    have hraw :
        (rawIndexFactorization S.activeFine S.parent).fiber k = S.fiber k := by
      ext i
      simp only [IndexFactorization.mem_fiber, rawIndexFactorization,
        StickyScaleCover.mem_fiber]
    have hcardNat : (S.fiber k).card ≤ 2 * B := by
      simpa only [hraw, B] using Nat.le_of_lt hbounds.2
    have hcardNat'' : Fintype.card {i // i ∈ S.fiber k} ≤ 2 * B := by
      simpa only [Fintype.card_coe] using hcardNat
    exact_mod_cast hcardNat''
  calc
    A * volume (S.coarse.tubes k).carrier ≤
        (2 * L) * assignedShadingMass S Y k := hcost
    _ = (2 * L) * (stickyFiberSourceShading S Y k).shadingMass := by
      rw [assignedShadingMass_eq_stickyFiberSourceShading_shadingMass]
    _ = (2 * L) * ((stickyFiberSourceShading S Y k).shadingDensity *
        familyVolume (S.fiberFamily k)) := by
      rw [Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra.shadingDensity_mul_familyVolume]
    _ ≤ (2 * L) * ((stickyFiberSourceShading S Y k).shadingDensity *
        ((Fintype.card {i // i ∈ S.fiber k} : ENNReal) *
          (8 * (delta : ENNReal) ^ 2))) := by
      gcongr
    _ ≤ (2 * L) * ((stickyFiberSourceShading S Y k).shadingDensity *
        (((2 * B : Nat) : ENNReal) *
          (8 * (delta : ENNReal) ^ 2))) := by
      gcongr
    _ = ((2 * L) * (((2 * B : Nat) : ENNReal) *
        (8 * (delta : ENNReal) ^ 2))) *
          (stickyFiberSourceShading S Y k).shadingDensity := by
      ac_rfl

#print axioms
  assignedShadingMass_eq_stickyFiberSourceShading_shadingMass
#print axioms
  shadingAwareSelectedParent_cost_le_cappedFiberVolume_mul_density

end
end Family8StickyShadingAwareSelectedFiberDensityCrossV1
