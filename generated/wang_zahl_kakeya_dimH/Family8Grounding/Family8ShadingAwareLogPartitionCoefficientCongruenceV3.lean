import Family8Grounding.Family8StickyShadingAwareCanonicalLogPartitionV1

/-!
# Scalar coefficient congruence for the shading-aware partition, V3

The selected fine/coarse family types depend on the source coefficient, so
the whole partitions are not homogeneously equal before transport.  Their
natural branching fields are ordinary scalars and are equal across an equal
coefficient; these are exactly the fields consumed by the source-cap bound.
V1--V2 attempted an ill-typed homogeneous partition equality and are not
imported.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ShadingAwareLogPartitionCoefficientCongruenceV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Equal source coefficients give the same literal selection/branching
natural-number cap, independently of the proof terms. -/
theorem shadingAwareLogPartition_sourceCap_congr_coefficient
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    {A B : ENNReal} (hAB : A = B)
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hB0 : B ≠ 0) (hBtop : B ≠ ∞)
    (hrho : 0 < rho) (hscale : delta ≤ rho)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    (2 * (Nat.log 2 (Fintype.card index) + 1)) *
        ((shadingAwareLogPartition S Y A hA0 hAtop
          hrho hscale hactive hmass).branchingLoss *
        (shadingAwareLogPartition S Y A hA0 hAtop
          hrho hscale hactive hmass).branching) =
      (2 * (Nat.log 2 (Fintype.card index) + 1)) *
        ((shadingAwareLogPartition S Y B hB0 hBtop
          hrho hscale hactive hmass).branchingLoss *
        (shadingAwareLogPartition S Y B hB0 hBtop
          hrho hscale hactive hmass).branching) := by
  subst B
  rfl

#print axioms shadingAwareLogPartition_sourceCap_congr_coefficient

end
end Family8ShadingAwareLogPartitionCoefficientCongruenceV3
