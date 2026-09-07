import Family8Grounding.Family8StickyDensityAwareLogBranchingNNRealAdapterV1
import Submission.Kakeya.ConvexFactoring.DyadicBranchingBucket

/-!
# Canonical density-aware logarithmic bucket choice

This file chooses only the logarithmic bucket level from the small weighted
bucket existence theorem.  It deliberately does not unpack the full
`JointTubeFactoring` existential.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyDensityAwareCanonicalLogBucketChoiceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open Family8StickyDensityAwareLogBranchingCoverLossV4
open Family8StickyDensityAwareLogBranchingNNRealAdapterV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Small existence interface: one logarithmic efficient bucket retains the
active-fine body mass with the standard logarithmic loss. -/
theorem exists_densityAwareLogBucket_withinFactor
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    ∃ b : Fin (Nat.log 2 (Fintype.card iota) + 1),
      WithinFactor (2 * (Nat.log 2 (Fintype.card iota) + 1))
        (bodyMassOn fine.bodyFamily S.activeFine)
        (∑ k ∈ efficientLogCardBucket
            fine S.coarse S.activeFine S.parent (A : ENNReal)
              (stickyDensityAwareCoverLossNNReal S A : ENNReal) b,
          assignedBodyMass fine S.activeFine S.parent k) := by
  apply exists_efficientLogCardBucket_withinFactor
  · exact ENNReal.coe_ne_zero.mpr
      (stickyDensityAwareCoverLossNNReal_pos
        S hA hdelta hrho hactive).ne'
  · exact ENNReal.coe_ne_top
  · simpa only [coe_stickyDensityAwareCoverLossNNReal
      S A hdelta hactive] using
        stickyDensityAwareCoverCost S (A : ENNReal) hdelta hactive

/-- The canonically chosen logarithmic level. -/
def densityAwareLogBucketLevel
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    Fin (Nat.log 2 (Fintype.card iota) + 1) :=
  Classical.choose
    (exists_densityAwareLogBucket_withinFactor
      S A hA hdelta hrho hactive)

/-- The retained-mass certificate of the chosen level. -/
theorem densityAwareLogBucketLevel_spec
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    WithinFactor (2 * (Nat.log 2 (Fintype.card iota) + 1))
      (bodyMassOn fine.bodyFamily S.activeFine)
      (∑ k ∈ efficientLogCardBucket
          fine S.coarse S.activeFine S.parent (A : ENNReal)
            (stickyDensityAwareCoverLossNNReal S A : ENNReal)
              (densityAwareLogBucketLevel
                S A hA hdelta hrho hactive),
        assignedBodyMass fine S.activeFine S.parent k) :=
  Classical.choose_spec
    (exists_densityAwareLogBucket_withinFactor
      S A hA hdelta hrho hactive)

#print axioms exists_densityAwareLogBucket_withinFactor
#print axioms densityAwareLogBucketLevel
#print axioms densityAwareLogBucketLevel_spec

end
end Family8StickyDensityAwareCanonicalLogBucketChoiceV1
