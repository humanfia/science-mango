import Family8Grounding.Family8ActiveCoarseCanonicalFrostmanXLowerV3
import Family8Grounding.Family8NormalizedCFDividingWitnessBridgeV2

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8StickyScaleCoverSelectedParentCFAtDichotomyV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ActiveCoarseCanonicalFrostmanXLowerV3
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

namespace StickyScaleCover

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- At any prescribed active parent, either the requested normalized-CF
barrier is attained, or that same literal fibre is Frostman inside its
literal parent with the barrier itself as constant.  This avoids identifying
the prescribed parent with a global `CFMax` maximizer. -/
theorem lower_le_cfAt_or_isFrostmanIn
    (S : StickyScaleCover fine rho) (hdelta : 0 < delta)
    (q : {q // q ∈ S.activeCoarse}) (lower : ENNReal) :
    lower ≤ parentNormalizedFiberCFAt S q ∨
      IsFrostmanIn lower (S.fiberFamily q.1) (S.activeCoarseFamily q) := by
  by_cases hhigh : lower ≤ parentNormalizedFiberCFAt S q
  · exact Or.inl hhigh
  · right
    have hcanonical :
        IsFrostmanIn (parentNormalizedFiberCFAt S q)
          (S.fiberFamily q.1) (S.activeCoarseFamily q) := by
      unfold parentNormalizedFiberCFAt
      apply canonicalFrostmanConstant_isFrostmanIn
      · exact fiberFamily_subset_parent S q
      · rw [containedMass_fiberFamily_parent_eq_familyVolume]
        exact (fiberFamilyVolume_pos S hdelta q).ne'
      · rw [containedMass_fiberFamily_parent_eq_familyVolume]
        exact familyVolume_ne_top (S.fiberFamily q.1)
    exact hcanonical.mono (le_of_not_ge hhigh)

#print axioms lower_le_cfAt_or_isFrostmanIn

end StickyScaleCover

end
end Family8StickyScaleCoverSelectedParentCFAtDichotomyV1
