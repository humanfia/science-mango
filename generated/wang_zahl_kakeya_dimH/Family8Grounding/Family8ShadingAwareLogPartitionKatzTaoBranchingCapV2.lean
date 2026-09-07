import Family8Grounding.Family8StickyShadingAwareCanonicalLogPartitionV1
import Family8Grounding.Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
import Mathlib.Tactic

/-!
# Katz--Tao cap for the shading-aware selected branching

The shading-aware logarithmic selector chooses a genuine parent fibre.  Its
balanced branching is therefore bounded by that assigned fibre, hence by the
geometric doubled fibre and the source Katz--Tao cap.  This is the literal
same-object bridge needed before absorbing the Eq. 46 source coefficient.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ShadingAwareLogPartitionKatzTaoBranchingCapV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The actual branching selected by the shading-aware logarithmic bucket is
bounded by the canonical doubled-fibre Katz--Tao cap. -/
theorem shadingAwareLogPartition_branching_le_katzTaoDoubledFiberNatCap
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (sourceA : ENNReal) (hsourceA0 : sourceA ≠ 0)
    (hsourceAtop : sourceA ≠ ∞)
    (hrho : 0 < rho) (hscale : delta <= rho)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrhoOne : rho <= 1)
    (hKT : IsKatzTao sourceA fine.bodyFamily) :
    (shadingAwareLogPartition S Y sourceA hsourceA0 hsourceAtop
        hrho hscale hactive hmass).branching <=
      katzTaoDoubledFiberNatCap delta rho sourceA := by
  let P := shadingAwareLogPartition S Y sourceA hsourceA0 hsourceAtop
    hrho hscale hactive hmass
  obtain ⟨k, hk⟩ := P.coarse_nonempty
  dsimp only [P] at hk
  have hbounds := shadingAwareLogPartition_fiber_bounds
    S Y sourceA hsourceA0 hsourceAtop hrho hscale hactive hmass k hk
  have hbranchSelected := hbounds.1
  change logBucketBranching
      (shadingAwareLogBucketLevel S Y sourceA hsourceA0 hsourceAtop
        hrho hactive hmass) <=
    ((selectedIndexFactorization S.activeFine S.parent
      (shadingAwareSelectedParents S Y sourceA hsourceA0 hsourceAtop
        hrho hactive hmass)).fiber k).card at hbranchSelected
  rw [selected_fiber_eq_raw_fiber S.activeFine S.parent
    (shadingAwareSelectedParents S Y sourceA hsourceA0 hsourceAtop
      hrho hactive hmass) hk] at hbranchSelected
  have hrawFiberEq :
      (rawIndexFactorization S.activeFine S.parent).fiber k =
        S.fiber k := by
    ext i
    simp only [IndexFactorization.mem_fiber, rawIndexFactorization,
      StickyScaleCover.mem_fiber]
  rw [hrawFiberEq] at hbranchSelected
  have hbranch :
      (shadingAwareLogPartition S Y sourceA hsourceA0 hsourceAtop
        hrho hscale hactive hmass).branching <= (S.fiber k).card := by
    rw [shadingAwareLogPartition_branching]
    exact hbranchSelected
  have hraw : (S.fiber k).card <= (doubledFiber S k).card :=
    Finset.card_le_card (fiber_subset_doubledFiber S k)
  exact hbranch.trans (hraw.trans
    (doubledFiber_card_le_katzTaoDoubledFiberNatCap
      (fine := fine) S hdeltaPos hdeltaHalf hrhoOne
      (A := sourceA) hsourceAtop hKT k))

#print axioms shadingAwareLogPartition_branching_le_katzTaoDoubledFiberNatCap

end
end Family8ShadingAwareLogPartitionKatzTaoBranchingCapV2
