import Family8Grounding.Family8AllFrostmanStickyPopularParentPowerV4
import Family8Grounding.Family8StickyShadingAwareCanonicalLogPartitionV1
import Family8Grounding.Family8CoarseTubePartitionExactUniformStickyFiberV4
import Mathlib.Tactic

/-!
# Parent-card power inherited by the shading-aware exact partition

The selected parents are a literal subset of the source Sticky cover's
active parents.  Hence the exact selected partition inherits the established
coarse Katz--Tao parent-card power without any object-identification premise.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ShadingAwareSelectedParentCardPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8AllFrostmanStickyPopularParentPowerV4
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The exact selected cover's active-parent cardinality obeys the same
power bound as the source cover. -/
theorem shadingAwareExactPartition_activeParentCard_le_delta_negativePower
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (Y : Shading D.family.bodyFamily)
    (sourceA : ENNReal) (hsourceA0 : sourceA ≠ 0)
    (hsourceAtop : sourceA ≠ ∞)
    (hrho : 0 < rho) (hdeltaRho : delta <= rho)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    {coarseA : ENNReal} (hcoarseKT : S.IsKatzTaoAtScale coarseA)
    {scaleExponent coarseKTExponent absorbExponent : Real}
    (habsorbExponent : 0 < absorbExponent)
    (hdeltaThreshold :
      delta <= stickyPopularParentPowerThreshold absorbExponent)
    (hscale : (delta : ENNReal) ^ scaleExponent <= (rho : ENNReal))
    (hcoarseAPower :
      coarseA <= (delta : ENNReal) ^ (-coarseKTExponent)) :
    let Ppart := shadingAwareLogPartition S Y sourceA hsourceA0 hsourceAtop
      hrho hdeltaRho hactive hmass
    let S1 := exactPartitionStickyCover Ppart
    (Fintype.card {k // k ∈ S1.activeCoarse} : ENNReal) <=
      (delta : ENNReal) ^
        (-(coarseKTExponent + 2 * scaleExponent + absorbExponent)) := by
  dsimp only
  let Ppart := shadingAwareLogPartition S Y sourceA hsourceA0 hsourceAtop
    hrho hdeltaRho hactive hmass
  let S1 := exactPartitionStickyCover Ppart
  have hselectedSubset : Ppart.coarseIndices <= S.activeCoarse := by
    dsimp only [Ppart]
    rw [shadingAwareLogPartition_coarseIndices]
    exact shadingAwareSelectedParents_subset_activeCoarse
      S Y sourceA hsourceA0 hsourceAtop hrho hactive hmass
  have hcardNat : S1.activeCoarse.card <= S.activeCoarse.card := by
    dsimp only [S1]
    exact Finset.card_le_card hselectedSubset
  have hcard :
      (Fintype.card {k // k ∈ S1.activeCoarse} : ENNReal) <=
        (Fintype.card {k // k ∈ S.activeCoarse} : ENNReal) := by
    simp only [Fintype.card_coe]
    exact_mod_cast hcardNat
  exact hcard.trans
    (activeCoarse_card_le_delta_negativePower_of_katzTaoAtScale
      D hD S hrhoHalf hcoarseKT habsorbExponent hdeltaThreshold
      hscale hcoarseAPower)

#print axioms
  shadingAwareExactPartition_activeParentCard_le_delta_negativePower

end
end Family8ShadingAwareSelectedParentCardPowerV1
