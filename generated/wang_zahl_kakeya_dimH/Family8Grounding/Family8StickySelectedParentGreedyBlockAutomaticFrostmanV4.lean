import Family8Grounding.Family8StickySelectedParentGreedyBlockFrostmanV3
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8StickySelectedParentGreedyBlockAutomaticFrostmanV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyAllOccurrenceFrostman
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyParentHullVolumeBoundV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

local instance v3SelectedParentFineFintype
    (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) :
    Fintype (SelectedParentFineIndex S B) :=
  Family8StickySelectedParentGreedyBlockFrostmanV3.selectedParentFineFintype
    S B

local instance v3SelectedParentFineDecidableEq
    (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) :
    DecidableEq (SelectedParentFineIndex S B) :=
  Family8StickySelectedParentGreedyBlockFrostmanV3.selectedParentFineDecidableEq
    S B

/-- Every actual greedy winning hull contains a selected parent tube, hence
has at least the literal one-parent tube-volume scale. -/
theorem selectedParentGreedyBlock_halfSq_le_hullVolume
    (S : StickyScaleCover fine rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length) :
    (rho : ENNReal) ^ 2 / 2 <=
      volume ((blockAt S.activeCoarseFamily P k).body : Set Space) := by
  obtain ⟨p, hp⟩ := (blockAt S.activeCoarseFamily P k).fiber_nonempty
  have hcontained := (blockAt S.activeCoarseFamily P k).contained p hp
  change (S.coarse.tubes p.1).carrier ⊆
    ((blockAt S.activeCoarseFamily P k).body : Set Space) at hcontained
  exact ((S.coarse.tubes p.1).half_sq_le_volume_of_le_half hrhoHalf).trans
    (measure_mono hcontained)

/-- Fully automatic fallback obtained from a single selected parent.  Its
`rho^-2` loss is honest but too large for the paper's small-loss seam; the
flat-prism branch must improve the hull-volume lower bound for the main line. -/
theorem selectedParentGreedyBlock_closedBallFour_canonical_le_rhoSqFallback
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hrho : 0 < rho) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length) :
    let B := (blockAt S.activeCoarseFamily P k).fiber
    canonicalFrostmanConstant
        (selectedParentBlockScaleCover S B).activeCoarseFamily
        closedBallFourBody <=
      1024 / (rho : ENNReal) ^ 2 := by
  apply selectedParentGreedyBlock_closedBallFour_canonical_le_of_hullVolume
    D hD S hrho (hrhoHalf.trans (by norm_num)) P k
  have hrhoZero : (rho : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hrho.ne'
  have hrhoSqZero : (rho : ENNReal) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hrhoZero
  have hrhoSqTop : (rho : ENNReal) ^ 2 ≠ ∞ :=
    ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hcancel :
      1024 / (rho : ENNReal) ^ 2 * (rho : ENNReal) ^ 2 = 1024 :=
    ENNReal.div_mul_cancel hrhoSqZero hrhoSqTop
  have hhalf : (2 : ENNReal)⁻¹ * 2 = 1 :=
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have hhull := selectedParentGreedyBlock_halfSq_le_hullVolume
    S hrhoHalf P k
  calc
    volume (closedBallFourBody : Set Space) <= 512 := by
      simpa only [coe_closedBallFourBody] using
        volume_closedBall_zero_four_le_512
    _ = (1024 / (rho : ENNReal) ^ 2) *
        ((rho : ENNReal) ^ 2 / 2) := by
      symm
      calc
        (1024 / (rho : ENNReal) ^ 2) *
            ((rho : ENNReal) ^ 2 / 2) =
            (1024 / (rho : ENNReal) ^ 2 *
              (rho : ENNReal) ^ 2) / 2 := by
          rw [← mul_div_assoc]
        _ = 1024 / 2 := by rw [hcancel]
        _ = 512 := by
          rw [ENNReal.div_eq_inv_mul,
            show (1024 : ENNReal) = 2 * 512 by norm_num,
            ← mul_assoc, hhalf, one_mul]
    _ <= (1024 / (rho : ENNReal) ^ 2) *
        volume ((blockAt S.activeCoarseFamily P k).body : Set Space) :=
      mul_le_mul' le_rfl hhull

#print axioms selectedParentGreedyBlock_halfSq_le_hullVolume
#print axioms
  selectedParentGreedyBlock_closedBallFour_canonical_le_rhoSqFallback

end


end Family8StickySelectedParentGreedyBlockAutomaticFrostmanV4
