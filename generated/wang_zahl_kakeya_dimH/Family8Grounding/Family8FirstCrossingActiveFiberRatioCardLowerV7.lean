import Family8Grounding.Family8Family7FirstCrossingBufferedFiberFrostmanV4
import Family8Grounding.Family8StickyFiberFrostmanParentCardScaleV3
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

/-!
# FirstCrossing Frostman lower bound for every active fibre, V7

The strict FirstCrossing certificate controls the canonical Frostman
constant of each literal buffered fibre.  Testing that certificate on the
actual parent and using the sharp tube-volume sandwich gives

`(rho / tau)^2 <= 16 * (rho / tau)^eta(stage) * #(fibre)`.

This is the lower half of the normalized-count cancellation.  It keeps the
original buffered cover and does not replace it by a uniform subcover.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8FirstCrossingActiveFiberRatioCardLowerV7

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Family7FirstCrossingBufferedFiberFrostmanV4
open Family8Family7FirstCrossingBufferedFiberFrostmanV4.FirstActualNormalizedCrossingWitness
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8StickyFiberFrostmanParentCardScaleV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat}

/-- Every active fibre at the strict FirstCrossing scale pays the exact
inverse-square scale ratio, up to the dimensional constant sixteen and the
literal FirstCrossing Frostman constant. -/
theorem firstCrossing_ratio_sq_le_sixteen_mul_frostman_mul_fiberCard
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (htauHalf : S.tau W.m ≤ (2 : NNReal)⁻¹)
    (hrhoHalf : W.rho ≤ (2 : NNReal)⁻¹)
    (k : Fin (bufferedIntervalCover
      D hD C S epsilon hepsilon W.m W.rho W.buffered).coarseCard)
    (hk : k ∈ (bufferedIntervalCover
      D hD C S epsilon hepsilon W.m W.rho W.buffered).activeCoarse) :
    (((W.rho : ENNReal) / (S.tau W.m : ENNReal)) ^ (2 : Real)) ≤
      16 *
        (((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage) *
        (((bufferedIntervalCover
          D hD C S epsilon hepsilon W.m W.rho W.buffered).fiber k).card :
            ENNReal) := by
  let U := bufferedIntervalCover
    D hD C S epsilon hepsilon W.m W.rho W.buffered
  let frostmanC : ENNReal :=
    (((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage)
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hkFiber : (U.fiber k).Nonempty := by
    obtain ⟨i, hi, hparent⟩ := U.parent_surjective k hk
    refine ⟨i, ?_⟩
    exact (U.mem_fiber i k).2 ⟨hi, hparent⟩
  have hF : IsFrostmanOn frostmanC
      (bufferedLowerFamily D C S W.m).bodyFamily
      (U.fiber k) (U.coarse.tubes k).body := by
    simpa only [U, frostmanC] using
      selectedBufferedIntervalCover_fiber_isFrostmanOn
        D hD C S epsilon hepsilon eta N W k hk
  have hparent : volume (U.coarse.tubes k).carrier ≤
      frostmanC * ((U.fiber k).card : ENNReal) *
        (8 * (S.tau W.m : ENNReal) ^ 2) :=
    parentVolume_le_frostman_mul_fiberCardScale
      U htau htauHalf k hkFiber hF
  have hraw : (W.rho : ENNReal) ^ 2 / 2 ≤
      frostmanC * ((U.fiber k).card : ENNReal) *
        (8 * (S.tau W.m : ENNReal) ^ 2) :=
    ((U.coarse.tubes k).half_sq_le_volume_of_le_half hrhoHalf).trans hparent
  have hscaled : (W.rho : ENNReal) ^ 2 ≤
      (16 * frostmanC * ((U.fiber k).card : ENNReal)) *
        (S.tau W.m : ENNReal) ^ 2 := by
    calc
      (W.rho : ENNReal) ^ 2 =
          2 * ((W.rho : ENNReal) ^ 2 / 2) := by
        calc
          (W.rho : ENNReal) ^ 2 =
              ((W.rho : ENNReal) ^ 2 / 2) * 2 :=
            (ENNReal.div_mul_cancel (by norm_num) (by norm_num)).symm
          _ = 2 * ((W.rho : ENNReal) ^ 2 / 2) := mul_comm _ _
      _ ≤ 2 * (frostmanC * ((U.fiber k).card : ENNReal) *
          (8 * (S.tau W.m : ENNReal) ^ 2)) :=
        mul_le_mul' le_rfl hraw
      _ = (16 * frostmanC * ((U.fiber k).card : ENNReal)) *
          (S.tau W.m : ENNReal) ^ 2 := by ring
  rw [ENNReal.div_rpow_of_nonneg _ _ (by norm_num)]
  rw [ENNReal.rpow_two]
  rw [ENNReal.rpow_two]
  apply (ENNReal.div_le_iff_le_mul
    (Or.inl (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr htau.ne')))
    (Or.inl (ENNReal.pow_ne_top ENNReal.coe_ne_top))).2
  simpa only [U, frostmanC, mul_assoc] using hscaled

#print axioms firstCrossing_ratio_sq_le_sixteen_mul_frostman_mul_fiberCard

end
end Family8FirstCrossingActiveFiberRatioCardLowerV7
