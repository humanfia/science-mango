import Family8Grounding.Family8ActiveCoarseFrostmanCardScaleMassLowerV3
import Family8Grounding.Family8StickyParentHullVolumeBoundV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8ActiveCoarseCanonicalFrostmanXLowerV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyParentHullVolumeBoundV1
open FamilyStickyAtEveryScaleCoreV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8ActiveCoarseFrostmanCardScaleMassLowerV3.StickyScaleCover

noncomputable section

/-!
# Canonical Frostman constant to the active-coarse `X` lower bound

The canonical constant already contains the exact ambient normalization.
For nonzero finite contained mass it produces the full cross-multiplied
`IsFrostmanIn` certificate automatically.  Applied to the actual
active-coarse family in the fixed radius-four ball, this removes an
unnecessary theorem-valued input from the paper's
`C_F(T_b)⁻¹ ≤ b² |T_b|` step.

The genuine upstream seam is now only the scalar bound on this canonical
constant supplied by the maximal-density/flat-prism argument.
-/

/-- The defining canonical Frostman constant certifies Frostman
non-concentration whenever its contained mass can be cancelled. -/
theorem canonicalFrostmanConstant_isFrostmanIn
    {index : Type*} [Fintype index]
    (F : ConvexFamily index) (K : ConvexBody Space)
    (hcontained : ∀ i, (F i : Set Space) ⊆ (K : Set Space))
    (hmass0 : containedMass F K ≠ 0)
    (hmassTop : containedMass F K ≠ ∞) :
    IsFrostmanIn (canonicalFrostmanConstant F K) F K := by
  have hKT : IsKatzTao (maximalConcentration F) F := by
    apply isKatzTao_iff_concentration_le.mpr
    intro Kprime
    exact concentration_le_maximalConcentration F Kprime
  apply IsKatzTao.isFrostmanIn hKT hcontained
  unfold canonicalFrostmanConstant
  rw [ENNReal.div_mul_cancel hmass0 hmassTop]

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The active coarse family has positive total mass whenever it has an
active parent and the coarse radius is positive. -/
theorem activeCoarseFamilyVolume_pos
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hcoarse : S.activeCoarse.Nonempty) :
    0 < familyVolume S.activeCoarseFamily := by
  obtain ⟨k, hk⟩ := hcoarse
  let kk : {k // k ∈ S.activeCoarse} := ⟨k, hk⟩
  have hsingle : volume (S.activeCoarseFamily kk : Set Space) ≤
      familyVolume S.activeCoarseFamily := by
    unfold familyVolume
    exact Finset.single_le_sum
      (fun j _ => show
        (0 : ENNReal) ≤ volume (S.activeCoarseFamily j : Set Space) from bot_le)
      (Finset.mem_univ kk)
  exact (S.coarse.tubes k).volume_pos hrho |>.trans_le hsingle

/-- The radius-four ambient body turns the canonical active-coarse constant
into a literal Frostman certificate. -/
theorem activeCoarseFamily_isFrostmanIn_canonical
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hcoarse : S.activeCoarse.Nonempty) :
    IsFrostmanIn
      (canonicalFrostmanConstant S.activeCoarseFamily closedBallFourBody)
      S.activeCoarseFamily closedBallFourBody := by
  have hcontained : ∀ k,
      (S.activeCoarseFamily k : Set Space) ⊆
        (closedBallFourBody : Set Space) := by
    intro k
    simpa only [coe_closedBallFourBody] using
      activeCoarseFamily_body_subset_closedBall_four D hD S hrhoOne k
  apply canonicalFrostmanConstant_isFrostmanIn
      S.activeCoarseFamily closedBallFourBody hcontained
  · rw [containedMass_eq_familyVolume_of_contained
      S.activeCoarseFamily closedBallFourBody hcontained]
    exact (activeCoarseFamilyVolume_pos S hrho hcoarse).ne'
  · rw [containedMass_eq_familyVolume_of_contained
      S.activeCoarseFamily closedBallFourBody hcontained]
    exact familyVolume_ne_top S.activeCoarseFamily

/-- The fixed radius-four ambient has volume at least one. -/
theorem one_le_volume_closedBallFourBody :
    1 ≤ volume (closedBallFourBody : Set Space) := by
  have hunit : 1 ≤ volume (unitBallBody : Set Space) := by
    rw [coe_unitBallBody, EuclideanSpace.volume_closedBall_fin_three]
    norm_num
    nlinarith [Real.pi_gt_three]
  exact hunit.trans (measure_mono (by
    simpa only [coe_unitBallBody, coe_closedBallFourBody] using
      (Metric.closedBall_subset_closedBall
        (show (1 : Real) ≤ 4 by norm_num) :
          Metric.closedBall (0 : Space) 1 ⊆ Metric.closedBall 0 4)))

/-- The paper-shaped lower bound up to the explicit dimensional factor
eight.  Its only non-structural geometric premise is the scalar bound on the
canonical Frostman constant. -/
theorem global_rpow_le_eight_mul_activeCoarseCardScaleMass_of_canonical
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    {globalDelta : NNReal} {etaPrime : Real}
    (hglobal : 0 < globalDelta)
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (hcoarse : S.activeCoarse.Nonempty)
    (hC : canonicalFrostmanConstant
        S.activeCoarseFamily closedBallFourBody ≤
      (globalDelta : ENNReal) ^ (-etaPrime)) :
    (globalDelta : ENNReal) ^ etaPrime ≤
      8 * (activeCoarseCardScaleMass S : ENNReal) := by
  apply global_rpow_le_eight_mul_activeCoarseCardScaleMass_of_frostman
    S closedBallFourBody hglobal hrho hrhoHalf hcoarse
    one_le_volume_closedBallFourBody
  · exact activeCoarseFamily_isFrostmanIn_canonical
      D hD S hrho (hrhoHalf.trans (by norm_num)) hcoarse
  · exact hC

#print axioms canonicalFrostmanConstant_isFrostmanIn
#print axioms StickyScaleCover.activeCoarseFamilyVolume_pos
#print axioms StickyScaleCover.activeCoarseFamily_isFrostmanIn_canonical
#print axioms StickyScaleCover.one_le_volume_closedBallFourBody
#print axioms
  StickyScaleCover.global_rpow_le_eight_mul_activeCoarseCardScaleMass_of_canonical

end StickyScaleCover
end
end Family8ActiveCoarseCanonicalFrostmanXLowerV3
