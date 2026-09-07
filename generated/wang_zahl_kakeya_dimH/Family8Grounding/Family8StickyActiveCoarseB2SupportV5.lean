import Family8Grounding.Family8PaperConflictAnisotropicBoundsV4
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import FamilyStickyGrounding.FamilyStickyAtEveryScaleCoreV1
import FamilyStickyGrounding.FamilyStickyTubeParentDirectionCoherenceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped NNReal

namespace Family8StickyActiveCoarseB2SupportV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8CommonPointTubePackingV1
open Family8PaperConflictAnisotropicBoundsV4
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyTubeParentDirectionCoherenceV1.Tube

noncomputable section

/-!
# Sharp radius-two support for active sticky parents

An assigned child contributes its entire unit axis.  Endpoint pairing puts
the child and parent midpoints within `3 rho`; consequently every active
parent lies in `B(0,2)` at radius at most `1/16` when the child datum lies in
the unit ball.  This is the honest support input for eighth-normalization.
-/

/-- If the complete unit axis of `T` lies in `U`, their unoriented midpoints
are within three containing radii. -/
theorem dist_tubeAxisMidpoint_le_three_mul_of_axis_subset_carrier
    {delta rho : NNReal} (T : Tube delta) (U : Tube rho)
    (hTU : T.axis.carrier ⊆ U.carrier) :
    dist (tubeAxisMidpoint T) (tubeAxisMidpoint U) ≤
      3 * (rho : Real) := by
  have haverage {a b c d : Space} {e : Real}
      (he : 0 ≤ e) (ha : dist a c ≤ e) (hb : dist b d ≤ e) :
      dist ((2 : Real)⁻¹ • (a + b)) ((2 : Real)⁻¹ • (c + d)) ≤ e := by
    rw [dist_eq_norm]
    have hvec :
        (2 : Real)⁻¹ • (a + b) - (2 : Real)⁻¹ • (c + d) =
          (2 : Real)⁻¹ • ((a - c) + (b - d)) := by module
    rw [hvec, norm_smul]
    have hhalf : ‖(2 : Real)⁻¹‖ = (2 : Real)⁻¹ := by norm_num
    rw [hhalf]
    calc
      (2 : Real)⁻¹ * ‖(a - c) + (b - d)‖ ≤
          (2 : Real)⁻¹ * (‖a - c‖ + ‖b - d‖) := by
        gcongr
        exact norm_add_le _ _
      _ ≤ (2 : Real)⁻¹ * (e + e) := by
        gcongr
        · simpa only [dist_eq_norm] using ha
        · simpa only [dist_eq_norm] using hb
      _ = e := by ring
  rcases endpoint_pairing_of_commonSegment U T.axis hTU with hforward | hreverse
  · change dist
      (T.axis.base + (2 : Real)⁻¹ • T.axis.direction)
      (U.axis.base + (2 : Real)⁻¹ • U.axis.direction) ≤ _
    have hT : T.axis.base + (2 : Real)⁻¹ • T.axis.direction =
        (2 : Real)⁻¹ • (T.axis.base + T.axis.endpoint) := by
      simp only [UnitSegment.endpoint]
      module
    have hU : U.axis.base + (2 : Real)⁻¹ • U.axis.direction =
        (2 : Real)⁻¹ • (U.axis.base + U.axis.endpoint) := by
      simp only [UnitSegment.endpoint]
      module
    rw [hT, hU]
    apply haverage (by positivity)
    · simpa only [dist_comm] using hforward.1
    · simpa only [dist_comm] using hforward.2
  · change dist
      (T.axis.base + (2 : Real)⁻¹ • T.axis.direction)
      (U.axis.base + (2 : Real)⁻¹ • U.axis.direction) ≤ _
    have hT : T.axis.base + (2 : Real)⁻¹ • T.axis.direction =
        (2 : Real)⁻¹ • (T.axis.base + T.axis.endpoint) := by
      simp only [UnitSegment.endpoint]
      module
    have hU : U.axis.base + (2 : Real)⁻¹ • U.axis.direction =
        (2 : Real)⁻¹ • (U.axis.endpoint + U.axis.base) := by
      simp only [UnitSegment.endpoint]
      module
    rw [hT, hU]
    apply haverage (by positivity)
    · simpa only [dist_comm] using hreverse.2
    · simpa only [dist_comm] using hreverse.1

/-- At radius at most `1/16`, every active sticky parent of a datum in the
unit ball lies in `B(0,2)`. -/
theorem activeCoarseFamily_body_subset_closedBall_two
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hrho : rho ≤ (1 / 16 : NNReal))
    (k : {k // k ∈ S.activeCoarse}) :
    (S.activeCoarseFamily k : Set Space) ⊆
      Metric.closedBall (0 : Space) 2 := by
  obtain ⟨i, hiActive, hparent⟩ := S.parent_surjective k.1 k.2
  have haxis : (D.family.tubes i).axis.carrier ⊆
      (S.coarse.tubes k.1).carrier := by
    have hcarrier := S.carrier_subset i hiActive
    rw [hparent] at hcarrier
    exact (D.family.tubes i).axis_subset_carrier.trans hcarrier
  have hmid : dist
      (tubeAxisMidpoint (S.coarse.tubes k.1))
      (tubeAxisMidpoint (D.family.tubes i)) ≤ 3 * (rho : Real) := by
    simpa only [dist_comm] using
      dist_tubeAxisMidpoint_le_three_mul_of_axis_subset_carrier
        (D.family.tubes i) (S.coarse.tubes k.1) haxis
  have hchildMidMem : tubeAxisMidpoint (D.family.tubes i) ∈
      (D.family.tubes i).carrier := by
    apply (D.family.tubes i).axis_subset_carrier
    exact (D.family.tubes i).axis.mem_carrier_of_mem_Icc (by norm_num)
  have hchildMidBall : tubeAxisMidpoint (D.family.tubes i) ∈
      Metric.closedBall (0 : Space) 1 :=
    hD.contained_in_unit_ball i hchildMidMem
  intro y hy
  change y ∈ (S.coarse.tubes k.1).carrier at hy
  have hyMid : dist y (tubeAxisMidpoint (S.coarse.tubes k.1)) ≤
      (2 : Real)⁻¹ + (rho : Real) :=
    dist_midpoint_le_half_add_radius (S.coarse.tubes k.1) hy
  have hchildNorm : dist (tubeAxisMidpoint (D.family.tubes i)) 0 ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hchildMidBall
  have hrhoReal : (rho : Real) ≤ (1 : Real) / 16 := by
    exact_mod_cast hrho
  rw [Metric.mem_closedBall]
  calc
    dist y 0 ≤
        dist y (tubeAxisMidpoint (S.coarse.tubes k.1)) +
          dist (tubeAxisMidpoint (S.coarse.tubes k.1))
            (tubeAxisMidpoint (D.family.tubes i)) +
          dist (tubeAxisMidpoint (D.family.tubes i)) 0 :=
      dist_triangle4 _ _ _ _
    _ ≤ ((2 : Real)⁻¹ + (rho : Real)) + 3 * (rho : Real) + 1 := by
      gcongr
    _ ≤ 2 := by nlinarith

#print axioms dist_tubeAxisMidpoint_le_three_mul_of_axis_subset_carrier
#print axioms activeCoarseFamily_body_subset_closedBall_two

end
end Family8StickyActiveCoarseB2SupportV5
