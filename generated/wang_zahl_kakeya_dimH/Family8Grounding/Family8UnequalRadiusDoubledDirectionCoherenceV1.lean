import Family8Grounding.Family8PaperConflictDirectionCoherenceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal

namespace Family8UnequalRadiusDoubledDirectionCoherenceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8CommonPointTubePackingV1
open Family8PaperConflictDirectionCoherenceV1
open FamilyStickyTubeParentDirectionCoherenceV1

noncomputable section

/-!
# Direction coherence for unequal-radius doubled containment

Only the radius of the containing tube enters the half-chord approximation.
This removes the artificial equal-radius restriction from the existing paper
conflict direction lemma.
-/

/-- A half-scaled axis chord of a `delta`-tube contained in the full doubled
carrier of a `rho`-tube is within `2 rho` of the parent direction line. -/
theorem exists_half_direction_chord_close_of_unequal_carrier_subset_twoFold
    {delta rho : NNReal} (T : Tube delta) (U : Tube rho)
    (hTU : T.carrier ⊆ twoFoldTubeCarrier U) :
    ∃ s : Real, s ∈ Set.Icc (-1 : Real) 1 ∧
      ‖(2 : Real)⁻¹ • T.axis.direction - s • U.axis.direction‖ ≤
        2 * (rho : Real) := by
  let y0 : Space :=
    tubeCenter U + (2 : Real)⁻¹ • (T.axis.base - tubeCenter U)
  let y1 : Space :=
    tubeCenter U + (2 : Real)⁻¹ • (T.axis.endpoint - tubeCenter U)
  have hbase : T.axis.base ∈ T.carrier := by
    apply T.axis_subset_carrier
    simpa using (T.axis.mem_carrier_of_mem_Icc (t := 0) (by norm_num))
  have hend : T.axis.endpoint ∈ T.carrier := by
    apply T.axis_subset_carrier
    simpa [UnitSegment.endpoint] using
      (T.axis.mem_carrier_of_mem_Icc (t := 1) (by norm_num))
  have hy0 : y0 ∈ U.carrier := by
    exact half_center_mem_carrier_of_mem_twoFold U (hTU hbase)
  have hy1 : y1 ∈ U.carrier := by
    exact half_center_mem_carrier_of_mem_twoFold U (hTU hend)
  obtain ⟨t0, ht0, hdist0⟩ := exists_axis_parameter_dist_le_of_mem U hy0
  obtain ⟨t1, ht1, hdist1⟩ := exists_axis_parameter_dist_le_of_mem U hy1
  let q0 : Space := U.axis.base + t0 • U.axis.direction
  let q1 : Space := U.axis.base + t1 • U.axis.direction
  let s : Real := t1 - t0
  have hs : s ∈ Set.Icc (-1 : Real) 1 := by
    constructor <;> dsimp only [s] <;>
      linarith [ht0.1, ht0.2, ht1.1, ht1.2]
  have hyChord : y1 - y0 = (2 : Real)⁻¹ • T.axis.direction := by
    simp only [y0, y1, UnitSegment.endpoint]
    module
  have hqChord : q1 - q0 = s • U.axis.direction := by
    simp only [q0, q1, s]
    module
  have hy0q0 : ‖y0 - q0‖ ≤ (rho : Real) := by
    simpa only [q0, dist_eq_norm] using hdist0
  have hy1q1 : ‖y1 - q1‖ ≤ (rho : Real) := by
    simpa only [q1, dist_eq_norm] using hdist1
  refine ⟨s, hs, ?_⟩
  rw [← hyChord, ← hqChord]
  have hrewrite : (y1 - y0) - (q1 - q0) =
      (y1 - q1) - (y0 - q0) := by module
  rw [hrewrite]
  calc
    ‖(y1 - q1) - (y0 - q0)‖ ≤
        ‖y1 - q1‖ + ‖y0 - q0‖ := norm_sub_le _ _
    _ ≤ (rho : Real) + (rho : Real) := add_le_add hy1q1 hy0q0
    _ = 2 * (rho : Real) := by ring

/-- Unequal-radius full doubled containment gives projective direction
coherence at the containing radius. -/
theorem unorientedDirectionClose_eight_mul_of_unequal_carrier_subset_twoFold
    {delta rho : NNReal} (T : Tube delta) (U : Tube rho)
    (hTU : T.carrier ⊆ twoFoldTubeCarrier U) :
    UnorientedDirectionClose T.axis U.axis (8 * (rho : Real)) := by
  obtain ⟨s, _hs, hclose⟩ :=
    exists_half_direction_chord_close_of_unequal_carrier_subset_twoFold T U hTU
  exact unorientedDirectionClose_eight_mul_of_half_chord_close
    T.axis.norm_direction U.axis.norm_direction hclose

#print axioms exists_half_direction_chord_close_of_unequal_carrier_subset_twoFold
#print axioms unorientedDirectionClose_eight_mul_of_unequal_carrier_subset_twoFold

end
end Family8UnequalRadiusDoubledDirectionCoherenceV1
