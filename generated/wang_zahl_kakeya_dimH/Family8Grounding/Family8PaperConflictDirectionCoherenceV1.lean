import Family8Grounding.Family8Def212ConvexWolffAtEveryScaleV2
import Family8Grounding.Family8CommonPointTubePackingV1
import FamilyStickyGrounding.FamilyStickyTubeParentDirectionCoherenceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal

namespace Family8PaperConflictDirectionCoherenceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8CommonPointTubePackingV1
open FamilyStickyTubeParentDirectionCoherenceV1

noncomputable section

/-!
# Scale-independent direction coherence from full two-fold containment

Full central dilation is not the repository's radial `twoTube`, so the old
common-container endpoint lemma does not apply.  Instead, halve the two
endpoints of the contained unit segment about the container midpoint.  The
resulting segment has length `1/2` and lies in the original container tube.
Approximating its endpoints by the container axis forces the two directions
to be `O(delta)` close up to reversal.
-/

/-- Halving a point of the full two-fold dilation about its center returns
a genuine point of the original tube. -/
theorem half_center_mem_carrier_of_mem_twoFold
    {delta : NNReal} (T : Tube delta) {x : Space}
    (hx : x ∈ twoFoldTubeCarrier T) :
    tubeCenter T + (2 : Real)⁻¹ • (x - tubeCenter T) ∈ T.carrier := by
  obtain ⟨y, hy, hxy⟩ := hx
  have heq :
      tubeCenter T + (2 : Real)⁻¹ • (x - tubeCenter T) = y := by
    rw [← hxy]
    module
  rwa [heq]

/-- The half-scaled axis chord of a tube contained in a full two-fold
dilation is within `2 delta` of a scalar multiple of the container axis. -/
theorem exists_half_direction_chord_close_of_carrier_subset_twoFold
    {delta : NNReal} (T U : Tube delta)
    (hTU : T.carrier ⊆ twoFoldTubeCarrier U) :
    ∃ s : Real, s ∈ Set.Icc (-1 : Real) 1 ∧
      ‖(2 : Real)⁻¹ • T.axis.direction - s • U.axis.direction‖ ≤
        2 * (delta : Real) := by
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
    constructor <;> dsimp only [s] <;> linarith [ht0.1, ht0.2, ht1.1, ht1.2]
  have hyChord : y1 - y0 = (2 : Real)⁻¹ • T.axis.direction := by
    simp only [y0, y1, UnitSegment.endpoint]
    module
  have hqChord : q1 - q0 = s • U.axis.direction := by
    simp only [q0, q1, s]
    module
  have hy0q0 : ‖y0 - q0‖ ≤ (delta : Real) := by
    simpa only [q0, dist_eq_norm] using hdist0
  have hy1q1 : ‖y1 - q1‖ ≤ (delta : Real) := by
    simpa only [q1, dist_eq_norm] using hdist1
  refine ⟨s, hs, ?_⟩
  rw [← hyChord, ← hqChord]
  have hrewrite : (y1 - y0) - (q1 - q0) =
      (y1 - q1) - (y0 - q0) := by module
  rw [hrewrite]
  calc
    ‖(y1 - q1) - (y0 - q0)‖ ≤
        ‖y1 - q1‖ + ‖y0 - q0‖ := norm_sub_le _ _
    _ ≤ (delta : Real) + (delta : Real) := add_le_add hy1q1 hy0q0
    _ = 2 * (delta : Real) := by ring

/-- A half-unit chord close to a scalar multiple of another unit direction
forces projective direction closeness. -/
theorem unorientedDirectionClose_eight_mul_of_half_chord_close
    {v w : Space} {delta s : Real}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hclose : ‖(2 : Real)⁻¹ • v - s • w‖ ≤ 2 * delta) :
    ‖v - w‖ ≤ 8 * delta ∨ ‖v + w‖ ≤ 8 * delta := by
  have hnormHalf : ‖(2 : Real)⁻¹ • v‖ = (2 : Real)⁻¹ := by
    rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
  have hnormS : ‖s • w‖ = |s| := by
    rw [norm_smul, hw, mul_one, Real.norm_eq_abs]
  have hsAbs : abs ((2 : Real)⁻¹ - |s|) ≤ 2 * delta := by
    rw [← hnormHalf, ← hnormS]
    exact (abs_norm_sub_norm_le _ _).trans hclose
  by_cases hs : 0 ≤ s
  · left
    have hsNear : |s - (2 : Real)⁻¹| ≤ 2 * delta := by
      rw [abs_sub_comm, abs_of_nonneg hs] at hsAbs
      exact hsAbs
    have hhalf :
        ‖(2 : Real)⁻¹ • (v - w)‖ ≤ 4 * delta := by
      calc
        ‖(2 : Real)⁻¹ • (v - w)‖ =
            ‖((2 : Real)⁻¹ • v - s • w) +
              (s - (2 : Real)⁻¹) • w‖ := by
          congr 1
          module
        _ ≤ ‖(2 : Real)⁻¹ • v - s • w‖ +
            ‖(s - (2 : Real)⁻¹) • w‖ := norm_add_le _ _
        _ = ‖(2 : Real)⁻¹ • v - s • w‖ +
            |s - (2 : Real)⁻¹| := by
          rw [norm_smul, hw, mul_one, Real.norm_eq_abs]
        _ ≤ 2 * delta + 2 * delta := add_le_add hclose hsNear
        _ = 4 * delta := by ring
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : Real) ≤ (2 : Real)⁻¹)] at hhalf
    nlinarith
  · right
    have hsNonpos : s ≤ 0 := le_of_not_ge hs
    have hsNear : |s + (2 : Real)⁻¹| ≤ 2 * delta := by
      rw [abs_of_nonpos hsNonpos] at hsAbs
      simpa only [sub_neg_eq_add, add_comm] using hsAbs
    have hhalf :
        ‖(2 : Real)⁻¹ • (v + w)‖ ≤ 4 * delta := by
      calc
        ‖(2 : Real)⁻¹ • (v + w)‖ =
            ‖((2 : Real)⁻¹ • v - s • w) +
              (s + (2 : Real)⁻¹) • w‖ := by
          congr 1
          module
        _ ≤ ‖(2 : Real)⁻¹ • v - s • w‖ +
            ‖(s + (2 : Real)⁻¹) • w‖ := norm_add_le _ _
        _ = ‖(2 : Real)⁻¹ • v - s • w‖ +
            |s + (2 : Real)⁻¹| := by
          rw [norm_smul, hw, mul_one, Real.norm_eq_abs]
        _ ≤ 2 * delta + 2 * delta := add_le_add hclose hsNear
        _ = 4 * delta := by ring
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : Real) ≤ (2 : Real)⁻¹)] at hhalf
    nlinarith

/-- Full two-fold containment gives scale-independent unoriented direction
coherence with the explicit constant eight. -/
theorem unorientedDirectionClose_eight_mul_of_carrier_subset_twoFold
    {delta : NNReal} (T U : Tube delta)
    (hTU : T.carrier ⊆ twoFoldTubeCarrier U) :
    UnorientedDirectionClose T.axis U.axis (8 * (delta : Real)) := by
  obtain ⟨s, _hs, hclose⟩ :=
    exists_half_direction_chord_close_of_carrier_subset_twoFold T U hTU
  exact unorientedDirectionClose_eight_mul_of_half_chord_close
    T.axis.norm_direction U.axis.norm_direction hclose

/-- Either orientation of a paper conflict gives the same symmetric
unoriented direction bound. -/
theorem unorientedDirectionClose_eight_mul_of_paperConflict
    {delta : NNReal} {T U : Tube delta}
    (hconflict :
      T.carrier ⊆ twoFoldTubeCarrier U ∨
        U.carrier ⊆ twoFoldTubeCarrier T) :
    UnorientedDirectionClose T.axis U.axis (8 * (delta : Real)) := by
  rcases hconflict with hTU | hUT
  · exact unorientedDirectionClose_eight_mul_of_carrier_subset_twoFold T U hTU
  · exact (unorientedDirectionClose_eight_mul_of_carrier_subset_twoFold
      U T hUT).symm

#print axioms half_center_mem_carrier_of_mem_twoFold
#print axioms exists_half_direction_chord_close_of_carrier_subset_twoFold
#print axioms unorientedDirectionClose_eight_mul_of_half_chord_close
#print axioms unorientedDirectionClose_eight_mul_of_carrier_subset_twoFold
#print axioms unorientedDirectionClose_eight_mul_of_paperConflict

end

end Family8PaperConflictDirectionCoherenceV1
