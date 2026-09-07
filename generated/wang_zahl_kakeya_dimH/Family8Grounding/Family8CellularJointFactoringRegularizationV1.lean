import Family8Grounding.Family8CellularJointFactoringFiniteCoreV1
import Submission.Kakeya.Uniformity.Pigeonhole
import Mathlib.Tactic

/-!
# Two-stage finite regularization for cellular joint factoring

This module formalizes the finite REG1/R2 selection after a geometric
construction has supplied a parent--cell edge set.  First an edge-weight
label is selected by weighted pigeonhole.  Then a right-degree label is
selected, but the second label depends only on the cell coordinate.  Hence
the second selection retains every first-stage edge at any selected cell and
is right-saturated by construction.

The label functions and their finite ranges remain explicit inputs.  In
particular, this file does not claim that dyadic numeric labels, spatial
cells, or the initial positive edge graph have already been constructed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open scoped BigOperators ENNReal

namespace Family8CellularJointFactoringRegularizationV1

open Submission.Kakeya.Uniformity
open Family8CellularJointFactoringFiniteCoreV1

noncomputable section

/-- The `ENNReal` version of finite weighted pigeonhole.  Empty source
fibres are permitted. -/
theorem exists_large_weighted_fiber_ennreal
    {alpha label : Type*} [DecidableEq alpha] [DecidableEq label]
    [Fintype label] [Nonempty label]
    (s : Finset alpha) (bucket : alpha -> label) (weight : alpha -> ENNReal) :
    exists b : label,
      (∑ x ∈ s, weight x) <=
        Fintype.card label •
          (∑ x ∈ dyadicFiber s bucket b, weight x) := by
  classical
  let fiberWeight : label -> ENNReal := fun b =>
    ∑ x ∈ dyadicFiber s bucket b, weight x
  obtain ⟨b, _hb, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset label) fiberWeight
      (Finset.univ_nonempty : (Finset.univ : Finset label).Nonempty)
  refine ⟨b, ?_⟩
  calc
    (∑ x ∈ s, weight x) =
        ∑ b' ∈ (Finset.univ : Finset label), fiberWeight b' := by
      change (∑ x ∈ s, weight x) =
        ∑ b' ∈ (Finset.univ : Finset label),
          ∑ x ∈ s with bucket x = b', weight x
      exact (Finset.sum_fiberwise_of_maps_to
        (s := s) (t := (Finset.univ : Finset label)) (g := bucket)
        (fun x hx => Finset.mem_univ (bucket x)) weight).symm
    _ <= (Finset.univ : Finset label).card • fiberWeight b :=
      Finset.sum_le_card_nsmul (Finset.univ : Finset label) fiberWeight
        (fiberWeight b) (fun b' hb' => hmax b' hb')
    _ = Fintype.card label •
        (∑ x ∈ dyadicFiber s bucket b, weight x) := by
      simp [fiberWeight]

variable {parent cell weightLabel degreeLabel : Type*}
  [Fintype parent] [DecidableEq parent]
  [Fintype cell] [DecidableEq cell]
  [Fintype weightLabel] [DecidableEq weightLabel] [Nonempty weightLabel]
  [Fintype degreeLabel] [DecidableEq degreeLabel] [Nonempty degreeLabel]

/-- Output of the two finite selections.  Both edge subsets are definitionally
fibres of the supplied labels, and the final edge set is right-saturated in
the first one because its label depends only on the cell. -/
structure TwoStageRegularization
    (source : Finset (parent × cell))
    (omega : parent × cell -> ENNReal)
    (weightBucket : parent × cell -> weightLabel)
    (degreeBucket : cell -> degreeLabel) where
  selectedWeightLabel : weightLabel
  firstEdges : Finset (parent × cell)
  firstEdges_eq : firstEdges =
    dyadicFiber source weightBucket selectedWeightLabel
  selectedDegreeLabel : degreeLabel
  finalEdges : Finset (parent × cell)
  finalEdges_eq : finalEdges =
    dyadicFiber firstEdges (fun e => degreeBucket e.2) selectedDegreeLabel
  sourceWeight_le : edgeWeight source omega <=
    (Fintype.card weightLabel * Fintype.card degreeLabel) •
      edgeWeight finalEdges omega
  final_rightSaturated : IsRightSaturatedSubedge firstEdges finalEdges

namespace TwoStageRegularization

theorem firstEdges_subset_source
    {source : Finset (parent × cell)}
    {omega : parent × cell -> ENNReal}
    {weightBucket : parent × cell -> weightLabel}
    {degreeBucket : cell -> degreeLabel}
    (R : TwoStageRegularization source omega weightBucket degreeBucket) :
    R.firstEdges ⊆ source := by
  rw [R.firstEdges_eq]
  exact Finset.filter_subset _ _

theorem finalEdges_subset_source
    {source : Finset (parent × cell)}
    {omega : parent × cell -> ENNReal}
    {weightBucket : parent × cell -> weightLabel}
    {degreeBucket : cell -> degreeLabel}
    (R : TwoStageRegularization source omega weightBucket degreeBucket) :
    R.finalEdges ⊆ source :=
  R.final_rightSaturated.1.trans R.firstEdges_subset_source

theorem degreeBucket_eq_on_rightCells
    {source : Finset (parent × cell)}
    {omega : parent × cell -> ENNReal}
    {weightBucket : parent × cell -> weightLabel}
    {degreeBucket : cell -> degreeLabel}
    (R : TwoStageRegularization source omega weightBucket degreeBucket)
    {q : cell} (hq : q ∈ rightCells R.finalEdges) :
    degreeBucket q = R.selectedDegreeLabel := by
  obtain ⟨p, hpq⟩ := (mem_rightCells_iff R.finalEdges q).1 hq
  rw [R.finalEdges_eq] at hpq
  exact (mem_dyadicFiber _ _ _ _).1 hpq |>.2

/-- Any right-degree band certified by the selected cell label transfers to
the saturated final edge set with no change in right degree. -/
theorem hasRightDegreeBand
    {source : Finset (parent × cell)}
    {omega : parent × cell -> ENNReal}
    {weightBucket : parent × cell -> weightLabel}
    {degreeBucket : cell -> degreeLabel}
    (R : TwoStageRegularization source omega weightBucket degreeBucket)
    (d : Nat)
    (hband : ∀ q ∈ rightCells R.firstEdges,
      degreeBucket q = R.selectedDegreeLabel ->
        d <= rightDegree R.firstEdges q ∧
          rightDegree R.firstEdges q < 2 * d) :
    HasRightDegreeBand R.finalEdges (rightCells R.finalEdges) d := by
  apply R.final_rightSaturated.hasRightDegreeBand d
  intro q hq
  exact hband q (R.final_rightSaturated.rightCells_subset hq)
    (R.degreeBucket_eq_on_rightCells hq)

end TwoStageRegularization

/-- Two successive finite weighted pigeonholes produce a right-saturated
final edge set with the product of the two explicit finite losses. -/
theorem exists_twoStageRegularization
    (source : Finset (parent × cell))
    (omega : parent × cell -> ENNReal)
    (weightBucket : parent × cell -> weightLabel)
    (degreeBucket : cell -> degreeLabel) :
    Nonempty (TwoStageRegularization source omega weightBucket degreeBucket) := by
  classical
  obtain ⟨b, hb⟩ :=
    exists_large_weighted_fiber_ennreal source weightBucket omega
  let first := dyadicFiber source weightBucket b
  obtain ⟨g, hg⟩ := exists_large_weighted_fiber_ennreal first
    (fun e => degreeBucket e.2) omega
  let final := dyadicFiber first (fun e => degreeBucket e.2) g
  have hweight : edgeWeight source omega <=
      (Fintype.card weightLabel * Fintype.card degreeLabel) •
        edgeWeight final omega := by
    calc
      edgeWeight source omega <=
          Fintype.card weightLabel • edgeWeight first omega := by
        simpa only [edgeWeight, first] using hb
      _ <= Fintype.card weightLabel •
          (Fintype.card degreeLabel • edgeWeight final omega) := by
        apply nsmul_le_nsmul_right
        simpa only [edgeWeight, final] using hg
      _ = (Fintype.card weightLabel * Fintype.card degreeLabel) •
          edgeWeight final omega := by
        simp only [nsmul_eq_mul, Nat.cast_mul]
        ring
  have hsaturated : IsRightSaturatedSubedge first final := by
    refine ⟨?_, ?_⟩
    · exact Finset.filter_subset _ _
    · intro p q hpq hq
      obtain ⟨p', hp'q⟩ := (mem_rightCells_iff final q).1 hq
      have hlabel : degreeBucket q = g := by
        exact (mem_dyadicFiber first (fun e => degreeBucket e.2) g
          (p', q)).1 hp'q |>.2
      exact (mem_dyadicFiber first (fun e => degreeBucket e.2) g
        (p, q)).2 ⟨hpq, hlabel⟩
  exact ⟨{
    selectedWeightLabel := b
    firstEdges := first
    firstEdges_eq := rfl
    selectedDegreeLabel := g
    finalEdges := final
    finalEdges_eq := rfl
    sourceWeight_le := hweight
    final_rightSaturated := hsaturated }⟩

#print axioms exists_large_weighted_fiber_ennreal
#print axioms TwoStageRegularization.firstEdges_subset_source
#print axioms TwoStageRegularization.finalEdges_subset_source
#print axioms TwoStageRegularization.degreeBucket_eq_on_rightCells
#print axioms TwoStageRegularization.hasRightDegreeBand
#print axioms exists_twoStageRegularization

end
end Family8CellularJointFactoringRegularizationV1
