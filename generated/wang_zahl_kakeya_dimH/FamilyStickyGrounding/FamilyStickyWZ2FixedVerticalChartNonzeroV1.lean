import FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1

set_option autoImplicit false

namespace FamilyStickyWZ2FixedVerticalChartNonzeroV1

open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity

noncomputable section

/-!
# Nonzero WZ2 height coordinate from the literal fixed chart

This is the minimal adapter between the finite fixed-vertical-chart selection
and the denominator premise in the WZ2 height parametrization. It uses only
membership in the actual filtered `Finset`; no tube-containment or projection
conclusion is supplied as an input.
-/

/-- Membership in the selected fixed chart rules out a zero final direction
coordinate. -/
theorem direction_two_ne_zero_of_mem_fixedVerticalChartIndices
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (source : Finset iota)
    {i : iota} (hi : i ∈ fixedVerticalChartIndices fine source) :
    (fine.tubes i).axis.direction 2 ≠ 0 := by
  have hhalf :=
    vertical_half_of_mem_fixedVerticalChartIndices fine source hi
  have hpositive : 0 < |(fine.tubes i).axis.direction 2| := by
    exact lt_of_lt_of_le (by norm_num) hhalf
  exact abs_pos.mp hpositive

#print axioms direction_two_ne_zero_of_mem_fixedVerticalChartIndices

end

end FamilyStickyWZ2FixedVerticalChartNonzeroV1
