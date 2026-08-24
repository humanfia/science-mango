import FamilyStickyCinematicL32WZL3UniformTubeSourceV1
import FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32WZL3FixedVerticalChartAdapterV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1

noncomputable section

/-!
# Transport of the original `L_3` chart to actual ambient indices

The only set-theoretic input here is that the later ambient family is a
subfamily of the original finite source.  The fixed vertical inequality is
then supplied by the `L_3` provenance field and not assumed again at the PYZ
stage.
-/

theorem source_subset_fixedVerticalChartIndices
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota) :
    S.source ⊆ fixedVerticalChartIndices S.family S.source := by
  intro i hi
  rw [mem_fixedVerticalChartIndices_iff]
  exact ⟨hi, S.source_direction_final_half i hi⟩

theorem ambient_subset_fixedVerticalChartIndices
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (ambient : Finset iota) (hambient : ambient ⊆ S.source) :
    ambient ⊆ fixedVerticalChartIndices S.family S.source := by
  exact Finset.Subset.trans hambient
    (source_subset_fixedVerticalChartIndices S)

theorem ambient_direction_final_half
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (ambient : Finset iota) (hambient : ambient ⊆ S.source) :
    ∀ i, i ∈ ambient →
      (1 / 2 : Real) ≤ |(S.family.tubes i).axis.direction 2| := by
  exact S.direction_final_half_of_mem_of_subset ambient hambient

end
end FamilyStickyCinematicL32WZL3FixedVerticalChartAdapterV1
