import Family8Grounding.Family8FiniteRigidMotionOrthogonalPatternCatalogueV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalNetCapCoverV3

open LeanEval.Analysis.WangZahlKakeya
open Family8FiniteRigidMotionOrthogonalHaarV4
open Family8FiniteRigidMotionOrthogonalOrbitV3
open Family8FiniteRigidMotionUnitSpherePackingV3
open Family8FiniteRigidMotionOrthogonalTwoCapLawV2

noncomputable section

/-!
# Replacing arbitrary cap centres by the finite unit-sphere net

If two unit directions are within a distance s, then each unoriented two-cap
event of radius r around the first direction lies in the two-cap event of
radius r+s around the second.  The maximal sphere net supplies such a centre
with s equal to twice the mesh, eliminating circular dependence on directions
occurring in the sampled rotation catalogue.
-/

theorem orthogonalTwoCapEvent_subset_of_center_dist
    (u w c : Space) (r s : NNReal)
    (hwc : dist w c ≤ (s : Real)) :
    orthogonalTwoCapEvent u w r ⊆
      orthogonalTwoCapEvent u c (r + s) := by
  intro U hU
  rcases hU with hU | hU
  · apply Set.mem_union_left
    change dist (orthogonalOrbit u U) c < ((r + s : NNReal) : Real)
    have hnear :
        dist (orthogonalOrbit u U) w < (r : Real) := hU
    calc
      dist (orthogonalOrbit u U) c ≤
          dist (orthogonalOrbit u U) w + dist w c :=
        dist_triangle _ _ _
      _ < (r : Real) + (s : Real) :=
        add_lt_add_of_lt_of_le hnear hwc
      _ = ((r + s : NNReal) : Real) :=
        (NNReal.coe_add r s).symm
  · apply Set.mem_union_right
    change dist (orthogonalOrbit u U) (-c) <
      ((r + s : NNReal) : Real)
    have hnear :
        dist (orthogonalOrbit u U) (-w) < (r : Real) := hU
    have hneg : dist (-w) (-c) = dist w c := by
      exact dist_neg_neg w c
    calc
      dist (orthogonalOrbit u U) (-c) ≤
          dist (orthogonalOrbit u U) (-w) + dist (-w) (-c) :=
        dist_triangle _ _ _
      _ < (r : Real) + (s : Real) := by
        rw [hneg]
        exact add_lt_add_of_lt_of_le hnear hwc
      _ = ((r + s : NNReal) : Real) :=
        (NNReal.coe_add r s).symm

theorem exists_unitDirectionChoice_twoCap_cover
    (u w : Space) (hw : ‖w‖ = 1)
    (mesh : NNReal) (hmesh : 0 < mesh) (r : NNReal) :
    ∃ k : UnitDirectionChoice mesh hmesh,
      orthogonalTwoCapEvent u w r ⊆
        orthogonalTwoCapEvent u (k.1 : Space) (r + 2 * mesh) := by
  obtain ⟨k, hwk⟩ := unitDirectionChoice_cover mesh hmesh w hw
  have hwkReal :
      dist w (k.1 : Space) ≤ ((2 * mesh : NNReal) : Real) := by
    have hreal := ENNReal.toReal_mono ENNReal.coe_ne_top hwk
    simpa [edist_dist] using hreal
  exact ⟨k,
    orthogonalTwoCapEvent_subset_of_center_dist
      u w (k.1 : Space) r (2 * mesh) hwkReal⟩

#print axioms orthogonalTwoCapEvent_subset_of_center_dist
#print axioms exists_unitDirectionChoice_twoCap_cover

end
end Family8FiniteRigidMotionOrthogonalNetCapCoverV3
