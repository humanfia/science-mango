import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32SublevelIntervalV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32RolleBridgeV1
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Set.Card

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41StrictCurvatureOppositeEndpointRootsV1

open FamilyStickyCinematicL32SublevelIntervalV1
open FamilyStickyCinematicL32RolleBridgeV1

/-!
# Opposite endpoint signs under strict curvature

A nonvanishing continuous second derivative has one fixed sign.  If two
roots existed, Rolle would place a critical point between them.  Positive
curvature then forces the left endpoint value to be positive; negative
curvature forces the right endpoint value to be negative.  Both contradict
the stated endpoint orientation.  Thus the root carrier has `encard <= 1`.
-/

theorem strictCurvature_oppositeEndpoint_rootSet_subsingleton
    (h q r : Real -> Real) {A B kappa : Real}
    (hAB : A < B) (hkappa : 0 < kappa)
    (hleft : h A < 0) (hright : 0 < h B)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (q z) z)
    (hqDeriv : forall z, z ∈ Icc A B -> HasDerivAt q (r z) z)
    (hrContinuous : ContinuousOn r (Icc A B))
    (hcurvatureLower : forall z, z ∈ Icc A B -> kappa <= |r z|) :
    {z | z ∈ Icc A B ∧ h z = 0}.Subsingleton := by
  have hhContinuous : ContinuousOn h (Icc A B) :=
    HasDerivAt.continuousOn hderiv
  have hqContinuous : ContinuousOn q (Icc A B) :=
    HasDerivAt.continuousOn hqDeriv
  rcases continuous_fixed_sign_of_abs_lower_on_Icc r hAB.le hkappa
      hrContinuous hcurvatureLower with hrPositive | hrNegative
  · have hqStrict : StrictMonoOn q (Icc A B) := by
      apply strictMonoOn_of_hasDerivWithinAt_pos
        (convex_Icc A B) hqContinuous
      · intro z hz
        exact (hqDeriv z (interior_subset hz)).hasDerivWithinAt
      · intro z hz
        exact hkappa.trans_le (hrPositive z (interior_subset hz))
    intro x hx y hy
    by_contra hxy
    rcases lt_or_gt_of_ne hxy with hxylt | hyxlt
    · obtain ⟨c, hc, hc0⟩ :=
        exists_derivative_zero_between_zeros h q hxylt
          (fun z hz => hderiv z
            ⟨hx.1.1.trans hz.1, hz.2.trans hy.1.2⟩)
          hx.2 hy.2
      have hcOuter : c ∈ Icc A B :=
        ⟨hx.1.1.trans (le_of_lt hc.1),
          (le_of_lt hc.2).trans hy.1.2⟩
      have hAx : A < x := by
        refine lt_of_le_of_ne hx.1.1 ?_
        intro hAxEq
        have hzeroA : h A = 0 := (congrArg h hAxEq).trans hx.2
        linarith
      have hhAnti : StrictAntiOn h (Icc A x) := by
        apply strictAntiOn_of_hasDerivWithinAt_neg
          (convex_Icc A x) (hhContinuous.mono
            (Icc_subset_Icc le_rfl hx.1.2))
        · intro z hz
          have hzClosed : z ∈ Icc A x := interior_subset hz
          exact (hderiv z
            ⟨hzClosed.1, hzClosed.2.trans hx.1.2⟩).hasDerivWithinAt
        · intro z hz
          have hzClosed : z ∈ Icc A x := interior_subset hz
          have hzc : z < c := hzClosed.2.trans_lt hc.1
          have hqzc := hqStrict
            ⟨hzClosed.1, hzClosed.2.trans hx.1.2⟩ hcOuter hzc
          rw [hc0] at hqzc
          exact hqzc
      have hdecrease := hhAnti
        (left_mem_Icc.2 hAx.le) (right_mem_Icc.2 hAx.le) hAx
      rw [hx.2] at hdecrease
      linarith
    · obtain ⟨c, hc, hc0⟩ :=
        exists_derivative_zero_between_zeros h q hyxlt
          (fun z hz => hderiv z
            ⟨hy.1.1.trans hz.1, hz.2.trans hx.1.2⟩)
          hy.2 hx.2
      have hcOuter : c ∈ Icc A B :=
        ⟨hy.1.1.trans (le_of_lt hc.1),
          (le_of_lt hc.2).trans hx.1.2⟩
      have hAy : A < y := by
        refine lt_of_le_of_ne hy.1.1 ?_
        intro hAyEq
        have hzeroA : h A = 0 := (congrArg h hAyEq).trans hy.2
        linarith
      have hhAnti : StrictAntiOn h (Icc A y) := by
        apply strictAntiOn_of_hasDerivWithinAt_neg
          (convex_Icc A y) (hhContinuous.mono
            (Icc_subset_Icc le_rfl hy.1.2))
        · intro z hz
          have hzClosed : z ∈ Icc A y := interior_subset hz
          exact (hderiv z
            ⟨hzClosed.1, hzClosed.2.trans hy.1.2⟩).hasDerivWithinAt
        · intro z hz
          have hzClosed : z ∈ Icc A y := interior_subset hz
          have hzc : z < c := hzClosed.2.trans_lt hc.1
          have hqzc := hqStrict
            ⟨hzClosed.1, hzClosed.2.trans hy.1.2⟩ hcOuter hzc
          rw [hc0] at hqzc
          exact hqzc
      have hdecrease := hhAnti
        (left_mem_Icc.2 hAy.le) (right_mem_Icc.2 hAy.le) hAy
      rw [hy.2] at hdecrease
      linarith
  · have hqAnti : StrictAntiOn q (Icc A B) := by
      apply strictAntiOn_of_hasDerivWithinAt_neg
        (convex_Icc A B) hqContinuous
      · intro z hz
        exact (hqDeriv z (interior_subset hz)).hasDerivWithinAt
      · intro z hz
        have hzClosed : z ∈ Icc A B := interior_subset hz
        have := hrNegative z hzClosed
        linarith
    intro x hx y hy
    by_contra hxy
    rcases lt_or_gt_of_ne hxy with hxylt | hyxlt
    · obtain ⟨c, hc, hc0⟩ :=
        exists_derivative_zero_between_zeros h q hxylt
          (fun z hz => hderiv z
            ⟨hx.1.1.trans hz.1, hz.2.trans hy.1.2⟩)
          hx.2 hy.2
      have hcOuter : c ∈ Icc A B :=
        ⟨hx.1.1.trans (le_of_lt hc.1),
          (le_of_lt hc.2).trans hy.1.2⟩
      have hyB : y < B := by
        refine lt_of_le_of_ne hy.1.2 ?_
        intro hyBEq
        have hzeroB : h B = 0 := (congrArg h hyBEq).symm.trans hy.2
        linarith
      have hhAnti : StrictAntiOn h (Icc y B) := by
        apply strictAntiOn_of_hasDerivWithinAt_neg
          (convex_Icc y B) (hhContinuous.mono
            (Icc_subset_Icc hy.1.1 le_rfl))
        · intro z hz
          have hzClosed : z ∈ Icc y B := interior_subset hz
          exact (hderiv z
            ⟨hy.1.1.trans hzClosed.1, hzClosed.2⟩).hasDerivWithinAt
        · intro z hz
          have hzClosed : z ∈ Icc y B := interior_subset hz
          have hcz : c < z := hc.2.trans_le hzClosed.1
          have hqcz := hqAnti hcOuter
            ⟨hy.1.1.trans hzClosed.1, hzClosed.2⟩ hcz
          rw [hc0] at hqcz
          exact hqcz
      have hdecrease := hhAnti
        (left_mem_Icc.2 hyB.le) (right_mem_Icc.2 hyB.le) hyB
      rw [hy.2] at hdecrease
      linarith
    · obtain ⟨c, hc, hc0⟩ :=
        exists_derivative_zero_between_zeros h q hyxlt
          (fun z hz => hderiv z
            ⟨hy.1.1.trans hz.1, hz.2.trans hx.1.2⟩)
          hy.2 hx.2
      have hcOuter : c ∈ Icc A B :=
        ⟨hy.1.1.trans (le_of_lt hc.1),
          (le_of_lt hc.2).trans hx.1.2⟩
      have hxB : x < B := by
        refine lt_of_le_of_ne hx.1.2 ?_
        intro hxBEq
        have hzeroB : h B = 0 := (congrArg h hxBEq).symm.trans hx.2
        linarith
      have hhAnti : StrictAntiOn h (Icc x B) := by
        apply strictAntiOn_of_hasDerivWithinAt_neg
          (convex_Icc x B) (hhContinuous.mono
            (Icc_subset_Icc hx.1.1 le_rfl))
        · intro z hz
          have hzClosed : z ∈ Icc x B := interior_subset hz
          exact (hderiv z
            ⟨hx.1.1.trans hzClosed.1, hzClosed.2⟩).hasDerivWithinAt
        · intro z hz
          have hzClosed : z ∈ Icc x B := interior_subset hz
          have hcz : c < z := hc.2.trans_le hzClosed.1
          have hqcz := hqAnti hcOuter
            ⟨hx.1.1.trans hzClosed.1, hzClosed.2⟩ hcz
          rw [hc0] at hqcz
          exact hqcz
      have hdecrease := hhAnti
        (left_mem_Icc.2 hxB.le) (right_mem_Icc.2 hxB.le) hxB
      rw [hx.2] at hdecrease
      linarith

theorem strictCurvature_oppositeEndpoint_rootSet_encard_le_one
    (h q r : Real -> Real) {A B kappa : Real}
    (hAB : A < B) (hkappa : 0 < kappa)
    (hleft : h A < 0) (hright : 0 < h B)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (q z) z)
    (hqDeriv : forall z, z ∈ Icc A B -> HasDerivAt q (r z) z)
    (hrContinuous : ContinuousOn r (Icc A B))
    (hcurvatureLower : forall z, z ∈ Icc A B -> kappa <= |r z|) :
    {z | z ∈ Icc A B ∧ h z = 0}.encard <= 1 :=
  encard_le_one_iff_subsingleton.mpr
    (strictCurvature_oppositeEndpoint_rootSet_subsingleton
      h q r hAB hkappa hleft hright hderiv hqDeriv hrContinuous hcurvatureLower)

#print axioms strictCurvature_oppositeEndpoint_rootSet_subsingleton
#print axioms strictCurvature_oppositeEndpoint_rootSet_encard_le_one

end FamilyStickyCinematicL32Prop41StrictCurvatureOppositeEndpointRootsV1
