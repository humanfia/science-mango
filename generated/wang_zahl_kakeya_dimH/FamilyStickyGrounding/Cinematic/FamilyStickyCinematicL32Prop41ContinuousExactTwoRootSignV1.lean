import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41ContinuousExactTwoRootSignV1

/-!
# Strict sign between two consecutive roots

A continuous real function that has no zero in an open interval has one
strict sign throughout that interval.  This is the scalar bridge turning the
actual two-root pseudo-circle input into a literal side-polarity statement.
-/

/-- A continuous function with no interior zero is everywhere positive or
everywhere negative between the endpoints. -/
theorem strict_sign_dichotomy_of_continuousOn_of_ne_zero_Ioo
    (h : Real -> Real) {A B : Real} (hAB : A < B)
    (hcontinuous : ContinuousOn h (Icc A B))
    (hnoRoot : forall theta, theta ∈ Ioo A B -> h theta ≠ 0) :
    (forall theta, theta ∈ Ioo A B -> 0 < h theta) ∨
      (forall theta, theta ∈ Ioo A B -> h theta < 0) := by
  let mid := (A + B) / 2
  have hmid : mid ∈ Ioo A B := by
    dsimp [mid]
    constructor <;> linarith
  have hmidNe : h mid ≠ 0 := hnoRoot mid hmid
  by_cases hmidPos : 0 < h mid
  · left
    intro theta htheta
    by_contra hnotPos
    have hthetaNonpos : h theta <= 0 := le_of_not_gt hnotPos
    rcases le_total theta mid with hthetaMid | hmidTheta
    · have hsub : Icc theta mid ⊆ Icc A B :=
        Icc_subset_Icc htheta.1.le hmid.2.le
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hthetaMid
        (hcontinuous.mono hsub)
        (show (0 : Real) ∈ Icc (h theta) (h mid) from
          ⟨hthetaNonpos, hmidPos.le⟩)
      exact hnoRoot z
        ⟨htheta.1.trans_le hz.1, hz.2.trans_lt hmid.2⟩ hz0
    · have hsub : Icc mid theta ⊆ Icc A B :=
        Icc_subset_Icc hmid.1.le htheta.2.le
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hmidTheta
        (hcontinuous.mono hsub)
        (show (0 : Real) ∈ Icc (h theta) (h mid) from
          ⟨hthetaNonpos, hmidPos.le⟩)
      exact hnoRoot z
        ⟨hmid.1.trans_le hz.1, hz.2.trans_lt htheta.2⟩ hz0
  · right
    have hmidNeg : h mid < 0 := lt_of_le_of_ne
      (le_of_not_gt hmidPos) hmidNe
    intro theta htheta
    by_contra hnotNeg
    have hthetaNonneg : 0 <= h theta := le_of_not_gt hnotNeg
    rcases le_total theta mid with hthetaMid | hmidTheta
    · have hsub : Icc theta mid ⊆ Icc A B :=
        Icc_subset_Icc htheta.1.le hmid.2.le
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hthetaMid
        (hcontinuous.mono hsub)
        (show (0 : Real) ∈ Icc (h mid) (h theta) from
          ⟨hmidNeg.le, hthetaNonneg⟩)
      exact hnoRoot z
        ⟨htheta.1.trans_le hz.1, hz.2.trans_lt hmid.2⟩ hz0
    · have hsub : Icc mid theta ⊆ Icc A B :=
        Icc_subset_Icc hmid.1.le htheta.2.le
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hmidTheta
        (hcontinuous.mono hsub)
        (show (0 : Real) ∈ Icc (h mid) (h theta) from
          ⟨hmidNeg.le, hthetaNonneg⟩)
      exact hnoRoot z
        ⟨hmid.1.trans_le hz.1, hz.2.trans_lt htheta.2⟩ hz0

#print axioms strict_sign_dichotomy_of_continuousOn_of_ne_zero_Ioo

end FamilyStickyCinematicL32Prop41ContinuousExactTwoRootSignV1
