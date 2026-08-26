import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41AlternatingSignThreeRootsV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41Shift3TwoRootsV1

open FamilyStickyCinematicL32Prop41AlternatingSignThreeRootsV1

/-!
# Two roots from one of three vertical shifts

Suppose the endpoint values of a continuous function have the same strict
sign, are farther than `s` from zero, and an interior value has absolute
value below `s`.  Shifting by `-s` in the positive-endpoint case or by `s`
in the negative-endpoint case preserves the endpoint sign and reverses the
sign at the interior point.  The intermediate value theorem then gives one
root on each side.

No root, root-count, or transversality premise is used.
-/

/-- One of the shifts `eta * s`, with `eta` in `{-1, 0, 1}`, preserves the
strict common endpoint sign and creates roots on both sides of the selected
interior parameter. -/
theorem exists_shift3_two_sided_roots
    (h : Real -> Real) {A B theta0 s : Real}
    (hcontinuous : ContinuousOn h (Icc A B))
    (hATheta : A < theta0) (hThetaB : theta0 < B)
    (_hs : 0 < s)
    (hcenter : |h theta0| < s)
    (hAfar : s < |h A|) (hBfar : s < |h B|)
    (hsame : 0 < h A * h B) :
    exists eta thetaLeft thetaRight : Real,
      eta ∈ ({(-1 : Real), 0, 1} : Set Real) ∧
      0 < (h A + eta * s) * (h B + eta * s) ∧
      thetaLeft ∈ Ioo A theta0 ∧
      h thetaLeft + eta * s = 0 ∧
      thetaRight ∈ Ioo theta0 B ∧
      h thetaRight + eta * s = 0 := by
  have hleftSubset : Icc A theta0 ⊆ Icc A B :=
    Icc_subset_Icc le_rfl hThetaB.le
  have hrightSubset : Icc theta0 B ⊆ Icc A B :=
    Icc_subset_Icc hATheta.le le_rfl
  have hcenterBounds : -s < h theta0 ∧ h theta0 < s :=
    (abs_lt.mp hcenter)
  rcases (mul_pos_iff.mp hsame) with hpositive | hnegative
  · have hAfar' : s < h A := by
      simpa [abs_of_pos hpositive.1] using hAfar
    have hBfar' : s < h B := by
      simpa [abs_of_pos hpositive.2] using hBfar
    have hshiftA : 0 < h A - s := by linarith [_hs]
    have hshiftB : 0 < h B - s := by linarith
    have hshiftCenter : h theta0 - s < 0 := by linarith
    have hshiftContinuous :
        ContinuousOn (fun theta => h theta - s) (Icc A B) :=
      hcontinuous.sub continuousOn_const
    obtain ⟨thetaLeft, hthetaLeft, hrootLeft⟩ :=
      exists_root_Ioo_of_strict_sign_change
        (fun theta => h theta - s) hATheta
        (hshiftContinuous.mono hleftSubset)
        (Or.inr ⟨hshiftCenter, hshiftA⟩)
    obtain ⟨thetaRight, hthetaRight, hrootRight⟩ :=
      exists_root_Ioo_of_strict_sign_change
        (fun theta => h theta - s) hThetaB
        (hshiftContinuous.mono hrightSubset)
        (Or.inl ⟨hshiftCenter, hshiftB⟩)
    have hendpoints :
        0 < (h A + (-1 : Real) * s) * (h B + (-1 : Real) * s) := by
      simpa [sub_eq_add_neg] using mul_pos hshiftA hshiftB
    refine ⟨-1, thetaLeft, thetaRight, by norm_num, hendpoints,
      hthetaLeft, ?_, hthetaRight, ?_⟩
    · simpa [sub_eq_add_neg] using hrootLeft
    · simpa [sub_eq_add_neg] using hrootRight
  · have hAfar' : s < -h A := by
      simpa [abs_of_neg hnegative.1] using hAfar
    have hBfar' : s < -h B := by
      simpa [abs_of_neg hnegative.2] using hBfar
    have hshiftA : h A + s < 0 := by linarith
    have hshiftB : h B + s < 0 := by linarith
    have hshiftCenter : 0 < h theta0 + s := by linarith
    have hshiftContinuous :
        ContinuousOn (fun theta => h theta + s) (Icc A B) :=
      hcontinuous.add continuousOn_const
    obtain ⟨thetaLeft, hthetaLeft, hrootLeft⟩ :=
      exists_root_Ioo_of_strict_sign_change
        (fun theta => h theta + s) hATheta
        (hshiftContinuous.mono hleftSubset)
        (Or.inl ⟨hshiftA, hshiftCenter⟩)
    obtain ⟨thetaRight, hthetaRight, hrootRight⟩ :=
      exists_root_Ioo_of_strict_sign_change
        (fun theta => h theta + s) hThetaB
        (hshiftContinuous.mono hrightSubset)
        (Or.inr ⟨hshiftB, hshiftCenter⟩)
    have hendpoints :
        0 < (h A + (1 : Real) * s) * (h B + (1 : Real) * s) := by
      simpa using mul_pos_of_neg_of_neg hshiftA hshiftB
    refine ⟨1, thetaLeft, thetaRight, by norm_num, hendpoints,
      hthetaLeft, ?_, hthetaRight, ?_⟩
    · simpa using hrootLeft
    · simpa using hrootRight

#print axioms exists_shift3_two_sided_roots

end FamilyStickyCinematicL32Prop41Shift3TwoRootsV1
