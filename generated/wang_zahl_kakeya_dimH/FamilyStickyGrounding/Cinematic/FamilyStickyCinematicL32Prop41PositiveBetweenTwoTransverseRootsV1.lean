import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ContinuousTransverseRootParityV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41PositiveBetweenTwoTransverseRootsV1

open FamilyStickyCinematicL32Prop41ContinuousTransverseRootParityV1

/-!
# Exact positive interval between two transverse roots

For a continuous scalar function whose only roots on a compact interval are
two transverse roots, positivity between them characterizes the open interval.
The proof uses the already established odd-parity theorem on each truncated
interval, rather than assuming a global sign diagram.
-/

theorem mem_Ioo_iff_pos_of_exact_two_transverse_roots
    (h : Real -> Real) {A B left right : Real}
    (hAleft : A < left) (hlr : left < right) (hrightB : right < B)
    (hcontinuous : ContinuousOn h (Icc A B))
    (hroots : {theta | theta ∈ Icc A B ∧ h theta = 0} =
      ({left, right} : Set Real))
    (hpositive : forall theta, theta ∈ Ioo left right -> 0 < h theta)
    (htransverse : forall theta, theta ∈ Icc A B -> h theta = 0 ->
      exists derivative : Real,
        HasDerivAt h derivative theta ∧ derivative ≠ 0)
    {theta : Real} (htheta : theta ∈ Icc A B) :
    theta ∈ Ioo left right ↔ 0 < h theta := by
  constructor
  · exact hpositive theta
  · intro hthetaPos
    by_contra hthetaNot
    have houtside : theta <= left ∨ right <= theta := by
      simpa only [mem_Ioo, not_and_or, not_lt] using hthetaNot
    let mid : Real := (left + right) / 2
    have hleftMid : left < mid := by
      dsimp [mid]
      linarith
    have hmidRight : mid < right := by
      dsimp [mid]
      linarith
    have hmidIoo : mid ∈ Ioo left right := ⟨hleftMid, hmidRight⟩
    have hmidPos : 0 < h mid := hpositive mid hmidIoo
    rcases houtside with hthetaLeft | hrightTheta
    · by_cases hthetaEq : theta = left
      · subst theta
        have hleftRoot : h left = 0 := by
          have hmem : left ∈ ({left, right} : Set Real) := by simp
          rw [← hroots] at hmem
          exact hmem.2
        linarith
      · have hthetaLt : theta < left := lt_of_le_of_ne hthetaLeft hthetaEq
        have hthetaMid : theta < mid := hthetaLt.trans hleftMid
        have hthetaNe : h theta ≠ 0 := by
          intro hzero
          have hmem : theta ∈ ({left, right} : Set Real) := by
            rw [← hroots]
            exact ⟨htheta, hzero⟩
          rcases hmem with hEq | hEq
          · exact hthetaEq hEq
          · linarith
        have hrestricted :
            {z | z ∈ Icc theta mid ∧ h z = 0} = ({left} : Set Real) := by
          ext z
          constructor
          · rintro ⟨hzInterval, hzZero⟩
            have hzGlobal : z ∈ ({left, right} : Set Real) := by
              rw [← hroots]
              exact ⟨⟨htheta.1.trans hzInterval.1,
                hzInterval.2.trans hmidRight.le |>.trans hrightB.le⟩, hzZero⟩
            rcases hzGlobal with hzLeft | hzRight
            · exact hzLeft
            · subst z
              exfalso
              linarith [hzInterval.2]
          · intro hz
            have hzEq : z = left := by simpa using hz
            subst z
            exact ⟨⟨hthetaLt.le, hleftMid.le⟩, by
              have hmem : left ∈ ({left, right} : Set Real) := by simp
              rw [← hroots] at hmem
              exact hmem.2⟩
        have hsub : Icc theta mid ⊆ Icc A B :=
          Icc_subset_Icc htheta.1
            (hmidRight.le.trans hrightB.le)
        have hprod := endpoint_product_neg_of_unique_transverse_root
          h hthetaMid (hcontinuous.mono hsub) hthetaNe (ne_of_gt hmidPos)
          (by rw [hrestricted, ncard_singleton])
          (fun z hz hzZero => htransverse z (hsub hz) hzZero)
        nlinarith
    · by_cases hthetaEq : theta = right
      · subst theta
        have hrightRoot : h right = 0 := by
          have hmem : right ∈ ({left, right} : Set Real) := by simp
          rw [← hroots] at hmem
          exact hmem.2
        linarith
      · have hrightLt : right < theta := lt_of_le_of_ne hrightTheta (Ne.symm hthetaEq)
        have hmidTheta : mid < theta := hmidRight.trans hrightLt
        have hthetaNe : h theta ≠ 0 := by
          intro hzero
          have hmem : theta ∈ ({left, right} : Set Real) := by
            rw [← hroots]
            exact ⟨htheta, hzero⟩
          rcases hmem with hEq | hEq
          · linarith
          · exact hthetaEq hEq
        have hrestricted :
            {z | z ∈ Icc mid theta ∧ h z = 0} = ({right} : Set Real) := by
          ext z
          constructor
          · rintro ⟨hzInterval, hzZero⟩
            have hzGlobal : z ∈ ({left, right} : Set Real) := by
              rw [← hroots]
              exact ⟨⟨hAleft.le.trans hleftMid.le |>.trans hzInterval.1,
                hzInterval.2.trans htheta.2⟩, hzZero⟩
            rcases hzGlobal with hzLeft | hzRight
            · subst z
              exfalso
              linarith [hzInterval.1]
            · exact hzRight
          · intro hz
            have hzEq : z = right := by simpa using hz
            subst z
            exact ⟨⟨hmidRight.le, hrightLt.le⟩, by
              have hmem : right ∈ ({left, right} : Set Real) := by simp
              rw [← hroots] at hmem
              exact hmem.2⟩
        have hsub : Icc mid theta ⊆ Icc A B :=
          Icc_subset_Icc
            (hAleft.le.trans hleftMid.le) htheta.2
        have hprod := endpoint_product_neg_of_unique_transverse_root
          h hmidTheta (hcontinuous.mono hsub) (ne_of_gt hmidPos) hthetaNe
          (by rw [hrestricted, ncard_singleton])
          (fun z hz hzZero => htransverse z (hsub hz) hzZero)
        nlinarith

#print axioms mem_Ioo_iff_pos_of_exact_two_transverse_roots

end FamilyStickyCinematicL32Prop41PositiveBetweenTwoTransverseRootsV1
