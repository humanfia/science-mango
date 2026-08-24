import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41GraphTransverseSignV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41ContinuousTransverseRootParityV1

open FamilyStickyCinematicL32Prop41GraphTransverseSignV1

/-!
# Parity of a finite transverse root set

A unique transverse root reverses the endpoint sign.  Consequently a
continuous function with equal nonzero endpoint signs and at most two
transverse roots has either zero or two roots.  This is the scalar parity
input needed before counting crossings of the explicit rectangular skirts.
-/

theorem endpoint_product_neg_of_unique_transverse_root
    (h : Real -> Real) {A B : Real} (_hAB : A < B)
    (hcontinuous : ContinuousOn h (Icc A B))
    (hAne : h A ≠ 0) (hBne : h B ≠ 0)
    (hunique : {theta | theta ∈ Icc A B ∧ h theta = 0}.ncard = 1)
    (htransverse : forall theta, theta ∈ Icc A B -> h theta = 0 ->
      exists derivative : Real,
        HasDerivAt h derivative theta ∧ derivative ≠ 0) :
    h A * h B < 0 := by
  obtain ⟨x, hxSet⟩ := Set.ncard_eq_one.mp hunique
  have hx : x ∈ Icc A B ∧ h x = 0 := by
    have : x ∈ ({x} : Set Real) := Set.mem_singleton x
    rwa [← hxSet] at this
  have hAx : A < x := by
    refine lt_of_le_of_ne hx.1.1 ?_
    intro hAxEq
    apply hAne
    simpa [hAxEq] using hx.2
  have hxB : x < B := by
    refine lt_of_le_of_ne hx.1.2 ?_
    intro hxBEq
    apply hBne
    simpa [← hxBEq] using hx.2
  obtain ⟨derivative, hderiv, hderivative⟩ :=
    htransverse x hx.1 hx.2
  obtain ⟨eta, heta, hlocal⟩ :=
    exists_radius_derivative_oriented_value_sign
      hx.2 hderiv hderivative
  let eps : Real := min (min (x - A) (B - x)) eta / 2
  have hspan : 0 < min (x - A) (B - x) := by
    rw [lt_min_iff]
    exact ⟨sub_pos.mpr hAx, sub_pos.mpr hxB⟩
  have hmin : 0 < min (min (x - A) (B - x)) eta := by
    rw [lt_min_iff]
    exact ⟨hspan, heta⟩
  have heps : 0 < eps := by
    exact div_pos hmin (by norm_num)
  have hepsLeft : eps < x - A := by
    have hle : min (min (x - A) (B - x)) eta <= x - A :=
      (min_le_left _ _).trans (min_le_left _ _)
    dsimp [eps]
    linarith
  have hepsRight : eps < B - x := by
    have hle : min (min (x - A) (B - x)) eta <= B - x :=
      (min_le_left _ _).trans (min_le_right _ _)
    dsimp [eps]
    linarith
  have hepsEta : eps < eta := by
    have hle : min (min (x - A) (B - x)) eta <= eta := min_le_right _ _
    dsimp [eps]
    linarith
  let leftPoint := x - eps
  let rightPoint := x + eps
  have hAleft : A < leftPoint := by dsimp [leftPoint]; linarith
  have hleftX : leftPoint < x := by dsimp [leftPoint]; linarith
  have hxRight : x < rightPoint := by dsimp [rightPoint]; linarith
  have hrightB : rightPoint < B := by dsimp [rightPoint]; linarith
  have hleftProd : derivative * h leftPoint < 0 := by
    have h := hlocal leftPoint (by linarith)
      (by simp only [leftPoint, sub_sub_cancel_left, abs_neg,
        abs_of_nonneg heps.le]; exact hepsEta)
    exact h.1 hleftX
  have hrightProd : 0 < derivative * h rightPoint := by
    have h := hlocal rightPoint (by linarith)
      (by simp only [rightPoint, add_sub_cancel_left,
        abs_of_nonneg heps.le]; exact hepsEta)
    exact h.2 hxRight
  have hnoLeftRoot : forall theta, theta ∈ Icc A leftPoint ->
      h theta ≠ 0 := by
    intro theta htheta hthetaZero
    have hthetaIn : theta ∈ {z | z ∈ Icc A B ∧ h z = 0} :=
      ⟨⟨htheta.1, htheta.2.trans (hleftX.le.trans hxB.le)⟩, hthetaZero⟩
    have hthetaEq : theta = x := by
      rw [hxSet] at hthetaIn
      simpa using hthetaIn
    rw [hthetaEq] at htheta
    exact (not_le_of_gt hleftX htheta.2).elim
  have hnoRightRoot : forall theta, theta ∈ Icc rightPoint B ->
      h theta ≠ 0 := by
    intro theta htheta hthetaZero
    have hthetaIn : theta ∈ {z | z ∈ Icc A B ∧ h z = 0} :=
      ⟨⟨(hAx.le.trans hxRight.le).trans htheta.1, htheta.2⟩, hthetaZero⟩
    have hthetaEq : theta = x := by
      rw [hxSet] at hthetaIn
      simpa using hthetaIn
    rw [hthetaEq] at htheta
    exact (not_le_of_gt hxRight htheta.1).elim
  have hleftSignNeg (hneg : h leftPoint < 0) : h A < 0 := by
    by_contra hnot
    have hAnonneg : 0 <= h A := le_of_not_gt hnot
    obtain ⟨theta, htheta, hthetaZero⟩ := intermediate_value_Icc'
      hAleft.le
      (hcontinuous.mono (Icc_subset_Icc le_rfl (hleftX.le.trans hxB.le)))
      (show (0 : Real) ∈ Icc (h leftPoint) (h A) from
        ⟨hneg.le, hAnonneg⟩)
    exact hnoLeftRoot theta htheta hthetaZero
  have hleftSignPos (hpos : 0 < h leftPoint) : 0 < h A := by
    by_contra hnot
    have hAnonpos : h A <= 0 := le_of_not_gt hnot
    obtain ⟨theta, htheta, hthetaZero⟩ := intermediate_value_Icc
      hAleft.le
      (hcontinuous.mono (Icc_subset_Icc le_rfl (hleftX.le.trans hxB.le)))
      (show (0 : Real) ∈ Icc (h A) (h leftPoint) from
        ⟨hAnonpos, hpos.le⟩)
    exact hnoLeftRoot theta htheta hthetaZero
  have hrightSignPos (hpos : 0 < h rightPoint) : 0 < h B := by
    by_contra hnot
    have hBnonpos : h B <= 0 := le_of_not_gt hnot
    obtain ⟨theta, htheta, hthetaZero⟩ := intermediate_value_Icc'
      hrightB.le
      (hcontinuous.mono (Icc_subset_Icc (hAx.le.trans hxRight.le) le_rfl))
      (show (0 : Real) ∈ Icc (h B) (h rightPoint) from
        ⟨hBnonpos, hpos.le⟩)
    exact hnoRightRoot theta htheta hthetaZero
  have hrightSignNeg (hneg : h rightPoint < 0) : h B < 0 := by
    by_contra hnot
    have hBnonneg : 0 <= h B := le_of_not_gt hnot
    obtain ⟨theta, htheta, hthetaZero⟩ := intermediate_value_Icc
      hrightB.le
      (hcontinuous.mono (Icc_subset_Icc (hAx.le.trans hxRight.le) le_rfl))
      (show (0 : Real) ∈ Icc (h rightPoint) (h B) from
        ⟨hneg.le, hBnonneg⟩)
    exact hnoRightRoot theta htheta hthetaZero
  rcases lt_or_gt_of_ne hderivative with hderivativeNeg | hderivativePos
  · have hleftPos : 0 < h leftPoint := by
      rcases (mul_neg_iff.mp hleftProd) with h | h
      · exfalso; linarith
      · exact h.2
    have hrightNeg : h rightPoint < 0 := by
      rcases (mul_pos_iff.mp hrightProd) with h | h
      · exfalso; linarith
      · exact h.2
    exact mul_neg_of_pos_of_neg
      (hleftSignPos hleftPos) (hrightSignNeg hrightNeg)
  · have hleftNeg : h leftPoint < 0 := by
      rcases (mul_neg_iff.mp hleftProd) with h | h
      · exact h.2
      · exfalso; linarith
    have hrightPos : 0 < h rightPoint := by
      rcases (mul_pos_iff.mp hrightProd) with h | h
      · exact h.2
      · exfalso; linarith
    exact mul_neg_of_neg_of_pos
      (hleftSignNeg hleftNeg) (hrightSignPos hrightPos)

theorem rootSet_ncard_eq_zero_or_two_of_same_endpoint_sign
    (h : Real -> Real) {A B : Real} (_hAB : A < B)
    (hcontinuous : ContinuousOn h (Icc A B))
    (hcard : {theta | theta ∈ Icc A B ∧ h theta = 0}.ncard <= 2)
    (hsame : 0 < h A * h B)
    (htransverse : forall theta, theta ∈ Icc A B -> h theta = 0 ->
      exists derivative : Real,
        HasDerivAt h derivative theta ∧ derivative ≠ 0) :
    {theta | theta ∈ Icc A B ∧ h theta = 0}.ncard = 0 ∨
      {theta | theta ∈ Icc A B ∧ h theta = 0}.ncard = 2 := by
  have hneOne : {theta | theta ∈ Icc A B ∧ h theta = 0}.ncard ≠ 1 := by
    intro hone
    have hAne : h A ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hsame
      linarith
    have hBne : h B ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hsame
      linarith
    have hnegative := endpoint_product_neg_of_unique_transverse_root
      h _hAB hcontinuous hAne hBne hone htransverse
    linarith
  omega

#print axioms endpoint_product_neg_of_unique_transverse_root
#print axioms rootSet_ncard_eq_zero_or_two_of_same_endpoint_sign

end FamilyStickyCinematicL32Prop41ContinuousTransverseRootParityV1
