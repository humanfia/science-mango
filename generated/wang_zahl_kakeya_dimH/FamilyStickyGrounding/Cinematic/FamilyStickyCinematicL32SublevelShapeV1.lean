import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CriticalPointGrowthV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32SublevelShapeV1

open FamilyStickyCinematicL32SublevelIntervalV1
open FamilyStickyCinematicL32CriticalPointGrowthV1

/-!
# At most two order-connected sublevel pieces

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3,
Lemma 3.8(2b), in the sentence asserting that `E_delta` is a closed interval
or a union of two closed intervals.

The module isolates the order geometry behind that assertion.  A monotone or
antitone branch has an order-connected sublevel set.  Nonvanishing continuous
curvature fixes its sign, and a critical point then makes the original
function antitone/monotone (or monotone/antitone) on the two sides.  Hence the
full sublevel set is the union of at most two order-connected pieces.
-/

/-- The `delta`-sublevel set of `h` restricted to a parameter set `t`. -/
def SublevelOn (h : Real -> Real) (delta : Real) (t : Set Real) : Set Real :=
  t ∩ h ⁻¹' Icc (-delta) delta

/-- A monotone branch has an order-connected sublevel set. -/
theorem sublevelOn_ordConnected_of_monotoneOn
    (h : Real -> Real) (delta : Real) {t : Set Real}
    (ht : t.OrdConnected) (hmono : MonotoneOn h t) :
    (SublevelOn h delta t).OrdConnected := by
  obtain ⟨u, hu, heq⟩ :=
    ordConnected_Icc.preimage_monotoneOn hmono
  rw [SublevelOn, heq]
  exact ht.inter hu

/-- An antitone branch has an order-connected sublevel set. -/
theorem sublevelOn_ordConnected_of_antitoneOn
    (h : Real -> Real) (delta : Real) {t : Set Real}
    (ht : t.OrdConnected) (hanti : AntitoneOn h t) :
    (SublevelOn h delta t).OrdConnected := by
  obtain ⟨u, hu, heq⟩ :=
    ordConnected_Icc.preimage_antitoneOn hanti
  rw [SublevelOn, heq]
  exact ht.inter hu

/-- Positive curvature and a zero first derivative produce an antitone left
branch and a monotone right branch. -/
theorem turning_monotonicity_of_curvature_lower
    (h h1 h2 : Real -> Real) {A B theta0 kappa : Real}
    (htheta0 : theta0 ∈ Icc A B) (hkappa : 0 <= kappa)
    (hcritical : h1 theta0 = 0)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ Icc A B -> HasDerivAt h1 (h2 z) z)
    (hcurvatureLower : forall z, z ∈ Icc A B -> kappa <= h2 z) :
    AntitoneOn h (Icc A theta0) ∧
      MonotoneOn h (Icc theta0 B) := by
  have hleftSubset : Icc A theta0 ⊆ Icc A B :=
    Icc_subset_Icc le_rfl htheta0.2
  have hrightSubset : Icc theta0 B ⊆ Icc A B :=
    Icc_subset_Icc htheta0.1 le_rfl
  have hfirstLeft : forall z, z ∈ Icc A theta0 -> h1 z <= 0 := by
    intro z hz
    have hzDomain := hleftSubset hz
    have hpathSubset : Icc z theta0 ⊆ Icc A B :=
      Icc_subset_Icc hzDomain.1 htheta0.2
    have hgrowth := mul_interval_length_le_function_sub_of_deriv_lower
      h1 h2 hz.2
      (fun w hw => hderiv1 w (hpathSubset hw))
      (fun w hw => hcurvatureLower w (hpathSubset hw))
    rw [hcritical, zero_sub] at hgrowth
    nlinarith [mul_nonneg hkappa (sub_nonneg.2 hz.2)]
  have hfirstRight : forall z, z ∈ Icc theta0 B -> 0 <= h1 z := by
    intro z hz
    have hzDomain := hrightSubset hz
    have hpathSubset : Icc theta0 z ⊆ Icc A B :=
      Icc_subset_Icc htheta0.1 hzDomain.2
    have hgrowth := mul_interval_length_le_function_sub_of_deriv_lower
      h1 h2 hz.1
      (fun w hw => hderiv1 w (hpathSubset hw))
      (fun w hw => hcurvatureLower w (hpathSubset hw))
    rw [hcritical, sub_zero] at hgrowth
    exact (mul_nonneg hkappa (sub_nonneg.2 hz.1)).trans hgrowth
  constructor
  · apply antitoneOn_of_hasDerivWithinAt_nonpos
      (convex_Icc A theta0)
      (HasDerivAt.continuousOn
        (fun z hz => hderiv z (hleftSubset hz)))
    · intro z hz
      exact (hderiv z (hleftSubset (interior_subset hz))).hasDerivWithinAt
    · intro z hz
      exact hfirstLeft z (interior_subset hz)
  · apply monotoneOn_of_hasDerivWithinAt_nonneg
      (convex_Icc theta0 B)
      (HasDerivAt.continuousOn
        (fun z hz => hderiv z (hrightSubset hz)))
    · intro z hz
      exact (hderiv z (hrightSubset (interior_subset hz))).hasDerivWithinAt
    · intro z hz
      exact hfirstRight z (interior_subset hz)

/-- Continuous curvature bounded away from zero produces one of the two
possible turning-point monotonicity patterns, without a sign callback. -/
theorem turning_monotonicity_of_abs_curvature_lower
    (h h1 h2 : Real -> Real) {A B theta0 kappa : Real}
    (htheta0 : theta0 ∈ Icc A B) (hkappa : 0 < kappa)
    (hcritical : h1 theta0 = 0)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ Icc A B -> HasDerivAt h1 (h2 z) z)
    (h2Continuous : ContinuousOn h2 (Icc A B))
    (hcurvatureLower : forall z, z ∈ Icc A B -> kappa <= |h2 z|) :
    (AntitoneOn h (Icc A theta0) ∧ MonotoneOn h (Icc theta0 B)) ∨
      (MonotoneOn h (Icc A theta0) ∧ AntitoneOn h (Icc theta0 B)) := by
  have hAB : A <= B := htheta0.1.trans htheta0.2
  rcases continuous_fixed_sign_of_abs_lower_on_Icc
      h2 hAB hkappa h2Continuous hcurvatureLower with hpositive | hnegative
  · exact Or.inl (turning_monotonicity_of_curvature_lower
      h h1 h2 htheta0 (le_of_lt hkappa) hcritical
      hderiv hderiv1 hpositive)
  · have hnegativeTurning := turning_monotonicity_of_curvature_lower
      (-h) (-h1) (-h2) htheta0 (le_of_lt hkappa)
      (show (-h1) theta0 = 0 by
        change -h1 theta0 = 0
        rw [hcritical, neg_zero])
      (fun z hz => (hderiv z hz).neg)
      (fun z hz => (hderiv1 z hz).neg)
      (fun z hz => by
        change kappa <= -h2 z
        linarith [hnegative z hz])
    right
    constructor
    · intro x hx y hy hxy
      have hneg := hnegativeTurning.1 hx hy hxy
      have hneg' : -h y <= -h x := by
        simpa only [Pi.neg_apply] using hneg
      linarith
    · intro x hx y hy hxy
      have hneg := hnegativeTurning.2 hx hy hxy
      have hneg' : -h x <= -h y := by
        simpa only [Pi.neg_apply] using hneg
      linarith

/-- A turning point splits the full sublevel set into two order-connected
pieces.  Either piece may be empty, so this is an at-most-two statement. -/
theorem sublevelOn_eq_union_two_ordConnected_of_turning
    (h : Real -> Real) (delta : Real) {A B theta0 : Real}
    (htheta0 : theta0 ∈ Icc A B)
    (hturning :
      (AntitoneOn h (Icc A theta0) ∧ MonotoneOn h (Icc theta0 B)) ∨
      (MonotoneOn h (Icc A theta0) ∧ AntitoneOn h (Icc theta0 B))) :
    ∃ left right : Set Real,
      left.OrdConnected ∧ right.OrdConnected ∧
        SublevelOn h delta (Icc A B) = left ∪ right := by
  let left := SublevelOn h delta (Icc A theta0)
  let right := SublevelOn h delta (Icc theta0 B)
  have hleftOrd : left.OrdConnected := by
    rcases hturning with hturning | hturning
    · exact sublevelOn_ordConnected_of_antitoneOn
        h delta ordConnected_Icc hturning.1
    · exact sublevelOn_ordConnected_of_monotoneOn
        h delta ordConnected_Icc hturning.1
  have hrightOrd : right.OrdConnected := by
    rcases hturning with hturning | hturning
    · exact sublevelOn_ordConnected_of_monotoneOn
        h delta ordConnected_Icc hturning.2
    · exact sublevelOn_ordConnected_of_antitoneOn
        h delta ordConnected_Icc hturning.2
  refine ⟨left, right, hleftOrd, hrightOrd, ?_⟩
  ext z
  simp only [left, right, SublevelOn, mem_inter_iff, mem_preimage,
    mem_union]
  have hsplit : z ∈ Icc A B ↔
      z ∈ Icc A theta0 ∨ z ∈ Icc theta0 B := by
    rw [← mem_union, Icc_union_Icc_eq_Icc htheta0.1 htheta0.2]
  constructor
  · intro hz
    rcases hsplit.1 hz.1 with hzLeft | hzRight
    · exact Or.inl ⟨hzLeft, hz.2⟩
    · exact Or.inr ⟨hzRight, hz.2⟩
  · rintro (hzLeft | hzRight)
    · exact ⟨hsplit.2 (Or.inl hzLeft.1), hzLeft.2⟩
    · exact ⟨hsplit.2 (Or.inr hzRight.1), hzRight.2⟩

/-- Callback-free at-most-two-piece structure under continuous nonvanishing
curvature and an actual critical point. -/
theorem sublevelOn_eq_union_two_ordConnected_of_abs_curvature_lower
    (h h1 h2 : Real -> Real) (delta : Real)
    {A B theta0 kappa : Real}
    (htheta0 : theta0 ∈ Icc A B) (hkappa : 0 < kappa)
    (hcritical : h1 theta0 = 0)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ Icc A B -> HasDerivAt h1 (h2 z) z)
    (h2Continuous : ContinuousOn h2 (Icc A B))
    (hcurvatureLower : forall z, z ∈ Icc A B -> kappa <= |h2 z|) :
    ∃ left right : Set Real,
      left.OrdConnected ∧ right.OrdConnected ∧
        SublevelOn h delta (Icc A B) = left ∪ right := by
  apply sublevelOn_eq_union_two_ordConnected_of_turning
    h delta htheta0
  exact turning_monotonicity_of_abs_curvature_lower
    h h1 h2 htheta0 hkappa hcritical hderiv hderiv1
    h2Continuous hcurvatureLower

#print axioms sublevelOn_ordConnected_of_monotoneOn
#print axioms sublevelOn_ordConnected_of_antitoneOn
#print axioms turning_monotonicity_of_curvature_lower
#print axioms turning_monotonicity_of_abs_curvature_lower
#print axioms sublevelOn_eq_union_two_ordConnected_of_turning
#print axioms sublevelOn_eq_union_two_ordConnected_of_abs_curvature_lower

end FamilyStickyCinematicL32SublevelShapeV1
