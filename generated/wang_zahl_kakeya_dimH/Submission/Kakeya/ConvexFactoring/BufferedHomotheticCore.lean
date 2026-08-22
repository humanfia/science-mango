import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Submission.Kakeya.ConvexFactoring.BufferedInducedGrowth
import Submission.Kakeya.ConvexFactoring.QuantitativeRefinement

/-!
# Homothetic buffered cores of certified convex bodies

This module constructs an inward homothetic core of an arbitrary convex
body carrying a `BoxDimensionsCertificate`.  The certificate is used only to
choose an actual interior frame box and its center.  Convexity puts the core
inside the body and, at every core point, puts an explicit contracted copy of
the certified inner box inside the body with that point as its center.

Lebesgue invariance and three-dimensional Haar scaling give the exact core
volume.  Consequently the removed boundary layer costs at most
`3 t * volume K`.  Summing this estimate gives a zero/infinity-safe global
mass-retention theorem for a finite shading at any buffer parameter satisfying
`6 t <= lambda`; this is a global average-density hypothesis, not a
per-carrier one.  The canonical choice `t = lambda / 6` gives
`WithinFactor 2`, while every core point has a centered inner box with side
lengths `t * C⁻¹ * side i`.

This module does not claim that the core restriction alone recovers the
paper's `lambda^2` induced-shading conclusion.
-/

open scoped ENNReal NNReal Pointwise
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

namespace BufferedHomotheticCore

variable {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}

/-- Move `y` a fraction `t` of the way toward the distinguished center `c`. -/
def inwardHomothety (c : Space) (t : ℝ≥0) (y : Space) : Space :=
  y + (t : ℝ) • (c - y)

/-- The inward homothetic image of the whole certified convex body. -/
def homotheticCore
    (cert : BoxDimensionsCertificate C side K) (t : ℝ≥0) : Set Space :=
  inwardHomothety cert.box.center t '' (K : Set Space)

theorem mem_homotheticCore_iff
    (cert : BoxDimensionsCertificate C side K) (t : ℝ≥0) (x : Space) :
    x ∈ homotheticCore cert t ↔
      ∃ y ∈ (K : Set Space), inwardHomothety cert.box.center t y = x :=
  Iff.rfl

/-- The center of the certified inner box is an actual point of the body. -/
theorem certificateCenter_mem_body
    (cert : BoxDimensionsCertificate C side K) :
    cert.box.center ∈ (K : Set Space) := by
  apply cert.inner_le
  change cert.box.center ∈ (cert.box.rescale C⁻¹).carrier
  simpa using (cert.box.rescale C⁻¹).center_mem_carrier

/-- For `t ≤ 1`, the inward formula is a translate of scalar multiplication
by the complementary factor `1 - t`. -/
theorem inwardHomothety_eq_vadd_smul_vadd
    (c y : Space) {t : ℝ≥0} (ht : t ≤ 1) :
    inwardHomothety c t y =
      c +ᵥ (1 - t : ℝ≥0) • ((-c) +ᵥ y) := by
  unfold inwardHomothety
  change y + (t : ℝ) • (c - y) =
    c + (((1 - t : ℝ≥0) : ℝ) • (-c + y))
  rw [NNReal.coe_sub ht]
  module

/-- Set-level translation/scaling description used by Haar measure. -/
theorem homotheticCore_eq_vadd_smul_vadd
    (cert : BoxDimensionsCertificate C side K) {t : ℝ≥0} (ht : t ≤ 1) :
    homotheticCore cert t =
      cert.box.center +ᵥ
        ((1 - t : ℝ≥0) • ((-cert.box.center) +ᵥ (K : Set Space))) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply Set.mem_vadd_set.mpr
    refine ⟨(1 - t : ℝ≥0) • ((-cert.box.center) +ᵥ y), ?_, ?_⟩
    · apply Set.mem_smul_set.mpr
      refine ⟨(-cert.box.center) +ᵥ y, ?_, rfl⟩
      exact Set.mem_vadd_set.mpr ⟨y, hy, rfl⟩
    · exact (inwardHomothety_eq_vadd_smul_vadd cert.box.center y ht).symm
  · intro hx
    obtain ⟨u, hu, hux⟩ := Set.mem_vadd_set.mp hx
    obtain ⟨v, hv, hvu⟩ := Set.mem_smul_set.mp hu
    obtain ⟨y, hy, hyv⟩ := Set.mem_vadd_set.mp hv
    refine ⟨y, hy, ?_⟩
    rw [← hux, ← hvu, ← hyv]
    exact inwardHomothety_eq_vadd_smul_vadd cert.box.center y ht

/-- The homothetic core is compact, hence measurable. -/
theorem homotheticCore_isCompact
    (cert : BoxDimensionsCertificate C side K) (t : ℝ≥0) :
    IsCompact (homotheticCore cert t) := by
  apply K.isCompact.image
  unfold inwardHomothety
  fun_prop

theorem homotheticCore_measurableSet
    (cert : BoxDimensionsCertificate C side K) (t : ℝ≥0) :
    MeasurableSet (homotheticCore cert t) :=
  (homotheticCore_isCompact cert t).measurableSet

/-- Convexity puts the inward homothetic core inside the original body. -/
theorem homotheticCore_subset_body
    (cert : BoxDimensionsCertificate C side K) {t : ℝ≥0} (ht : t ≤ 1) :
    homotheticCore cert t ⊆ (K : Set Space) := by
  rintro x ⟨y, hy, rfl⟩
  exact K.convex.add_smul_sub_mem hy (certificateCenter_mem_body cert)
    ⟨NNReal.coe_nonneg t, by exact_mod_cast ht⟩

/-- Every point of the core is the center of an explicit contracted certified
inner box lying in `K`.  Its three side lengths are displayed exactly. -/
theorem exists_centered_localInnerBox
    (cert : BoxDimensionsCertificate C side K) {t : ℝ≥0} (ht : t ≤ 1)
    {x : Space} (hx : x ∈ homotheticCore cert t) :
    ∃ y ∈ (K : Set Space),
      (cert.localInnerBox y t).center = x ∧
      (cert.localInnerBox y t).carrier ⊆ (K : Set Space) ∧
      ∀ i, (cert.localInnerBox y t).side i = t * C⁻¹ * side i := by
  obtain ⟨y, hy, hxy⟩ := hx
  refine ⟨y, hy, ?_, cert.localInnerBox_subset_body hy ht, ?_⟩
  · simpa [BoxDimensionsCertificate.localInnerBox, inwardHomothety] using hxy
  · intro i
    simp [BoxDimensionsCertificate.localInnerBox, cert.side_eq, mul_assoc]

/-- Exact three-dimensional core volume. -/
theorem volume_homotheticCore
    (cert : BoxDimensionsCertificate C side K) {t : ℝ≥0} (ht : t ≤ 1) :
    volume (homotheticCore cert t) =
      ((1 - t : ℝ≥0) : ℝ≥0∞) ^ 3 * volume (K : Set Space) := by
  rw [homotheticCore_eq_vadd_smul_vadd cert ht,
    MeasureTheory.measure_vadd,
    MeasureTheory.Measure.addHaar_nnreal_smul,
    MeasureTheory.measure_vadd]
  norm_num [Space]

/-- The elementary three-dimensional Bernoulli bound
`1 ≤ (1-t)^3 + 3t`. -/
theorem one_le_complement_cube_add_three_mul
    (t : ℝ≥0) (ht : t ≤ 1) :
    (1 : ℝ≥0∞) ≤
      ((1 - t : ℝ≥0) : ℝ≥0∞) ^ 3 + 3 * (t : ℝ≥0∞) := by
  have htR : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  have ht0 : 0 ≤ (t : ℝ) := NNReal.coe_nonneg t
  have hpoly :
      (1 : ℝ) ≤ (1 - (t : ℝ)) ^ 3 + 3 * (t : ℝ) := by
    have hnonneg : 0 ≤ (t : ℝ) ^ 2 * (3 - (t : ℝ)) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith
  apply (ENNReal.coe_le_coe).2
  apply (NNReal.coe_le_coe).1
  push_cast [NNReal.coe_sub ht]
  exact hpoly

/-- The part removed from a homothetic core has volume at most
`3t * volume K`.  This includes zero-volume bodies. -/
theorem volume_body_sdiff_homotheticCore_le
    (cert : BoxDimensionsCertificate C side K) {t : ℝ≥0} (ht : t ≤ 1) :
    volume ((K : Set Space) \ homotheticCore cert t) ≤
      (3 * (t : ℝ≥0∞)) * volume (K : Set Space) := by
  rw [MeasureTheory.measure_sdiff
    (homotheticCore_subset_body cert ht)
    (homotheticCore_measurableSet cert t).nullMeasurableSet
    (homotheticCore_isCompact cert t).measure_ne_top,
    volume_homotheticCore cert ht]
  apply (tsub_le_iff_left).2
  calc
    volume (K : Set Space) = 1 * volume (K : Set Space) := by simp
    _ ≤ (((1 - t : ℝ≥0) : ℝ≥0∞) ^ 3 + 3 * (t : ℝ≥0∞)) *
        volume (K : Set Space) :=
      mul_le_mul' (one_le_complement_cube_add_three_mul t ht) le_rfl
    _ = ((1 - t : ℝ≥0) : ℝ≥0∞) ^ 3 * volume (K : Set Space) +
        (3 * (t : ℝ≥0∞)) * volume (K : Set Space) := by
      rw [add_mul]

/-- Any subset of `K` loses at most the same explicit boundary-layer mass. -/
theorem volume_le_inter_homotheticCore_add_boundary
    (cert : BoxDimensionsCertificate C side K) {t : ℝ≥0} (ht : t ≤ 1)
    {A : Set Space} (hA : A ⊆ (K : Set Space)) :
    volume A ≤ volume (A ∩ homotheticCore cert t) +
      (3 * (t : ℝ≥0∞)) * volume (K : Set Space) := by
  have hcover :
      A ⊆ (A ∩ homotheticCore cert t) ∪
        ((K : Set Space) \ homotheticCore cert t) := by
    intro x hx
    by_cases hxc : x ∈ homotheticCore cert t
    · exact Or.inl ⟨hx, hxc⟩
    · exact Or.inr ⟨hA hx, hxc⟩
  calc
    volume A ≤ volume ((A ∩ homotheticCore cert t) ∪
        ((K : Set Space) \ homotheticCore cert t)) :=
      measure_mono hcover
    _ ≤ volume (A ∩ homotheticCore cert t) +
        volume ((K : Set Space) \ homotheticCore cert t) :=
      measure_union_le _ _
    _ ≤ volume (A ∩ homotheticCore cert t) +
        (3 * (t : ℝ≥0∞)) * volume (K : Set Space) :=
      add_le_add_right (volume_body_sdiff_homotheticCore_le cert ht) _

/-- Restrict every carrier of a shading to the corresponding certified
homothetic core. -/
def coreRestriction
    {ι : Type*} {F : ConvexFamily ι} {C : ℝ≥0}
    {side : ι → Fin 3 → ℝ≥0}
    (Y : Shading F)
    (cert : ∀ i, BoxDimensionsCertificate C (side i) (F i))
    (t : ℝ≥0) : Shading F where
  carrier i := Y.carrier i ∩ homotheticCore (cert i) t
  measurable_carrier i :=
    (Y.measurable_carrier i).inter (homotheticCore_measurableSet (cert i) t)
  carrier_subset i := inter_subset_left.trans (Y.carrier_subset i)

@[simp] theorem coreRestriction_carrier
    {ι : Type*} {F : ConvexFamily ι} {C : ℝ≥0}
    {side : ι → Fin 3 → ℝ≥0}
    (Y : Shading F)
    (cert : ∀ i, BoxDimensionsCertificate C (side i) (F i))
    (t : ℝ≥0) (i : ι) :
    (coreRestriction Y cert t).carrier i =
      Y.carrier i ∩ homotheticCore (cert i) t :=
  rfl

/-- Summed boundary loss for a finite shading. -/
theorem shadingMass_le_coreRestriction_add_boundary
    {ι : Type*} [Fintype ι] {F : ConvexFamily ι} {C : ℝ≥0}
    {side : ι → Fin 3 → ℝ≥0}
    (Y : Shading F)
    (cert : ∀ i, BoxDimensionsCertificate C (side i) (F i))
    {t : ℝ≥0} (ht : t ≤ 1) :
    Y.shadingMass ≤ (coreRestriction Y cert t).shadingMass +
      (3 * (t : ℝ≥0∞)) * familyVolume F := by
  unfold Shading.shadingMass familyVolume
  calc
    (∑ i, volume (Y.carrier i)) ≤
        ∑ i, (volume ((coreRestriction Y cert t).carrier i) +
          (3 * (t : ℝ≥0∞)) * volume (F i : Set Space)) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa using volume_le_inter_homotheticCore_add_boundary
        (cert i) ht (Y.carrier_subset i)
    _ = (∑ i, volume ((coreRestriction Y cert t).carrier i)) +
        (3 * (t : ℝ≥0∞)) * ∑ i, volume (F i : Set Space) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Pure finite-ENNReal retention algebra. -/
theorem le_two_nsmul_of_le_add_of_two_mul_le
    {mass retained boundary : ℝ≥0∞}
    (hmass_top : mass ≠ ∞)
    (hloss : mass ≤ retained + boundary)
    (hboundary : 2 * boundary ≤ mass) :
    mass ≤ 2 • retained := by
  have hbb : boundary + boundary ≤ mass := by
    simpa [two_mul] using hboundary
  have hcancel : mass + boundary ≤ mass + retained := by
    calc
      mass + boundary ≤ (retained + boundary) + boundary :=
        add_le_add_left hloss boundary
      _ = retained + (boundary + boundary) := by ac_rfl
      _ ≤ retained + mass := add_le_add_right hbb retained
      _ = mass + retained := add_comm _ _
  have hboundary_retained : boundary ≤ retained :=
    (ENNReal.add_le_add_iff_left hmass_top).1 hcancel
  calc
    mass ≤ retained + boundary := hloss
    _ ≤ retained + retained := add_le_add_right hboundary_retained retained
    _ = 2 • retained := (two_nsmul retained).symm

/-- A global density lower bound and `6t ≤ lambda` retain at least half of
the actual shading mass inside the homothetic cores. -/
theorem shadingMass_le_two_nsmul_coreRestriction
    {ι : Type*} [Fintype ι] {F : ConvexFamily ι} {C : ℝ≥0}
    {side : ι → Fin 3 → ℝ≥0}
    (Y : Shading F)
    (cert : ∀ i, BoxDimensionsCertificate C (side i) (F i))
    {t : ℝ≥0} (ht : t ≤ 1) (lambda : ℝ≥0∞)
    (htlambda : 6 * (t : ℝ≥0∞) ≤ lambda)
    (hdensity : lambda * familyVolume F ≤ Y.shadingMass) :
    Y.shadingMass ≤ 2 • (coreRestriction Y cert t).shadingMass := by
  apply le_two_nsmul_of_le_add_of_two_mul_le
    Y.shadingMass_lt_top.ne
    (shadingMass_le_coreRestriction_add_boundary Y cert ht)
  calc
    2 * ((3 * (t : ℝ≥0∞)) * familyVolume F) =
        (6 * (t : ℝ≥0∞)) * familyVolume F := by ring
    _ ≤ lambda * familyVolume F := mul_le_mul' htlambda le_rfl
    _ ≤ Y.shadingMass := hdensity

/-- The same result packaged in the library's refinement-loss language. -/
theorem coreRestriction_withinFactor_two
    {ι : Type*} [Fintype ι] {F : ConvexFamily ι} {C : ℝ≥0}
    {side : ι → Fin 3 → ℝ≥0}
    (Y : Shading F)
    (cert : ∀ i, BoxDimensionsCertificate C (side i) (F i))
    {t : ℝ≥0} (ht : t ≤ 1) (lambda : ℝ≥0∞)
    (htlambda : 6 * (t : ℝ≥0∞) ≤ lambda)
    (hdensity : lambda * familyVolume F ≤ Y.shadingMass) :
    WithinFactor 2 Y.shadingMass (coreRestriction Y cert t).shadingMass :=
  shadingMass_le_two_nsmul_coreRestriction
    Y cert ht lambda htlambda hdensity

/-- Canonical density-dependent buffer parameter. -/
def densityBufferParameter (lambda : ℝ≥0) : ℝ≥0 :=
  lambda / 6

theorem densityBufferParameter_le_one
    {lambda : ℝ≥0} (hlambda : lambda ≤ 1) :
    densityBufferParameter lambda ≤ 1 := by
  unfold densityBufferParameter
  apply (div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 6)).2
  exact hlambda.trans (by norm_num)

theorem six_mul_densityBufferParameter (lambda : ℝ≥0) :
    (6 : ℝ≥0∞) * (densityBufferParameter lambda : ℝ≥0∞) =
      (lambda : ℝ≥0∞) := by
  rw [densityBufferParameter, ENNReal.coe_div (by norm_num : (6 : ℝ≥0) ≠ 0)]
  exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)

/-- Every finite shading of average density at least `lambda` retains at least
half its mass in the canonical `lambda / 6` homothetic core. -/
theorem coreRestriction_densityBufferParameter_withinFactor_two
    {ι : Type*} [Fintype ι] {F : ConvexFamily ι} {C : ℝ≥0}
    {side : ι → Fin 3 → ℝ≥0}
    (Y : Shading F)
    (cert : ∀ i, BoxDimensionsCertificate C (side i) (F i))
    (lambda : ℝ≥0) (hlambda : lambda ≤ 1)
    (hdensity : (lambda : ℝ≥0∞) * familyVolume F ≤ Y.shadingMass) :
    WithinFactor 2 Y.shadingMass
      (coreRestriction Y cert (densityBufferParameter lambda)).shadingMass := by
  apply coreRestriction_withinFactor_two Y cert
    (densityBufferParameter_le_one hlambda) (lambda : ℝ≥0∞)
  · rw [six_mul_densityBufferParameter]
  · exact hdensity

end BufferedHomotheticCore

end

end Submission.Kakeya.ConvexFactoring
