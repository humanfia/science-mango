import Submission.Kakeya.ConvexFactoring.FrameBoxPairwiseTransverseOverlap

/-!
# Outer-box certificates and transverse overlap for certified slabs

This module turns the existential `HasBoxDimensions` and `IsSlab` predicates
into data-bearing certificates.  It computes the short-axis width, bounds
every unit longitudinal projection perpendicular to that axis, and uses the
certified outer boxes to derive reciprocal-sine bounds for body and shading
intersections.  No pairwise overlap estimate is assumed.
-/

open scoped ENNReal NNReal Pointwise InnerProductSpace
open MeasureTheory

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya
open TransverseCoordinateOverlap

noncomputable section

/-- Data-bearing form of `HasBoxDimensions`. -/
structure BoxDimensionsCertificate (C : ℝ≥0) (side : Fin 3 → ℝ≥0)
    (K : ConvexBody Space) where
  one_le : 1 ≤ C
  box : FrameBox
  side_eq : box.side = side
  inner_le : (box.rescale C⁻¹).body ≤ K
  outer_le : K ≤ box.body

/-- A `HasBoxDimensions` witness can be unpacked into a usable certificate. -/
theorem HasBoxDimensions.nonempty_boxDimensionsCertificate
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}
    (h : HasBoxDimensions C side K) :
    Nonempty (BoxDimensionsCertificate C side K) := by
  rcases h with ⟨hC, B, hside, hinner, houter⟩
  exact ⟨⟨hC, B, hside, hinner, houter⟩⟩

/-- Data-bearing form of `IsSlab`. -/
structure SlabDimensionsCertificate (C θ : ℝ≥0) (K : ConvexBody Space)
    extends BoxDimensionsCertificate C (slabSides θ) K where
  theta_pos : 0 < θ
  theta_le_one : θ ≤ 1

/-- An `IsSlab` witness can be unpacked into a usable slab certificate. -/
theorem IsSlab.nonempty_slabDimensionsCertificate
    {C θ : ℝ≥0} {K : ConvexBody Space} (h : IsSlab C θ K) :
    Nonempty (SlabDimensionsCertificate C θ K) := by
  rcases h with ⟨hθ, hθone, hbox⟩
  rcases hbox.nonempty_boxDimensionsCertificate with ⟨cert⟩
  exact ⟨⟨cert, hθ, hθone⟩⟩

/-- Projection onto the short frame normal has exactly the short half-width. -/
theorem SlabDimensionsCertificate.directionalHalf_shortAxis
    {C θ : ℝ≥0} {K : ConvexBody Space}
    (cert : SlabDimensionsCertificate C θ K) :
    cert.box.directionalHalf (cert.box.frame 0) = θ / 2 := by
  apply NNReal.eq
  rw [FrameBox.directionalHalf, NNReal.coe_sum, Fin.sum_univ_three]
  rw [cert.side_eq]
  simp only [slabSides, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
  change
    |⟪cert.box.frame 0, cert.box.frame 0⟫_ℝ| * ((θ : ℝ) / 2) +
      |⟪cert.box.frame 0, cert.box.frame 1⟫_ℝ| * (1 / 2) +
      |⟪cert.box.frame 0, cert.box.frame 2⟫_ℝ| * (1 / 2) =
        (θ : ℝ) / 2
  have h00 : ⟪cert.box.frame 0, cert.box.frame 0⟫_ℝ = 1 := by
    simp
  have h01 : ⟪cert.box.frame 0, cert.box.frame 1⟫_ℝ = 0 := by
    simp [cert.box.frame.inner_eq_ite]
  have h02 : ⟪cert.box.frame 0, cert.box.frame 2⟫_ℝ = 0 := by
    simp [cert.box.frame.inner_eq_ite]
  rw [h00, h01, h02]
  norm_num

/-- A unit vector perpendicular to the short axis sees longitudinal
half-width at most one. -/
theorem SlabDimensionsCertificate.directionalHalf_le_one
    {C θ : ℝ≥0} {K : ConvexBody Space}
    (cert : SlabDimensionsCertificate C θ K) (e : Space)
    (he : ‖e‖ = 1) (heperp : ⟪e, cert.box.frame 0⟫_ℝ = 0) :
    cert.box.directionalHalf e ≤ 1 := by
  have h₁ : |⟪e, cert.box.frame 1⟫_ℝ| ≤ 1 := by
    simpa [he, cert.box.frame.norm_eq_one] using
      abs_real_inner_le_norm e (cert.box.frame 1)
  have h₂ : |⟪e, cert.box.frame 2⟫_ℝ| ≤ 1 := by
    simpa [he, cert.box.frame.norm_eq_one] using
      abs_real_inner_le_norm e (cert.box.frame 2)
  apply NNReal.coe_le_coe.mp
  rw [FrameBox.directionalHalf, NNReal.coe_sum, Fin.sum_univ_three]
  rw [cert.side_eq]
  simp only [slabSides, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
  change
    |⟪e, cert.box.frame 0⟫_ℝ| * ((θ : ℝ) / 2) +
      |⟪e, cert.box.frame 1⟫_ℝ| * (1 / 2) +
      |⟪e, cert.box.frame 2⟫_ℝ| * (1 / 2) ≤ 1
  rw [heperp, abs_zero, zero_mul, zero_add]
  linarith

/-- The chosen short coordinate has half-width `θ / 2`. -/
theorem SlabDimensionsCertificate.coordinateHalf_shortAxis
    {C θ : ℝ≥0} {K : ConvexBody Space}
    (cert : SlabDimensionsCertificate C θ K) :
    cert.box.coordinateHalf 0 = θ / 2 := by
  rw [FrameBox.coordinateHalf, cert.side_eq]
  rfl

/-- Outer-box certificates contain the intersection of the certified bodies. -/
theorem SlabDimensionsCertificate.inter_body_subset_inter_box
    {C₀ C₁ θ₀ θ₁ : ℝ≥0} {K₀ K₁ : ConvexBody Space}
    (cert₀ : SlabDimensionsCertificate C₀ θ₀ K₀)
    (cert₁ : SlabDimensionsCertificate C₁ θ₁ K₁) :
    (K₀ : Set Space) ∩ (K₁ : Set Space) ⊆
      cert₀.box.carrier ∩ cert₁.box.carrier := by
  intro x hx
  constructor
  · change x ∈ cert₀.box.body
    exact cert₀.outer_le hx.1
  · change x ∈ cert₁.box.body
    exact cert₁.outer_le hx.2

/-- Certified slab bodies satisfy an explicit reciprocal-sine intersection
bound, obtained solely from their outer frame boxes. -/
theorem SlabDimensionsCertificate.volume_inter_body_le_sin_angle
    {C₀ C₁ θ₀ θ₁ : ℝ≥0} {K₀ K₁ : ConvexBody Space}
    (cert₀ : SlabDimensionsCertificate C₀ θ₀ K₀)
    (cert₁ : SlabDimensionsCertificate C₁ θ₁ K₁)
    (e : Space) (he : ‖e‖ = 1)
    (he₀ : ⟪e, cert₀.box.frame 0⟫_ℝ = 0)
    (he₁ : ⟪e, cert₁.box.frame 0⟫_ℝ = 0)
    (hangle : 0 < Real.sin
      (InnerProductGeometry.angle (cert₀.box.frame 0) (cert₁.box.frame 0))) :
    volume ((K₀ : Set Space) ∩ (K₁ : Set Space)) ≤
      ENNReal.ofReal
          ((Real.sin (InnerProductGeometry.angle
            (cert₀.box.frame 0) (cert₁.box.frame 0)))⁻¹) *
        2 * (θ₀ : ℝ≥0∞) * (θ₁ : ℝ≥0∞) := by
  have hdir : cert₀.box.directionalHalf e ≤ 1 :=
    cert₀.directionalHalf_le_one e he he₀
  have hdirE : (cert₀.box.directionalHalf e : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast hdir
  have hfull₀ :
      (2 : ℝ≥0∞) * ((θ₀ / 2 : ℝ≥0) : ℝ≥0∞) = (θ₀ : ℝ≥0∞) := by
    rw [ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0)]
    exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  have hfull₁ :
      (2 : ℝ≥0∞) * ((θ₁ / 2 : ℝ≥0) : ℝ≥0∞) = (θ₁ : ℝ≥0∞) := by
    rw [ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0)]
    exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  have hbox := cert₀.box.volume_inter_carrier_le_sin_angle
    cert₁.box 0 0 e he he₀ he₁ hangle
  rw [cert₀.coordinateHalf_shortAxis, cert₁.coordinateHalf_shortAxis] at hbox
  calc
    volume ((K₀ : Set Space) ∩ (K₁ : Set Space)) ≤
        volume (cert₀.box.carrier ∩ cert₁.box.carrier) :=
      measure_mono (cert₀.inter_body_subset_inter_box cert₁)
    _ ≤ ENNReal.ofReal
          ((Real.sin (InnerProductGeometry.angle
            (cert₀.box.frame 0) (cert₁.box.frame 0)))⁻¹) *
        (2 * (cert₀.box.directionalHalf e : ℝ≥0∞)) *
        (2 * (θ₀ / 2 : ℝ≥0) : ℝ≥0∞) *
        (2 * (θ₁ / 2 : ℝ≥0) : ℝ≥0∞) := hbox
    _ ≤ ENNReal.ofReal
          ((Real.sin (InnerProductGeometry.angle
            (cert₀.box.frame 0) (cert₁.box.frame 0)))⁻¹) *
        (2 * 1) *
        (2 * (θ₀ / 2 : ℝ≥0) : ℝ≥0∞) *
        (2 * (θ₁ / 2 : ℝ≥0) : ℝ≥0∞) := by
      gcongr
    _ = ENNReal.ofReal
          ((Real.sin (InnerProductGeometry.angle
            (cert₀.box.frame 0) (cert₁.box.frame 0)))⁻¹) *
        2 * (θ₀ : ℝ≥0∞) * (θ₁ : ℝ≥0∞) := by
      rw [hfull₀, hfull₁, mul_one]

/-- The same explicit bound applies to arbitrary shadings contained in the
two certified slab bodies. -/
theorem SlabDimensionsCertificate.volume_inter_sets_le_sin_angle
    {C₀ C₁ θ₀ θ₁ : ℝ≥0} {K₀ K₁ : ConvexBody Space}
    (cert₀ : SlabDimensionsCertificate C₀ θ₀ K₀)
    (cert₁ : SlabDimensionsCertificate C₁ θ₁ K₁)
    (A₀ A₁ : Set Space)
    (hA₀ : A₀ ⊆ (K₀ : Set Space)) (hA₁ : A₁ ⊆ (K₁ : Set Space))
    (e : Space) (he : ‖e‖ = 1)
    (he₀ : ⟪e, cert₀.box.frame 0⟫_ℝ = 0)
    (he₁ : ⟪e, cert₁.box.frame 0⟫_ℝ = 0)
    (hangle : 0 < Real.sin
      (InnerProductGeometry.angle (cert₀.box.frame 0) (cert₁.box.frame 0))) :
    volume (A₀ ∩ A₁) ≤
      ENNReal.ofReal
          ((Real.sin (InnerProductGeometry.angle
            (cert₀.box.frame 0) (cert₁.box.frame 0)))⁻¹) *
        2 * (θ₀ : ℝ≥0∞) * (θ₁ : ℝ≥0∞) := by
  calc
    volume (A₀ ∩ A₁) ≤ volume ((K₀ : Set Space) ∩ (K₁ : Set Space)) := by
      exact measure_mono (Set.inter_subset_inter hA₀ hA₁)
    _ ≤ ENNReal.ofReal
          ((Real.sin (InnerProductGeometry.angle
            (cert₀.box.frame 0) (cert₁.box.frame 0)))⁻¹) *
        2 * (θ₀ : ℝ≥0∞) * (θ₁ : ℝ≥0∞) :=
      cert₀.volume_inter_body_le_sin_angle cert₁ e he he₀ he₁ hangle

end

end Submission.Kakeya.ConvexGeometry
