import Submission.Kakeya.ConvexFactoring.TransverseUnit
import Submission.Kakeya.ConvexFactoring.BoxDimensionsMeasure

/-!
# Certified overlap for genuine planks

This module turns `IsPlank C a b K` into a data-bearing frame certificate and
proves the short-normal overlap bound for two genuine `a x b x 1` planks.
The common perpendicular direction sees half-width at most
`b / 2 + 1 / 2 <= 1`; no plank is replaced by an `a x 1 x 1` slab.
-/

open scoped ENNReal NNReal Pointwise InnerProductSpace Matrix
open MeasureTheory Set

namespace Family8CertifiedPlankPairOverlapV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-- Data-bearing form of `IsPlank`, recording its actual `a x b x 1`
dimensions and scalar ordering. -/
structure PlankDimensionsCertificate (C a b : NNReal)
    (K : ConvexBody Space) extends
    BoxDimensionsCertificate C (plankSides a b) K where
  a_pos : 0 < a
  a_le_b : a ≤ b
  b_le_one : b ≤ 1

/-- Unpack an existing proposition-level plank certificate. -/
theorem IsPlank.nonempty_plankDimensionsCertificate
    {C a b : NNReal} {K : ConvexBody Space} (h : IsPlank C a b K) :
    Nonempty (PlankDimensionsCertificate C a b K) := by
  rcases h with ⟨ha, hab, hb, hbox⟩
  rcases hbox.nonempty_boxDimensionsCertificate with ⟨cert⟩
  exact ⟨⟨cert, ha, hab, hb⟩⟩

/-- Forget only the chosen frame, recovering the exact `IsPlank`
proposition. -/
theorem PlankDimensionsCertificate.isPlank
    {C a b : NNReal} {K : ConvexBody Space}
    (cert : PlankDimensionsCertificate C a b K) :
    IsPlank C a b K :=
  ⟨cert.a_pos, cert.a_le_b, cert.b_le_one,
    ⟨cert.one_le, cert.box, cert.side_eq, cert.inner_le, cert.outer_le⟩⟩

/-- A unit vector perpendicular to the short `a`-normal has true plank
half-width at most `b / 2 + 1 / 2 ≤ 1`. -/
theorem PlankDimensionsCertificate.directionalHalf_le_one
    {C a b : NNReal} {K : ConvexBody Space}
    (cert : PlankDimensionsCertificate C a b K) (e : Space)
    (he : ‖e‖ = 1) (heperp : ⟪e, cert.box.frame 0⟫_ℝ = 0) :
    cert.box.directionalHalf e ≤ 1 := by
  have h1 : |⟪e, cert.box.frame 1⟫_ℝ| ≤ 1 := by
    simpa [he, cert.box.frame.norm_eq_one] using
      abs_real_inner_le_norm e (cert.box.frame 1)
  have h2 : |⟪e, cert.box.frame 2⟫_ℝ| ≤ 1 := by
    simpa [he, cert.box.frame.norm_eq_one] using
      abs_real_inner_le_norm e (cert.box.frame 2)
  have hb : (b : Real) ≤ 1 := by exact_mod_cast cert.b_le_one
  apply NNReal.coe_le_coe.mp
  rw [FrameBox.directionalHalf, NNReal.coe_sum, Fin.sum_univ_three]
  rw [cert.side_eq]
  simp only [plankSides, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
  change
    |⟪e, cert.box.frame 0⟫_ℝ| * ((a : Real) / 2) +
      |⟪e, cert.box.frame 1⟫_ℝ| * ((b : Real) / 2) +
      |⟪e, cert.box.frame 2⟫_ℝ| * (1 / 2) ≤ 1
  rw [heperp, abs_zero, zero_mul, zero_add]
  calc
    |⟪e, cert.box.frame 1⟫_ℝ| * ((b : Real) / 2) +
        |⟪e, cert.box.frame 2⟫_ℝ| * (1 / 2) ≤
        1 * (1 / 2) + 1 * (1 / 2) := by
      gcongr
    _ = 1 := by norm_num

/-- The selected short coordinate has exact half-width `a / 2`. -/
theorem PlankDimensionsCertificate.coordinateHalf_shortAxis
    {C a b : NNReal} {K : ConvexBody Space}
    (cert : PlankDimensionsCertificate C a b K) :
    cert.box.coordinateHalf 0 = a / 2 := by
  rw [FrameBox.coordinateHalf, cert.side_eq]
  rfl

/-- Certified plank bodies lie in their outer frame boxes. -/
theorem PlankDimensionsCertificate.inter_body_subset_inter_box
    {C0 C1 a0 a1 b0 b1 : NNReal} {K0 K1 : ConvexBody Space}
    (cert0 : PlankDimensionsCertificate C0 a0 b0 K0)
    (cert1 : PlankDimensionsCertificate C1 a1 b1 K1) :
    (K0 : Set Space) ∩ (K1 : Set Space) ⊆
      cert0.box.carrier ∩ cert1.box.carrier := by
  intro x hx
  constructor
  · change x ∈ cert0.box.body
    exact cert0.outer_le hx.1
  · change x ∈ cert1.box.body
    exact cert1.outer_le hx.2

/-- Short-axis pair overlap derived from the actual frame boxes. -/
theorem PlankDimensionsCertificate.volume_inter_body_le_sin_angle
    {C0 C1 a0 a1 b0 b1 : NNReal} {K0 K1 : ConvexBody Space}
    (cert0 : PlankDimensionsCertificate C0 a0 b0 K0)
    (cert1 : PlankDimensionsCertificate C1 a1 b1 K1)
    (e : Space) (he : ‖e‖ = 1)
    (he0 : ⟪e, cert0.box.frame 0⟫_ℝ = 0)
    (he1 : ⟪e, cert1.box.frame 0⟫_ℝ = 0)
    (hangle : 0 < Real.sin
      (InnerProductGeometry.angle (cert0.box.frame 0) (cert1.box.frame 0))) :
    volume ((K0 : Set Space) ∩ (K1 : Set Space)) ≤
      ENNReal.ofReal
          ((Real.sin (InnerProductGeometry.angle
            (cert0.box.frame 0) (cert1.box.frame 0)))⁻¹) *
        2 * (a0 : ENNReal) * (a1 : ENNReal) := by
  have hdir : cert0.box.directionalHalf e ≤ 1 :=
    cert0.directionalHalf_le_one e he he0
  have hdirE : (cert0.box.directionalHalf e : ENNReal) ≤ 1 := by
    exact_mod_cast hdir
  have hfull0 :
      (2 : ENNReal) * ((a0 / 2 : NNReal) : ENNReal) = (a0 : ENNReal) := by
    rw [ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0)]
    exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  have hfull1 :
      (2 : ENNReal) * ((a1 / 2 : NNReal) : ENNReal) = (a1 : ENNReal) := by
    rw [ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0)]
    exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  have hbox := cert0.box.volume_inter_carrier_le_sin_angle
    cert1.box 0 0 e he he0 he1 hangle
  rw [cert0.coordinateHalf_shortAxis,
    cert1.coordinateHalf_shortAxis] at hbox
  calc
    volume ((K0 : Set Space) ∩ (K1 : Set Space)) ≤
        volume (cert0.box.carrier ∩ cert1.box.carrier) :=
      measure_mono (cert0.inter_body_subset_inter_box cert1)
    _ ≤ ENNReal.ofReal
          ((Real.sin (InnerProductGeometry.angle
            (cert0.box.frame 0) (cert1.box.frame 0)))⁻¹) *
        (2 * (cert0.box.directionalHalf e : ENNReal)) *
        (2 * (a0 / 2 : NNReal) : ENNReal) *
        (2 * (a1 / 2 : NNReal) : ENNReal) := hbox
    _ ≤ ENNReal.ofReal
          ((Real.sin (InnerProductGeometry.angle
            (cert0.box.frame 0) (cert1.box.frame 0)))⁻¹) *
        (2 * 1) *
        (2 * (a0 / 2 : NNReal) : ENNReal) *
        (2 * (a1 / 2 : NNReal) : ENNReal) := by
      gcongr
    _ = ENNReal.ofReal
          ((Real.sin (InnerProductGeometry.angle
            (cert0.box.frame 0) (cert1.box.frame 0)))⁻¹) *
        2 * (a0 : ENNReal) * (a1 : ENNReal) := by
      rw [hfull0, hfull1, mul_one]

/-- Positive sine canonically generates the common perpendicular direction
by the normalized cross product. -/
theorem PlankDimensionsCertificate.volume_inter_body_le_sin_angle_auto
    {C0 C1 a0 a1 b0 b1 : NNReal} {K0 K1 : ConvexBody Space}
    (cert0 : PlankDimensionsCertificate C0 a0 b0 K0)
    (cert1 : PlankDimensionsCertificate C1 a1 b1 K1)
    (hangle : 0 < Real.sin
      (InnerProductGeometry.angle (cert0.box.frame 0) (cert1.box.frame 0))) :
    volume ((K0 : Set Space) ∩ (K1 : Set Space)) ≤
      ENNReal.ofReal
          ((Real.sin (InnerProductGeometry.angle
            (cert0.box.frame 0) (cert1.box.frame 0)))⁻¹) *
        2 * (a0 : ENNReal) * (a1 : ENNReal) := by
  let e := transverseUnit (cert0.box.frame 0) (cert1.box.frame 0)
  apply cert0.volume_inter_body_le_sin_angle cert1 e
  · exact norm_transverseUnit_of_unit _ _
      (cert0.box.frame.norm_eq_one 0) (cert1.box.frame.norm_eq_one 0) hangle
  · exact inner_transverseUnit_left _ _
  · exact inner_transverseUnit_right _ _
  · exact hangle

#print axioms IsPlank.nonempty_plankDimensionsCertificate
#print axioms PlankDimensionsCertificate.directionalHalf_le_one
#print axioms PlankDimensionsCertificate.volume_inter_body_le_sin_angle
#print axioms PlankDimensionsCertificate.volume_inter_body_le_sin_angle_auto

end

end Family8CertifiedPlankPairOverlapV2
