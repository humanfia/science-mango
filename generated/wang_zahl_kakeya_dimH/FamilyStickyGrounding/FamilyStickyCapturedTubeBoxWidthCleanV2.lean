import FamilyStickyGrounding.FamilyStickyConvexCertifiedWidthGrowthV1
import FamilyStickyGrounding.JohnCapturedTubeCertificateCleanAdapterV1
import Submission.Kakeya.ConvexFactoring.CertifiedInducedThickeningLower

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCapturedTubeBoxWidthV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyConvexCertifiedWidthGrowthV1

noncomputable section

/-!
# Widths forced by a captured tube

A positive-radius unit tube inside a convex test body supplies an actual
John-box certificate.  Tube thickness forces every frame-box side to be at
least `2 * delta`; the unit axis forces at least one side to be at least
`1 / 6`.  Consequently a `4 * rho` thickening has only two scale-ratio
losses, plus one dimension-only longitudinal factor.
-/

/-- The unit axis of a captured tube forces at least one outer-box side to
have dimension-only size.  The factor six comes from the repository's
deliberately loose `FrameBox.diameterBound`. -/
theorem BoxDimensionsCertificate.exists_longAxis_of_tube_subset
    {C delta : NNReal} {side : Fin 3 → NNReal}
    {K : ConvexBody Space} (T : Tube delta)
    (hTK : T.carrier ⊆ (K : Set Space))
    (cert : BoxDimensionsCertificate C side K) :
    ∃ j : Fin 3, 1 ≤ 6 * side j := by
  have hbase : T.axis.base ∈ cert.box.carrier :=
    cert.outer_le (hTK (T.axis_subset_carrier T.axis.base_mem_carrier))
  have hend : T.axis.endpoint ∈ cert.box.carrier :=
    cert.outer_le (hTK (T.axis_subset_carrier T.axis.endpoint_mem_carrier))
  have hdistReal : (1 : Real) ≤ (cert.box.diameterBound : Real) := by
    rw [← T.axis.dist_base_endpoint]
    exact cert.box.dist_le_diameterBound hbase hend
  have hdist : (1 : NNReal) ≤ cert.box.diameterBound := by
    exact_mod_cast hdistReal
  rw [FrameBox.diameterBound, Fin.sum_univ_three] at hdist
  rw [cert.side_eq] at hdist
  by_contra hlong
  push Not at hlong
  have h0 := hlong (0 : Fin 3)
  have h1 := hlong (1 : Fin 3)
  have h2 := hlong (2 : Fin 3)
  nlinarith

/-- Uniform factor for each of the two potentially short directions. -/
def shortWidthFactor (delta rho : NNReal) : NNReal :=
  1 + 4 * (rho / delta)

/-- Dimension-only factor for the direction selected by the unit axis. -/
def longWidthFactor (rho : NNReal) : NNReal :=
  1 + 48 * rho

/-- Coordinate factors, with one longitudinal coordinate and two short
coordinates. -/
def tubeBoxWidthFactor (delta rho : NNReal) (longAxis : Fin 3) :
    Fin 3 → NNReal :=
  fun i ↦ if i = longAxis then longWidthFactor rho
    else shortWidthFactor delta rho

/-- A side of length at least `2 * delta` absorbs its `8 * rho` increase
with the stated short-direction factor. -/
theorem widenedSide_le_shortWidthFactor
    {delta rho side : NNReal} (hdelta : 0 < delta)
    (hside : 2 * delta ≤ side) :
    side + 2 * (4 * rho) ≤ shortWidthFactor delta rho * side := by
  have hcancel : (rho / delta) * delta = rho :=
    div_mul_cancel₀ rho hdelta.ne'
  calc
    side + 2 * (4 * rho) = side + 8 * rho := by ring
    _ = side + 4 * (rho / delta) * (2 * delta) := by
      rw [show 4 * (rho / delta) * (2 * delta) =
          8 * ((rho / delta) * delta) by ring, hcancel]
    _ ≤ side + 4 * (rho / delta) * side := by
      gcongr
    _ = shortWidthFactor delta rho * side := by
      rw [shortWidthFactor]
      ring

/-- A side carrying the unit-axis projection absorbs its `8 * rho` increase
with a dimension-only longitudinal factor. -/
theorem widenedSide_le_longWidthFactor
    {rho side : NNReal} (hlong : 1 ≤ 6 * side) :
    side + 2 * (4 * rho) ≤ longWidthFactor rho * side := by
  calc
    side + 2 * (4 * rho) = side + (8 * rho) * 1 := by ring
    _ ≤ side + (8 * rho) * (6 * side) := by
      gcongr
    _ = longWidthFactor rho * side := by
      rw [longWidthFactor]
      ring

/-- The product of the selected coordinate factors has exactly two short
factors. -/
theorem prod_tubeBoxWidthFactor
    (delta rho : NNReal) (longAxis : Fin 3) :
    (∏ i, tubeBoxWidthFactor delta rho longAxis i) =
      longWidthFactor rho * shortWidthFactor delta rho ^ 2 := by
  fin_cases longAxis <;>
    simp [tubeBoxWidthFactor, Fin.prod_univ_three, pow_two] <;> ac_rfl

/-- Explicit dimension/scale loss for thickening a body that captures one
radius-`delta` unit tube. -/
def capturedTubeBoxLoss (delta rho : NNReal) : ENNReal :=
  (288 : ENNReal) ^ 3 *
    ((longWidthFactor rho : NNReal) : ENNReal) *
      (((shortWidthFactor delta rho : NNReal) : ENNReal) ^ 2)

/-- Actual captured-tube geometry produces the closed `4 * rho` thickening
volume comparison.  The only assumptions are positive tube radius and
literal tube containment. -/
theorem volume_four_rho_closedThickening_le_capturedTubeBoxLoss
    {delta rho : NNReal} (hdelta : 0 < delta)
    {K : ConvexBody Space} (T : Tube delta)
    (hTK : T.carrier ⊆ (K : Set Space)) :
    volume (Metric.cthickening ((4 * rho : NNReal) : Real)
        (K : Set Space)) ≤
      capturedTubeBoxLoss delta rho * volume (K : Set Space) := by
  obtain ⟨side, hsidePos, ⟨cert⟩⟩ :=
    exists_positive_boxDimensionsCertificate_288_of_tube_subset_clean
      K T hdelta hTK
  obtain ⟨longAxis, hlong⟩ :=
    FamilyStickyCapturedTubeBoxWidthV1.BoxDimensionsCertificate.exists_longAxis_of_tube_subset
      T hTK cert
  have hdim : HasBoxDimensions 288 side K :=
    ⟨cert.one_le, cert.box, cert.side_eq, cert.inner_le, cert.outer_le⟩
  have hwiden : ∀ i, side i + 2 * (4 * rho) ≤
      tubeBoxWidthFactor delta rho longAxis i * side i := by
    intro i
    by_cases hi : i = longAxis
    · subst i
      simpa [tubeBoxWidthFactor] using
        widenedSide_le_longWidthFactor hlong
    · have hshort : 2 * delta ≤ side i :=
        JohnSideLowerFinal.boxCertificate_side_lower_of_tube_subset
          T hTK cert i
      simpa [tubeBoxWidthFactor, hi] using
        widenedSide_le_shortWidthFactor hdelta hshort
  have hgrowth :=
    FamilyStickyConvexCertifiedWidthGrowthV1.HasBoxDimensions.volume_closedThickening_le_factorProduct
      hdim (factor := tubeBoxWidthFactor delta rho longAxis) (4 * rho) hwiden
  have hprodENN :
      (∏ i, ((tubeBoxWidthFactor delta rho longAxis i : NNReal) : ENNReal)) =
        ((longWidthFactor rho : NNReal) : ENNReal) *
          (((shortWidthFactor delta rho : NNReal) : ENNReal) ^ 2) := by
    exact_mod_cast prod_tubeBoxWidthFactor delta rho longAxis
  rw [hprodENN] at hgrowth
  simpa [capturedTubeBoxLoss, ENNReal.coe_mul, ENNReal.coe_pow,
    mul_assoc] using hgrowth

#print axioms BoxDimensionsCertificate.exists_longAxis_of_tube_subset
#print axioms widenedSide_le_shortWidthFactor
#print axioms widenedSide_le_longWidthFactor
#print axioms prod_tubeBoxWidthFactor
#print axioms volume_four_rho_closedThickening_le_capturedTubeBoxLoss

end
end FamilyStickyCapturedTubeBoxWidthV1
