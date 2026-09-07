import Family8Grounding.Family8PolynomialJohnFrameBoxContainmentV1
import Submission.Kakeya.ConvexFactoring.BoxDimensionsMeasure

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8PolynomialJohnFrameBoxVolumeV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8PolynomialJohnFrameBoxTestNetV1

noncomputable section

def johnCatalogueVolumeConstant : ENNReal := 64 * (288 : ENNReal) ^ 3

theorem certificate_hasBoxDimensions
    {C : NNReal} {side : Fin 3 → NNReal} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K) :
    HasBoxDimensions C side K :=
  ⟨cert.one_le, cert.box, cert.side_eq, cert.inner_le, cert.outer_le⟩

theorem representative_side_le_two_mul_source
    {delta : NNReal} (hdelta : 0 < delta)
    (p : CapturedJohnParameter delta) (i : Fin 3) :
    let r := representativeParameter delta hdelta (parameterCode hdelta p)
    r.side i ≤ 2 * p.side i := by
  let r := representativeParameter delta hdelta (parameterCode hdelta p)
  have hclose := side_coordinate_close hdelta p i
  change |(p.side i : Real) - (r.side i : Real)| <
    parameterMesh delta at hclose
  have hdiff :
      (r.side i : Real) - (p.side i : Real) < parameterMesh delta := by
    rw [abs_sub_comm] at hclose
    exact (le_abs_self ((r.side i : Real) -
      (p.side i : Real))).trans_lt hclose
  have hlowerNN : 2 * delta ≤ p.side i := p.two_mul_delta_le_side i
  have hlower : 2 * (delta : Real) ≤ (p.side i : Real) := by
    exact_mod_cast hlowerNN
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.2 hdelta
  apply NNReal.coe_le_coe.mp
  push_cast
  dsimp only [parameterMesh] at hdiff
  linarith

theorem representativeTestBody_volume_le_sixtyFour_mul_sideProduct
    {delta : NNReal} (hdelta : 0 < delta)
    (p : CapturedJohnParameter delta) :
    volume (representativeTestBody delta hdelta (parameterCode hdelta p) :
      Set Space) ≤ 64 * ∏ i, (p.side i : ENNReal) := by
  let r := representativeParameter delta hdelta (parameterCode hdelta p)
  have hside (i : Fin 3) :
      (((r.certificate.box.rescale 2).side i : NNReal) : ENNReal) ≤
        4 * (p.side i : ENNReal) := by
    rw [FrameBox.rescale_side, congrFun r.certificate.side_eq i,
      ENNReal.coe_mul]
    have hri := representative_side_le_two_mul_source hdelta p i
    dsimp only [r] at hri
    have hriE : (r.side i : ENNReal) ≤
        2 * (p.side i : ENNReal) := by
      exact_mod_cast hri
    calc
      (2 : ENNReal) * (r.side i : ENNReal) ≤
          2 * (2 * (p.side i : ENNReal)) :=
        mul_le_mul' le_rfl hriE
      _ = 4 * (p.side i : ENNReal) := by ring
  change volume ((r.certificate.box.rescale 2).body : Set Space) ≤ _
  rw [FrameBox.volume_body]
  calc
    ∏ i, (((r.certificate.box.rescale 2).side i : NNReal) : ENNReal) ≤
        ∏ i, 4 * (p.side i : ENNReal) :=
      Finset.prod_le_prod (fun _ _ ↦ bot_le) (fun i _ ↦ hside i)
    _ = 64 * ∏ i, (p.side i : ENNReal) := by
      rw [Finset.prod_mul_distrib]
      norm_num

theorem source_sideProduct_le_johnFactor_mul_volume
    {delta : NNReal} (p : CapturedJohnParameter delta) :
    (∏ i, (p.side i : ENNReal)) ≤
      (288 : ENNReal) ^ 3 * volume (p.body : Set Space) := by
  have hlower :=
    (certificate_hasBoxDimensions p.certificate).volume_lower_bound
  have hcoefficient :
      (288 : ENNReal) ^ 3 *
          (((((288 : NNReal)⁻¹ : NNReal) : ENNReal) ^ 3)) = 1 := by
    rw [ENNReal.coe_inv (by norm_num : (288 : NNReal) ≠ 0)]
    have hcancel : (288 : ENNReal) * (288 : ENNReal)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    calc
      (288 : ENNReal) ^ 3 * (288 : ENNReal)⁻¹ ^ 3 =
          ((288 : ENNReal) * (288 : ENNReal)⁻¹) ^ 3 := by ring
      _ = 1 := by rw [hcancel]; norm_num
  calc
    (∏ i, (p.side i : ENNReal)) =
        (288 : ENNReal) ^ 3 *
          (((((288 : NNReal)⁻¹ : NNReal) : ENNReal) ^ 3) *
            ∏ i, (p.side i : ENNReal)) := by
      rw [← mul_assoc, hcoefficient, one_mul]
    _ ≤ (288 : ENNReal) ^ 3 * volume (p.body : Set Space) :=
      mul_le_mul' le_rfl hlower

theorem representativeTestBody_volume_le_johnCatalogueVolumeConstant
    {delta : NNReal} (hdelta : 0 < delta)
    (p : CapturedJohnParameter delta) :
    volume (representativeTestBody delta hdelta (parameterCode hdelta p) :
      Set Space) ≤
        johnCatalogueVolumeConstant * volume (p.body : Set Space) := by
  calc
    volume (representativeTestBody delta hdelta (parameterCode hdelta p) :
        Set Space) ≤ 64 * ∏ i, (p.side i : ENNReal) :=
      representativeTestBody_volume_le_sixtyFour_mul_sideProduct hdelta p
    _ ≤ 64 * ((288 : ENNReal) ^ 3 * volume (p.body : Set Space)) :=
      mul_le_mul' le_rfl (source_sideProduct_le_johnFactor_mul_volume p)
    _ = johnCatalogueVolumeConstant * volume (p.body : Set Space) := by
      simp only [johnCatalogueVolumeConstant]
      ring

#print axioms representative_side_le_two_mul_source
#print axioms representativeTestBody_volume_le_sixtyFour_mul_sideProduct
#print axioms source_sideProduct_le_johnFactor_mul_volume
#print axioms representativeTestBody_volume_le_johnCatalogueVolumeConstant

end
end Family8PolynomialJohnFrameBoxVolumeV2
