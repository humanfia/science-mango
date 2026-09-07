import FamilyStickyRandomFiniteFloorParameterNetV1
import FamilyStickyGrounding.JohnCapturedTubeCertificateCleanAdapterV1
import Submission.Kakeya.ConvexFactoring.FrameBoxCoordinateWindowEquiv
import Submission.Kakeya.ConvexFactoring.FrameBoxVolume
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace BigOperators

namespace Family8PolynomialJohnFrameBoxTestNetV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyRandomFiniteFloorParameterNetV1

noncomputable section

/-!
# A polynomial floor catalogue of actual John frame boxes

The canonical-hull catalogue has one test for every nonempty tube subset and
is therefore exponential.  Here a source parameter is an *actual* John
certificate for a convex body already clipped to the unit ball and containing
a positive-radius tube.  We encode only fifteen bounded real coordinates:
three center coordinates, nine frame-matrix coordinates, and three side
lengths.  Occupied floor cells retain a genuine source representative, hence
in particular a genuine orthonormal frame and a genuine John certificate.

No coverage assertion or cardinal estimate is stored in data.  Coverage is
proved below from equality of floor codes, and the cardinality is inherited
from the explicit integer product box of
`FamilyStickyRandomFiniteFloorParameterNetV1`.
-/

/-- Intersection with the normalized unit ball, packaged as a convex body.
The captured tube supplies nonemptiness. -/
def clippedUnitBallBody {delta : NNReal} (K : ConvexBody Space)
    (T : Tube delta) (hTK : T.carrier ⊆ (K : Set Space))
    (hTU : T.carrier ⊆ Metric.closedBall (0 : Space) 1) :
    ConvexBody Space where
  carrier := (K : Set Space) ∩ Metric.closedBall (0 : Space) 1
  convex' := K.convex.inter (convex_closedBall (0 : Space) 1)
  isCompact' := K.isCompact.inter_right Metric.isClosed_closedBall
  nonempty' := by
    have hbaseTube : T.axis.base ∈ T.carrier :=
      Metric.closedBall_subset_cthickening T.axis.base_mem_carrier
        (delta : Real) (Metric.mem_closedBall_self NNReal.zero_le_coe)
    exact ⟨T.axis.base, hTK hbaseTube, hTU hbaseTube⟩

@[simp] theorem coe_clippedUnitBallBody {delta : NNReal}
    (K : ConvexBody Space) (T : Tube delta)
    (hTK : T.carrier ⊆ (K : Set Space))
    (hTU : T.carrier ⊆ Metric.closedBall (0 : Space) 1) :
    (clippedUnitBallBody K T hTK hTU : Set Space) =
      (K : Set Space) ∩ Metric.closedBall (0 : Space) 1 := rfl

theorem tube_subset_clippedUnitBallBody {delta : NNReal}
    (K : ConvexBody Space) (T : Tube delta)
    (hTK : T.carrier ⊆ (K : Set Space))
    (hTU : T.carrier ⊆ Metric.closedBall (0 : Space) 1) :
    T.carrier ⊆ (clippedUnitBallBody K T hTK hTU : Set Space) :=
  fun _ hx => ⟨hTK hx, hTU hx⟩

theorem clippedUnitBallBody_subset_unitBall {delta : NNReal}
    (K : ConvexBody Space) (T : Tube delta)
    (hTK : T.carrier ⊆ (K : Set Space))
    (hTU : T.carrier ⊆ Metric.closedBall (0 : Space) 1) :
    (clippedUnitBallBody K T hTK hTU : Set Space) ⊆
      Metric.closedBall (0 : Space) 1 :=
  fun _ hx => hx.2

/-- The honest source objects whose bounded coordinates are discretized. -/
structure CapturedJohnParameter (delta : NNReal) where
  body : ConvexBody Space
  witnessTube : Tube delta
  tube_subset_body : witnessTube.carrier ⊆ (body : Set Space)
  body_subset_unitBall : (body : Set Space) ⊆
    Metric.closedBall (0 : Space) 1
  side : Fin 3 → NNReal
  certificate : BoxDimensionsCertificate 288 side body

/-- A captured tube in an arbitrary convex body produces an actual parameter
after intersecting the body with the unit ball. -/
noncomputable def CapturedJohnParameter.ofCapturedTube
    {delta : NNReal} (hdelta : 0 < delta)
    (K : ConvexBody Space) (T : Tube delta)
    (hTK : T.carrier ⊆ (K : Set Space))
    (hTU : T.carrier ⊆ Metric.closedBall (0 : Space) 1) :
    CapturedJohnParameter delta := by
  let Kcap := clippedUnitBallBody K T hTK hTU
  have hTcap : T.carrier ⊆ (Kcap : Set Space) :=
    tube_subset_clippedUnitBallBody K T hTK hTU
  let hex := exists_positive_boxDimensionsCertificate_288_of_tube_subset_clean
    Kcap T hdelta hTcap
  let side : Fin 3 → NNReal := Classical.choose hex
  have hsideCert := Classical.choose_spec hex
  let cert : BoxDimensionsCertificate 288 side Kcap :=
    Classical.choice hsideCert.2
  exact {
    body := Kcap
    witnessTube := T
    tube_subset_body := hTcap
    body_subset_unitBall :=
      clippedUnitBallBody_subset_unitBall K T hTK hTU
    side := side
    certificate := cert }

/-- Every John side is at least the transverse diameter of the captured
tube. -/
theorem CapturedJohnParameter.two_mul_delta_le_side
    {delta : NNReal} (p : CapturedJohnParameter delta) (i : Fin 3) :
    2 * delta ≤ p.side i :=
  JohnSideLowerFinal.boxCertificate_side_lower_of_tube_subset
    p.witnessTube p.tube_subset_body p.certificate i

/-- The center of the John box belongs to the clipped body. -/
theorem CapturedJohnParameter.center_mem_body
    {delta : NNReal} (p : CapturedJohnParameter delta) :
    p.certificate.box.center ∈ (p.body : Set Space) := by
  apply p.certificate.inner_le
  change p.certificate.box.center ∈
    (p.certificate.box.rescale (288 : NNReal)⁻¹).carrier
  simpa using
    (p.certificate.box.rescale (288 : NNReal)⁻¹).center_mem_carrier

theorem CapturedJohnParameter.center_mem_unitBall
    {delta : NNReal} (p : CapturedJohnParameter delta) :
    p.certificate.box.center ∈ Metric.closedBall (0 : Space) 1 :=
  p.body_subset_unitBall p.center_mem_body

theorem CapturedJohnParameter.norm_center_le_one
    {delta : NNReal} (p : CapturedJohnParameter delta) :
    ‖p.certificate.box.center‖ ≤ 1 := by
  simpa [Metric.mem_closedBall, dist_eq_norm] using p.center_mem_unitBall

theorem CapturedJohnParameter.abs_center_apply_le_one
    {delta : NNReal} (p : CapturedJohnParameter delta) (i : Fin 3) :
    |p.certificate.box.center i| ≤ 1 := by
  have h := PiLp.norm_apply_le p.certificate.box.center i
  rw [Real.norm_eq_abs] at h
  exact h.trans p.norm_center_le_one

theorem CapturedJohnParameter.abs_frame_apply_le_one
    {delta : NNReal} (p : CapturedJohnParameter delta) (i j : Fin 3) :
    |(p.certificate.box.frame i) j| ≤ 1 := by
  have h := PiLp.norm_apply_le (p.certificate.box.frame i) j
  rw [Real.norm_eq_abs, p.certificate.box.frame.norm_eq_one] at h
  exact h

/-- Positive endpoint of one axis of the inner `1/288` John box. -/
def CapturedJohnParameter.innerAxisEndpoint
    {delta : NNReal} (p : CapturedJohnParameter delta) (i : Fin 3) : Space :=
  p.certificate.box.center +
    (((((288 : NNReal)⁻¹ : NNReal) : Real) * (p.side i : Real) / 2) •
      p.certificate.box.frame i)

theorem CapturedJohnParameter.innerAxisEndpoint_mem_innerBox
    {delta : NNReal} (p : CapturedJohnParameter delta) (i : Fin 3) :
    p.innerAxisEndpoint i ∈
      (p.certificate.box.rescale (288 : NNReal)⁻¹).carrier := by
  apply FrameBox.centeredCoordinateWindow_subset_carrier
  rw [TransverseCoordinateOverlap.mem_centeredCoordinateWindow_iff]
  intro j
  simp only [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
    FrameBox.rescale_frame, FrameBox.rescale_center,
    FrameBox.rescale_side, innerAxisEndpoint, inner_add_right,
    real_inner_smul_right]
  rw [congrFun p.certificate.side_eq j]
  have hscalar (k : Fin 3) :
      0 ≤ (((288 : NNReal)⁻¹ : NNReal) : Real) * (p.side k : Real) / 2 := by
    positivity
  by_cases hji : j = i
  · subst j
    have hii : ⟪p.certificate.box.frame i,
        p.certificate.box.frame i⟫_Real = 1 := by simp
    rw [hii, mul_one, add_sub_cancel_left,
      abs_of_nonneg (hscalar i)]
    norm_num
  · have hjiInner : ⟪p.certificate.box.frame j,
        p.certificate.box.frame i⟫_Real = 0 := by
      rw [p.certificate.box.frame.inner_eq_ite]
      simp [hji]
    rw [hjiInner, mul_zero, add_zero, sub_self, abs_zero]
    positivity

theorem CapturedJohnParameter.innerAxisEndpoint_mem_unitBall
    {delta : NNReal} (p : CapturedJohnParameter delta) (i : Fin 3) :
    p.innerAxisEndpoint i ∈ Metric.closedBall (0 : Space) 1 := by
  apply p.body_subset_unitBall
  apply p.certificate.inner_le
  change p.innerAxisEndpoint i ∈
    (p.certificate.box.rescale (288 : NNReal)⁻¹).carrier
  exact p.innerAxisEndpoint_mem_innerBox i

/-- Clipping to the unit ball gives a uniform upper bound for every John
side.  Together with `two_mul_delta_le_side`, this is the compact parameter
window needed by the floor catalogue. -/
theorem CapturedJohnParameter.side_le_1152
    {delta : NNReal} (p : CapturedJohnParameter delta) (i : Fin 3) :
    p.side i ≤ 1152 := by
  have hend := p.innerAxisEndpoint_mem_unitBall i
  have hcenter := p.center_mem_unitBall
  have hdist : dist (p.innerAxisEndpoint i) p.certificate.box.center ≤ 2 := by
    exact (dist_triangle _ (0 : Space) _).trans (by
      rw [dist_comm (p.innerAxisEndpoint i) 0]
      have he : dist (0 : Space) (p.innerAxisEndpoint i) ≤ 1 := by
        simpa [Metric.mem_closedBall] using hend
      have hc : dist (0 : Space) p.certificate.box.center ≤ 1 := by
        simpa [Metric.mem_closedBall] using hcenter
      linarith)
  have hcalc :
      dist (p.innerAxisEndpoint i) p.certificate.box.center =
        (((288 : NNReal)⁻¹ * p.side i : NNReal) : Real) / 2 := by
    rw [dist_eq_norm]
    simp [innerAxisEndpoint, norm_smul]
  rw [hcalc] at hdist
  apply NNReal.coe_le_coe.mp
  norm_num at hdist ⊢
  linarith

/-- Fifteen scalar coordinates: center (3), frame matrix (9), sides (3). -/
abbrev CoordinateIndex := (Fin 3) ⊕ ((Fin 3 × Fin 3) ⊕ Fin 3)

@[simp] theorem card_coordinateIndex : Fintype.card CoordinateIndex = 15 := by
  simp [CoordinateIndex]

def parameterCoordinate {delta : NNReal} (p : CapturedJohnParameter delta) :
    CoordinateIndex → Real
  | Sum.inl i => p.certificate.box.center i
  | Sum.inr (Sum.inl ij) => (p.certificate.box.frame ij.1) ij.2
  | Sum.inr (Sum.inr i) => p.side i

def coordinateBound : Real := 1152

theorem abs_parameterCoordinate_le_coordinateBound
    {delta : NNReal} (p : CapturedJohnParameter delta)
    (k : CoordinateIndex) :
    |parameterCoordinate p k| ≤ coordinateBound := by
  rcases k with i | ij
  · exact (p.abs_center_apply_le_one i).trans (by norm_num [coordinateBound])
  · rcases ij with ij | i
    · exact (p.abs_frame_apply_le_one ij.1 ij.2).trans
        (by norm_num [coordinateBound])
    · change |(p.side i : Real)| ≤ coordinateBound
      rw [abs_of_nonneg (NNReal.zero_le_coe : 0 ≤ (p.side i : Real))]
      exact_mod_cast p.side_le_1152 i

/-- Mesh `delta/20`; the constant leaves enough room for a factor-two
enlargement after perturbing all fifteen coordinates. -/
def parameterMesh (delta : NNReal) : Real := (delta : Real) / 20

theorem parameterMesh_pos {delta : NNReal} (hdelta : 0 < delta) :
    0 < parameterMesh delta := by
  exact div_pos (NNReal.coe_pos.2 hdelta) (by norm_num)

/-- The actual occupied parameter cells. -/
abbrev CatalogueIndex (delta : NNReal) (hdelta : 0 < delta) :=
  OccupiedCode (parameterMesh delta) coordinateBound
    (parameterMesh_pos hdelta) (@parameterCoordinate delta)
    (@abs_parameterCoordinate_le_coordinateBound delta)

/-- The genuine John parameter chosen from an occupied cell. -/
noncomputable def representativeParameter
    (delta : NNReal) (hdelta : 0 < delta)
    (q : CatalogueIndex delta hdelta) : CapturedJohnParameter delta :=
  representative (parameterMesh delta) coordinateBound
    (parameterMesh_pos hdelta) (@parameterCoordinate delta)
    (@abs_parameterCoordinate_le_coordinateBound delta) q

/-- The polynomial catalogue uses a factor-two enlargement of the genuine
representative John box. -/
noncomputable def representativeTestBox
    (delta : NNReal) (hdelta : 0 < delta)
    (q : CatalogueIndex delta hdelta) : FrameBox :=
  (representativeParameter delta hdelta q).certificate.box.rescale 2

noncomputable def representativeTestBody
    (delta : NNReal) (hdelta : 0 < delta)
    (q : CatalogueIndex delta hdelta) : ConvexBody Space :=
  (representativeTestBox delta hdelta q).body

/-- Exact floor-polynomial cardinality bound; the exponent is literally the
fifteen encoded real coordinates. -/
theorem card_catalogueIndex_le_floorPolynomial
    (delta : NNReal) (hdelta : 0 < delta) :
    Fintype.card (CatalogueIndex delta hdelta) ≤
      ((Int.floor (coordinateBound / parameterMesh delta) + 1 -
          Int.floor (-coordinateBound / parameterMesh delta)).toNat) ^ 15 := by
  simpa only [card_coordinateIndex] using
    card_occupiedCode_le (parameterMesh delta) coordinateBound
      (parameterMesh_pos hdelta) (@parameterCoordinate delta)
      (@abs_parameterCoordinate_le_coordinateBound delta)

/-- Every source parameter has a canonical occupied cell. -/
def parameterCode {delta : NNReal} (hdelta : 0 < delta)
    (p : CapturedJohnParameter delta) : CatalogueIndex delta hdelta :=
  ownCode (parameterMesh delta) coordinateBound
    (parameterMesh_pos hdelta) (@parameterCoordinate delta)
    (@abs_parameterCoordinate_le_coordinateBound delta) p

theorem parameter_representative_coordinate_close
    {delta : NNReal} (hdelta : 0 < delta)
    (p : CapturedJohnParameter delta) (k : CoordinateIndex) :
    |parameterCoordinate p k - parameterCoordinate
      (representativeParameter delta hdelta (parameterCode hdelta p)) k| <
        parameterMesh delta := by
  exact abs_coord_sub_representative_ownCode_lt
    (parameterMesh_pos hdelta) (@parameterCoordinate delta)
    (@abs_parameterCoordinate_le_coordinateBound delta) p k

theorem center_coordinate_close
    {delta : NNReal} (hdelta : 0 < delta)
    (p : CapturedJohnParameter delta) (i : Fin 3) :
    |p.certificate.box.center i -
      (representativeParameter delta hdelta
        (parameterCode hdelta p)).certificate.box.center i| <
      parameterMesh delta :=
  parameter_representative_coordinate_close hdelta p (Sum.inl i)

theorem frame_coordinate_close
    {delta : NNReal} (hdelta : 0 < delta)
    (p : CapturedJohnParameter delta) (i j : Fin 3) :
    |(p.certificate.box.frame i) j -
      ((representativeParameter delta hdelta
        (parameterCode hdelta p)).certificate.box.frame i) j| <
      parameterMesh delta :=
  parameter_representative_coordinate_close hdelta p
    (Sum.inr (Sum.inl (i, j)))

theorem side_coordinate_close
    {delta : NNReal} (hdelta : 0 < delta)
    (p : CapturedJohnParameter delta) (i : Fin 3) :
    |(p.side i : Real) -
      ((representativeParameter delta hdelta
        (parameterCode hdelta p)).side i : Real)| <
      parameterMesh delta :=
  parameter_representative_coordinate_close hdelta p
    (Sum.inr (Sum.inr i))

#print axioms coe_clippedUnitBallBody
#print axioms CapturedJohnParameter.ofCapturedTube
#print axioms CapturedJohnParameter.two_mul_delta_le_side
#print axioms CapturedJohnParameter.side_le_1152
#print axioms abs_parameterCoordinate_le_coordinateBound
#print axioms card_catalogueIndex_le_floorPolynomial
#print axioms parameter_representative_coordinate_close

end
end Family8PolynomialJohnFrameBoxTestNetV1
