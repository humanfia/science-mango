import Family8Grounding.Family8SelectedParentJohnPlankSideWidthBridgeV4
import Submission.Kakeya.ConvexFactoring.CertifiedInducedThickeningLower
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentJohnPlankSideWidthBridgeV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnBoxAffineTransportV16
open Family8SelectedParentJohnPlankProductionV18
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyWZ2JohnBoxVolumeNormalizationV1

noncomputable section

/-! ## A common positive scalar contraction in the winning-hull John frame -/

/-- Scalar multiplication by a positive `r`, as a genuine linear
equivalence of the ambient three-space. -/
def scalarDilationLinearEquiv (r : NNReal) (hr : 0 < r) :
    Space ≃ₗ[Real] Space where
  toFun x := (r : Real) • x
  invFun x := ((r : Real)⁻¹) • x
  left_inv x := by
    dsimp
    rw [smul_smul, inv_mul_cancel₀]
    · simp
    · exact_mod_cast hr.ne'
  right_inv x := by
    dsimp
    rw [smul_smul, mul_inv_cancel₀]
    · simp
    · exact_mod_cast hr.ne'
  map_add' x y := by module
  map_smul' c x := by
    simp only [smul_smul, RingHom.id_apply]
    rw [mul_comm]

@[simp] theorem scalarDilationLinearEquiv_apply
    (r : NNReal) (hr : 0 < r) (x : Space) :
    scalarDilationLinearEquiv r hr x = (r : Real) • x := rfl

@[simp] theorem scalarDilationLinearEquiv_symm_apply
    (r : NNReal) (hr : 0 < r) (x : Space) :
    (scalarDilationLinearEquiv r hr).symm x = ((r : Real)⁻¹) • x := rfl

/-- The origin-fixing affine version of `scalarDilationLinearEquiv`. -/
def scalarDilationAffineEquiv (r : NNReal) (hr : 0 < r) :
    Space ≃ᵃ[Real] Space :=
  (scalarDilationLinearEquiv r hr).toAffineEquiv

@[simp] theorem scalarDilationAffineEquiv_apply
    (r : NNReal) (hr : 0 < r) (x : Space) :
    scalarDilationAffineEquiv r hr x = (r : Real) • x := rfl

@[simp] theorem scalarDilationAffineEquiv_symm_apply
    (r : NNReal) (hr : 0 < r) (x : Space) :
    (scalarDilationAffineEquiv r hr).symm x = ((r : Real)⁻¹) • x := rfl

/-- The common winning-hull John normalization followed by one scalar
contraction.  This changes no John axis and is common to the whole block. -/
def contractedJohnAffineEquiv {H : ConvexBody Space}
    (J : PositiveJohnFrame H) (r : NNReal) (hr : 0 < r) :
    Space ≃ᵃ[Real] Space :=
  J.affineEquiv.trans (scalarDilationAffineEquiv r hr)

@[simp] theorem contractedJohnAffineEquiv_apply
    {H : ConvexBody Space} (J : PositiveJohnFrame H)
    (r : NNReal) (hr : 0 < r) (x : Space) :
    contractedJohnAffineEquiv J r hr x =
      (r : Real) • J.affineEquiv x := rfl

/-- Scalar dilation sends the exact normalized John box at side `s` to the
one at side `r*s`. -/
theorem scalarDilation_image_normalizedJohnBox
    {H : ConvexBody Space} (J : PositiveJohnFrame H)
    (r : NNReal) (hr : 0 < r) (s : NNReal) :
    scalarDilationAffineEquiv r hr '' (normalizedJohnBox J s).carrier =
      (normalizedJohnBox J (r * s)).carrier := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [FrameBox.carrier_eq_centeredCoordinateWindow,
      mem_centeredCoordinateWindow_iff]
    intro i
    have hxcoord :=
      (normalizedJohnBox J s).centeredCoordinate_abs_le_halfSide hx i
    simp only [normalizedJohnBox_frame, normalizedJohnBox_center,
      normalizedJohnBox_side, inner_zero_right, sub_zero] at hxcoord
    change |⟪J.certificate.box.frame i, scalarDilationAffineEquiv r hr x⟫_ℝ -
      ⟪J.certificate.box.frame i, (0 : Space)⟫_ℝ| ≤
        (((r * s) / 2 : NNReal) : Real)
    rw [scalarDilationAffineEquiv_apply, inner_zero_right, sub_zero,
      real_inner_smul_right, abs_mul,
      abs_of_pos (show (0 : Real) < (r : Real) by exact_mod_cast hr)]
    calc
      (r : Real) * |⟪J.certificate.box.frame i, x⟫_ℝ| ≤
          (r : Real) * (s : Real) / 2 := by
        nlinarith [show (0 : Real) ≤ (r : Real) by positivity]
      _ = (((r * s) / 2 : NNReal) : Real) := by
        norm_num [NNReal.coe_div, NNReal.coe_mul]
  · intro hy
    let x := (scalarDilationAffineEquiv r hr).symm y
    refine ⟨x, ?_, (scalarDilationAffineEquiv r hr).apply_symm_apply y⟩
    rw [FrameBox.carrier_eq_centeredCoordinateWindow,
      mem_centeredCoordinateWindow_iff]
    intro i
    have hycoord :=
      (normalizedJohnBox J (r * s)).centeredCoordinate_abs_le_halfSide hy i
    simp only [normalizedJohnBox_frame, normalizedJohnBox_center,
      normalizedJohnBox_side, inner_zero_right, sub_zero] at hycoord
    change |⟪J.certificate.box.frame i, x⟫_ℝ -
      ⟪J.certificate.box.frame i, (0 : Space)⟫_ℝ| ≤
        (((s / 2 : NNReal) : Real))
    rw [inner_zero_right, sub_zero]
    dsimp only [x]
    rw [scalarDilationAffineEquiv_symm_apply, real_inner_smul_right, abs_mul,
      abs_of_pos (inv_pos.mpr
        (show (0 : Real) < (r : Real) by exact_mod_cast hr))]
    apply (inv_mul_le_iff₀
      (show (0 : Real) < (r : Real) by exact_mod_cast hr)).2
    norm_num [NNReal.coe_div, NNReal.coe_mul] at hycoord ⊢
    nlinarith [hycoord]

/-! ## A certificate side is bounded by any common outer frame box -/

/-- The positive endpoint of one centered frame-box edge. -/
def _root_.Submission.Kakeya.ConvexGeometry.FrameBox.positiveFacePoint (B : FrameBox) (i : Fin 3) : Space :=
  B.center + ((B.side i : Real) / 2) • B.frame i

/-- The negative endpoint of one centered frame-box edge. -/
def _root_.Submission.Kakeya.ConvexGeometry.FrameBox.negativeFacePoint (B : FrameBox) (i : Fin 3) : Space :=
  B.center - ((B.side i : Real) / 2) • B.frame i

theorem _root_.Submission.Kakeya.ConvexGeometry.FrameBox.positiveFacePoint_mem_carrier
    (B : FrameBox) (i : Fin 3) :
    B.positiveFacePoint i ∈ B.carrier := by
  rw [FrameBox.carrier_eq_centeredCoordinateWindow,
    mem_centeredCoordinateWindow_iff]
  intro j
  simp only [FrameBox.positiveFacePoint, FrameBox.coordinateCenter,
    FrameBox.coordinateHalf, inner_add_right, real_inner_smul_right]
  by_cases hji : j = i
  · subst j
    have hnonneg : 0 ≤ (B.side i : Real) / 2 := by positivity
    simp [NNReal.coe_div,
      abs_of_nonneg hnonneg]
  · have hnonneg : 0 ≤ (B.side j : Real) / 2 := by positivity
    simpa [B.frame.inner_eq_ite, hji, NNReal.coe_div] using hnonneg

theorem _root_.Submission.Kakeya.ConvexGeometry.FrameBox.negativeFacePoint_mem_carrier
    (B : FrameBox) (i : Fin 3) :
    B.negativeFacePoint i ∈ B.carrier := by
  rw [FrameBox.carrier_eq_centeredCoordinateWindow,
    mem_centeredCoordinateWindow_iff]
  intro j
  simp only [FrameBox.negativeFacePoint, FrameBox.coordinateCenter,
    FrameBox.coordinateHalf, inner_sub_right, real_inner_smul_right]
  by_cases hji : j = i
  · subst j
    have hnonneg : 0 ≤ (B.side i : Real) / 2 := by positivity
    simp [NNReal.coe_div,
      abs_of_nonneg hnonneg]
  · have hnonneg : 0 ≤ (B.side j : Real) / 2 := by positivity
    simpa [B.frame.inner_eq_ite, hji, NNReal.coe_div] using hnonneg

theorem _root_.Submission.Kakeya.ConvexGeometry.FrameBox.dist_positiveFacePoint_negativeFacePoint
    (B : FrameBox) (i : Fin 3) :
    dist (B.positiveFacePoint i) (B.negativeFacePoint i) =
      (B.side i : Real) := by
  rw [dist_eq_norm]
  have hsub :
      B.positiveFacePoint i - B.negativeFacePoint i =
        (B.side i : Real) • B.frame i := by
    simp only [FrameBox.positiveFacePoint, FrameBox.negativeFacePoint]
    module
  rw [hsub, norm_smul, B.frame.norm_eq_one, mul_one, Real.norm_eq_abs,
    abs_of_nonneg NNReal.zero_le_coe]

/-- If the body of a box certificate lies in a second frame box, every
certificate side is bounded by `C` times the latter's coarse diameter.  The
proof uses two literal opposite points of the certified inner box. -/
theorem BoxDimensionsCertificate.side_le_comparison_mul_diameterBound
    {C : NNReal} {side : Fin 3 → NNReal} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K) (A : FrameBox)
    (hKA : (K : Set Space) ⊆ A.carrier) (i : Fin 3) :
    side i ≤ C * A.diameterBound := by
  let B := cert.box.rescale C⁻¹
  have hxA : B.positiveFacePoint i ∈ A.carrier :=
    hKA (cert.inner_le (B.positiveFacePoint_mem_carrier i))
  have hyA : B.negativeFacePoint i ∈ A.carrier :=
    hKA (cert.inner_le (B.negativeFacePoint_mem_carrier i))
  have hdist := A.dist_le_diameterBound hxA hyA
  rw [B.dist_positiveFacePoint_negativeFacePoint] at hdist
  have hNN : B.side i ≤ A.diameterBound := by
    exact_mod_cast hdist
  change C⁻¹ * cert.box.side i ≤ A.diameterBound at hNN
  rw [cert.side_eq] at hNN
  have hC : 0 < C := zero_lt_one.trans_le cert.one_le
  exact (inv_mul_le_iff₀ hC).1 hNN

theorem normalizedJohnBox_diameterBound
    {H : ConvexBody Space} (J : PositiveJohnFrame H) (r : NNReal) :
    (normalizedJohnBox J r).diameterBound = 6 * r := by
  simp [FrameBox.diameterBound, normalizedJohnBox]
  ring

/-! ## Actual selected-parent sides in the contracted common frame -/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Every actual selected parent in a greedy block lies in the contracted
common winning-hull John box. -/
theorem selectedParentContracted_subset_normalizedJohnBox
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}) :
    (selectedParentAffineFamily
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber p : Set Space) ⊆
      (normalizedJohnBox
        (selectedParentGreedyBlockJohnFrame S hrho P k) r).carrier := by
  let Q := blockAt S.activeCoarseFamily P k
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  let d := scalarDilationAffineEquiv r hr
  intro y
  rintro ⟨x, hx, rfl⟩
  have hxH : x ∈ (Q.body : Set Space) := by
    exact Q.contained p.1 p.2 hx
  have hxe : J.affineEquiv x ∈ (normalizedJohnBox J 1).carrier := by
    have hbox : x ∈ J.certificate.box.carrier := J.certificate.outer_le hxH
    have himage : J.affineEquiv x ∈
        J.affineEquiv '' J.certificate.box.carrier := ⟨x, hbox, rfl⟩
    have hrescale : J.certificate.box.rescale 1 = J.certificate.box := by
      simp [FrameBox.rescale]
    have hout := image_rescaledBox_subset_normalizedJohnBox J 1
    rw [hrescale] at hout
    exact hout himage
  have hdimage : d (J.affineEquiv x) ∈
      d '' (normalizedJohnBox J 1).carrier := ⟨_, hxe, rfl⟩
  rw [scalarDilation_image_normalizedJohnBox J r hr 1] at hdimage
  simpa [Q, J, d, contractedJohnAffineEquiv] using hdimage

/-- The three actual John sides of every contracted selected parent have the
same explicit upper bound `1728*r`. -/
theorem selectedParentContractedJohnSide_le
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
    (i : Fin 3) :
    selectedParentAffineJohnSide
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho p i ≤
      1728 * r := by
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  let e := contractedJohnAffineEquiv J r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  have hside :=
    BoxDimensionsCertificate.side_le_comparison_mul_diameterBound
      (selectedParentAffineJohnCertificate e S B hrho p)
      (normalizedJohnBox J r)
      (selectedParentContracted_subset_normalizedJohnBox
        S hrho P k r hr p) i
  rw [normalizedJohnBox_diameterBound] at hside
  simpa [J, e, B] using (show
    (288 : NNReal) * (6 * r) = 1728 * r by ring) ▸ hside

/-- Every automatically selected memberwise John side is strictly positive;
this is derived from actual positive tube volume after the common affine
normalization. -/
theorem selectedParentAffineJohnSide_pos
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (p : {p // p ∈ B}) (i : Fin 3) :
    0 < selectedParentAffineJohnSide e S B hrho p i := by
  exact
    BoxDimensionsCertificate.side_pos_of_volume_pos
      (selectedParentAffineJohnCertificate e S B hrho p)
      (selectedParentAffineFamily_volume_pos e S B hrho p) i

#print axioms scalarDilation_image_normalizedJohnBox
#print axioms FrameBox.positiveFacePoint_mem_carrier
#print axioms FrameBox.negativeFacePoint_mem_carrier
#print axioms FrameBox.dist_positiveFacePoint_negativeFacePoint
#print axioms BoxDimensionsCertificate.side_le_comparison_mul_diameterBound
#print axioms selectedParentContracted_subset_normalizedJohnBox
#print axioms selectedParentContractedJohnSide_le
#print axioms selectedParentAffineJohnSide_pos

end
end Family8SelectedParentJohnPlankSideWidthBridgeV5
