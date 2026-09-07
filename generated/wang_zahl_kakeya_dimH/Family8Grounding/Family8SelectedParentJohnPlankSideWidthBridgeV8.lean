import Family8Grounding.Family8SelectedParentJohnPlankSideWidthBridgeV7

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentJohnPlankSideWidthBridgeV8

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

/-! ## Exact scalar transport of a frame box -/

/-- The actual image frame box under positive scalar dilation. -/
def scalarDilationFrameBox (r : NNReal) (B : FrameBox) : FrameBox where
  center := (r : Real) • B.center
  frame := B.frame
  side := fun i ↦ r * B.side i

@[simp] theorem scalarDilationFrameBox_center
    (r : NNReal) (B : FrameBox) :
    (scalarDilationFrameBox r B).center = (r : Real) • B.center := rfl

@[simp] theorem scalarDilationFrameBox_frame
    (r : NNReal) (B : FrameBox) :
    (scalarDilationFrameBox r B).frame = B.frame := rfl

@[simp] theorem scalarDilationFrameBox_side
    (r : NNReal) (B : FrameBox) (i : Fin 3) :
    (scalarDilationFrameBox r B).side i = r * B.side i := rfl

theorem scalarDilationFrameBox_rescale
    (r s : NNReal) (B : FrameBox) :
    scalarDilationFrameBox r (B.rescale s) =
      (scalarDilationFrameBox r B).rescale s := by
  cases B with
  | mk center frame side =>
      simp only [scalarDilationFrameBox, FrameBox.rescale]
      congr 1
      funext i
      ac_rfl

/-- Positive scalar dilation sends a literal frame-box carrier exactly to
the correspondingly centered and side-scaled frame box. -/
theorem scalarDilation_image_frameBox_carrier
    (r : NNReal) (hr : 0 < r) (B : FrameBox) :
    scalarDilationAffineEquiv r hr '' B.carrier =
      (scalarDilationFrameBox r B).carrier := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [FrameBox.carrier_eq_centeredCoordinateWindow,
      mem_centeredCoordinateWindow_iff]
    intro i
    have hxcoord := B.centeredCoordinate_abs_le_halfSide hx i
    change
      |inner Real (B.frame i) (scalarDilationAffineEquiv r hr x) -
        inner Real (B.frame i) ((r : Real) • B.center)| ≤
          (((r * B.side i) / 2 : NNReal) : Real)
    rw [scalarDilationAffineEquiv_apply, real_inner_smul_right,
      real_inner_smul_right, ← mul_sub, abs_mul,
      abs_of_pos (show (0 : Real) < (r : Real) by exact_mod_cast hr)]
    calc
      (r : Real) * |inner Real (B.frame i) x - inner Real (B.frame i) B.center| ≤
          (r : Real) * ((B.side i : Real) / 2) :=
        mul_le_mul_of_nonneg_left hxcoord (by positivity)
      _ = (((r * B.side i) / 2 : NNReal) : Real) := by
        norm_num [NNReal.coe_div, NNReal.coe_mul]
        ring
  · intro hy
    let x := (scalarDilationAffineEquiv r hr).symm y
    refine ⟨x, ?_, (scalarDilationAffineEquiv r hr).apply_symm_apply y⟩
    rw [FrameBox.carrier_eq_centeredCoordinateWindow,
      mem_centeredCoordinateWindow_iff]
    intro i
    have hycoord :=
      (scalarDilationFrameBox r B).centeredCoordinate_abs_le_halfSide hy i
    change
      |inner Real (B.frame i) y -
        inner Real (B.frame i) ((r : Real) • B.center)| ≤
        (((r * B.side i) / 2 : NNReal) : Real) at hycoord
    rw [real_inner_smul_right] at hycoord
    change |inner Real (B.frame i) x - inner Real (B.frame i) B.center| ≤
      (((B.side i) / 2 : NNReal) : Real)
    dsimp only [x]
    rw [scalarDilationAffineEquiv_symm_apply, real_inner_smul_right]
    have hrReal : (0 : Real) < (r : Real) := by exact_mod_cast hr
    have heq :
        (r : Real)⁻¹ * inner Real (B.frame i) y -
            inner Real (B.frame i) B.center =
          (r : Real)⁻¹ *
            (inner Real (B.frame i) y -
              (r : Real) * inner Real (B.frame i) B.center) := by
      field_simp [hrReal.ne']
    rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hrReal)]
    apply (inv_mul_le_iff₀ hrReal).2
    norm_num [NNReal.coe_div, NNReal.coe_mul] at hycoord ⊢
    nlinarith

/-! ## Exact scalar transport of box certificates -/

/-- Scalar dilation transports every part of a box certificate: the body,
outer box, inner box, and all three side lengths. -/
def scalarDilationBoxDimensionsCertificate
    {C : NNReal} {side : Fin 3 → NNReal} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K)
    (r : NNReal) (hr : 0 < r) :
    BoxDimensionsCertificate C (fun i ↦ r * side i)
      (affineImageConvexBody (scalarDilationAffineEquiv r hr) K) where
  one_le := cert.one_le
  box := scalarDilationFrameBox r cert.box
  side_eq := by
    funext i
    simp only [scalarDilationFrameBox_side]
    rw [congrFun cert.side_eq i]
  inner_le := by
    intro x hx
    change x ∈ scalarDilationAffineEquiv r hr '' (K : Set Space)
    change x ∈ ((scalarDilationFrameBox r cert.box).rescale C⁻¹).carrier at hx
    rw [← scalarDilationFrameBox_rescale] at hx
    rw [← scalarDilation_image_frameBox_carrier (r := r) (hr := hr)] at hx
    rcases hx with ⟨y, hy, hxy⟩
    exact ⟨y, cert.inner_le hy, hxy⟩
  outer_le := by
    rintro x ⟨y, hy, rfl⟩
    change scalarDilationAffineEquiv r hr y ∈
      (scalarDilationFrameBox r cert.box).carrier
    rw [← scalarDilation_image_frameBox_carrier (r := r) (hr := hr)]
    exact ⟨y, cert.outer_le hy, rfl⟩

/-- Affine images compose literally at the convex-body level. -/
theorem affineImageConvexBody_trans
    (e d : Space ≃ᵃ[Real] Space) (K : ConvexBody Space) :
    affineImageConvexBody d (affineImageConvexBody e K) =
      affineImageConvexBody (e.trans d) K := by
  apply ConvexBody.ext
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨e z, ⟨z, hz, rfl⟩, rfl⟩

/-- The common affine normalization attached to one occupied side bucket. -/
def bucketNormalizedAffineEquiv
    (e : Space ≃ᵃ[Real] Space) (label : Fin 3 → Int) :
    Space ≃ᵃ[Real] Space :=
  e.trans (scalarDilationAffineEquiv
    (sideShapeUpper label 2)⁻¹
    (inv_pos.mpr (sideShapeUpper_pos label 2)))

theorem scalarNormalizedRelabeledSide_eq
    (source : Fin 3 → NNReal) (label : Fin 3 → Int) :
    (fun i ↦ (sideShapeUpper label 2)⁻¹ *
      relabeledSide source (transverseOrderPermutation label) i) =
        normalizedBucketSide source label := by
  funext i
  simp only [normalizedBucketSide, div_eq_mul_inv]
  ac_rfl

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The body transport used by the bucket certificate has the exact scalar
Jacobian on volume; the transverse permutation is only a carrier-preserving
relabeling of the same frame box. -/
theorem selectedParentNormalizedBucket_volume
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (label : Fin 3 → Int)
    (p : {p // p ∈ B}) :
    volume
        (selectedParentAffineFamily
          (bucketNormalizedAffineEquiv e label) S B p : Set Space) =
      affineJacobian
          (scalarDilationAffineEquiv
            (sideShapeUpper label 2)⁻¹
            (inv_pos.mpr (sideShapeUpper_pos label 2))) *
        volume (selectedParentAffineFamily e S B p : Set Space) := by
  rw [selectedParentAffineFamily_apply, selectedParentAffineFamily_apply,
    bucketNormalizedAffineEquiv]
  rw [← affineImageConvexBody_trans, volume_affineImageConvexBody]

/-- In particular, the normalized actual parent keeps positive volume; this
uses positivity of the genuine affine Jacobian, not a synthetic body premise. -/
theorem selectedParentNormalizedBucket_volume_pos
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int) (p : {p // p ∈ B}) :
    0 < volume
      (selectedParentAffineFamily
        (bucketNormalizedAffineEquiv e label) S B p : Set Space) :=
  selectedParentAffineFamily_volume_pos
    (bucketNormalizedAffineEquiv e label) S B hrho p

/-- The normalized side envelope in V7 is backed by an actual certificate
for the actual parent under the common bucket affine map. -/
noncomputable def selectedParentNormalizedBucketCertificate
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int) (p : {p // p ∈ B}) :
    BoxDimensionsCertificate 288
      (normalizedBucketSide
        (selectedParentLongRelabeledSide e S B hrho p) label)
      (selectedParentAffineFamily
        (bucketNormalizedAffineEquiv e label) S B p) := by
  let cert₀ := selectedParentLongRelabeledCertificate e S B hrho p
  let cert₁ := relabelBoxDimensionsCertificate cert₀
    (transverseOrderPermutation label)
  let d := scalarDilationAffineEquiv
    (sideShapeUpper label 2)⁻¹
    (inv_pos.mpr (sideShapeUpper_pos label 2))
  let cert₂ := scalarDilationBoxDimensionsCertificate cert₁
    (sideShapeUpper label 2)⁻¹
    (inv_pos.mpr (sideShapeUpper_pos label 2))
  have hside :
      (fun i ↦ (sideShapeUpper label 2)⁻¹ *
        relabeledSide (selectedParentLongRelabeledSide e S B hrho p)
          (transverseOrderPermutation label) i) =
        normalizedBucketSide
          (selectedParentLongRelabeledSide e S B hrho p) label :=
    scalarNormalizedRelabeledSide_eq _ _
  have hbody :
      affineImageConvexBody d (selectedParentAffineFamily e S B p) =
        selectedParentAffineFamily
          (bucketNormalizedAffineEquiv e label) S B p := by
    change affineImageConvexBody d
        (affineImageConvexBody e (S.activeCoarseFamily p.1)) =
      affineImageConvexBody (e.trans d) (S.activeCoarseFamily p.1)
    exact affineImageConvexBody_trans e d _
  exact hbody ▸ hside ▸ cert₂

/-- V4's consumer now produces a genuine actual `IsPlank`; it is not a
premise or callback.  The comparison constant is explicitly `576`. -/
theorem selectedParentNormalizedBucket_isPlank
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int) (p : {p // p ∈ B})
    (hb : bucketShortB label ≤ 1)
    (hwidth : SideWidthEnvelope
      (normalizedBucketSide
        (selectedParentLongRelabeledSide e S B hrho p) label)
      (plankSides (bucketShortA label) (bucketShortB label)) 2) :
    IsPlank 576 (bucketShortA label) (bucketShortB label)
      (selectedParentAffineFamily
        (bucketNormalizedAffineEquiv e label) S B p) := by
  have h := isPlank_of_boxCertificate_sideWidthEnvelope
    (selectedParentNormalizedBucketCertificate e S B hrho label p)
    (bucketShortA_pos label) (bucketShortA_le_bucketShortB label) hb hwidth
  simpa only [show (288 : NNReal) * 2 = 576 by norm_num] using h

/-! ## Fully actual weighted bucket-to-plank production -/

/-- Actual selected parents admit a retained dyadic bucket on which the
same common affine normalization makes every member a `576`-plank with the
same anisotropic short sides `a,b`. -/
theorem exists_selectedParentActualIsPlankBucket_weight_retention
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (weight :
      {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber} → Real) :
    let parent := {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let side : parent → Fin 3 → NNReal := fun p ↦
      selectedParentLongRelabeledSide e S
        (blockAt S.activeCoarseFamily P k).fiber hrho p
    ∃ label : Fin 3 → Int,
      label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
        (fun p ↦ sideShapeLabel (side p)) ∧
      (∑ p : parent, weight p) ≤
        (occupiedWeightBuckets (Finset.univ : Finset parent)
          (fun p ↦ sideShapeLabel (side p))).card *
          (∑ p ∈ sideShapeBucket Finset.univ side label, weight p) ∧
      0 < bucketShortA label ∧
      bucketShortA label ≤ bucketShortB label ∧
      bucketShortB label ≤ 1 ∧
      ∀ p, p ∈ sideShapeBucket Finset.univ side label →
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv e label) S
            (blockAt S.activeCoarseFamily P k).fiber p) := by
  dsimp only
  have hbucket :=
    exists_selectedParentNormalizedPlankBucket_weight_retention
      S hrho P k r hr weight
  dsimp only at hbucket
  obtain ⟨label, hoccupied, hweight, ha, hab, hb, hwidth⟩ := hbucket
  refine ⟨label, hoccupied, hweight, ha, hab, hb, ?_⟩
  intro p hp
  exact selectedParentNormalizedBucket_isPlank _ S _ hrho label p hb
    (hwidth p hp)

#print axioms scalarDilation_image_frameBox_carrier
#print axioms scalarDilationBoxDimensionsCertificate
#print axioms affineImageConvexBody_trans
#print axioms selectedParentNormalizedBucket_volume
#print axioms selectedParentNormalizedBucket_volume_pos
#print axioms selectedParentNormalizedBucketCertificate
#print axioms selectedParentNormalizedBucket_isPlank
#print axioms exists_selectedParentActualIsPlankBucket_weight_retention

end
end Family8SelectedParentJohnPlankSideWidthBridgeV8
