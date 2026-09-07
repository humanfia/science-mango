import Family8Grounding.Family8SelectedParentJohnPlankProductionV18
import FamilyStickyGrounding.FamilyStickyWZ2JohnBoxVolumeNormalizationV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentJohnPlankSideWidthBridgeV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankProductionV18
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyWZ2JohnBoxVolumeNormalizationV1

noncomputable section

/-- Replace only the side vector of a frame box. -/
def rebox (B : FrameBox) (side : Fin 3 → NNReal) : FrameBox where
  center := B.center
  frame := B.frame
  side := side

@[simp] theorem rebox_center (B : FrameBox) (side : Fin 3 → NNReal) :
    (rebox B side).center = B.center := rfl

@[simp] theorem rebox_frame (B : FrameBox) (side : Fin 3 → NNReal) :
    (rebox B side).frame = B.frame := rfl

@[simp] theorem rebox_side (B : FrameBox) (side : Fin 3 → NNReal)
    (i : Fin 3) : (rebox B side).side i = side i := rfl

/-- Coordinatewise side enlargement with fixed center and frame enlarges the
carrier. -/
theorem FrameBox.carrier_subset_of_same_center_frame_side
    (B D : FrameBox) (hcenter : B.center = D.center)
    (hframe : B.frame = D.frame) (hside : ∀ i, B.side i ≤ D.side i) :
    B.carrier ⊆ D.carrier := by
  intro x hx
  rw [D.carrier_eq_centeredCoordinateWindow,
    mem_centeredCoordinateWindow_iff]
  intro i
  have hcoord := B.centeredCoordinate_abs_le_halfSide hx i
  simp only [FrameBox.coordinateCenter, FrameBox.coordinateHalf]
  rw [← hcenter, ← hframe]
  have hs : (B.side i : Real) ≤ (D.side i : Real) := by
    exact_mod_cast hside i
  exact hcoord.trans (by
    norm_num [NNReal.coe_div]
    linarith)

/-- An honest common coordinate-width envelope. -/
structure SideWidthEnvelope (source target : Fin 3 → NNReal)
    (L : NNReal) : Prop where
  one_le : 1 ≤ L
  source_le_target : ∀ i, source i ≤ target i
  target_le_mul_source : ∀ i, target i ≤ L * source i

/-- Reboxing a `C₀` certificate at sides within factor `L` gives comparison
constant exactly `C₀ * L`. -/
theorem hasBoxDimensions_rebox_of_sideWidthEnvelope
    {C₀ L : NNReal} {source target : Fin 3 → NNReal}
    {K : ConvexBody Space} (cert : BoxDimensionsCertificate C₀ source K)
    (hwidth : SideWidthEnvelope source target L) :
    HasBoxDimensions (C₀ * L) target K := by
  refine ⟨one_le_mul cert.one_le hwidth.one_le, rebox cert.box target,
    rfl, ?_, ?_⟩
  · intro x hx
    change x ∈ ((rebox cert.box target).rescale (C₀ * L)⁻¹).carrier at hx
    apply cert.inner_le
    apply FrameBox.carrier_subset_of_same_center_frame_side
      ((rebox cert.box target).rescale (C₀ * L)⁻¹)
      (cert.box.rescale C₀⁻¹)
    · rfl
    · rfl
    · intro i
      simp only [FrameBox.rescale_side, rebox_side]
      rw [cert.side_eq]
      have hLpos : 0 < L := zero_lt_one.trans_le hwidth.one_le
      have hC₀pos : 0 < C₀ := zero_lt_one.trans_le cert.one_le
      calc
        (C₀ * L)⁻¹ * target i = C₀⁻¹ * (L⁻¹ * target i) := by
          apply NNReal.eq
          norm_num [NNReal.coe_mul, NNReal.coe_inv]
          field_simp [hC₀pos.ne', hLpos.ne']
        _ ≤ C₀⁻¹ * source i := by
          gcongr
          exact (inv_mul_le_iff₀ hLpos).2
            (hwidth.target_le_mul_source i)
    exact hx
  · intro x hx
    apply FrameBox.carrier_subset_of_same_center_frame_side cert.box
      (rebox cert.box target)
    · rfl
    · rfl
    · intro i
      rw [cert.side_eq]
      exact hwidth.source_le_target i
    exact cert.outer_le hx

/-- Exact `IsPlank` consumer form. -/
theorem isPlank_of_boxCertificate_sideWidthEnvelope
    {C₀ L a b : NNReal} {source : Fin 3 → NNReal}
    {K : ConvexBody Space} (cert : BoxDimensionsCertificate C₀ source K)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    (hwidth : SideWidthEnvelope source (plankSides a b) L) :
    IsPlank (C₀ * L) a b K :=
  ⟨ha, hab, hb, hasBoxDimensions_rebox_of_sideWidthEnvelope cert hwidth⟩

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- An actual selected parent remains positive-volume after the common affine
normalization. -/
theorem selectedParentAffineFamily_volume_pos
    (e : Space ≃ᵃ[ℝ] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (p : {p // p ∈ B}) :
    0 < volume (selectedParentAffineFamily e S B p : Set Space) := by
  rw [selectedParentAffineFamily_apply, volume_affineImageConvexBody]
  apply ENNReal.mul_pos (affineJacobian_pos e).ne'
  simpa [FamilyStickyAtEveryScaleCoreV1.StickyScaleCover.activeCoarseFamily,
    UniformTubeFamily.bodyFamily] using
      (S.coarse.tubes p.1.1).volume_pos hrho |>.ne'

/-- Automatically chosen John side vector for a normalized selected parent. -/
noncomputable def selectedParentAffineJohnSide
    (e : Space ≃ᵃ[ℝ] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (p : {p // p ∈ B}) : Fin 3 → NNReal :=
  Classical.choose
    (exists_boxDimensionsCertificate_288_of_finrank_direction_affineSpan_eq_three2
      (selectedParentAffineFamily e S B p)
      (finrank_direction_affineSpan_eq_three_of_volume_pos
        (selectedParentAffineFamily e S B p)
        (selectedParentAffineFamily_volume_pos e S B hrho p)))

/-- The automatic genuine certificate behind the chosen side vector. -/
noncomputable def selectedParentAffineJohnCertificate
    (e : Space ≃ᵃ[ℝ] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (p : {p // p ∈ B}) :
    BoxDimensionsCertificate 288
      (selectedParentAffineJohnSide e S B hrho p)
      (selectedParentAffineFamily e S B p) :=
  Classical.choice (Classical.choose_spec
    (exists_boxDimensionsCertificate_288_of_finrank_direction_affineSpan_eq_three2
      (selectedParentAffineFamily e S B p)
      (finrank_direction_affineSpan_eq_three_of_volume_pos
        (selectedParentAffineFamily e S B p)
        (selectedParentAffineFamily_volume_pos e S B hrho p))))

/-- V18 with `hplank` discharged from an honest common side-width envelope.
The resulting member comparison constant is exactly `288 * L`. -/
noncomputable def selectedParentGreedyBlockJohnPlankFamily_of_sideWidthEnvelope
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (a b L : NNReal) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    (hwidth : ∀ p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber},
      SideWidthEnvelope
        (selectedParentAffineJohnSide
          (selectedParentGreedyBlockJohnFrame S hrho P k).affineEquiv S
          (blockAt S.activeCoarseFamily P k).fiber hrho p)
        (plankSides a b) L) :
    ShadedConvexPlankFamily
      {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber} a b :=
  selectedParentGreedyBlockJohnPlankFamily S Y hrho P k (288 * L) a b
    (fun p ↦ isPlank_of_boxCertificate_sideWidthEnvelope
      (selectedParentAffineJohnCertificate
        (selectedParentGreedyBlockJohnFrame S hrho P k).affineEquiv S
        (blockAt S.activeCoarseFamily P k).fiber hrho p)
      ha hab hb (hwidth p))

#print axioms FrameBox.carrier_subset_of_same_center_frame_side
#print axioms hasBoxDimensions_rebox_of_sideWidthEnvelope
#print axioms isPlank_of_boxCertificate_sideWidthEnvelope
#print axioms selectedParentAffineFamily_volume_pos
#print axioms selectedParentAffineJohnSide
#print axioms selectedParentAffineJohnCertificate
#print axioms selectedParentGreedyBlockJohnPlankFamily_of_sideWidthEnvelope

end
end Family8SelectedParentJohnPlankSideWidthBridgeV4
