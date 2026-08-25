import FamilyStickyGrounding.FamilyStickyWZ2AmbientShearContainedMassV1
import FamilyStickyGrounding.JohnCapturedTubeCertificateCleanAdapterV1
import Submission.Kakeya.ConvexFactoring.BoxDimensionsMeasure

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace FamilyStickyWZ2JohnBoxVolumeNormalizationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedActualShadingInstantiationV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2AmbientCinematicTranslationVolumeV1
open FamilyStickyWZ2ReducedParameterClusterWindowV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyWZ2AmbientShearWindowBridgeV1
open FamilyStickyWZ2AmbientShearLocalCountV1
open FamilyStickyWZ2AmbientShearContainedMassV1

noncomputable section

/-!
# WZ2 John-box coordinate-one window and volume normalization

An arbitrary WZ2 shear image of a project tube is not itself a project
`Tube`: the shear is volume preserving but not an isometry.  Consequently
the captured-`Tube` John adapter cannot be applied directly to a nonzero
shear copy.  This module uses the exact information that survives:

* a contained positive-radius translated body has positive volume;
* positive volume of the convex test forces full affine span, hence an
  actual dimension-three John certificate with constant `288`;
* the certificate's outer frame box gives a literal window in the fixed
  ambient coordinate `1`;
* containment of the translated tube also absorbs its `delta^2` volume
  scale into `volume K`.

The resulting endpoint leaves only the explicit local shear-hit count and
source-window budget.  Removing those factors requires quantitative spacing
and source nonconcentration not present in the current interface.
-/

/-! ## Fixed ambient coordinate one -/

/-- Unit vector representing the fixed ambient coordinate `1`. -/
def coordinateOneDirection : Space :=
  EuclideanSpace.single (1 : Fin 3) (1 : Real)

@[simp] theorem inner_coordinateOneDirection (p : Space) :
    ⟪coordinateOneDirection, p⟫_ℝ = p 1 := by
  simp [coordinateOneDirection, EuclideanSpace.inner_single_left]

@[simp] theorem norm_coordinateOneDirection :
    ‖coordinateOneDirection‖ = 1 := by
  simp [coordinateOneDirection, PiLp.norm_single]

/-- Every John outer box gives a real `CoordinateOneWindow` in the fixed
WZ2 ambient coordinate, even though its orthonormal frame is arbitrary. -/
theorem BoxDimensionsCertificate.coordinateOneWindow
    {C : NNReal} {side : Fin 3 -> NNReal} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K) :
    CoordinateOneWindow K (cert.box.center 1)
      (cert.box.directionalHalf coordinateOneDirection : Real) := by
  intro p hp
  have hslab := cert.box.carrier_subset_directionalAffineSlab
    coordinateOneDirection (cert.outer_le hp)
  change |⟪coordinateOneDirection, p⟫_ℝ -
      ⟪coordinateOneDirection, cert.box.center⟫_ℝ| <=
    (cert.box.directionalHalf coordinateOneDirection : Real) at hslab
  simpa using hslab

/-! ## A contained translated tube forces a genuine John certificate -/

variable {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
  {delta : NNReal} {spacing : Real} {siteCount : Nat}

omit [Fintype kappa] in
/-- Literal containment of one positive-radius translated tube body makes
the arbitrary convex test have positive volume. -/
theorem volume_pos_of_contained_indexedTranslatedTube
    (fine : UniformTubeFamily delta kappa) (K : ConvexBody Space)
    (hdelta : 0 < delta) (j : Fin siteCount) (i : kappa)
    (hcontained :
      ((indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes) (j, i) : ConvexBody Space) : Set Space) <=
        (K : Set Space)) :
    0 < volume (K : Set Space) := by
  have himage :
      volume
          ((indexedTranslatedBodyFamily
            (shearReducedShift spacing (siteCount := siteCount))
            (tubeBodyFamily fine.tubes) (j, i) : ConvexBody Space) : Set Space) =
        volume (fine.tubes i).carrier := by
    rw [coe_indexedTranslatedBodyFamily,
      volume_ambientCinematicTranslation_image]
    rfl
  calc
    0 < volume
        ((indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes) (j, i) : ConvexBody Space) : Set Space) := by
      rw [himage]
      exact (fine.tubes i).volume_pos hdelta
    _ <= volume (K : Set Space) := measure_mono hcontained

/-- Positive volume of a convex body in the ambient three-space forces the
full-dimensional affine-span identity used by the John theorem. -/
theorem finrank_direction_affineSpan_eq_three_of_volume_pos
    (K : ConvexBody Space) (hvolume : 0 < volume (K : Set Space)) :
    Module.finrank Real (affineSpan Real (K : Set Space)).direction = 3 := by
  have hspan : affineSpan Real (K : Set Space) = ⊤ := by
    by_contra hne
    have hzero : volume (K : Set Space) = 0 :=
      measure_mono_null (subset_affineSpan Real (K : Set Space))
        (Measure.addHaar_affineSubspace volume
          (affineSpan Real (K : Set Space)) hne)
    exact (ne_of_gt hvolume) hzero
  rw [hspan, AffineSubspace.direction_top, finrank_top]
  simp [Space]

/-- A positive-volume body cannot have a zero side in any outer John box. -/
theorem BoxDimensionsCertificate.side_pos_of_volume_pos
    {C : NNReal} {side : Fin 3 -> NNReal} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K)
    (hvolume : 0 < volume (K : Set Space)) (i : Fin 3) :
    0 < side i := by
  by_contra hnot
  have hi : side i = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hnot)
  have hprod : (∏ j, (side j : ENNReal)) = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  let hdim : HasBoxDimensions C side K :=
    ⟨cert.one_le, cert.box, cert.side_eq, cert.inner_le, cert.outer_le⟩
  have hzero : volume (K : Set Space) = 0 := by
    exact bot_unique (hdim.volume_upper_bound.trans_eq hprod)
  exact (ne_of_gt hvolume) hzero

omit [Fintype kappa] in
/-- Any contained positive-radius WZ2 shear copy automatically supplies
positive John sides, a certificate with constant `288`, and a fixed
coordinate-one window.  No additional distorted-tube or window hypothesis is assumed. -/
theorem exists_positive_johnWindow_of_contained_indexedTranslatedTube
    (fine : UniformTubeFamily delta kappa) (K : ConvexBody Space)
    (hdelta : 0 < delta) (j : Fin siteCount) (i : kappa)
    (hcontained :
      ((indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes) (j, i) : ConvexBody Space) : Set Space) <=
        (K : Set Space)) :
    ∃ side : Fin 3 -> NNReal,
      ∃ cert : BoxDimensionsCertificate 288 side K,
        (∀ l, 0 < side l) ∧
          CoordinateOneWindow K (cert.box.center 1)
            (cert.box.directionalHalf coordinateOneDirection : Real) := by
  have hvolume := volume_pos_of_contained_indexedTranslatedTube
    fine K hdelta j i hcontained
  obtain ⟨side, ⟨cert⟩⟩ :=
    exists_boxDimensionsCertificate_288_of_finrank_direction_affineSpan_eq_three2 K
      (finrank_direction_affineSpan_eq_three_of_volume_pos K hvolume)
  exact ⟨side, cert,
    fun l => FamilyStickyWZ2JohnBoxVolumeNormalizationV1.BoxDimensionsCertificate.side_pos_of_volume_pos cert hvolume l,
    FamilyStickyWZ2JohnBoxVolumeNormalizationV1.BoxDimensionsCertificate.coordinateOneWindow cert⟩

/-! ## The strongest unconditional volume normalization -/
omit [Fintype kappa] in

/-- Containment of one translated source tube absorbs the source scale
`delta^2` into twice the volume of the arbitrary convex test. -/
theorem delta_sq_le_two_mul_volume_of_contained_indexedTranslatedTube
    (fine : UniformTubeFamily delta kappa) (K : ConvexBody Space)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (j : Fin siteCount) (i : kappa)
    (hcontained :
      ((indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes) (j, i) : ConvexBody Space) : Set Space) <=
        (K : Set Space)) :
    (delta : ENNReal) ^ 2 <= 2 * volume (K : Set Space) := by
  have hsource : (delta : ENNReal) ^ 2 / 2 <=
      volume (fine.tubes i).carrier :=
    (fine.tubes i).half_sq_le_volume_of_le_half hdeltaHalf
  have himage : volume (fine.tubes i).carrier =
      volume
        ((indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes) (j, i) : ConvexBody Space) : Set Space) := by
    rw [coe_indexedTranslatedBodyFamily,
      volume_ambientCinematicTranslation_image]
    rfl
  have hhalf : (delta : ENNReal) ^ 2 / 2 <=
      volume (K : Set Space) := by
    calc
      (delta : ENNReal) ^ 2 / 2 <= volume (fine.tubes i).carrier := hsource
      _ = volume
          ((indexedTranslatedBodyFamily
            (shearReducedShift spacing (siteCount := siteCount))
            (tubeBodyFamily fine.tubes) (j, i) : ConvexBody Space) : Set Space) :=
        himage
      _ <= volume (K : Set Space) := measure_mono hcontained
  have hmul : (delta : ENNReal) ^ 2 <=
      volume (K : Set Space) * 2 :=
    (ENNReal.div_le_iff_le_mul
      (Or.inl (by norm_num)) (Or.inl (by norm_num))).mp hhalf
  simpa [mul_comm] using hmul

/-- End-to-end John-window/local-count endpoint.  A contained translated
positive-radius tube automatically chooses the John certificate and fixed
coordinate-one window.  The tube-volume scale is completely normalized by
`volume K`; the exact residual is

`16 * min(siteCount, shearShiftHitBudget spacing (4 * radius + rho)) * sourceBudget`.

The source-window hypothesis is stated after the automatically selected
John radius, so no certificate or window is supplied by the caller. -/
theorem exists_johnWindow_and_containedMass_le_explicitResidual_mul_volume
    (fine : UniformTubeFamily delta kappa) (K : ConvexBody Space)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (j : Fin siteCount) (i : kappa)
    (hcontained :
      ((indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes) (j, i) : ConvexBody Space) : Set Space) <=
        (K : Set Space))
    (baseD rho : Real) (hspacing : 0 < spacing) (hrho : 0 <= rho)
    (hvertical : forall l,
      (1 / 2 : Real) <= |(fine.tubes l).axis.direction 2|)
    (hcluster : forall l, |tubeGraphD (fine.tubes l) - baseD| <= rho) :
    ∃ side : Fin 3 -> NNReal,
      ∃ cert : BoxDimensionsCertificate 288 side K,
        (∀ l, 0 < side l) ∧
        CoordinateOneWindow K (cert.box.center 1)
          (cert.box.directionalHalf coordinateOneDirection : Real) ∧
        ∀ sourceBudget : Nat,
          (∀ q,
            (parameterWindowIndices
              (fun l => tubeShearReducedParameter (fine.tubes l)) q
              (4 * (cert.box.directionalHalf
                coordinateOneDirection : Real))).card <= sourceBudget) ->
          containedMass
              (indexedTranslatedBodyFamily
                (shearReducedShift spacing (siteCount := siteCount))
                (tubeBodyFamily fine.tubes)) K <=
            (16 *
              ((min siteCount
                (shearShiftHitBudget spacing
                  (4 * (cert.box.directionalHalf
                    coordinateOneDirection : Real) + rho)) *
                  sourceBudget : Nat) : ENNReal)) *
              volume (K : Set Space) := by
  obtain ⟨side, cert, hside, hwindow⟩ :=
    exists_positive_johnWindow_of_contained_indexedTranslatedTube
      fine K hdelta j i hcontained
  refine ⟨side, cert, hside, hwindow, ?_⟩
  intro sourceBudget hsource
  let radius : Real :=
    (cert.box.directionalHalf coordinateOneDirection : Real)
  have hradius : 0 <= radius := by positivity
  have hmass :=
    containedMass_indexedShear_le_local_sourceBudget_mul_tubeVolumeCap
      (siteCount := siteCount) fine K (cert.box.center 1) radius baseD rho hdeltaHalf hspacing
      hradius hrho hwindow hvertical hcluster sourceBudget hsource
  have hdeltaVolume :=
    delta_sq_le_two_mul_volume_of_contained_indexedTranslatedTube
      fine K hdeltaHalf j i hcontained
  calc
    containedMass
        (indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes)) K <=
      ((min siteCount
          (shearShiftHitBudget spacing (4 * radius + rho)) *
          sourceBudget : Nat) : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) := hmass
    _ <= ((min siteCount
          (shearShiftHitBudget spacing (4 * radius + rho)) *
          sourceBudget : Nat) : ENNReal) *
        (8 * (2 * volume (K : Set Space))) := by
      gcongr
    _ = (16 *
          ((min siteCount
            (shearShiftHitBudget spacing (4 * radius + rho)) *
            sourceBudget : Nat) : ENNReal)) *
        volume (K : Set Space) := by ring

/-! ## Genuine-tube quantitative side seam -/

/-- If a genuine project `Tube delta` (rather than merely its sheared affine
image) is contained in `K`, the clean John adapter additionally supplies the
quantitative side bounds `2 * delta <= side l`.  This is precisely the datum
missing for arbitrary nonzero shear copies. -/
theorem exists_johnWindow_with_side_lower_of_tube_subset
    (K : ConvexBody Space) (T : Tube delta)
    (hdelta : 0 < delta) (hTK : T.carrier ⊆ (K : Set Space)) :
    ∃ side : Fin 3 -> NNReal,
      ∃ cert : BoxDimensionsCertificate 288 side K,
        (∀ l, 2 * delta <= side l) ∧
          CoordinateOneWindow K (cert.box.center 1)
            (cert.box.directionalHalf coordinateOneDirection : Real) := by
  obtain ⟨side, _hsidePos, ⟨cert⟩⟩ :=
    exists_positive_boxDimensionsCertificate_288_of_tube_subset_clean
      K T hdelta hTK
  exact ⟨side, cert,
    fun l => JohnSideLowerFinal.boxCertificate_side_lower_of_tube_subset
      T hTK cert l,
    FamilyStickyWZ2JohnBoxVolumeNormalizationV1.BoxDimensionsCertificate.coordinateOneWindow cert⟩

#print axioms inner_coordinateOneDirection
#print axioms norm_coordinateOneDirection
#print axioms BoxDimensionsCertificate.coordinateOneWindow
#print axioms volume_pos_of_contained_indexedTranslatedTube
#print axioms finrank_direction_affineSpan_eq_three_of_volume_pos
#print axioms BoxDimensionsCertificate.side_pos_of_volume_pos
#print axioms exists_positive_johnWindow_of_contained_indexedTranslatedTube
#print axioms delta_sq_le_two_mul_volume_of_contained_indexedTranslatedTube
#print axioms exists_johnWindow_and_containedMass_le_explicitResidual_mul_volume
#print axioms exists_johnWindow_with_side_lower_of_tube_subset

end
end FamilyStickyWZ2JohnBoxVolumeNormalizationV1
