import FamilyStickyGrounding.FamilyStickyWZ2AmbientShearDistortedTubeAdapterV1
import FamilyStickyGrounding.FamilyStickyWZ2JohnBoxVolumeNormalizationV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace FamilyStickyWZ2DistortedJohnRadiusNormalizationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2TranslatedShadingUnionCovarianceV1
open FamilyStickyWZ2ReducedParameterClusterWindowV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyWZ2AmbientShearWindowBridgeV1
open FamilyStickyWZ2AmbientShearLocalCountV1
open FamilyStickyWZ2AmbientShearContainedMassV1
open FamilyStickyWZ2JohnBoxVolumeNormalizationV1
open FamilyStickyWZ2AmbientShearDistortedTubeAdapterV1

noncomputable section

/-!
# Eliminating the John coordinate radius for a distorted WZ2 tube

The ambient shear leaves a round radius `delta / (1 + |d₀|)` inside the
translated tube.  Two such transverse side lower bounds, together with the
John inner-volume inequality, control every fixed-coordinate projection
radius by an explicit multiple of `volume K / delta²`.  This removes the
certificate-dependent radius from the final shear-grid count.
-/

/-- Projection of a frame box onto a unit direction is at most half the sum
of its three side lengths. -/
theorem FrameBox.directionalHalf_le_sum_half_side
    (B : FrameBox) (e : Space) (he : ‖e‖ = 1) :
    (B.directionalHalf e : Real) <=
      ∑ i, (B.side i : Real) / 2 := by
  have hinner (i : Fin 3) : |⟪e, B.frame i⟫_ℝ| <= 1 := by
    simpa [he, B.frame.norm_eq_one] using
      abs_real_inner_le_norm e (B.frame i)
  rw [FrameBox.directionalHalf, NNReal.coe_sum]
  apply Finset.sum_le_sum
  intro i _hi
  change |⟪e, B.frame i⟫_ℝ| * ((B.side i : Real) / 2) <=
    (B.side i : Real) / 2
  exact mul_le_of_le_one_left (by positivity) (hinner i)

/-- The John constant used by the dimension-three certificate. -/
def johnRadiusVolumeConstant : Nat := 288 ^ 3

@[simp]
theorem johnRadiusVolumeConstant_eq : johnRadiusVolumeConstant = 23887872 := by
  norm_num [johnRadiusVolumeConstant]

/-- Quantitative radius cap after eliminating both transverse John sides. -/
def johnRadiusVolumeCap
    (K : ConvexBody Space) (delta : NNReal) (d0 : Real) : Real :=
  (johnRadiusVolumeConstant : Real) *
    (inverseShearLipschitzConstant d0 : Real) ^ 2 *
      (volume (K : Set Space)).toReal / (delta : Real) ^ 2

theorem johnRadiusVolumeCap_nonneg
    (K : ConvexBody Space) (delta : NNReal) (d0 : Real) :
    0 <= johnRadiusVolumeCap K delta d0 := by
  unfold johnRadiusVolumeCap
  positivity

/-- A John certificate whose sides contain the surviving distorted radius
satisfies the scale-invariant fixed-coordinate estimate

`R * delta² <= 288³ * (1 + |d₀|)² * volume K`.
-/
theorem BoxDimensionsCertificate.directionalHalf_mul_delta_sq_le_volume
    {side : Fin 3 -> NNReal} {K : ConvexBody Space}
    {delta : NNReal} {d0 : Real}
    (cert : BoxDimensionsCertificate 288 side K) (e : Space)
    (he : ‖e‖ = 1)
    (hside : forall i,
      2 * distortedTubeRadius delta d0 <= side i) :
    (cert.box.directionalHalf e : Real) * (delta : Real) ^ 2 <=
      (johnRadiusVolumeConstant : Real) *
        (inverseShearLipschitzConstant d0 : Real) ^ 2 *
          (volume (K : Set Space)).toReal := by
  let L : Real := inverseShearLipschitzConstant d0
  have hLpos : 0 < L := by
    exact_mod_cast inverseShearLipschitzConstant_pos d0
  have hsideR (i : Fin 3) :
      2 * ((delta : Real) / L) <= (side i : Real) := by
    exact_mod_cast hside i
  have hs (i : Fin 3) :
      2 * (delta : Real) <= L * (side i : Real) := by
    have hdiv : (2 * (delta : Real)) / L <= (side i : Real) := by
      calc
        (2 * (delta : Real)) / L = 2 * ((delta : Real) / L) := by ring
        _ <= (side i : Real) := hsideR i
    simpa [mul_comm] using (div_le_iff₀ hLpos).mp hdiv
  have hpair (i j : Fin 3) :
      4 * (delta : Real) ^ 2 <=
        L ^ 2 * (side i : Real) * (side j : Real) := by
    have hmul := mul_le_mul (hs i) (hs j)
      (by positivity : 0 <= 2 * (delta : Real))
      (by positivity : 0 <= L * (side i : Real))
    nlinarith
  have hterm0 :
      4 * (delta : Real) ^ 2 * (side 0 : Real) <=
        L ^ 2 * (side 0 : Real) * (side 1 : Real) * (side 2 : Real) := by
    have h := mul_le_mul_of_nonneg_left (hpair 1 2)
      (NNReal.coe_nonneg (side 0))
    nlinarith
  have hterm1 :
      4 * (delta : Real) ^ 2 * (side 1 : Real) <=
        L ^ 2 * (side 0 : Real) * (side 1 : Real) * (side 2 : Real) := by
    have h := mul_le_mul_of_nonneg_left (hpair 0 2)
      (NNReal.coe_nonneg (side 1))
    nlinarith
  have hterm2 :
      4 * (delta : Real) ^ 2 * (side 2 : Real) <=
        L ^ 2 * (side 0 : Real) * (side 1 : Real) * (side 2 : Real) := by
    have h := mul_le_mul_of_nonneg_right (hpair 0 1)
      (NNReal.coe_nonneg (side 2))
    nlinarith
  have hR :=
    FamilyStickyWZ2DistortedJohnRadiusNormalizationV1.FrameBox.directionalHalf_le_sum_half_side
      cert.box e he
  rw [cert.side_eq, Fin.sum_univ_three] at hR
  have hRprod :
      (cert.box.directionalHalf e : Real) * (delta : Real) ^ 2 <=
        L ^ 2 * (side 0 : Real) * (side 1 : Real) * (side 2 : Real) := by
    have hmul := mul_le_mul_of_nonneg_right hR (sq_nonneg (delta : Real))
    have hprodNonneg :
        0 <= L ^ 2 * (side 0 : Real) * (side 1 : Real) *
          (side 2 : Real) := by positivity
    nlinarith
  let hdim : HasBoxDimensions 288 side K :=
    ⟨cert.one_le, cert.box, cert.side_eq, cert.inner_le, cert.outer_le⟩
  have hvolumeENN := hdim.volume_lower_bound
  have hvolumeReal := ENNReal.toReal_mono hdim.volume_lt_top.ne hvolumeENN
  have hprodVolume :
      (side 0 : Real) * (side 1 : Real) * (side 2 : Real) <=
        (johnRadiusVolumeConstant : Real) *
          (volume (K : Set Space)).toReal := by
    norm_num [Fin.prod_univ_three, ENNReal.toReal_mul,
      johnRadiusVolumeConstant] at hvolumeReal ⊢
    nlinarith
  calc
    (cert.box.directionalHalf e : Real) * (delta : Real) ^ 2 <=
        L ^ 2 * (side 0 : Real) * (side 1 : Real) * (side 2 : Real) :=
      hRprod
    _ = L ^ 2 *
        ((side 0 : Real) * (side 1 : Real) * (side 2 : Real)) := by
      ring
    _ <= L ^ 2 *
        ((johnRadiusVolumeConstant : Real) *
          (volume (K : Set Space)).toReal) := by
      exact mul_le_mul_of_nonneg_left hprodVolume (sq_nonneg L)
    _ = (johnRadiusVolumeConstant : Real) *
        (inverseShearLipschitzConstant d0 : Real) ^ 2 *
          (volume (K : Set Space)).toReal := by
      simp only [L]
      ring

/-- Division by the positive tube scale turns the preceding product bound
into a direct fixed-coordinate radius cap. -/
theorem BoxDimensionsCertificate.directionalHalf_le_johnRadiusVolumeCap
    {side : Fin 3 -> NNReal} {K : ConvexBody Space}
    {delta : NNReal} {d0 : Real}
    (cert : BoxDimensionsCertificate 288 side K)
    (hdelta : 0 < delta)
    (hside : forall i,
      2 * distortedTubeRadius delta d0 <= side i) :
    (cert.box.directionalHalf coordinateOneDirection : Real) <=
      johnRadiusVolumeCap K delta d0 := by
  rw [johnRadiusVolumeCap]
  apply (le_div_iff₀ (sq_pos_of_pos (NNReal.coe_pos.2 hdelta))).2
  exact
    FamilyStickyWZ2DistortedJohnRadiusNormalizationV1.BoxDimensionsCertificate.directionalHalf_mul_delta_sq_le_volume
      cert coordinateOneDirection norm_coordinateOneDirection hside


@[simp]
theorem johnRadiusVolumeCap_eq_explicit
    (K : ConvexBody Space) (delta : NNReal) (d0 : Real) :
    johnRadiusVolumeCap K delta d0 =
      23887872 * (1 + |d0|) ^ 2 *
        (volume (K : Set Space)).toReal / (delta : Real) ^ 2 := by
  rw [johnRadiusVolumeCap, coe_inverseShearLipschitzConstant]
  norm_num [johnRadiusVolumeConstant]

/-- Enlarging a reduced-parameter window only adds indices. -/
theorem parameterWindowIndices_mono_radius
    {index : Type*} [Fintype index] [DecidableEq index]
    (parameter : index -> ReducedLineParameter)
    (center : ReducedLineParameter) {r s : Real} (hrs : r <= s) :
    parameterWindowIndices parameter center r ⊆
      parameterWindowIndices parameter center s := by
  intro i hi
  simp only [parameterWindowIndices, Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hi.2.trans hrs⟩

theorem card_parameterWindowIndices_le_of_radius_le
    {index : Type*} [Fintype index] [DecidableEq index]
    (parameter : index -> ReducedLineParameter)
    (center : ReducedLineParameter) {r s : Real} (hrs : r <= s) :
    (parameterWindowIndices parameter center r).card <=
      (parameterWindowIndices parameter center s).card :=
  Finset.card_le_card (parameterWindowIndices_mono_radius
    parameter center hrs)

/-- The explicit shear-grid ceiling budget is monotone in its radius when
the grid spacing is positive. -/
theorem shearShiftHitBudget_mono_radius
    {spacing r s : Real} (hspacing : 0 < spacing) (hrs : r <= s) :
    shearShiftHitBudget spacing r <= shearShiftHitBudget spacing s := by
  unfold shearShiftHitBudget
  apply Nat.add_le_add_right
  apply Nat.ceil_mono
  apply (div_le_div_iff_of_pos_right hspacing).2
  nlinarith

/-- The actual `d`-shear at a finite grid site. -/
def shearSiteD {siteCount : Nat} (spacing : Real) (j : Fin siteCount) : Real :=
  ((j : Nat) : Real) * spacing

@[simp]
theorem shearReducedShift_eq_site
    {siteCount : Nat} (spacing : Real) (j : Fin siteCount) :
    shearReducedShift spacing j = (0, (0, shearSiteD spacing j)) :=
  rfl

variable {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
  {delta : NNReal} {spacing : Real} {siteCount : Nat}

/-- End-to-end WZ2 John-window normalization with no certificate-dependent
radius in either the source-window premise or the output shear count.

The displayed natural-number budget is literally the expansion of
`shearShiftHitBudget` at the volume-normalized radius cap.
-/
theorem exists_distortedJohnWindow_and_containedMass_le_expandedBudget_mul_volume
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
        (∀ l,
          2 * distortedTubeRadius delta (shearSiteD spacing j) <= side l) ∧
        (∃ l : Fin 3,
          distortedAxisLength (shearSiteD spacing j) <= 6 * side l) ∧
        CoordinateOneWindow K (cert.box.center 1)
          (cert.box.directionalHalf coordinateOneDirection : Real) ∧
        (cert.box.directionalHalf coordinateOneDirection : Real) <=
          johnRadiusVolumeCap K delta (shearSiteD spacing j) ∧
        ∀ sourceBudget : Nat,
          (∀ q,
            (parameterWindowIndices
              (fun l => tubeShearReducedParameter (fine.tubes l)) q
              (4 * johnRadiusVolumeCap K delta
                (shearSiteD spacing j))).card <= sourceBudget) ->
          containedMass
              (indexedTranslatedBodyFamily
                (shearReducedShift spacing (siteCount := siteCount))
                (tubeBodyFamily fine.tubes)) K <=
            (16 *
              ((min siteCount
                (Nat.ceil
                  ((2 *
                    (4 * johnRadiusVolumeCap K delta
                      (shearSiteD spacing j) + rho)) / spacing) + 1) *
                  sourceBudget : Nat) : ENNReal)) *
              volume (K : Set Space) := by
  have himage :
      ambientCinematicTranslation 0 0 (shearSiteD spacing j) ''
          (fine.tubes i).carrier ⊆ (K : Set Space) := by
    simpa [coe_indexedTranslatedBodyFamily, shearReducedShift, shearSiteD,
      tubeBodyFamily, Tube.coe_body] using hcontained
  obtain ⟨side, cert, hside, hlong⟩ :=
    FamilyStickyWZ2AmbientShearDistortedTubeAdapterV1.exists_boxDimensionsCertificate_288_with_distortedTube_bounds
      K (fine.tubes i) 0 0 (shearSiteD spacing j) hdelta himage
  have hwindow :
      CoordinateOneWindow K (cert.box.center 1)
        (cert.box.directionalHalf coordinateOneDirection : Real) :=
    FamilyStickyWZ2JohnBoxVolumeNormalizationV1.BoxDimensionsCertificate.coordinateOneWindow
      cert
  have hRcap :
      (cert.box.directionalHalf coordinateOneDirection : Real) <=
        johnRadiusVolumeCap K delta (shearSiteD spacing j) :=
    FamilyStickyWZ2DistortedJohnRadiusNormalizationV1.BoxDimensionsCertificate.directionalHalf_le_johnRadiusVolumeCap
      cert hdelta hside
  refine ⟨side, cert, hside, hlong, hwindow, hRcap, ?_⟩
  intro sourceBudget hsourceCap
  let radius : Real :=
    (cert.box.directionalHalf coordinateOneDirection : Real)
  have hradius : 0 <= radius := by positivity
  have hfourRadius :
      4 * radius <=
        4 * johnRadiusVolumeCap K delta (shearSiteD spacing j) := by
    dsimp only [radius]
    nlinarith
  have hsource : forall q,
      (parameterWindowIndices
        (fun l => tubeShearReducedParameter (fine.tubes l)) q
        (4 * radius)).card <= sourceBudget := by
    intro q
    exact
      (card_parameterWindowIndices_le_of_radius_le
        (fun l => tubeShearReducedParameter (fine.tubes l)) q
        hfourRadius).trans (hsourceCap q)
  have hmass :=
    containedMass_indexedShear_le_local_sourceBudget_mul_tubeVolumeCap
      (siteCount := siteCount) fine K (cert.box.center 1) radius baseD rho
      hdeltaHalf hspacing hradius hrho hwindow hvertical hcluster
      sourceBudget hsource
  let explicitBudget : Nat :=
    Nat.ceil
      ((2 *
        (4 * johnRadiusVolumeCap K delta (shearSiteD spacing j) + rho)) /
          spacing) + 1
  have hhit :
      shearShiftHitBudget spacing (4 * radius + rho) <= explicitBudget := by
    have hradius' :
        4 * radius + rho <=
          4 * johnRadiusVolumeCap K delta (shearSiteD spacing j) + rho := by
      nlinarith
    simpa [explicitBudget, shearShiftHitBudget] using
      shearShiftHitBudget_mono_radius hspacing hradius'
  have hmin :
      min siteCount (shearShiftHitBudget spacing (4 * radius + rho)) <=
        min siteCount explicitBudget :=
    min_le_min_left siteCount hhit
  have hmassBudget :
      containedMass
          (indexedTranslatedBodyFamily
            (shearReducedShift spacing (siteCount := siteCount))
            (tubeBodyFamily fine.tubes)) K <=
        ((min siteCount explicitBudget * sourceBudget : Nat) : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) := by
    calc
      containedMass
          (indexedTranslatedBodyFamily
            (shearReducedShift spacing (siteCount := siteCount))
            (tubeBodyFamily fine.tubes)) K <=
        ((min siteCount
            (shearShiftHitBudget spacing (4 * radius + rho)) *
              sourceBudget : Nat) : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) := hmass
      _ <= ((min siteCount explicitBudget * sourceBudget : Nat) : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) := by
        gcongr
  have hdeltaVolume :=
    delta_sq_le_two_mul_volume_of_contained_indexedTranslatedTube
      fine K hdeltaHalf j i hcontained
  have hfinal :
      containedMass
          (indexedTranslatedBodyFamily
            (shearReducedShift spacing (siteCount := siteCount))
            (tubeBodyFamily fine.tubes)) K <=
        (16 *
          ((min siteCount explicitBudget * sourceBudget : Nat) : ENNReal)) *
            volume (K : Set Space) := by
    calc
      containedMass
          (indexedTranslatedBodyFamily
            (shearReducedShift spacing (siteCount := siteCount))
            (tubeBodyFamily fine.tubes)) K <=
        ((min siteCount explicitBudget * sourceBudget : Nat) : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) := hmassBudget
      _ <= ((min siteCount explicitBudget * sourceBudget : Nat) : ENNReal) *
          (8 * (2 * volume (K : Set Space))) := by
        gcongr
      _ = (16 *
          ((min siteCount explicitBudget * sourceBudget : Nat) : ENNReal)) *
            volume (K : Set Space) := by ring
  simpa only [explicitBudget] using hfinal

#print axioms FrameBox.directionalHalf_le_sum_half_side
#print axioms BoxDimensionsCertificate.directionalHalf_mul_delta_sq_le_volume
#print axioms BoxDimensionsCertificate.directionalHalf_le_johnRadiusVolumeCap
#print axioms parameterWindowIndices_mono_radius
#print axioms shearShiftHitBudget_mono_radius
#print axioms exists_distortedJohnWindow_and_containedMass_le_expandedBudget_mul_volume

end
end FamilyStickyWZ2DistortedJohnRadiusNormalizationV1
