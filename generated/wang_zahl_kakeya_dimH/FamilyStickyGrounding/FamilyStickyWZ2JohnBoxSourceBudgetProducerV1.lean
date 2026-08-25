import FamilyStickyGrounding.FamilyStickyWZ2JohnBoxVolumeNormalizationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteSeparatedSlopePackingV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace FamilyStickyWZ2JohnBoxSourceBudgetProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedActualShadingInstantiationV1
open FamilyStickyWZ2ReducedParameterClusterWindowV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2AmbientCinematicTranslationVolumeV1
open FamilyStickyWZ2AmbientShearWindowBridgeV1
open FamilyStickyWZ2AmbientShearLocalCountV1
open FamilyStickyWZ2JohnBoxVolumeNormalizationV1
open FamilyStickyCinematicL32FiniteSeparatedSlopePackingV1

noncomputable section

/-!
# Internal source-shear budgets for the WZ2 John-box endpoint

The ambient containment bridge deliberately retains only the graph shear
coordinate `d = direction 1 / direction 2`.  Full WZ endpoint separation is
separation in the complete oriented basepoint--direction parameter and does
not imply separation of this one coordinate: distinct tubes may have equal
`d` and be separated in a basepoint or another direction coordinate.

This module records the exact additional one-dimensional datum that the
existing window consumer needs.  Pairwise source-`d` separation produces a
ceiling window budget internally.  The already available `d`-cluster then
gives the minimum of the local-window and whole-cluster budgets.  A separate
unconditional endpoint removes the caller-supplied window bound by using the
honest finite source cardinality.
-/

variable {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
  {delta : NNReal} {spacing : Real} {siteCount : Nat}

/-- The minimal projected separation required by a window that remembers
only the actual source shear slope `tubeGraphD`. -/
def SourceShearSeparated
    (fine : UniformTubeFamily delta kappa) (sourceSpacing : Real) : Prop :=
  forall i j, i ≠ j ->
    sourceSpacing <=
      |tubeGraphD (fine.tubes i) - tubeGraphD (fine.tubes j)|

/-- Every source-parameter window is bounded by the full finite source
cardinality.  This is the strongest producer requiring no separation datum. -/
theorem card_tubeShearReducedParameter_window_le_card
    (fine : UniformTubeFamily delta kappa)
    (q : ReducedLineParameter) (radius : Real) :
    (parameterWindowIndices
      (fun i => tubeShearReducedParameter (fine.tubes i)) q radius).card <=
      Fintype.card kappa := by
  have hcard := Finset.card_filter_le (Finset.univ : Finset kappa)
    (fun i => reducedParameterDistance
      (tubeShearReducedParameter (fine.tubes i)) q <= radius)
  simpa [parameterWindowIndices] using hcard

/-- Pairwise separation of the source shear slopes produces the exact same
ceiling budget used for the explicit copy grid. -/
theorem card_tubeShearReducedParameter_window_le_hitBudget
    (fine : UniformTubeFamily delta kappa)
    {sourceSpacing radius : Real}
    (hsourceSpacing : 0 < sourceSpacing) (hradius : 0 <= radius)
    (hseparated : SourceShearSeparated fine sourceSpacing)
    (q : ReducedLineParameter) :
    (parameterWindowIndices
      (fun i => tubeShearReducedParameter (fine.tubes i)) q radius).card <=
      shearShiftHitBudget sourceSpacing radius := by
  let indices : Finset kappa :=
    parameterWindowIndices
      (fun i => tubeShearReducedParameter (fine.tubes i)) q radius
  have hrange : forall i, i ∈ indices ->
      |tubeGraphD (fine.tubes i) - q.2.2| <= radius := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    exact (abs_snd_snd_sub_le_reducedParameterDistance _ _).trans hi'
  have hpacking :
      (indices.card : ENNReal) * ENNReal.ofReal sourceSpacing <=
        ENNReal.ofReal (2 * radius + sourceSpacing) :=
    card_mul_sep_le_of_slopes_near indices
      (fun i => tubeGraphD (fine.tubes i)) hsourceSpacing.le hrange
      (fun i _hi j _hj hij => hseparated i j hij)
  have hreal :
      (indices.card : Real) * sourceSpacing <=
        2 * radius + sourceSpacing := by
    have hfiniteLeft :
        (indices.card : ENNReal) * ENNReal.ofReal sourceSpacing ≠ ∞ := by
      finiteness
    have hfiniteRight :
        ENNReal.ofReal (2 * radius + sourceSpacing) ≠ ∞ := by
      finiteness
    have htoReal :=
      (ENNReal.toReal_le_toReal hfiniteLeft hfiniteRight).2 hpacking
    have hsum : 0 <= 2 * radius + sourceSpacing :=
      add_nonneg (mul_nonneg (by norm_num) hradius) hsourceSpacing.le
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hsourceSpacing.le,
      ENNReal.toReal_ofReal hsum] using htoReal
  have hratio :
      (indices.card : Real) <= 2 * radius / sourceSpacing + 1 := by
    have heq :
        2 * radius / sourceSpacing + 1 =
          (2 * radius + sourceSpacing) / sourceSpacing := by
      field_simp
    rw [heq]
    exact (le_div_iff₀ hsourceSpacing).2 hreal
  have hceil :
      2 * radius / sourceSpacing <=
        (Nat.ceil (2 * radius / sourceSpacing) : Real) := Nat.le_ceil _
  have hcast :
      (indices.card : Real) <=
        ((Nat.ceil (2 * radius / sourceSpacing) + 1 : Nat) : Real) := by
    calc
      (indices.card : Real) <= 2 * radius / sourceSpacing + 1 := hratio
      _ <= (Nat.ceil (2 * radius / sourceSpacing) : Real) + 1 := by
        linarith
      _ = ((Nat.ceil (2 * radius / sourceSpacing) + 1 : Nat) : Real) := by
        norm_num
  exact_mod_cast hcast

/-- The source cluster bounds the whole family by the corresponding
one-dimensional separated-shear budget. -/
theorem card_le_sourceShearHitBudget_of_cluster
    (fine : UniformTubeFamily delta kappa) (baseD : Real)
    {sourceSpacing rho : Real}
    (hsourceSpacing : 0 < sourceSpacing) (hrho : 0 <= rho)
    (hcluster : forall i,
      |tubeGraphD (fine.tubes i) - baseD| <= rho)
    (hseparated : SourceShearSeparated fine sourceSpacing) :
    Fintype.card kappa <= shearShiftHitBudget sourceSpacing rho := by
  let center : ReducedLineParameter := (0, (0, baseD))
  have hwindow := card_tubeShearReducedParameter_window_le_hitBudget
    fine hsourceSpacing hrho hseparated center
  have hall : parameterWindowIndices
      (fun i => tubeShearReducedParameter (fine.tubes i)) center rho =
      (Finset.univ : Finset kappa) := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    rw [parameterWindowIndices, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [center, reducedParameterDistance, tubeShearReducedParameter]
      using hcluster i
  simpa [hall] using hwindow

/-- Local source occupancy uses the smallest of the actual source count,
the test-window packing budget, and the whole-cluster packing budget. -/
theorem card_tubeShearReducedParameter_window_le_min_hitBudget
    (fine : UniformTubeFamily delta kappa) (baseD : Real)
    {sourceSpacing rho radius : Real}
    (hsourceSpacing : 0 < sourceSpacing)
    (hrho : 0 <= rho) (hradius : 0 <= radius)
    (hcluster : forall i,
      |tubeGraphD (fine.tubes i) - baseD| <= rho)
    (hseparated : SourceShearSeparated fine sourceSpacing)
    (q : ReducedLineParameter) :
    (parameterWindowIndices
      (fun i => tubeShearReducedParameter (fine.tubes i)) q radius).card <=
      min (Fintype.card kappa)
        (min (shearShiftHitBudget sourceSpacing radius)
          (shearShiftHitBudget sourceSpacing rho)) := by
  apply Nat.le_min.mpr
  constructor
  · exact card_tubeShearReducedParameter_window_le_card fine q radius
  · apply Nat.le_min.mpr
    constructor
    · exact card_tubeShearReducedParameter_window_le_hitBudget
        fine hsourceSpacing hradius hseparated q
    · exact (card_tubeShearReducedParameter_window_le_card fine q radius).trans
        (card_le_sourceShearHitBudget_of_cluster fine baseD hsourceSpacing
          hrho hcluster hseparated)

/-! ## Internally produced John-box endpoints -/

/-- Completely unconditional internal source-budget endpoint.  It removes
the caller's `forall q` premise at the honest cost `Fintype.card kappa`. -/
theorem exists_johnWindow_and_containedMass_le_cardResidual_mul_volume
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
        containedMass
            (indexedTranslatedBodyFamily
              (shearReducedShift spacing (siteCount := siteCount))
              (tubeBodyFamily fine.tubes)) K <=
          (16 *
            ((min siteCount
              (shearShiftHitBudget spacing
                (4 * (cert.box.directionalHalf
                  coordinateOneDirection : Real) + rho)) *
                Fintype.card kappa : Nat) : ENNReal)) *
            volume (K : Set Space) := by
  obtain ⟨side, cert, hside, hwindow, hendpoint⟩ :=
    exists_johnWindow_and_containedMass_le_explicitResidual_mul_volume
      fine K hdelta hdeltaHalf j i hcontained baseD rho hspacing hrho
      hvertical hcluster
  refine ⟨side, cert, hside, hwindow, ?_⟩
  exact hendpoint (Fintype.card kappa)
    (fun q => card_tubeShearReducedParameter_window_le_card fine q
      (4 * (cert.box.directionalHalf coordinateOneDirection : Real)))

/-- With the minimal projected source-shear separation, both source budgets
are produced internally.  The remaining factors are the two explicit
one-dimensional ceiling counts and the John-box volume. -/
theorem exists_johnWindow_and_containedMass_le_separatedResidual_mul_volume
    (fine : UniformTubeFamily delta kappa) (K : ConvexBody Space)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (j : Fin siteCount) (i : kappa)
    (hcontained :
      ((indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes) (j, i) : ConvexBody Space) : Set Space) <=
        (K : Set Space))
    (baseD rho sourceSpacing : Real)
    (hspacing : 0 < spacing) (hrho : 0 <= rho)
    (hsourceSpacing : 0 < sourceSpacing)
    (hvertical : forall l,
      (1 / 2 : Real) <= |(fine.tubes l).axis.direction 2|)
    (hcluster : forall l, |tubeGraphD (fine.tubes l) - baseD| <= rho)
    (hsourceSeparated : SourceShearSeparated fine sourceSpacing) :
    ∃ side : Fin 3 -> NNReal,
      ∃ cert : BoxDimensionsCertificate 288 side K,
        (∀ l, 0 < side l) ∧
        CoordinateOneWindow K (cert.box.center 1)
          (cert.box.directionalHalf coordinateOneDirection : Real) ∧
        containedMass
            (indexedTranslatedBodyFamily
              (shearReducedShift spacing (siteCount := siteCount))
              (tubeBodyFamily fine.tubes)) K <=
          (16 *
            ((min siteCount
                (shearShiftHitBudget spacing
                  (4 * (cert.box.directionalHalf
                    coordinateOneDirection : Real) + rho)) *
              min (Fintype.card kappa)
                (min
                  (shearShiftHitBudget sourceSpacing
                    (4 * (cert.box.directionalHalf
                      coordinateOneDirection : Real)))
                  (shearShiftHitBudget sourceSpacing rho)) : Nat) : ENNReal)) *
            volume (K : Set Space) := by
  obtain ⟨side, cert, hside, hwindow, hendpoint⟩ :=
    exists_johnWindow_and_containedMass_le_explicitResidual_mul_volume
      fine K hdelta hdeltaHalf j i hcontained baseD rho hspacing hrho
      hvertical hcluster
  refine ⟨side, cert, hside, hwindow, ?_⟩
  let radius : Real :=
    (cert.box.directionalHalf coordinateOneDirection : Real)
  have hradius : 0 <= radius := by positivity
  exact hendpoint
    (min (Fintype.card kappa)
      (min (shearShiftHitBudget sourceSpacing (4 * radius))
        (shearShiftHitBudget sourceSpacing rho)))
    (fun q => card_tubeShearReducedParameter_window_le_min_hitBudget
      fine baseD hsourceSpacing hrho
      (mul_nonneg (by norm_num) hradius) hcluster hsourceSeparated q)

#print axioms card_tubeShearReducedParameter_window_le_card
#print axioms card_tubeShearReducedParameter_window_le_hitBudget
#print axioms card_le_sourceShearHitBudget_of_cluster
#print axioms card_tubeShearReducedParameter_window_le_min_hitBudget
#print axioms exists_johnWindow_and_containedMass_le_cardResidual_mul_volume
#print axioms exists_johnWindow_and_containedMass_le_separatedResidual_mul_volume

end
end FamilyStickyWZ2JohnBoxSourceBudgetProducerV1
