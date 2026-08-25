import FamilyStickyGrounding.FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
import FamilyStickyGrounding.FamilyStickyWZ2ShearParameterPackingV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set
open scoped NNReal

namespace FamilyStickyWZ2AmbientShearWindowBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyWZ2TranslatedShadingUnionCovarianceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedActualShadingInstantiationV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2ReducedParameterClusterWindowV1
open FamilyStickyWZ2ShearParameterPackingV1

noncomputable section

/-!
# Ambient convex-test containment forces a local WZ2 shear window

For a source tube in the fixed vertical chart, the two transported axis
endpoints belong to every convex test containing the transported tube body.
If that test lies in a coordinate-`1` window of radius `R`, their difference
shows that the translated graph slope `d` has absolute value at most `4 R`.
Combining this geometric fact with a radius-`rho` source cluster and the
explicit shear grid gives a local count of the copy sites, and hence of all
product indices whose transported tube body is contained in the test.

This is an actual ambient-to-parameter-window bridge.  It does not yet turn
the coordinate width into the volume-normalized constant required by a full
uniform Katz--Tao estimate.
-/

/-- An ambient body is contained in a closed window in coordinate `1`. -/
def CoordinateOneWindow (K : ConvexBody Space) (center radius : Real) : Prop :=
  forall p, p ∈ (K : Set Space) -> |p 1 - center| <= radius

/-- Containment of one transported actual tube in a coordinate window bounds
the translated reduced shear parameter. -/
theorem abs_indexedTranslatedTubeParameter_shear_le_four_mul
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (K : ConvexBody Space) (center radius : Real)
    (hwindow : CoordinateOneWindow K center radius)
    {j : tau} {i : kappa}
    (hvertical : (1 / 2 : Real) <=
      |(fine.tubes i).axis.direction 2|)
    (hcontained :
      ((indexedTranslatedBodyFamily shift
          (tubeBodyFamily fine.tubes) (j, i) : ConvexBody Space) : Set Space) <=
        (K : Set Space)) :
    |(indexedTranslatedTubeParameter shift fine (j, i)).2.2| <=
      4 * radius := by
  let T := fine.tubes i
  let q0 := ambientCinematicTranslation
    (shift j).1 (shift j).2.1 (shift j).2.2 T.axis.base
  let q1 := ambientCinematicTranslation
    (shift j).1 (shift j).2.1 (shift j).2.2 T.axis.endpoint
  have hq0 : q0 ∈ (K : Set Space) := by
    apply hcontained
    rw [coe_indexedTranslatedBodyFamily]
    exact ⟨T.axis.base,
      T.axis_subset_carrier T.axis.base_mem_carrier, rfl⟩
  have hq1 : q1 ∈ (K : Set Space) := by
    apply hcontained
    rw [coe_indexedTranslatedBodyFamily]
    exact ⟨T.axis.endpoint,
      T.axis_subset_carrier T.axis.endpoint_mem_carrier, rfl⟩
  have hy0 := hwindow q0 hq0
  have hy1 := hwindow q1 hq1
  have hdiff : |q1 1 - q0 1| <= 2 * radius := by
    calc
      |q1 1 - q0 1| =
          |(q1 1 - center) - (q0 1 - center)| := by ring_nf
      _ <= |q1 1 - center| + |q0 1 - center| := abs_sub _ _
      _ <= radius + radius := add_le_add hy1 hy0
      _ = 2 * radius := by ring
  have hverticalPos : 0 < |T.axis.direction 2| :=
    lt_of_lt_of_le (by norm_num) hvertical
  have hverticalNe : T.axis.direction 2 ≠ 0 := by
    exact abs_pos.mp hverticalPos
  have hparameter :
      q1 1 - q0 1 =
        (indexedTranslatedTubeParameter shift fine (j, i)).2.2 *
          T.axis.direction 2 := by
    simp [q0, q1, T, UnitSegment.endpoint,
      ambientCinematicTranslation, point3,
      indexedTranslatedTubeParameter, translateReducedLineParameter,
      tubeReducedLineParameter, tubeGraphD]
    rw [div_eq_mul_inv, add_mul, mul_assoc, inv_mul_cancel₀ hverticalNe, mul_one]
    ring
  rw [hparameter, abs_mul] at hdiff
  nlinarith [mul_le_mul_of_nonneg_left hvertical (abs_nonneg
    (indexedTranslatedTubeParameter shift fine (j, i)).2.2)]

/-- Copy sites for which at least one actual transported tube body is
contained in the ambient test. -/
def containedShearSites
    {kappa : Type*} [Fintype kappa]
    {delta : NNReal} [DecidableEq kappa]
    (spacing : Real) {siteCount : Nat}
    (fine : UniformTubeFamily delta kappa)
    (K : ConvexBody Space) : Finset (Fin siteCount) := by
  classical
  exact Finset.univ.filter fun j =>
    exists i : kappa,
      (((indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes) (j, i) : ConvexBody Space) : Set Space) <=
        (K : Set Space))

/-- Every ambiently relevant shear site lies in the explicit one-dimensional
parameter window centered at the negative source-cluster center. -/
theorem containedShearSites_subset_parameterWindow
    {kappa : Type*} [Fintype kappa]
    {delta : NNReal} [DecidableEq kappa]
    {spacing : Real} {siteCount : Nat}
    (fine : UniformTubeFamily delta kappa)
    (K : ConvexBody Space) (center radius baseD rho : Real)
    (hwindow : CoordinateOneWindow K center radius)
    (hvertical : forall i,
      (1 / 2 : Real) <= |(fine.tubes i).axis.direction 2|)
    (hcluster : forall i, |tubeGraphD (fine.tubes i) - baseD| <= rho) :
    containedShearSites spacing (siteCount := siteCount) fine K <=
      parameterWindowIndices
        (shearReducedShift spacing (siteCount := siteCount))
        (0, (0, -baseD)) (4 * radius + rho) := by
  classical
  intro j hj
  obtain ⟨_hjUniv, i, hi⟩ := Finset.mem_filter.mp hj
  rw [parameterWindowIndices, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have htranslated :=
    abs_indexedTranslatedTubeParameter_shear_le_four_mul
      (shearReducedShift spacing (siteCount := siteCount)) fine
      K center radius hwindow (hvertical i) hi
  simp only [indexedTranslatedTubeParameter, translateReducedLineParameter,
    tubeReducedLineParameter, shearReducedShift] at htranslated
  simp only [reducedParameterDistance, shearReducedShift]
  rw [max_eq_right]
  · rw [max_eq_right]
    · calc
        |((j : Nat) : Real) * spacing - -baseD| =
            |(tubeGraphD (fine.tubes i) +
                ((j : Nat) : Real) * spacing) -
              (tubeGraphD (fine.tubes i) - baseD)| := by
              congr 1
              ring
        _ <= |tubeGraphD (fine.tubes i) +
              ((j : Nat) : Real) * spacing| +
            |tubeGraphD (fine.tubes i) - baseD| := abs_sub _ _
        _ <= 4 * radius + rho := add_le_add htranslated (hcluster i)
    · simp
  · simp

/-- The number of shear copies which can contribute a contained transported
tube is independent of the total copy count. -/
theorem card_containedShearSites_le_hitBudget
    {kappa : Type*} [Fintype kappa]
    {delta : NNReal} [DecidableEq kappa]
    {spacing : Real} {siteCount : Nat}
    (fine : UniformTubeFamily delta kappa)
    (K : ConvexBody Space) (center radius baseD rho : Real)
    (hspacing : 0 < spacing) (hradius : 0 <= radius) (hrho : 0 <= rho)
    (hwindow : CoordinateOneWindow K center radius)
    (hvertical : forall i,
      (1 / 2 : Real) <= |(fine.tubes i).axis.direction 2|)
    (hcluster : forall i, |tubeGraphD (fine.tubes i) - baseD| <= rho) :
    (containedShearSites spacing (siteCount := siteCount) fine K).card <=
      shearShiftHitBudget spacing (4 * radius + rho) := by
  exact (Finset.card_le_card
    (containedShearSites_subset_parameterWindow fine K center radius baseD rho
      hwindow hvertical hcluster)).trans
    (card_shearReducedShift_window_le_hitBudget hspacing
      (add_nonneg (mul_nonneg (by norm_num) hradius) hrho)
      (0, (0, -baseD)))

/-- Literal product indices whose transported actual tube bodies lie in the
ambient test. -/
def containedShearProductIndices
    {kappa : Type*} [Fintype kappa]
    {delta : NNReal} [DecidableEq kappa]
    (spacing : Real) {siteCount : Nat}
    (fine : UniformTubeFamily delta kappa)
    (K : ConvexBody Space) : Finset (Fin siteCount × kappa) := by
  classical
  exact Finset.univ.filter fun ji =>
    (((indexedTranslatedBodyFamily
        (shearReducedShift spacing (siteCount := siteCount))
        (tubeBodyFamily fine.tubes) ji : ConvexBody Space) : Set Space) <=
      (K : Set Space))

/-- Ambient containment count: a local shear-site budget times the source
cardinality, with no global `siteCount` factor. -/
theorem card_containedShearProductIndices_le_local
    {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
    {delta : NNReal}
    {spacing : Real} {siteCount : Nat}
    (fine : UniformTubeFamily delta kappa)
    (K : ConvexBody Space) (center radius baseD rho : Real)
    (hspacing : 0 < spacing) (hradius : 0 <= radius) (hrho : 0 <= rho)
    (hwindow : CoordinateOneWindow K center radius)
    (hvertical : forall i,
      (1 / 2 : Real) <= |(fine.tubes i).axis.direction 2|)
    (hcluster : forall i, |tubeGraphD (fine.tubes i) - baseD| <= rho) :
    (containedShearProductIndices spacing (siteCount := siteCount) fine K).card <=
      shearShiftHitBudget spacing (4 * radius + rho) *
        Fintype.card kappa := by
  classical
  have hsubset : containedShearProductIndices spacing (siteCount := siteCount) fine K <=
      containedShearSites spacing (siteCount := siteCount) fine K ×ˢ
        (Finset.univ : Finset kappa) := by
    intro ji hji
    rw [Finset.mem_product]
    constructor
    · rw [containedShearSites, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ji.2, ?_⟩
      exact (Finset.mem_filter.mp hji).2
    · exact Finset.mem_univ _
  calc
    (containedShearProductIndices spacing (siteCount := siteCount) fine K).card <=
        (containedShearSites spacing (siteCount := siteCount) fine K ×ˢ
          (Finset.univ : Finset kappa)).card := Finset.card_le_card hsubset
    _ = (containedShearSites spacing (siteCount := siteCount) fine K).card * Fintype.card kappa := by
      simp
    _ <= shearShiftHitBudget spacing (4 * radius + rho) *
        Fintype.card kappa := by
      gcongr
      exact card_containedShearSites_le_hitBudget fine K center radius baseD rho
        hspacing hradius hrho hwindow hvertical hcluster

#print axioms abs_indexedTranslatedTubeParameter_shear_le_four_mul
#print axioms containedShearSites_subset_parameterWindow
#print axioms card_containedShearSites_le_hitBudget
#print axioms card_containedShearProductIndices_le_local

end
end FamilyStickyWZ2AmbientShearWindowBridgeV1
