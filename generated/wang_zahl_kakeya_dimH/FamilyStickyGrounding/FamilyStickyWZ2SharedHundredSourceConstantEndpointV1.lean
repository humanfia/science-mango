import FamilyStickyGrounding.FamilyStickyWZ2DistortedJohnSourceBudgetEliminationV1
import FamilyStickyGrounding.FamilyStickyRandomWZCommonNeighbourPackingV1
import FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyWZ2SharedHundredSourceConstantEndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomHundredContainerSelectionV1
open FamilyStickyRandomHundredContainerSelectionV1.MaximalSelection
open FamilyStickyRandomWZLineParameterGeometryV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2AmbientShearContainedMassV1
open FamilyStickyWZ2JohnBoxVolumeNormalizationV1
open FamilyStickyWZ2AmbientShearDistortedTubeAdapterV1
open FamilyStickyWZ2DistortedJohnRadiusNormalizationV1
open FamilyStickyWZ2DistortedJohnSourceBudgetEliminationV1

noncomputable section

/-!
# A fixed WZ source factor from one literal common `100`-tube container

The geometric input below records only that every source carrier lies in one
literal hundred-fold tube.  Together with endpoint-parameter separation, the
existing common-neighbour packing theorem then bounds the entire source
index type by `commonHundredNeighbourPackingConstant`.  An auxiliary grid
with no tests is used solely to expose the source family to that theorem; it
adds no incidence or cardinality assumption.

The resulting distorted-John endpoint replaces the finite source-cardinality
factor by the fixed WZ constant.  A final corollary obtains its vertical-chart
hypothesis from the repository's literal fixed-chart filter.
-/

variable {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
  {delta : NNReal} {spacing : Real} {siteCount : Nat}

/-- Minimal geometric data saying that all source tubes occur in one literal
hundred-fold tube.  No counting or analytic endpoint is stored here. -/
structure SharedHundredSourceContainer
    (fine : UniformTubeFamily delta kappa) where
  container : Tube delta
  carrier_subset : forall i,
    (fine.tubes i).carrier <= (hundredTube container).carrier

/-- A source-only presentation of a uniform tube family as an actual tube
grid.  Its test family is empty because only common-neighbour packing is used. -/
def sourcePackingGrid (fine : UniformTubeFamily delta kappa) :
    ActualTubeTranslationGrid delta Unit kappa where
  gridVector := fun _ => 0
  tubes := Finset.univ
  tube := fine.tubes
  testCard := 0
  testBody := fun i => Fin.elim0 i
  activeTests := ∅

@[simp]
theorem sourcePackingGrid_tubes (fine : UniformTubeFamily delta kappa) :
    (sourcePackingGrid fine).tubes = Finset.univ := rfl

@[simp]
theorem sourcePackingGrid_tube (fine : UniformTubeFamily delta kappa)
    (i : kappa) :
    (sourcePackingGrid fine).tube i = fine.tubes i := rfl

/-- A common literal hundred-fold container and WZ endpoint separation force
the full finite source type to have dimension-only cardinality. -/
theorem fintype_card_le_commonHundredNeighbourPackingConstant
    (fine : UniformTubeFamily delta kappa) (hdelta : 0 < delta)
    (hpair : Set.Pairwise (Set.univ : Set kappa) fun i j =>
      WZEndpointParameterSeparated (fine.tubes i) (fine.tubes j))
    (shared : SharedHundredSourceContainer fine) :
    Fintype.card kappa <= commonHundredNeighbourPackingConstant := by
  classical
  let all : Finset kappa := Finset.univ
  by_cases hall : all.Nonempty
  · obtain ⟨b, _hb⟩ := hall
    let G : ActualTubeTranslationGrid delta Unit kappa := sourcePackingGrid fine
    let bActive : ActiveSource G := ⟨b, by simp [G, sourcePackingGrid]⟩
    let target := CommonNeighbour G bActive
    let f : kappa -> target := fun i =>
      ⟨⟨i, by simp [G, sourcePackingGrid]⟩, by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, Or.inr ?_⟩
        exact ⟨shared.container, shared.carrier_subset i,
          shared.carrier_subset b⟩⟩
    have hinjective : Function.Injective f := by
      intro i j hij
      exact congrArg (fun z : target => z.1.1) hij
    have hpairG : Set.Pairwise (G.tubes : Set kappa) fun i j =>
        WZEndpointParameterSeparated (G.tube i) (G.tube j) := by
      simpa [G, sourcePackingGrid] using hpair
    calc
      Fintype.card kappa <= Fintype.card target :=
        Fintype.card_le_of_injective f hinjective
      _ = (commonHundredNeighbourFinset G bActive).card :=
        Fintype.card_coe _
      _ <= commonHundredNeighbourPackingConstant :=
        commonHundredNeighbourFinset_card_le_constant
          G hdelta hpairG bActive
  · have hempty : all = ∅ := Finset.not_nonempty_iff_eq_empty.mp hall
    have hzero : Fintype.card kappa = 0 := by
      simpa [all] using congrArg Finset.card hempty
    simp [hzero]

/-- The full source family inherits the vertical inequality when all of its
indices belong to one literal fixed-chart selection. -/
theorem vertical_half_of_univ_subset_fixedVerticalChart
    (fine : UniformTubeFamily delta kappa) (source : Finset kappa)
    (hselected : (Finset.univ : Finset kappa) <=
      fixedVerticalChartIndices fine source) :
    forall i, (1 / 2 : Real) <= |(fine.tubes i).axis.direction 2| := by
  intro i
  exact ambient_vertical_half_of_subset_fixedVerticalChart
    fine source Finset.univ hselected i (Finset.mem_univ i)

/-- The distorted-John WZ2 endpoint with the source-cardinality factor
replaced by the fixed common-neighbour packing constant. -/
theorem exists_distortedJohnCertificate_and_containedMass_le_WZConstant_mul_volume
    (fine : UniformTubeFamily delta kappa) (K : ConvexBody Space)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (j : Fin siteCount) (i : kappa)
    (hcontained :
      ((indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes) (j, i) : ConvexBody Space) : Set Space) <=
        (K : Set Space))
    (baseD rho : Real) (hspacing : 0 < spacing) (hrho : 0 <= rho)
    (hpair : Set.Pairwise (Set.univ : Set kappa) fun a b =>
      WZEndpointParameterSeparated (fine.tubes a) (fine.tubes b))
    (shared : SharedHundredSourceContainer fine)
    (hvertical : forall l,
      (1 / 2 : Real) <= |(fine.tubes l).axis.direction 2|)
    (hcluster : forall l, |tubeGraphD (fine.tubes l) - baseD| <= rho) :
    ∃ side : Fin 3 -> NNReal,
      ∃ _cert : BoxDimensionsCertificate 288 side K,
        (forall l,
          2 * distortedTubeRadius delta (shearSiteD spacing j) <= side l) ∧
        (∃ l : Fin 3,
          distortedAxisLength (shearSiteD spacing j) <= 6 * side l) ∧
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
                commonHundredNeighbourPackingConstant : Nat) : ENNReal)) *
            volume (K : Set Space) := by
  have hcard := fintype_card_le_commonHundredNeighbourPackingConstant
    fine hdelta hpair shared
  obtain ⟨side, cert, hside, hlong, hmass⟩ :=
    exists_distortedJohnCertificate_and_containedMass_le_cardBudget_mul_volume
      fine K hdelta hdeltaHalf j i hcontained baseD rho hspacing hrho
      hvertical hcluster
  refine ⟨side, cert, hside, hlong, ?_⟩
  let copyBudget : Nat :=
    min siteCount
      (Nat.ceil
        ((2 *
          (4 * johnRadiusVolumeCap K delta
            (shearSiteD spacing j) + rho)) / spacing) + 1)
  have hmass' :
      containedMass
          (indexedTranslatedBodyFamily
            (shearReducedShift spacing (siteCount := siteCount))
            (tubeBodyFamily fine.tubes)) K <=
        (16 * ((copyBudget * Fintype.card kappa : Nat) : ENNReal)) *
          volume (K : Set Space) := by
    simpa only [copyBudget] using hmass
  have hnat :
      copyBudget * Fintype.card kappa <=
        copyBudget * commonHundredNeighbourPackingConstant :=
    Nat.mul_le_mul_left copyBudget hcard
  have hcast :
      ((copyBudget * Fintype.card kappa : Nat) : ENNReal) <=
        ((copyBudget * commonHundredNeighbourPackingConstant : Nat) : ENNReal) := by
    exact_mod_cast hnat
  change containedMass
      (indexedTranslatedBodyFamily
        (shearReducedShift spacing (siteCount := siteCount))
        (tubeBodyFamily fine.tubes)) K <=
      (16 *
        ((copyBudget * commonHundredNeighbourPackingConstant : Nat) : ENNReal)) *
        volume (K : Set Space)
  calc
    containedMass
        (indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes)) K <=
      (16 * ((copyBudget * Fintype.card kappa : Nat) : ENNReal)) *
        volume (K : Set Space) := hmass'
    _ <= (16 *
        ((copyBudget * commonHundredNeighbourPackingConstant : Nat) : ENNReal)) *
          volume (K : Set Space) := by gcongr

/-- Fixed-chart form of the constant-source-factor endpoint.  The pointwise
vertical bound is produced from the literal chart membership. -/
theorem exists_distortedJohnCertificate_and_containedMass_le_WZConstant_of_fixedVerticalChart
    (fine : UniformTubeFamily delta kappa) (K : ConvexBody Space)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (j : Fin siteCount) (i : kappa)
    (hcontained :
      ((indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes) (j, i) : ConvexBody Space) : Set Space) <=
        (K : Set Space))
    (baseD rho : Real) (hspacing : 0 < spacing) (hrho : 0 <= rho)
    (hpair : Set.Pairwise (Set.univ : Set kappa) fun a b =>
      WZEndpointParameterSeparated (fine.tubes a) (fine.tubes b))
    (shared : SharedHundredSourceContainer fine)
    (source : Finset kappa)
    (hselected : (Finset.univ : Finset kappa) <=
      fixedVerticalChartIndices fine source)
    (hcluster : forall l, |tubeGraphD (fine.tubes l) - baseD| <= rho) :
    ∃ side : Fin 3 -> NNReal,
      ∃ _cert : BoxDimensionsCertificate 288 side K,
        (forall l,
          2 * distortedTubeRadius delta (shearSiteD spacing j) <= side l) ∧
        (∃ l : Fin 3,
          distortedAxisLength (shearSiteD spacing j) <= 6 * side l) ∧
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
                commonHundredNeighbourPackingConstant : Nat) : ENNReal)) *
            volume (K : Set Space) := by
  exact exists_distortedJohnCertificate_and_containedMass_le_WZConstant_mul_volume
    fine K hdelta hdeltaHalf j i hcontained baseD rho hspacing hrho hpair shared
      (vertical_half_of_univ_subset_fixedVerticalChart fine source hselected)
      hcluster

#print axioms exists_distortedJohnCertificate_and_containedMass_le_WZConstant_mul_volume
#print axioms exists_distortedJohnCertificate_and_containedMass_le_WZConstant_of_fixedVerticalChart
#print axioms sourcePackingGrid_tubes
#print axioms sourcePackingGrid_tube
#print axioms fintype_card_le_commonHundredNeighbourPackingConstant
#print axioms vertical_half_of_univ_subset_fixedVerticalChart

end
end FamilyStickyWZ2SharedHundredSourceConstantEndpointV1
