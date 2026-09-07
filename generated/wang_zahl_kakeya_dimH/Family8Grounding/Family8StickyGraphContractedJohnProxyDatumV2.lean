import Family8Grounding.Family8GeneralizedKatzTaoMultiplicityV1
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Family8Grounding.Family8StickyFiberContractedJohnProxyDatumV1
import Family8Grounding.Family8StickyScaleCoverFrozenComparableAdapterV2

/-!
# A contracted-John proxy datum on one literal graph, V2

V1 is frozen after direct validation found that `ActualTubeDatum` was only
available transitively and that one proof parameter in the family constructor
was intentionally unused.  This ADD-only successor imports and opens the
authoritative datum module explicitly and marks that constructor parameter.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyGraphContractedJohnProxyDatumV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnActualTubeProxyV2
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyScaleCoverFrozenComparableAdapterV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The original fine datum restricted directly to one literal graph. -/
def stickyGraphSourceDatum
    (Y : Shading fine.bodyFamily) (graph : Finset index) :
    ActualTubeDatum delta {i // i ∈ graph} :=
  restrictActualTubeDatum
    { family := fine
      shading := Y }
    graph

/-- Genuine equal-radius contracted-John proxy tubes on exactly the graph
indices, all attached to the same active coarse parent. -/
def stickyGraphContractedJohnProxyFamily
    (S : StickyScaleCover fine rho)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (k : {k // k ∈ S.activeCoarse})
    (graph : Finset index) (_hgraph : graph ⊆ S.fiber k.1) :
    UniformTubeFamily (contractedJohnProxyRadius delta rho)
      {i // i ∈ graph} where
  tubes i := contractedJohnProxyTube (S.coarse.tubes k.1) hrho
    (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne
      S hrho hrhoOne k) (fine.tubes i.1)
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp]
theorem stickyGraphContractedJohnProxyFamily_tubes
    (S : StickyScaleCover fine rho)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (k : {k // k ∈ S.activeCoarse})
    (graph : Finset index) (hgraph : graph ⊆ S.fiber k.1)
    (i : {i // i ∈ graph}) :
    (stickyGraphContractedJohnProxyFamily
      S hrho hrhoOne k graph hgraph).tubes i =
      contractedJohnProxyTube (S.coarse.tubes k.1) hrho
        (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne
          S hrho hrhoOne k) (fine.tubes i.1) :=
  rfl

/-- The common-affine graph shading, housed in the genuine proxy tubes. -/
def stickyGraphContractedJohnProxyShading
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (k : {k // k ∈ S.activeCoarse})
    (graph : Finset index) (hgraph : graph ⊆ S.fiber k.1) :
    Shading
      (stickyGraphContractedJohnProxyFamily
        S hrho hrhoOne k graph hgraph).bodyFamily where
  carrier i := stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k ''
    Y.carrier i.1
  measurable_carrier i :=
    (stickyFiberContractedJohnAffineEquiv
      S hrho hrhoOne k).toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
      (Y.measurable_carrier i.1)
  carrier_subset i := by
    let fi : {j // j ∈ S.fiber k.1} := ⟨i.1, hgraph i.2⟩
    exact (Set.image_mono (Y.carrier_subset i.1)).trans
      (image_child_carrier_subset_contractedJohnProxyTube
        (S.coarse.tubes k.1) hrho
        (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne
          S hrho hrhoOne k) (fine.tubes i.1)
        (S.fiber_carrier_subset_parent k.1 fi))

@[simp]
theorem stickyGraphContractedJohnProxyShading_carrier
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (k : {k // k ∈ S.activeCoarse})
    (graph : Finset index) (hgraph : graph ⊆ S.fiber k.1)
    (i : {i // i ∈ graph}) :
    (stickyGraphContractedJohnProxyShading
      S Y hrho hrhoOne k graph hgraph).carrier i =
      stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k ''
        Y.carrier i.1 :=
  rfl

/-- The actual proxy datum indexed by exactly the graph subtype. -/
def stickyGraphContractedJohnProxyDatum
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (k : {k // k ∈ S.activeCoarse})
    (graph : Finset index) (hgraph : graph ⊆ S.fiber k.1) :
    ActualTubeDatum (contractedJohnProxyRadius delta rho)
      {i // i ∈ graph} where
  family := stickyGraphContractedJohnProxyFamily
    S hrho hrhoOne k graph hgraph
  shading := stickyGraphContractedJohnProxyShading
    S Y hrho hrhoOne k graph hgraph

/-- The direct graph-subtype source datum has the same mass as the standard
full-index graph restriction. -/
theorem stickyGraphSourceDatum_shadingMass_eq_restrictTo
    (Y : Shading fine.bodyFamily) (graph : Finset index) :
    (stickyGraphSourceDatum Y graph).shading.shadingMass =
      (IndexedShadingRefinement.restrictTo Y graph).shading.shadingMass := by
  rw [stickyGraphSourceDatum, restrictActualTubeDatum_shadingMass,
    shadingMass_restrictTo_eq_sum]

/-- The direct graph-subtype source datum has the same shaded union as the
standard full-index graph restriction. -/
theorem stickyGraphSourceDatum_shadedUnion_eq_restrictTo
    (Y : Shading fine.bodyFamily) (graph : Finset index) :
    (stickyGraphSourceDatum Y graph).shading.shadedUnion =
      (IndexedShadingRefinement.restrictTo Y graph).shading.shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨i.1, ?_⟩
    rw [IndexedShadingRefinement.restrictTo_carrier, if_pos i.2]
    exact hxi
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    rw [IndexedShadingRefinement.restrictTo_carrier] at hxi
    by_cases hi : i ∈ graph
    · rw [if_pos hi] at hxi
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
    · rw [if_neg hi] at hxi
      exact hxi.elim

/-- The proxy shading mass is the common affine Jacobian times the source
graph-subtype shading mass. -/
theorem stickyGraphContractedJohnProxyShading_shadingMass
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (k : {k // k ∈ S.activeCoarse})
    (graph : Finset index) (hgraph : graph ⊆ S.fiber k.1) :
    (stickyGraphContractedJohnProxyShading
      S Y hrho hrhoOne k graph hgraph).shadingMass =
      affineJacobian
          (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k) *
        (stickyGraphSourceDatum Y graph).shading.shadingMass := by
  unfold Shading.shadingMass
  simp_rw [stickyGraphContractedJohnProxyShading_carrier,
    volume_image_affineEquiv]
  rw [Finset.mul_sum]
  rfl

/-- The proxy shaded union is the common affine image of the exact graph
source union. -/
theorem stickyGraphContractedJohnProxyShading_shadedUnion
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (k : {k // k ∈ S.activeCoarse})
    (graph : Finset index) (hgraph : graph ⊆ S.fiber k.1) :
    (stickyGraphContractedJohnProxyShading
      S Y hrho hrhoOne k graph hgraph).shadedUnion =
      stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k ''
        (stickyGraphSourceDatum Y graph).shading.shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨y, Set.mem_iUnion.mpr ⟨i, hy⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    exact Set.mem_iUnion.mpr ⟨i, y, hi, rfl⟩

/-- The graph proxy preserves the literal graph restriction's average exactly. -/
theorem stickyGraphContractedJohnProxyShading_averageMultiplicity
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (k : {k // k ∈ S.activeCoarse})
    (graph : Finset index) (hgraph : graph ⊆ S.fiber k.1) :
    (stickyGraphContractedJohnProxyShading
      S Y hrho hrhoOne k graph hgraph).averageMultiplicity =
      (IndexedShadingRefinement.restrictTo Y graph).shading.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [stickyGraphContractedJohnProxyShading_shadingMass,
    stickyGraphContractedJohnProxyShading_shadedUnion,
    volume_image_affineEquiv,
    stickyGraphSourceDatum_shadingMass_eq_restrictTo,
    stickyGraphSourceDatum_shadedUnion_eq_restrictTo]
  apply ENNReal.mul_div_mul_left
  · exact (affineJacobian_pos
      (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k)).ne'
  · exact affineJacobian_ne_top _

/-- Every tube of the literal graph proxy is contained in the unit ball. -/
theorem stickyGraphContractedJohnProxyDatum_contained_in_unit_ball
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    (k : {k // k ∈ S.activeCoarse})
    (graph : Finset index) (hgraph : graph ⊆ S.fiber k.1) :
    ∀ i,
      ((stickyGraphContractedJohnProxyDatum
        S Y hrho hrhoOne k graph hgraph).family.tubes i).carrier ⊆
          Metric.closedBall (0 : Space) 1 := by
  intro i
  let fi : {j // j ∈ S.fiber k.1} := ⟨i.1, hgraph i.2⟩
  exact contractedJohnProxyTube_carrier_subset_unitBall
    (S.coarse.tubes k.1) hrho
    (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne
      S hrho hrhoOne k) (fine.tubes i.1)
    (S.fiber_carrier_subset_parent k.1 fi) hdeltaRho

#print axioms stickyGraphSourceDatum
#print axioms stickyGraphContractedJohnProxyFamily
#print axioms stickyGraphContractedJohnProxyShading
#print axioms stickyGraphContractedJohnProxyDatum
#print axioms stickyGraphContractedJohnProxyShading_averageMultiplicity
#print axioms stickyGraphContractedJohnProxyDatum_contained_in_unit_ball

end
end Family8StickyGraphContractedJohnProxyDatumV2
