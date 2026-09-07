import Family8Grounding.Family8ContractedJohnActualTubeProxyV2
import Family8Grounding.Family8TubeJohnUnitRescalingGeometryLeOneV7
import Family8Grounding.Family8SelectedParentAffineShadingTransportV4
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8StickyFiberContractedJohnProxyDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnActualTubeProxyV2
open Family8TubeJohnContractedLipschitzV1
open Family8TubeJohnUnitRescalingGeometryLeOneV7
open Family8SelectedParentAffineShadingTransportV4
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# An actual contracted-John proxy datum for one literal Sticky fibre

For an active coarse parent we use the repository's explicit John witness,
replace each affine child image by the genuine equal-radius proxy tube, and
put the literal affine image of the original shading inside that proxy.
The source fibre and proxy have exactly the same average multiplicity because
every shading carrier is moved by one common affine equivalence.  No
essential-distinctness or Frostman conclusion is asserted here.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Literal restriction of a source shading to one actual Sticky fibre. -/
def stickyFiberSourceShading
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (k : Fin S.coarseCard) : Shading (S.fiberFamily k) where
  carrier i := Y.carrier i.1
  measurable_carrier i := Y.measurable_carrier i.1
  carrier_subset i := Y.carrier_subset i.1

@[simp]
theorem stickyFiberSourceShading_carrier
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (k : Fin S.coarseCard) (i : {i // i ∈ S.fiber k}) :
    (stickyFiberSourceShading S Y k).carrier i = Y.carrier i.1 :=
  rfl

/-- The canonical contracted John equivalence attached to one active parent. -/
def stickyFiberContractedJohnAffineEquiv
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (k : {k // k ∈ S.activeCoarse}) :
    Space ≃ᵃ[Real] Space :=
  contractedTubeJohnAffineEquiv (S.coarse.tubes k.1) hrho
    (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne S hrho hrhoOne k)

/-- Genuine equal-radius proxy tubes for the literal child fibre. -/
def stickyFiberContractedJohnProxyFamily
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (k : {k // k ∈ S.activeCoarse}) :
    UniformTubeFamily (contractedJohnProxyRadius delta rho)
      {i // i ∈ S.fiber k.1} where
  tubes i := contractedJohnProxyTube (S.coarse.tubes k.1) hrho
    (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne S hrho hrhoOne k) (fine.tubes i.1)
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp]
theorem stickyFiberContractedJohnProxyFamily_tubes
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (k : {k // k ∈ S.activeCoarse})
    (i : {i // i ∈ S.fiber k.1}) :
    (stickyFiberContractedJohnProxyFamily S hrho hrhoOne k).tubes i =
      contractedJohnProxyTube (S.coarse.tubes k.1) hrho
        (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne S hrho hrhoOne k) (fine.tubes i.1) :=
  rfl

@[simp]
theorem stickyFiberContractedJohnProxyFamily_refined
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (k : {k // k ∈ S.activeCoarse}) :
    (stickyFiberContractedJohnProxyFamily S hrho hrhoOne k).refinement.refined =
      Finset.univ :=
  rfl

/-- The literal common-affine image shading, re-housed in the actual proxy
tubes via the proved carrier containment. -/
def stickyFiberContractedJohnProxyShading
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (k : {k // k ∈ S.activeCoarse}) :
    Shading
      (stickyFiberContractedJohnProxyFamily S hrho hrhoOne k).bodyFamily where
  carrier i := stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k ''
    Y.carrier i.1
  measurable_carrier i :=
    (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k).toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
      (Y.measurable_carrier i.1)
  carrier_subset i := by
    exact (Set.image_mono (Y.carrier_subset i.1)).trans
      (image_child_carrier_subset_contractedJohnProxyTube
        (S.coarse.tubes k.1) hrho
        (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne S hrho hrhoOne k) (fine.tubes i.1)
        (S.fiber_carrier_subset_parent k.1 i))

@[simp]
theorem stickyFiberContractedJohnProxyShading_carrier
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (k : {k // k ∈ S.activeCoarse})
    (i : {i // i ∈ S.fiber k.1}) :
    (stickyFiberContractedJohnProxyShading S Y hrho hrhoOne k).carrier i =
      stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k ''
        Y.carrier i.1 :=
  rfl

/-- The actual datum consumed by the paper Frostman predicate. -/
def stickyFiberContractedJohnProxyDatum
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (k : {k // k ∈ S.activeCoarse}) :
    ActualTubeDatum (contractedJohnProxyRadius delta rho)
      {i // i ∈ S.fiber k.1} where
  family := stickyFiberContractedJohnProxyFamily S hrho hrhoOne k
  shading := stickyFiberContractedJohnProxyShading S Y hrho hrhoOne k

@[simp]
theorem stickyFiberContractedJohnProxyDatum_family
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (k : {k // k ∈ S.activeCoarse}) :
    (stickyFiberContractedJohnProxyDatum S Y hrho hrhoOne k).family =
      stickyFiberContractedJohnProxyFamily S hrho hrhoOne k :=
  rfl

@[simp]
theorem stickyFiberContractedJohnProxyDatum_shading
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (k : {k // k ∈ S.activeCoarse}) :
    (stickyFiberContractedJohnProxyDatum S Y hrho hrhoOne k).shading =
      stickyFiberContractedJohnProxyShading S Y hrho hrhoOne k :=
  rfl

/-- Exact common-Jacobian mass transport into the actual proxy shading. -/
theorem stickyFiberContractedJohnProxyShading_shadingMass
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (k : {k // k ∈ S.activeCoarse}) :
    (stickyFiberContractedJohnProxyShading S Y hrho hrhoOne k).shadingMass =
      affineJacobian (stickyFiberContractedJohnAffineEquiv
        S hrho hrhoOne k) *
          (stickyFiberSourceShading S Y k.1).shadingMass := by
  unfold Shading.shadingMass
  simp_rw [stickyFiberContractedJohnProxyShading_carrier,
    volume_image_affineEquiv]
  rw [Finset.mul_sum]
  rfl

/-- The proxy shaded union is exactly the common affine image of the source
fibre shaded union. -/
theorem stickyFiberContractedJohnProxyShading_shadedUnion
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (k : {k // k ∈ S.activeCoarse}) :
    (stickyFiberContractedJohnProxyShading S Y hrho hrhoOne k).shadedUnion =
      stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k ''
        (stickyFiberSourceShading S Y k.1).shadedUnion := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, y, hy, rfl⟩
    exact ⟨y, Set.mem_iUnion.mpr ⟨i, hy⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, y, hi, rfl⟩

/-- The genuine proxy datum preserves the source fibre's average
multiplicity exactly. -/
theorem stickyFiberContractedJohnProxyShading_averageMultiplicity
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (k : {k // k ∈ S.activeCoarse}) :
    (stickyFiberContractedJohnProxyShading S Y hrho hrhoOne k).averageMultiplicity =
      (stickyFiberSourceShading S Y k.1).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [stickyFiberContractedJohnProxyShading_shadingMass,
    stickyFiberContractedJohnProxyShading_shadedUnion,
    volume_image_affineEquiv]
  apply ENNReal.mul_div_mul_left
  · exact (affineJacobian_pos
      (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k)).ne'
  · exact affineJacobian_ne_top _

/-- Every actual proxy tube lies in the unit ball at nested scales. -/
theorem stickyFiberContractedJohnProxyDatum_contained_in_unit_ball
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho) (k : {k // k ∈ S.activeCoarse}) :
    forall i,
      ((stickyFiberContractedJohnProxyDatum
        S Y hrho hrhoOne k).family.tubes i).carrier ⊆
          Metric.closedBall (0 : Space) 1 := by
  intro i
  exact contractedJohnProxyTube_carrier_subset_unitBall
    (S.coarse.tubes k.1) hrho
    (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne S hrho hrhoOne k) (fine.tubes i.1)
    (S.fiber_carrier_subset_parent k.1 i) hdeltaRho

/-- The actual proxy scale is positive. -/
theorem stickyFiberContractedJohnProxyDatum_delta_pos
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    0 < contractedJohnProxyRadius delta rho :=
  contractedJohnProxyRadius_pos hdelta hrho

/-- The actual proxy scale is at most one half throughout the nested window. -/
theorem stickyFiberContractedJohnProxyDatum_delta_le_half
    (hdeltaRho : delta <= rho) (hrho : 0 < rho) :
    contractedJohnProxyRadius delta rho <= (2 : NNReal)⁻¹ := by
  rw [← NNReal.coe_le_coe]
  have hproxy := contractedJohnProxyRadius_le_threeEighths hdeltaRho hrho
  have hhalf : (((2 : NNReal)⁻¹ : NNReal) : Real) = (1 / 2 : Real) := by
    norm_num
  rw [hhalf]
  linarith

#print axioms stickyFiberSourceShading
#print axioms stickyFiberContractedJohnProxyFamily
#print axioms stickyFiberContractedJohnProxyShading
#print axioms stickyFiberContractedJohnProxyDatum
#print axioms stickyFiberContractedJohnProxyShading_shadingMass
#print axioms stickyFiberContractedJohnProxyShading_shadedUnion
#print axioms stickyFiberContractedJohnProxyShading_averageMultiplicity
#print axioms stickyFiberContractedJohnProxyDatum_contained_in_unit_ball
#print axioms stickyFiberContractedJohnProxyDatum_delta_pos
#print axioms stickyFiberContractedJohnProxyDatum_delta_le_half

end

end Family8StickyFiberContractedJohnProxyDatumV1
