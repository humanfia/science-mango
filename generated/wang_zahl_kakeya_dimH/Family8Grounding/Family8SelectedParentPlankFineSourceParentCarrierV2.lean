import Family8Grounding.Family8SelectedParentPlankFineMassProxyDatumV2
import FamilyStickyGrounding.FamilyStickyHierarchyEndpointPrefixShadingTransportV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankFineSourceParentCarrierV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineMassProxyDatumV2
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyDatumV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

/-!
# The literal selected-plank fine source and its actual parent carrier

The selected-plank source subtype is exactly one actual Sticky fibre.  Its
shaded union is therefore the literal carrier used by
`parentAggregatedShading` at that same parent.  This file records the
subtype/iUnion reindexing and its mass, volume, and average-multiplicity
consequences.  No geometric or analytic estimate is assumed.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The selected-plank source union is exactly the local carrier of the
same actual parent in the parent-aggregated shading. -/
theorem selectedPlankFineSourceShading_shadedUnion_eq_parentCarrier
    (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label}) :
    (selectedPlankFineSourceShading Y e S B hrho label W).shadedUnion =
      (parentAggregatedShading S Y).carrier W.1.1 := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have hi := (S.mem_fiber i.1 W.1.1.1).1 i.2
    let ii : {i // i ∈ S.activeFine} := ⟨i.1, hi.1⟩
    have hiiFiber : ii ∈ (activeIndexFactorization S).fiber W.1.1 := by
      rw [IndexFactorization.mem_fiber]
      refine ⟨Finset.mem_univ ii, ?_⟩
      apply Subtype.ext
      exact hi.2
    change x ∈ parentAggregatedCarrier S Y W.1.1
    exact Set.mem_iUnion.mpr
      ⟨ii, Set.mem_iUnion.mpr ⟨hiiFiber, by
        simpa only [selectedPlankFineSourceShading_carrier] using hxi⟩⟩
  · intro hx
    change x ∈ parentAggregatedCarrier S Y W.1.1 at hx
    obtain ⟨ii, hxii⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hiiFiber, hxi⟩ := Set.mem_iUnion.mp hxii
    have hparent :=
      (IndexFactorization.mem_fiber
        (activeIndexFactorization S) ii W.1.1).1 hiiFiber
    have hiFiber : ii.1 ∈ S.fiber W.1.1.1 := by
      apply (S.mem_fiber ii.1 W.1.1.1).2
      exact ⟨ii.2, congrArg Subtype.val hparent.2⟩
    let i : SelectedPlankFineIndex S W := ⟨ii.1, hiFiber⟩
    exact Set.mem_iUnion.mpr
      ⟨i, by
        simpa only [selectedPlankFineSourceShading_carrier] using hxi⟩

/-- The source mass is the exact multiplicity-counted sum over the literal
old-index Sticky fibre. -/
theorem selectedPlankFineSourceShading_shadingMass_eq_sum_fiber
    (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label}) :
    (selectedPlankFineSourceShading Y e S B hrho label W).shadingMass =
      ∑ i ∈ S.fiber W.1.1.1, volume (Y.carrier i) := by
  classical
  unfold Shading.shadingMass
  simp only [selectedPlankFineSourceShading_carrier]
  symm
  exact Finset.sum_subtype _ (fun _i => Iff.rfl) _

/-- Taking volume of the exact local-union identity introduces no loss. -/
theorem selectedPlankFineSourceShading_shadedUnion_volume_eq_parentCarrier
    (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label}) :
    volume (selectedPlankFineSourceShading
      Y e S B hrho label W).shadedUnion =
      volume ((parentAggregatedShading S Y).carrier W.1.1) := by
  rw [selectedPlankFineSourceShading_shadedUnion_eq_parentCarrier]

/-- The actual source-fibre average has the local parent carrier as its
literal union-volume denominator. -/
theorem selectedPlankFineSourceShading_averageMultiplicity_eq_parentCarrier
    (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label}) :
    (selectedPlankFineSourceShading Y e S B hrho label W).averageMultiplicity =
      (selectedPlankFineSourceShading Y e S B hrho label W).shadingMass /
        volume ((parentAggregatedShading S Y).carrier W.1.1) := by
  unfold Shading.averageMultiplicity
  rw [selectedPlankFineSourceShading_shadedUnion_eq_parentCarrier]

/-- Consequently the mass-retaining affine proxy has the same explicit
actual-parent denominator. -/
theorem selectedPlankFineMassProxyShading_averageMultiplicity_eq_parentCarrier
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (haxisLength : ∀ i : SelectedPlankFineIndex S W,
      ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)‖ ≤ 1)
    (hradius :
      affineLinearOperatorNorm (bucketNormalizedAffineEquiv e label) *
        (delta : Real) ≤ (s : Real)) :
    (selectedPlankFineMassProxyShading s Y e S B hrho label W
      haxisLength hradius).averageMultiplicity =
      (selectedPlankFineSourceShading Y e S B hrho label W).shadingMass /
        volume ((parentAggregatedShading S Y).carrier W.1.1) := by
  rw [selectedPlankFineMassProxyShading_averageMultiplicity,
    selectedPlankFineSourceShading_averageMultiplicity_eq_parentCarrier]

#print axioms selectedPlankFineSourceShading_shadedUnion_eq_parentCarrier
#print axioms selectedPlankFineSourceShading_shadingMass_eq_sum_fiber
#print axioms
  selectedPlankFineSourceShading_shadedUnion_volume_eq_parentCarrier
#print axioms
  selectedPlankFineSourceShading_averageMultiplicity_eq_parentCarrier
#print axioms
  selectedPlankFineMassProxyShading_averageMultiplicity_eq_parentCarrier

end
end Family8SelectedParentPlankFineSourceParentCarrierV2
