import Family8Grounding.Family8CoarseTubePartitionExactUniformStickyFiberV4
import Family8Grounding.Family8FullGreedyCanonicalMassDensityAssemblyV1
import Family8Grounding.Family8SelectedParentMassPopularProp66AInnerV4
import Family8Grounding.Family8SourceMassPartitionParentAggregatedFloorV3
import Mathlib.Tactic

/-!
# Balanced exact partitions give the actual Eq46 source floor

The selected partition's branching bound controls the literal active-subtype
fibres of the corresponding Sticky cover.  After parent aggregation, the
full greedy factorization restricts to `univ`, so no further source mass is
lost.  This yields the exact Jacobian-weighted source factor used by Equation
(46), with the genuine partition branching loss visible.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ExactPartitionBalancedSourceFactorFloorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family6AffineConvexVolumeCoreV1
open Family8FullGreedyCanonicalMassDensityAssemblyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentMassPopularProp66AInnerV4
open Family8SourceMassPartitionParentAggregatedFloorV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

variable {delta rho : NNReal} {iota : Type} {coarseCard : Nat}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho (Fin coarseCard)}

/-- A partition fibre cap transfers exactly to the active-subtype parent
factorization used by parent aggregation. -/
theorem activeIndexFiber_card_le_partition_loss_mul_branching
    (P : CoarseTubePartition fine coarse)
    (k : {k // k ∈ (exactPartitionStickyCover P).activeCoarse}) :
    ((activeIndexFactorization (exactPartitionStickyCover P)).fiber k).card ≤
      P.branchingLoss * P.branching := by
  let S := exactPartitionStickyCover P
  have himage :
      ((activeIndexFactorization S).fiber k).image Subtype.val ⊆
        P.fiber k.1 := by
    intro i hi
    obtain ⟨ii, hii, rfl⟩ := Finset.mem_image.mp hi
    have hfactor :=
      (IndexFactorization.mem_fiber (activeIndexFactorization S) ii k).mp hii
    apply (P.mem_fiber ii.1 k.1).mpr
    refine ⟨?_, congrArg Subtype.val hfactor.2⟩
    exact ii.2
  calc
    ((activeIndexFactorization S).fiber k).card =
        (((activeIndexFactorization S).fiber k).image Subtype.val).card := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective]
    _ ≤ (P.fiber k.1).card := Finset.card_le_card himage
    _ ≤ P.branchingLoss * P.branching :=
      P.fiber_card_le_loss_mul_branching k.1 k.2

/-- The selected active shading, divided by the actual balanced fibre cap,
survives both parent aggregation and the full greedy source restriction. -/
theorem exactPartition_fullGreedy_sourceMass_floor
    (P : CoarseTubePartition fine coarse) (Y : Shading fine.bodyFamily)
    (G : GreedyDensityPartition
      (exactPartitionStickyCover P).activeCoarseFamily
      (hullCandidates (Finset.univ : Finset
        (ActiveParentIndex (exactPartitionStickyCover P))))
      (hullContainer (exactPartitionStickyCover P).activeCoarseFamily)
      Finset.univ) :
    (activeFineShading (exactPartitionStickyCover P) Y).shadingMass /
        (P.branchingLoss * P.branching : Nat) ≤
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading (exactPartitionStickyCover P) Y)
        (greedyParentFactorization
          (exactPartitionStickyCover P) G).index.fine).shading.shadingMass := by
  let S := exactPartitionStickyCover P
  let M := P.branchingLoss * P.branching
  have hMpos : 0 < M := Nat.mul_pos P.branchingLoss_pos P.branching_pos
  have hM0 : (M : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hMpos
  have hMTop : (M : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hscaled : (M : ENNReal) *
      ((activeFineShading S Y).shadingMass / (M : ENNReal)) ≤
        (activeFineShading S Y).shadingMass := by
    rw [mul_comm]
    exact le_of_eq (ENNReal.div_mul_cancel hM0 hMTop)
  have hfloor :
      (activeFineShading S Y).shadingMass / (M : ENNReal) ≤
        (parentAggregatedShading S Y).shadingMass :=
    sourceFloor_le_parentAggregatedShading_of_fiberCard
      S Y M hMpos
        (activeIndexFiber_card_le_partition_loss_mul_branching P) hscaled
  rw [fullGreedy_sourceActive_mass_eq]
  simpa only [S, M] using hfloor

variable {index : Type} [Fintype index] [DecidableEq index]

/-- The preceding source-mass floor, multiplied by the actual normalized
John Jacobian, is bounded by the literal Eq46 source factor. -/
theorem exactPartition_selectedParentMassPopularSourceFactor_floor
    (D : ActualTubeDatum delta index)
    {coarseCard : Nat}
    {coarse : UniformTubeFamily rho (Fin coarseCard)}
    (P0 : CoarseTubePartition D.family coarse)
    (hrho : 0 < rho)
    (G : GreedyDensityPartition
      (exactPartitionStickyCover P0).activeCoarseFamily
      (hullCandidates (Finset.univ : Finset
        (ActiveParentIndex (exactPartitionStickyCover P0))))
      (hullContainer (exactPartitionStickyCover P0).activeCoarseFamily)
      Finset.univ)
    (k : Fin (blocks
      (exactPartitionStickyCover P0).activeCoarseFamily G).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int) :
    affineJacobian
        (bucketNormalizedAffineEquiv
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame
              (exactPartitionStickyCover P0) hrho G k) r hr)
          label) *
      ((activeFineShading
          (exactPartitionStickyCover P0) D.shading).shadingMass /
        (P0.branchingLoss * P0.branching : Nat)) ≤
      selectedParentMassPopularSourceFactor D
        (exactPartitionStickyCover P0) hrho G k r hr label := by
  unfold selectedParentMassPopularSourceFactor
  exact mul_le_mul' le_rfl
    (exactPartition_fullGreedy_sourceMass_floor P0 D.shading G)

#print axioms activeIndexFiber_card_le_partition_loss_mul_branching
#print axioms exactPartition_fullGreedy_sourceMass_floor
#print axioms exactPartition_selectedParentMassPopularSourceFactor_floor

end
end Family8ExactPartitionBalancedSourceFactorFloorV1
