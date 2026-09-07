import Family8Grounding.Family8JointTubeFactoringExactUniformProp66AProductV4
import Family8Grounding.Family8ExactAssemblySameDataFiberBridgeV1
import Family8Grounding.Family8StickyFiberSubtypeAverageBridgeV1
import Mathlib.Tactic

/-!
# Exact-uniform coarse partitions as literal Sticky fibres

The exact-card `JointTubeFactoring` output is a `CoarseTubePartition`, whereas
the contracted-John analytic route consumes a literal `StickyScaleCover`
fibre subtype.  The constructor below copies the partition's actual index
data without changing it.  The consumed subtype shading is then the same
actual final fibre of an `ExactAssembly`, and its subtype cardinality is the
joint partition's exact branching when `branchingLoss = 1`.

V1--V3 are failed definitional-equality drafts and are not imported.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CoarseTubePartitionExactUniformStickyFiberV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.Uniformity
open Family8ExactAssemblySameDataFiberBridgeV1
open Family8ExactAssemblySameDataFiberBridgeV1.ExactAssembly
open Family8JointTubeFactoringExactUniformProp66AProductV4
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberSubtypeAverageBridgeV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {iota : Type} {coarseCard : Nat}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho (Fin coarseCard)}

/-- The literal Sticky cover obtained by forgetting only the two branching
bounds of a coarse tube partition.  All active sets and the parent map are
copied from the same `IndexFactorization`. -/
abbrev exactPartitionStickyCover
    (P : CoarseTubePartition fine coarse) : StickyScaleCover fine rho where
  coarseCard := coarseCard
  coarse := coarse
  activeFine := P.fineIndices
  activeCoarse := P.coarseIndices
  parent := P.index.parent
  activeFine_eq_refined := P.fine_eq_refined
  activeCoarse_eq_refined := P.coarse_eq_refined
  parent_mem := P.index.parent_mem
  parent_surjective := P.parent_surjective
  carrier_subset := P.carrier_subset

@[simp] theorem exactPartitionStickyCover_activeFine
    (P : CoarseTubePartition fine coarse) :
    (exactPartitionStickyCover P).activeFine = P.fineIndices := by
  rfl

@[simp] theorem exactPartitionStickyCover_activeCoarse
    (P : CoarseTubePartition fine coarse) :
    (exactPartitionStickyCover P).activeCoarse = P.coarseIndices := by
  rfl

@[simp] theorem exactPartitionStickyCover_fiber
    (P : CoarseTubePartition fine coarse) (k : Fin coarseCard) :
    (exactPartitionStickyCover P).fiber k = P.fiber k := by
  rfl

/-- Exact-uniformity gives the literal Fintype cardinality consumed by the
contracted-John fibre endpoint. -/
theorem exactPartitionStickyCover_fiber_fintypeCard_eq_branching
    (P : CoarseTubePartition fine coarse)
    (hloss : P.branchingLoss = 1)
    (k : Fin coarseCard) (hk : k ∈ P.coarseIndices) :
    Fintype.card {i // i ∈ (exactPartitionStickyCover P).fiber k} =
      P.branching := by
  rw [Fintype.card_coe, exactPartitionStickyCover_fiber]
  exact fiber_card_eq_branching_of_branchingLoss_eq_one P hloss hk

/-- The exact assembly's full-index final fibre and the literal Sticky fibre
subtype have identical genuine average multiplicity. -/
theorem stickyFiber_exactPartition_averageMultiplicity_eq_finalFiber
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {loss : Nat}
    (A : ExactAssembly P.asConvexFactorization Y loss)
    (k : Fin coarseCard) :
    (stickyFiberSourceShading (exactPartitionStickyCover P)
      A.refinement.shading k).averageMultiplicity =
      (Family8ExactAssemblySameDataFiberBridgeV1.ExactAssembly.finalFiberShading
        A k).averageMultiplicity := by
  rw [stickyFiberSourceShading_averageMultiplicity_eq_restrictTo]
  rfl

/-- The same exact identification for multiplicity-counted mass. -/
theorem stickyFiber_exactPartition_shadingMass_eq_finalFiber
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {loss : Nat}
    (A : ExactAssembly P.asConvexFactorization Y loss)
    (k : Fin coarseCard) :
    (stickyFiberSourceShading (exactPartitionStickyCover P)
      A.refinement.shading k).shadingMass =
      (Family8ExactAssemblySameDataFiberBridgeV1.ExactAssembly.finalFiberShading
        A k).shadingMass := by
  rw [stickyFiberSourceShading_shadingMass_eq_restrictTo]
  rfl

#print axioms exactPartitionStickyCover
#print axioms exactPartitionStickyCover_activeFine
#print axioms exactPartitionStickyCover_activeCoarse
#print axioms exactPartitionStickyCover_fiber
#print axioms exactPartitionStickyCover_fiber_fintypeCard_eq_branching
#print axioms stickyFiber_exactPartition_averageMultiplicity_eq_finalFiber
#print axioms stickyFiber_exactPartition_shadingMass_eq_finalFiber

end
end Family8CoarseTubePartitionExactUniformStickyFiberV4
