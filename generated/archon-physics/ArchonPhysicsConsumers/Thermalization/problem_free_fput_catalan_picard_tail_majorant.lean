import ArchonPhysics.FreeFPUTCatalanPicardTailMajorant

/-!
Named consumer for the arbitrary-order fixed-root Catalan/Picard majorant.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.FreeFPUTCatalanPicardTailMajorant
open ArchonPhysics.FreeFPUTBinaryTreeTimeSimplexWeight
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open Filter Topology

noncomputable section

theorem free_FPUT_Catalan_order_and_tail_bounds_consumer
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    {A q : Real} (hA : 0 <= A) (hq0 : 0 <= q) (hq1 : q < 1)
    (hsingle : forall r history,
      ‖coefficient r history‖ <=
        A * singleHistoryCatalanScale N q r) :
    (forall r,
      ‖fixedRootRawHistoryOrderSum N rootMomentum coefficient r‖ <=
        A * q ^ r) ∧
    (forall R,
      ‖fixedRootRawHistoryTail N rootMomentum coefficient R‖ <=
        A * q ^ R / (1 - q)) := by
  constructor
  · intro r
    exact norm_fixedRootRawHistoryOrderSum_le_geometric
      N rootMomentum coefficient hA hq0 hsingle r
  · intro R
    exact norm_fixedRootRawHistoryTail_le_geometric
      N rootMomentum coefficient hA hq0 hq1 hsingle R

theorem free_FPUT_Catalan_absolute_sum_and_vanishing_tail_consumer
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    {A q : Real} (hA : 0 <= A) (hq0 : 0 <= q) (hq1 : q < 1)
    (hsingle : forall r history,
      ‖coefficient r history‖ <=
        A * singleHistoryCatalanScale N q r) :
    Summable (fun r : Nat =>
      fixedRootRawHistoryOrderSum N rootMomentum coefficient r) ∧
    Tendsto (fun R : Nat =>
      ‖fixedRootRawHistoryTail N rootMomentum coefficient R‖)
      atTop (nhds 0) := by
  exact ⟨summable_fixedRootRawHistoryOrderSum
      N rootMomentum coefficient hA hq0 hq1 hsingle,
    norm_fixedRootRawHistoryTail_tendsto_zero
      N rootMomentum coefficient hA hq0 hq1 hsingle⟩

theorem free_FPUT_realized_Physlib_kernel_tail_consumer
    {Mode : Type*} {kernel : BinaryTreeCoefficientKernel Mode}
    (bound : BinaryTreeCoefficientKernelMajorant kernel)
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (realize : (r : Nat) ->
      FixedRootRawHistoryIndex N r rootMomentum ->
        RandomEigenmodeBinaryTree Mode)
    (horder : forall r history, (realize r history).shape.order = r)
    {A q : Real} (hA : 0 <= A) (hq0 : 0 <= q) (hq1 : q < 1)
    (hleafA : bound.leafBound <= A)
    (hbranch : bound.leafBound * bound.branchBound <=
      q / (16 * (N : Real))) :
    (forall r,
      ‖fixedRootRealizedKernelOrderSum
        kernel N rootMomentum realize r‖ <= A * q ^ r) ∧
    (forall R,
      ‖fixedRootRealizedKernelTail
        kernel N rootMomentum realize R‖ <= A * q ^ R / (1 - q)) ∧
    Tendsto (fun R : Nat =>
      ‖fixedRootRealizedKernelTail
        kernel N rootMomentum realize R‖) atTop (nhds 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    exact norm_fixedRootRealizedKernelOrderSum_le_geometric bound
      N rootMomentum realize horder hA hq0 hleafA hbranch r
  · intro R
    exact norm_fixedRootRealizedKernelTail_le_geometric bound
      N rootMomentum realize horder hA hq0 hq1 hleafA hbranch R
  · exact norm_fixedRootRealizedKernelTail_tendsto_zero bound
      N rootMomentum realize horder hA hq0 hq1 hleafA hbranch

theorem free_FPUT_exact_time_simplex_tail_consumer
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    {A q T : Real} (hA : 0 <= A) (hq : 0 <= q) (hT : 0 <= T)
    (hcontract : q * T < 1)
    (hsingle : forall r history,
      ‖coefficient r history‖ <=
        A * singleHistoryExactTimeScale N q r *
          binaryTreeTimeSimplexWeight history.1.1 T) :
    (forall r,
      ‖fixedRootRawHistoryOrderSum N rootMomentum coefficient r‖ <=
        A * singleHistoryExactTimeScale N q r *
          fixedRootRawHistoryTimeWeight r rootMomentum T) ∧
    (forall r,
      ‖fixedRootRawHistoryOrderSum N rootMomentum coefficient r‖ <=
        A * (q * T) ^ r) ∧
    (forall R,
      ‖fixedRootRawHistoryTail N rootMomentum coefficient R‖ <=
        A * (q * T) ^ R / (1 - q * T)) ∧
    Tendsto (fun R : Nat =>
      ‖fixedRootRawHistoryTail N rootMomentum coefficient R‖)
      atTop (nhds 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r
    exact norm_fixedRootRawHistoryOrderSum_le_exactTimeSimplex
      N rootMomentum coefficient hA hq hT hsingle r
  · intro r
    exact norm_fixedRootRawHistoryOrderSum_le_timeSimplexGeometric
      N rootMomentum coefficient hA hq hT hsingle r
  · intro R
    exact norm_fixedRootRawHistoryTimeSimplexTail_le
      N rootMomentum coefficient hA hq hT hcontract hsingle R
  · exact norm_fixedRootRawHistoryTimeSimplexTail_tendsto_zero
      N rootMomentum coefficient hA hq hT hcontract hsingle

theorem free_FPUT_per_vertex_cost_tail_consumer
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    {A rho T : Real} (hA : 0 <= A) (hrho : 0 <= rho) (hT : 0 <= T)
    (hcontract : 4 * (N : Real) * rho * T < 1)
    (hsingle : forall r history,
      ‖coefficient r history‖ <=
        A * rho ^ r *
          binaryTreeTimeSimplexWeight history.1.1 T) :
    (forall r,
      ‖fixedRootRawHistoryOrderSum N rootMomentum coefficient r‖ <=
        A * (4 * (N : Real) * rho * T) ^ r) ∧
    (forall R,
      ‖fixedRootRawHistoryTail N rootMomentum coefficient R‖ <=
        A * (4 * (N : Real) * rho * T) ^ R /
          (1 - 4 * (N : Real) * rho * T)) := by
  constructor
  · intro r
    exact norm_fixedRootRawHistoryOrderSum_le_of_perVertexTimeSimplexCost
      N rootMomentum coefficient hA hrho hT hsingle r
  · intro R
    exact norm_fixedRootRawHistoryTail_le_of_perVertexTimeSimplexCost
      N rootMomentum coefficient hA hrho hT hcontract hsingle R

#print axioms free_FPUT_Catalan_order_and_tail_bounds_consumer
#print axioms free_FPUT_Catalan_absolute_sum_and_vanishing_tail_consumer
#print axioms free_FPUT_realized_Physlib_kernel_tail_consumer
#print axioms free_FPUT_exact_time_simplex_tail_consumer
#print axioms free_FPUT_per_vertex_cost_tail_consumer

end

end ArchonPhysicsConsumers.Thermalization
