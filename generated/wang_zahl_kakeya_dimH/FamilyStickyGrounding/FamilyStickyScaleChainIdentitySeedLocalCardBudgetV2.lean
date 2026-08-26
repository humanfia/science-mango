import FamilyStickyGrounding.FamilyStickyScaleChainFullyAutomaticFixedLocalCardEndpointV2
import FamilyStickyGrounding.FamilyStickyHierarchyWidenedCrossParentSourceBoundV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainIdentitySeedLocalCardBudgetV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainActualStrictLossWithConstantV1
open FamilyStickyScaleChainLocalCardAutomaticBoundsV2
open FamilyStickyScaleChainLocalCardBudgetInvariantV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyScaleChainFullyAutomaticFixedLocalCardEndpointV2
open FamilyStickyHierarchyWidenedCrossParentSourceBoundV1

noncomputable section

/-!
# Identity-cover seed local-card budgets

For the canonical identity-radius coherent cover, every interval keeps one
active coarse occurrence for each active refined source occurrence.  Hence
its adjacent active-fine cardinality is exactly the original refined
cardinality, independently of the finite scale sequence and interval.

This turns any explicit upper bound on that refined cardinality into the
local-card certificate required by the fully automatic fixed-`n` endpoint.
For a genuine multiscale hierarchy, the existing branching-product theorem
supplies such a bound from the parent count at any selected layer.  The
resulting `n` is hierarchy data; no dimension-only estimate is asserted.
-/

universe u

variable {delta : NNReal} {gapEpsilon : Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## The generic refined-card bound and the exact identity value -/

/-- For every coherent cover, parent surjectivity bounds the lower-end
active coarse set of an adjacent interval by the original refined source
set.  This observation is stronger than the identity-cover specialization
below. -/
theorem adjacentIntervalActiveFineCard_le_refined_card
    (C : CoherentStickyMultiscaleCover fine)
    {depth : Nat} (S : FiniteScaleSequence delta depth) (m : Fin depth) :
    adjacentIntervalActiveFineCard C S m <=
      fine.refinement.refined.card := by
  let Q := C.base.cover (S.tau m) (S.delta_le_tau m)
    ((S.tau_le_theta m).trans (S.theta_le_one m))
  change Q.activeCoarse.card <= fine.refinement.refined.card
  rw [<- Q.activeFine_eq_refined]
  exact StickyScaleCover.activeCoarse_card_le_activeFine_card Q

/-- Every adjacent interval of the identity-radius coherent cover has one
active fine occurrence for every refined source occurrence. -/
theorem identity_adjacentIntervalActiveFineCard_eq
    {depth : Nat} (fine : UniformTubeFamily delta iota)
    (S : FiniteScaleSequence delta depth) (m : Fin depth) :
    adjacentIntervalActiveFineCard
        (identityRadiusCoherentCover fine) S m =
      fine.refinement.refined.card := by
  change (fine.refinement.refined.map
    (Fintype.equivFin iota).toEmbedding).card =
      fine.refinement.refined.card
  exact Finset.card_map _

/-- A refined-card upper bound is automatically a non-large local-card
budget for every scale sequence under the identity cover. -/
theorem identity_nonLargeLocalCardBudget_of_refined_card_le
    {depth n : Nat} (fine : UniformTubeFamily delta iota)
    (S : FiniteScaleSequence delta depth) (gapEpsilon : Real)
    (hcard : fine.refinement.refined.card <= n) :
    NonLargeLocalCardBudget
      (identityRadiusCoherentCover fine) S gapEpsilon n := by
  intro m _not_large
  rw [identity_adjacentIntervalActiveFineCard_eq fine S m]
  exact hcard

/-- The generic refined-card upper bound gives a non-large local-card
budget for an arbitrary coherent cover and scale sequence. -/
theorem nonLargeLocalCardBudget_of_refined_card_le
    (C : CoherentStickyMultiscaleCover fine)
    {depth n : Nat} (S : FiniteScaleSequence delta depth)
    (gapEpsilon : Real)
    (hcard : fine.refinement.refined.card <= n) :
    NonLargeLocalCardBudget C S gapEpsilon n := by
  intro m _not_large
  exact (adjacentIntervalActiveFineCard_le_refined_card C S m).trans hcard

/-! ## The generated seed -/

/-- The same refined-card bound discharges the sole local-card premise of
the fully automatic fixed-`n` endpoint at its exact generated seed. -/
theorem identity_fullyAutomaticFixedLocalCardSeedBudget_of_refined_card_le
    (fine : UniformTubeFamily delta iota)
    (n : Nat) (eta : Nat -> Real) (N : Nat)
    (gap_pos : 0 < gapEpsilon)
    (delta_le : delta <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        n eta N gapEpsilon)
    (hcard : fine.refinement.refined.card <= n) :
    FullyAutomaticFixedLocalCardSeedBudget
      (identityRadiusCoherentCover fine)
      n eta N gap_pos delta_le := by
  exact identity_nonLargeLocalCardBudget_of_refined_card_le fine
    (fullyAutomaticFixedLocalCardSeed n eta N gap_pos delta_le)
    gapEpsilon hcard

/-- The same construction works for every coherent cover; identity is not
needed once an upper bound on the original refined cardinality is known. -/
theorem fullyAutomaticFixedLocalCardSeedBudget_of_refined_card_le
    (C : CoherentStickyMultiscaleCover fine)
    (n : Nat) (eta : Nat -> Real) (N : Nat)
    (gap_pos : 0 < gapEpsilon)
    (delta_le : delta <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        n eta N gapEpsilon)
    (hcard : fine.refinement.refined.card <= n) :
    FullyAutomaticFixedLocalCardSeedBudget
      C n eta N gap_pos delta_le := by
  exact nonLargeLocalCardBudget_of_refined_card_le C
    (fullyAutomaticFixedLocalCardSeed n eta N gap_pos delta_le)
    gapEpsilon hcard

/-! ## Hierarchy branching-product specialization -/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]

/-- The explicit local-card bound furnished by a hierarchy layer: its
active parent count times the honest prefix branching product. -/
def hierarchyIdentitySeedLocalCardBound
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (k : Fin depth) : Nat :=
  hierarchyLayerParentCount (H := H) k *
    H.branchingProduct 0 (k.1 + 1) (by omega)

/-- The branching-product source bound supplies the generated seed budget
for every coherent cover of `H.effectiveFamily 0`. -/
theorem hierarchy_fullyAutomaticFixedLocalCardSeedBudget
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (C : CoherentStickyMultiscaleCover (H.effectiveFamily 0))
    (k : Fin depth) (eta : Nat -> Real) (N : Nat)
    (gap_pos : 0 < gapEpsilon)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        (hierarchyIdentitySeedLocalCardBound H k)
        eta N gapEpsilon) :
    FullyAutomaticFixedLocalCardSeedBudget C
      (hierarchyIdentitySeedLocalCardBound H k)
      eta N gap_pos delta_le := by
  apply fullyAutomaticFixedLocalCardSeedBudget_of_refined_card_le
  change (H.family 0).refinement.refined.card <=
    hierarchyLayerParentCount (H := H) k *
      H.branchingProduct 0 (k.1 + 1) (by omega)
  exact initialFine_card_le_parentCount_mul_branchingProduct
    (H := H) k

/-- The hierarchy branching-product source bound automatically supplies the
generated-seed budget for the identity cover of `H.effectiveFamily 0`.
The bound is explicitly
`hierarchyLayerParentCount H k * H.branchingProduct 0 (k+1)`. -/
theorem hierarchyIdentity_fullyAutomaticFixedLocalCardSeedBudget
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (k : Fin depth) (eta : Nat -> Real) (N : Nat)
    (gap_pos : 0 < gapEpsilon)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        (hierarchyIdentitySeedLocalCardBound H k)
        eta N gapEpsilon) :
    FullyAutomaticFixedLocalCardSeedBudget
      (identityRadiusCoherentCover (H.effectiveFamily 0))
      (hierarchyIdentitySeedLocalCardBound H k)
      eta N gap_pos delta_le := by
  exact hierarchy_fullyAutomaticFixedLocalCardSeedBudget H
    (identityRadiusCoherentCover (H.effectiveFamily 0))
    k eta N gap_pos delta_le

/-- A positive-depth convenience wrapper using the first hierarchy layer. -/
theorem hierarchyZeroIdentity_fullyAutomaticFixedLocalCardSeedBudget
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth) (eta : Nat -> Real) (N : Nat)
    (gap_pos : 0 < gapEpsilon)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        (hierarchyIdentitySeedLocalCardBound H ⟨0, hdepth⟩)
        eta N gapEpsilon) :
    FullyAutomaticFixedLocalCardSeedBudget
      (identityRadiusCoherentCover (H.effectiveFamily 0))
      (hierarchyIdentitySeedLocalCardBound H ⟨0, hdepth⟩)
      eta N gap_pos delta_le := by
  exact hierarchyIdentity_fullyAutomaticFixedLocalCardSeedBudget
    H ⟨0, hdepth⟩ eta N gap_pos delta_le

#print axioms adjacentIntervalActiveFineCard_le_refined_card
#print axioms identity_adjacentIntervalActiveFineCard_eq
#print axioms nonLargeLocalCardBudget_of_refined_card_le
#print axioms identity_nonLargeLocalCardBudget_of_refined_card_le
#print axioms fullyAutomaticFixedLocalCardSeedBudget_of_refined_card_le
#print axioms identity_fullyAutomaticFixedLocalCardSeedBudget_of_refined_card_le
#print axioms hierarchy_fullyAutomaticFixedLocalCardSeedBudget
#print axioms hierarchyIdentity_fullyAutomaticFixedLocalCardSeedBudget
#print axioms hierarchyZeroIdentity_fullyAutomaticFixedLocalCardSeedBudget

end
end FamilyStickyScaleChainIdentitySeedLocalCardBudgetV2
