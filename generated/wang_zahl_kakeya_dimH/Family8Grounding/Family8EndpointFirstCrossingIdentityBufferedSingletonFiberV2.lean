import Family8Grounding.Family8NormalizedFirstCrossingFullRefinementAssemblyV1
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictedParentTransportV2
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
import Mathlib.Tactic

/-!
# Singleton fibres for the endpoint FirstCrossing identity cover

For the canonical identity-radius coherent cover, every interval parent map
is literally the identity.  This remains injective after restricting to the
active fine set and reindexing the active coarse set by `Fin`.  Hence every
fibre used by the endpoint FirstCrossing active-index assembly has cardinality
at most one.  No Katz--Tao or Frostman hypothesis is used.
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace Family8EndpointFirstCrossingIdentityBufferedSingletonFiberV2

open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8StickyActiveRestrictedCoarseKatzTaoV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverActiveFineRestrictedParentTransportV2.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilon : Real} {eta : Nat → Real}

/-- The selected buffered interval parent is literally the identity map. -/
@[simp] theorem endpointFirstCrossing_identityBufferedIntervalCover_parent
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      D hD (identityRadiusCoherentCover D.family)
        S epsilon hepsilon eta N)
    (k : Fin (Fintype.card index)) :
    (bufferedIntervalCover D hD
      (identityRadiusCoherentCover D.family) S epsilon hepsilon
        W.m W.rho W.buffered).parent k = k := by
  rfl

/-- The literal selected interval parent is injective. -/
theorem endpointFirstCrossing_identityBufferedIntervalCover_parent_injective
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      D hD (identityRadiusCoherentCover D.family)
        S epsilon hepsilon eta N) :
    Function.Injective
      (bufferedIntervalCover D hD
        (identityRadiusCoherentCover D.family) S epsilon hepsilon
          W.m W.rho W.buffered).parent := by
  intro i j hij
  change i = j at hij
  exact hij

/-- Restricting the active fine set and reindexing active parents preserves
injectivity of the endpoint identity parent. -/
theorem endpointFirstCrossing_identityActiveRestricted_parent_injective
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      D hD (identityRadiusCoherentCover D.family)
        S epsilon hepsilon eta N) :
    let U0 := bufferedIntervalCover D hD
      (identityRadiusCoherentCover D.family) S epsilon hepsilon
        W.m W.rho W.buffered
    let U := activeFineRestrictedScaleCover U0
    Set.InjOn U.parent (U.activeFine : Set _) := by
  dsimp only
  let U0 := bufferedIntervalCover D hD
    (identityRadiusCoherentCover D.family) S epsilon hepsilon
      W.m W.rho W.buffered
  let U := activeFineRestrictedScaleCover U0
  have hU0 : Function.Injective U0.parent := by
    simpa only [U0] using
      endpointFirstCrossing_identityBufferedIntervalCover_parent_injective
        D hD S epsilon hepsilon eta N W
  intro i _hi j _hj hij
  apply Subtype.ext
  apply hU0
  have hp := congrArg (restrictedCoarseEquivActive U0) hij
  rw [restrictedCoarseEquivActive_parent,
    restrictedCoarseEquivActive_parent] at hp
  exact congrArg Subtype.val hp

/-- Every fibre in the endpoint FirstCrossing active-index cover has
cardinality at most one. -/
theorem endpointFirstCrossing_identityActiveRestricted_fiber_card_le_one
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      D hD (identityRadiusCoherentCover D.family)
        S epsilon hepsilon eta N)
    (q : Fin
      (activeFineRestrictedScaleCover
        (bufferedIntervalCover D hD
          (identityRadiusCoherentCover D.family) S epsilon hepsilon
            W.m W.rho W.buffered)).coarseCard) :
    Fintype.card {i // i ∈
      (activeFineRestrictedScaleCover
        (bufferedIntervalCover D hD
          (identityRadiusCoherentCover D.family) S epsilon hepsilon
            W.m W.rho W.buffered)).fiber q} ≤ 1 := by
  classical
  let U0 := bufferedIntervalCover D hD
    (identityRadiusCoherentCover D.family) S epsilon hepsilon
      W.m W.rho W.buffered
  let U := activeFineRestrictedScaleCover U0
  change Fintype.card {i // i ∈ U.fiber q} ≤ 1
  rw [Fintype.card_coe]
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hiData := (U.mem_fiber i q).mp hi
  have hjData := (U.mem_fiber j q).mp hj
  exact
    (endpointFirstCrossing_identityActiveRestricted_parent_injective
      D hD S epsilon hepsilon eta N W)
      hiData.1 hjData.1 (hiData.2.trans hjData.2.symm)

#print axioms endpointFirstCrossing_identityBufferedIntervalCover_parent
#print axioms endpointFirstCrossing_identityBufferedIntervalCover_parent_injective
#print axioms endpointFirstCrossing_identityActiveRestricted_parent_injective
#print axioms endpointFirstCrossing_identityActiveRestricted_fiber_card_le_one

end
end Family8EndpointFirstCrossingIdentityBufferedSingletonFiberV2
