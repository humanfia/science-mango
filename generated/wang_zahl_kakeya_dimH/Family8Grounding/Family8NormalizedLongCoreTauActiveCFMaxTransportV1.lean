import Family8Grounding.Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
import Family8Grounding.Family8StickySelectedParentGreedyBlockFrostmanV3

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8NormalizedLongCoreTauActiveCFMaxTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

/-!
# Normalized fibre constants under the canonical tau-active reindexing

The core-native tau-active cover restricts the interval cover's active fine
indices to their attached subtype.  It does not change any tube, parent, or
active coarse body.  This file records the literal fibre equivalence and uses
body-preserving finite-family invariance to transport both `C_F` at one parent
and its finite maximum.  No arbitrary-cover compatibility is inferred.
-/

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

/-- The tau-active fibre and the original interval fibre have the same
indices, with only the active-fine subtype tag inserted or removed. -/
noncomputable def canonicalBufferedTauActiveFiberEquiv
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (k : Fin (canonicalBufferedIntervalCover
      W hD.delta_pos hepsilon hepsilonHalf).coarseCard) :
    {j // j ∈ (canonicalBufferedTauActiveCover
      D hD C S W hepsilon hepsilonHalf).fiber k} ≃
      {i // i ∈ (canonicalBufferedIntervalCover
        W hD.delta_pos hepsilon hepsilonHalf).fiber k} := by
  classical
  let I := canonicalBufferedIntervalCover
    W hD.delta_pos hepsilon hepsilonHalf
  let U := canonicalBufferedTauActiveCover
    D hD C S W hepsilon hepsilonHalf
  change {j // j ∈ U.fiber k} ≃ {i // i ∈ I.fiber k}
  refine
    { toFun := fun j => ⟨j.1.1, ?_⟩
      invFun := fun i => ⟨⟨i.1, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hj := (U.mem_fiber j.1 k).1 j.2
    apply (I.mem_fiber j.1.1 k).2
    constructor
    · exact j.1.2
    · exact hj.2
  · exact ((I.mem_fiber i.1 k).1 i.2).1
  · apply (U.mem_fiber ⟨i.1, ((I.mem_fiber i.1 k).1 i.2).1⟩ k).2
    exact ⟨Finset.mem_univ _, ((I.mem_fiber i.1 k).1 i.2).2⟩
  · intro j
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro i
    apply Subtype.ext
    rfl

/-- The fibre bodies are pointwise unchanged by the explicit equivalence. -/
@[simp]
theorem canonicalBufferedTauActiveFiberEquiv_body
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (k : Fin (canonicalBufferedIntervalCover
      W hD.delta_pos hepsilon hepsilonHalf).coarseCard)
    (j : {j // j ∈ (canonicalBufferedTauActiveCover
      D hD C S W hepsilon hepsilonHalf).fiber k}) :
    (canonicalBufferedTauActiveCover
        D hD C S W hepsilon hepsilonHalf).fiberFamily k j =
      (canonicalBufferedIntervalCover
        W hD.delta_pos hepsilon hepsilonHalf).fiberFamily k
          (canonicalBufferedTauActiveFiberEquiv
            D hD C S W hepsilon hepsilonHalf k j) := by
  rfl

/-- The normalized Frostman constant at each literal active parent is
invariant under the tau-active finite reindexing. -/
theorem canonicalBufferedTauActive_parentNormalizedFiberCFAt_eq_interval
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (k : {k // k ∈ (canonicalBufferedIntervalCover
      W hD.delta_pos hepsilon hepsilonHalf).activeCoarse}) :
    parentNormalizedFiberCFAt
        (canonicalBufferedTauActiveCover
          D hD C S W hepsilon hepsilonHalf) k =
      parentNormalizedFiberCFAt
        (canonicalBufferedIntervalCover
          W hD.delta_pos hepsilon hepsilonHalf) k := by
  unfold parentNormalizedFiberCFAt
  exact canonicalFrostmanConstant_eq_of_bodyPreservingEquiv
    (e := canonicalBufferedTauActiveFiberEquiv
      D hD C S W hepsilon hepsilonHalf k.1)
    (F := (canonicalBufferedTauActiveCover
      D hD C S W hepsilon hepsilonHalf).fiberFamily k.1)
    (G := (canonicalBufferedIntervalCover
      W hD.delta_pos hepsilon hepsilonHalf).fiberFamily k.1)
    (hbody := canonicalBufferedTauActiveFiberEquiv_body
      D hD C S W hepsilon hepsilonHalf k.1)
    (K := (canonicalBufferedIntervalCover
      W hD.delta_pos hepsilon hepsilonHalf).activeCoarseFamily k)

/-- Consequently the finite worst-parent normalized constant is exactly the
same scalar on the interval and tau-active assembly covers. -/
theorem canonicalBufferedTauActive_parentNormalizedFiberCFMax_eq_interval
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2) :
    parentNormalizedFiberCFMax
        (canonicalBufferedTauActiveCover
          D hD C S W hepsilon hepsilonHalf) =
      parentNormalizedFiberCFMax
        (canonicalBufferedIntervalCover
          W hD.delta_pos hepsilon hepsilonHalf) := by
  unfold parentNormalizedFiberCFMax
  apply le_antisymm
  · apply iSup_le
    intro k
    rw [canonicalBufferedTauActive_parentNormalizedFiberCFAt_eq_interval
      D hD C S W hepsilon hepsilonHalf k]
    exact le_iSup _ k
  · apply iSup_le
    intro k
    rw [← canonicalBufferedTauActive_parentNormalizedFiberCFAt_eq_interval
      D hD C S W hepsilon hepsilonHalf k]
    exact le_iSup _ k

#print axioms canonicalBufferedTauActiveFiberEquiv
#print axioms canonicalBufferedTauActiveFiberEquiv_body
#print axioms
  canonicalBufferedTauActive_parentNormalizedFiberCFAt_eq_interval
#print axioms
  canonicalBufferedTauActive_parentNormalizedFiberCFMax_eq_interval

end
end Family8NormalizedLongCoreTauActiveCFMaxTransportV1
