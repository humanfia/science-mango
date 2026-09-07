import Family8Grounding.Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
import Family8Grounding.Family8ParentInjectiveAggregatedAverageIdentityV2
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictedParentTransportV2
import Mathlib.Tactic

/-!
# Singleton fibres on the endpoint identity-core tau-active cover, V4

V1 used dependent rewriting across separately elaborated interval proofs; V2
omitted the datum namespace.  Neither failed draft is imported.  This successor
instead proves injectivity of the literal parent
map and then applies that injectivity directly to each literal fibre.  The
active-fine and active-coarse reindexings therefore introduce no cardinality
loss.  No Katz--Tao or Frostman hypothesis is used.
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace Family8IdentityCoreTauActiveSingletonFiberV4

open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
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
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

/-- The literal interval parent of an identity coherent cover is the same
finite index. -/
@[simp] theorem identityCore_canonicalBufferedIntervalCover_parent
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family
      (identityRadiusCoherentCover D.family) N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (k : Fin (Fintype.card index)) :
    (canonicalBufferedIntervalCover
      W hD.delta_pos hepsilon hepsilonHalf).parent k = k := by
  rfl

/-- The identity-core interval parent is injective. -/
theorem identityCore_canonicalBufferedIntervalCover_parent_injective
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family
      (identityRadiusCoherentCover D.family) N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2) :
    Function.Injective
      (canonicalBufferedIntervalCover
        W hD.delta_pos hepsilon hepsilonHalf).parent := by
  intro i j hij
  change i = j at hij
  exact hij

/-- Inserting the active-tau membership proof preserves parent injectivity. -/
theorem identityCore_canonicalBufferedTauActiveCover_parent_injective
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family
      (identityRadiusCoherentCover D.family) N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2) :
    let U0 := canonicalBufferedTauActiveCover D hD
      (identityRadiusCoherentCover D.family) S W hepsilon hepsilonHalf
    Set.InjOn U0.parent (U0.activeFine : Set _) := by
  dsimp only
  let I := canonicalBufferedIntervalCover
    W hD.delta_pos hepsilon hepsilonHalf
  have hI :
      Function.Injective I.parent := by
    simpa only [I] using
      identityCore_canonicalBufferedIntervalCover_parent_injective
        D hD S W hepsilon hepsilonHalf
  intro i _hi j _hj hij
  apply Subtype.ext
  apply hI
  exact hij

/-- The final active-coarse Fin reindexing also preserves parent injectivity. -/
theorem identityCore_canonicalBufferedTauActiveRestricted_parent_injective
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family
      (identityRadiusCoherentCover D.family) N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2) :
    let U0 := canonicalBufferedTauActiveCover D hD
      (identityRadiusCoherentCover D.family) S W hepsilon hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    Set.InjOn U.parent (U.activeFine : Set _) := by
  dsimp only
  let U0 := canonicalBufferedTauActiveCover D hD
    (identityRadiusCoherentCover D.family) S W hepsilon hepsilonHalf
  let U := activeFineRestrictedScaleCover U0
  have hU0 :
      Set.InjOn U0.parent (U0.activeFine : Set _) := by
    simpa only [U0] using
      identityCore_canonicalBufferedTauActiveCover_parent_injective
        D hD S W hepsilon hepsilonHalf
  intro i _hi j _hj hij
  apply Subtype.ext
  apply hU0 i.2 j.2
  have hp := congrArg (restrictedCoarseEquivActive U0) hij
  rw [restrictedCoarseEquivActive_parent,
    restrictedCoarseEquivActive_parent] at hp
  exact congrArg Subtype.val hp

/-- Every literal fibre of the tau-active cover has cardinality at most one. -/
theorem identityCore_canonicalBufferedTauActiveCover_fiber_card_le_one
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family
      (identityRadiusCoherentCover D.family) N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (q : Fin
      (canonicalBufferedTauActiveCover D hD
        (identityRadiusCoherentCover D.family) S W
          hepsilon hepsilonHalf).coarseCard) :
    Fintype.card {i // i ∈
      (canonicalBufferedTauActiveCover D hD
        (identityRadiusCoherentCover D.family) S W
          hepsilon hepsilonHalf).fiber q} <= 1 := by
  classical
  let U0 := canonicalBufferedTauActiveCover D hD
    (identityRadiusCoherentCover D.family) S W hepsilon hepsilonHalf
  change Fintype.card {i // i ∈ U0.fiber q} <= 1
  rw [Fintype.card_coe]
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hiData := (U0.mem_fiber i q).mp hi
  have hjData := (U0.mem_fiber j q).mp hj
  exact
    (identityCore_canonicalBufferedTauActiveCover_parent_injective
      D hD S W hepsilon hepsilonHalf)
      hiData.1 hjData.1 (hiData.2.trans hjData.2.symm)

/-- Every active literal tau-active fibre is exactly a singleton. -/
theorem identityCore_canonicalBufferedTauActiveCover_active_fiber_card_eq_one
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family
      (identityRadiusCoherentCover D.family) N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (q : {q // q ∈
      (canonicalBufferedTauActiveCover D hD
        (identityRadiusCoherentCover D.family) S W
          hepsilon hepsilonHalf).activeCoarse}) :
    Fintype.card {i // i ∈
      (canonicalBufferedTauActiveCover D hD
        (identityRadiusCoherentCover D.family) S W
          hepsilon hepsilonHalf).fiber q.1} = 1 := by
  classical
  let U0 := canonicalBufferedTauActiveCover D hD
    (identityRadiusCoherentCover D.family) S W hepsilon hepsilonHalf
  change Fintype.card {i // i ∈ U0.fiber q.1} = 1
  rw [Fintype.card_coe]
  apply Nat.le_antisymm
  · simpa only [Fintype.card_coe] using
      identityCore_canonicalBufferedTauActiveCover_fiber_card_le_one
        D hD S W hepsilon hepsilonHalf q.1
  · obtain ⟨i, hi, hparent⟩ := U0.parent_surjective q.1 q.2
    exact Finset.one_le_card.mpr
      ⟨i, (U0.mem_fiber i q.1).mpr ⟨hi, hparent⟩⟩

/-- Every literal fibre after the active-coarse Fin reindexing has
cardinality at most one. -/
theorem identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family
      (identityRadiusCoherentCover D.family) N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (q : Fin
      (activeFineRestrictedScaleCover
        (canonicalBufferedTauActiveCover D hD
          (identityRadiusCoherentCover D.family) S W
            hepsilon hepsilonHalf)).coarseCard) :
    Fintype.card {i // i ∈
      (activeFineRestrictedScaleCover
        (canonicalBufferedTauActiveCover D hD
          (identityRadiusCoherentCover D.family) S W
            hepsilon hepsilonHalf)).fiber q} <= 1 := by
  classical
  let U0 := canonicalBufferedTauActiveCover D hD
    (identityRadiusCoherentCover D.family) S W hepsilon hepsilonHalf
  let U := activeFineRestrictedScaleCover U0
  change Fintype.card {i // i ∈ U.fiber q} <= 1
  rw [Fintype.card_coe]
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hiData := (U.mem_fiber i q).mp hi
  have hjData := (U.mem_fiber j q).mp hj
  exact
    (identityCore_canonicalBufferedTauActiveRestricted_parent_injective
      D hD S W hepsilon hepsilonHalf)
      hiData.1 hjData.1 (hiData.2.trans hjData.2.symm)

/-- Every active fibre after the final reindexing is exactly a singleton. -/
theorem identityCore_canonicalBufferedTauActiveRestricted_active_fiber_card_eq_one
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family
      (identityRadiusCoherentCover D.family) N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (q : {q // q ∈
      (activeFineRestrictedScaleCover
        (canonicalBufferedTauActiveCover D hD
          (identityRadiusCoherentCover D.family) S W
            hepsilon hepsilonHalf)).activeCoarse}) :
    Fintype.card {i // i ∈
      (activeFineRestrictedScaleCover
        (canonicalBufferedTauActiveCover D hD
          (identityRadiusCoherentCover D.family) S W
            hepsilon hepsilonHalf)).fiber q.1} = 1 := by
  classical
  let U0 := canonicalBufferedTauActiveCover D hD
    (identityRadiusCoherentCover D.family) S W hepsilon hepsilonHalf
  let U := activeFineRestrictedScaleCover U0
  change Fintype.card {i // i ∈ U.fiber q.1} = 1
  rw [Fintype.card_coe]
  apply Nat.le_antisymm
  · simpa only [Fintype.card_coe] using
      identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
        D hD S W hepsilon hepsilonHalf q.1
  · obtain ⟨i, hi, hparent⟩ := U.parent_surjective q.1 q.2
    exact Finset.one_le_card.mpr
      ⟨i, (U.mem_fiber i q.1).mpr ⟨hi, hparent⟩⟩

#print axioms identityCore_canonicalBufferedIntervalCover_parent
#print axioms identityCore_canonicalBufferedIntervalCover_parent_injective
#print axioms identityCore_canonicalBufferedTauActiveCover_parent_injective
#print axioms
  identityCore_canonicalBufferedTauActiveRestricted_parent_injective
#print axioms
  identityCore_canonicalBufferedTauActiveCover_fiber_card_le_one
#print axioms
  identityCore_canonicalBufferedTauActiveCover_active_fiber_card_eq_one
#print axioms
  identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
#print axioms
  identityCore_canonicalBufferedTauActiveRestricted_active_fiber_card_eq_one

end
end Family8IdentityCoreTauActiveSingletonFiberV4
