import Family8Grounding.Family8NormalizedLongIntervalCoreSelectorV1
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

/-!
# Concrete identity-coherent selector for the long-interval consumer core

Once the unused outside-upper fields are removed from the canonical consumer
path, the repository's concrete all-radius identity cover is sufficient for
the finite stopping trichotomy.  This supplies an unconditional coherent
cover at the actual-datum boundary; it does not claim that the identity cover
has paper-strength Definition 2.12 endpoint bounds.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped ENNReal NNReal

namespace Family8IdentityCoherentCoreSelectorV1

open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreSelectorV1
open Family8ParameterLadderV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The explicit identity coherent cover already supports the exact common
core/first-crossing/all-large trichotomy needed by canonical middle-scale
consumers. -/
theorem identity_allLarge_or_normalizedLongIntervalCore_or_firstCrossing
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma) :
    ((S.AllStepsLarge P.epsilon ∨
        Nonempty (NormalizedLongIntervalCoreWitness
          D.family (identityRadiusCoherentCover D.family)
            P.N P.epsilon P.eta S)) ∨
      Nonempty (FirstActualNormalizedCrossingWitness
        D hD (identityRadiusCoherentCover D.family) S
          P.epsilon P.epsilon_pos.le P.eta P.N)) := by
  exact allLarge_or_normalizedLongIntervalCore_or_firstCrossing
    D hD (identityRadiusCoherentCover D.family) S P

/-- Existential form used by orchestration layers which select a coherent
cover before inspecting the finite stopping branch. -/
theorem exists_coherentCover_with_core_stopping_trichotomy
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma) :
    ∃ C : CoherentStickyMultiscaleCover D.family,
      ((S.AllStepsLarge P.epsilon ∨
          Nonempty (NormalizedLongIntervalCoreWitness
            D.family C P.N P.epsilon P.eta S)) ∨
        Nonempty (FirstActualNormalizedCrossingWitness
          D hD C S P.epsilon P.epsilon_pos.le P.eta P.N)) := by
  exact ⟨identityRadiusCoherentCover D.family,
    identity_allLarge_or_normalizedLongIntervalCore_or_firstCrossing
      D hD S P⟩

#print axioms
  identity_allLarge_or_normalizedLongIntervalCore_or_firstCrossing
#print axioms exists_coherentCover_with_core_stopping_trichotomy

end
end Family8IdentityCoherentCoreSelectorV1
