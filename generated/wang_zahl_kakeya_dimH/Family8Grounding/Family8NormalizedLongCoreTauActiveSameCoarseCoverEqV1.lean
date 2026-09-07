import Family8Grounding.Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
import Family8Grounding.Family8StickyScaleCoverActiveFineSameCoarseCoverV1

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8NormalizedLongCoreTauActiveSameCoarseCoverEqV1

open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8StickyScaleCoverActiveFineSameCoarseCoverV1.StickyScaleCover

noncomputable section

/-! # Literal identification of the core tau-active cover -/

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

/-- The core-native cover is exactly the generic same-coarse active-fine
reindexing of its interval cover. -/
theorem canonicalBufferedTauActiveCover_eq_activeFineSameCoarseCover
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2) :
    canonicalBufferedTauActiveCover
        D hD C S W hepsilon hepsilonHalf =
      activeFineSameCoarseCover
        (canonicalBufferedIntervalCover
          W hD.delta_pos hepsilon hepsilonHalf) := by
  rfl

#print axioms
  canonicalBufferedTauActiveCover_eq_activeFineSameCoarseCover

end
end Family8NormalizedLongCoreTauActiveSameCoarseCoverEqV1
