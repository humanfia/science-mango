import Family8Grounding.Family8NormalizedLongCoreTauActiveCFMaxTransportV1

/-!
# Pointwise normalized-CF transport for the canonical tau-active cover

This thin module exposes only the literal-parent `CFAt` equality needed by
the parentwise LongCore chain.  The body-preserving reindexing proof lives in
the already verified V1 transport module; no `CFMax` conclusion is re-exported
from this namespace.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8NormalizedLongCoreTauActiveCFAtTransportV2

open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

/-- Normalized CF at the same literal active parent is unchanged by the
canonical tau-active finite reindexing. -/
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
          W hD.delta_pos hepsilon hepsilonHalf) k :=
  Family8NormalizedLongCoreTauActiveCFMaxTransportV1.canonicalBufferedTauActive_parentNormalizedFiberCFAt_eq_interval
    D hD C S W hepsilon hepsilonHalf k

#print axioms
  canonicalBufferedTauActive_parentNormalizedFiberCFAt_eq_interval

end
end Family8NormalizedLongCoreTauActiveCFAtTransportV2
