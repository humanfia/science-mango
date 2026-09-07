import Family8Grounding.Family8NormalizedLongIntervalSourceUpperV1

/-!
# Actual interval all-scale upper bounds for the normalized long selector

The adjacent `tau_m -> theta_m` normalized upper is not inherited by a
definitional rewrite from the source multiscale cover: after rerooting at
`tau_m` the fine family is the literal chosen `tau_m`-tube family.  This
module gives the quantifier-correct bridge from a genuine all-scale Frostman
certificate on each such rerooted interval cover to the entire adjacent
upper family consumed by the stopping selector.

Thus neither a bare numerical adjacent callback nor an asserted final
trichotomy is needed.  The remaining geometric task is precisely to produce
these interval all-scale certificates (with the required common power loss)
from the hierarchy's actual parent-normalizer and density comparisons.
-/

open scoped ENNReal NNReal

namespace Family8NormalizedLongIntervalAdjacentUpperV1

open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalWitnessV1
open Family8NormalizedLongIntervalSourceUpperV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-- Genuine all-scale Frostman certificates on the literal rerooted interval
covers supply all adjacent `tau_m -> theta_m` normalized upper bounds. -/
theorem adjacentUpper_of_intervalIsFrostmanAtEveryScale
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    {error : ENNReal}
    (hF : forall m : Fin depth,
      StickyMultiscaleCover.IsFrostmanAtEveryScale
        (C.intervalMultiscaleCover (S.tau m) (S.delta_le_tau m)
          ((S.tau_le_theta m).trans (S.theta_le_one m))) error)
    (eta : Nat -> Real) (N : Nat)
    (herror : forall m : Fin depth,
      error <= (((S.theta m / S.tau m : NNReal) : ENNReal) ^
        eta (N - 1))) :
    forall m : Fin depth,
      parentNormalizedFiberCFMax
          (C.intervalScaleCover (S.tau m) (S.theta m)
            (S.delta_le_tau m) (S.tau_le_theta m)
            (S.theta_le_one m)) <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          eta (N - 1)) := by
  intro m
  have htauPos : 0 < S.tau m :=
    hD.delta_pos.trans_le (S.delta_le_tau m)
  have hAt :
      (C.intervalScaleCover (S.tau m) (S.theta m)
        (S.delta_le_tau m) (S.tau_le_theta m)
        (S.theta_le_one m)).IsFrostmanAtScale error := by
    simpa only [intervalMultiscaleCover_cover] using
      hF m (S.theta m) (S.tau_le_theta m) (S.theta_le_one m)
  exact
    ((isFrostmanAtScale_iff_parentNormalizedFiberCFMax_le
      (C.intervalScaleCover (S.tau m) (S.theta m)
        (S.delta_le_tau m) (S.tau_le_theta m)
        (S.theta_le_one m)) htauPos error).mp hAt).trans (herror m)

/-- The normalized stopping trichotomy with both outside upper families
produced from actual all-scale Frostman certificates. -/
theorem allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_allScaleFrostman
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat) (hN : 1 <= N)
    {sourceError adjacentError : ENNReal}
    (hFsource : C.base.IsFrostmanAtEveryScale sourceError)
    (hsourceError : forall m : Fin depth,
      sourceError <= (((S.tau m / delta : NNReal) : ENNReal) ^
        eta (N - 1)))
    (hFadjacent : forall m : Fin depth,
      StickyMultiscaleCover.IsFrostmanAtEveryScale
        (C.intervalMultiscaleCover (S.tau m) (S.delta_le_tau m)
          ((S.tau_le_theta m).trans (S.theta_le_one m))) adjacentError)
    (hadjacentError : forall m : Fin depth,
      adjacentError <= (((S.theta m / S.tau m : NNReal) : ENNReal) ^
        eta (N - 1))) :
    ((S.AllStepsLarge epsilon ∨
        Nonempty
          (NormalizedLongIntervalWitness D.family C N epsilon eta S)) ∨
      Nonempty
        (FirstActualNormalizedCrossingWitness
          D hD C S epsilon hepsilon eta N)) := by
  exact
    allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_sourceAllScaleFrostman
      D hD C S epsilon hepsilon eta N hN hFsource hsourceError
        (adjacentUpper_of_intervalIsFrostmanAtEveryScale
          D hD C S hFadjacent eta N hadjacentError)

#print axioms adjacentUpper_of_intervalIsFrostmanAtEveryScale
#print axioms
  allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_allScaleFrostman

end

end Family8NormalizedLongIntervalAdjacentUpperV1
