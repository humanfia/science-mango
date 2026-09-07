import Family8Grounding.Family8NormalizedFirstCrossingFullRefinementAssemblyV1

/-!
# Actual all-scale source upper bound for the normalized long selector

The normalized long witness asks for an upper bound on each literal
source-to-`tau_m` cover and on each adjacent `tau_m`-to-`theta_m` cover.  The
first family of bounds is not an additional geometric input: it follows
directly from the actual all-scale Frostman certificate of the coherent base
cover and the parameter power comparison.

This file removes that source-side premise from the stopping trichotomy.  It
deliberately leaves the adjacent relative-cover bound visible; deriving that
bound is the genuine interval-local Frostman step and does not follow by a
definitional rewrite from the global source cover.
-/

open scoped ENNReal NNReal

namespace Family8NormalizedLongIntervalSourceUpperV1

open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalWitnessV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-- The genuine all-scale Frostman certificate supplies every normalized
source-to-`tau_m` upper bound once its common error is below the requested
stage power. -/
theorem sourceUpper_of_isFrostmanAtEveryScale
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    {error : ENNReal} (hF : C.base.IsFrostmanAtEveryScale error)
    (eta : Nat -> Real) (N : Nat)
    (herror : forall m : Fin depth,
      error <= (((S.tau m / delta : NNReal) : ENNReal) ^ eta (N - 1))) :
    forall m : Fin depth,
      parentNormalizedFiberCFMax
          (C.base.cover (S.tau m) (S.delta_le_tau m)
            ((S.tau_le_theta m).trans (S.theta_le_one m))) <=
        (((S.tau m / delta : NNReal) : ENNReal) ^ eta (N - 1)) := by
  intro m
  exact
    (actualDatum_sourceToTau_parentNormalizedFiberCFMax_le
      D hD C S hF m).trans (herror m)

/-- The normalized stopping trichotomy with the source upper family produced
from actual all-scale Frostman data.  Only the relative adjacent-cover upper
family remains as an explicit geometric input. -/
theorem allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_sourceAllScaleFrostman
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat) (hN : 1 <= N)
    {error : ENNReal} (hF : C.base.IsFrostmanAtEveryScale error)
    (herror : forall m : Fin depth,
      error <= (((S.tau m / delta : NNReal) : ENNReal) ^ eta (N - 1)))
    (hadjacent : forall m : Fin depth,
      parentNormalizedFiberCFMax
          (C.intervalScaleCover (S.tau m) (S.theta m)
            (S.delta_le_tau m) (S.tau_le_theta m)
            (S.theta_le_one m)) <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (N - 1))) :
    ((S.AllStepsLarge epsilon ∨
        Nonempty
          (NormalizedLongIntervalWitness D.family C N epsilon eta S)) ∨
      Nonempty
        (FirstActualNormalizedCrossingWitness
          D hD C S epsilon hepsilon eta N)) := by
  exact allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness
    D hD C S epsilon hepsilon eta N hN
      (sourceUpper_of_isFrostmanAtEveryScale
        D hD C S hF eta N herror)
      hadjacent

#print axioms sourceUpper_of_isFrostmanAtEveryScale
#print axioms
  allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_sourceAllScaleFrostman

end

end Family8NormalizedLongIntervalSourceUpperV1
