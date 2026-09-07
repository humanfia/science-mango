import Family8Grounding.Family8NormalizedLongIntervalCUniformAdjacentUpperV2
import Family8Grounding.Family8Def212RescaledCWASourceFrostmanV1

/-!
# Exact Definition 2.12 closes both normalized interval upper families

The same exact-scale package supplies the two formerly independent sides:
rescaled fibre CWA gives the source all-scale Frostman bound, while doubled
parent partitioning and C-uniformity give every adjacent interval bound.
Only the explicit comparisons of the resulting fixed constants with the
chosen scale powers remain numerical hypotheses.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8NormalizedLongIntervalExactDef212ClosureV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212RescaledCWASourceFrostmanV1
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalCUniformAdjacentUpperV2
open Family8NormalizedLongIntervalWitnessV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-- The fixed source Frostman error produced from the rescaled fibre CWA in
an exact Definition 2.12 hierarchy. -/
def def212SourceFrostmanError (K : NNReal) : ENNReal :=
  (K : ENNReal) * 16 * volume (unitBallBody : Set Space)

/-- Exact Definition 2.12 data closes the structural and analytic seams of
the normalized long-interval stopping trichotomy. -/
theorem allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_exactDef212
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (N : Nat) (hN : 1 ≤ N)
    {K : NNReal}
    (H : ExactScaleDef212Inputs C.base K)
    (hsourceError : ∀ m : Fin depth,
      def212SourceFrostmanError K ≤
        (((S.tau m / delta : NNReal) : ENNReal) ^
          eta (N - 1)))
    (htauHalf : ∀ m : Fin depth, S.tau m ≤ (2 : NNReal)⁻¹)
    (hadjacentError : ∀ m : Fin depth,
      def212SourceFrostmanError K *
          ((16 * (K : ENNReal)) * 16) ≤
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          eta (N - 1))) :
    ((S.AllStepsLarge epsilon ∨
        Nonempty (NormalizedLongIntervalWitness
          D.family C N epsilon eta S)) ∨
      Nonempty (FirstActualNormalizedCrossingWitness
        D hD C S epsilon hepsilon eta N)) := by
  have hFsource :
      C.base.IsFrostmanAtEveryScale
        (def212SourceFrostmanError K) := by
    simpa only [def212SourceFrostmanError] using
      (Family8Def212RescaledCWASourceFrostmanV1.ExactScaleDef212Inputs.isFrostmanAtEveryScale
        H hD.delta_le_half)
  exact
    allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_exactScaleDef212Inputs
      D hD C S epsilon hepsilon eta N hN H hFsource
      hsourceError htauHalf hadjacentError

#print axioms def212SourceFrostmanError
#print axioms
  allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_exactDef212

end
end Family8NormalizedLongIntervalExactDef212ClosureV3
