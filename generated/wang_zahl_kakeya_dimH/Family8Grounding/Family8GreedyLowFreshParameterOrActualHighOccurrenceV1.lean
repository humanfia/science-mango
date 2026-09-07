import Family8Grounding.Family8FactorTwoLowKatzTaoFreshParameterEndpointV1
import Mathlib.Tactic

/-!
# Greedy low fresh-parameter bound or actual high occurrences

This is the shortest public assembly of the honest greedy dichotomy with the
factor-two low Katz--Tao endpoint.  In the low branch all restriction
certificates remain internal and the original datum receives the fresh
parameter multiplicity bound directly.  The high branch is returned without
changing its partition, selected set, or actual occurrence certificates.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8GreedyLowFreshParameterOrActualHighOccurrenceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8SharpKatzTaoOrGreedyHighConcentrationV1
open Family8GreedyHighPrefixActualOccurrenceV1
open Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1
open Family8FactorTwoLowKatzTaoFreshParameterEndpointV1

noncomputable section

/-- The honest greedy split with the low restriction certificates discharged
internally.  The low conclusion is already a bound for the original datum,
indexed by a nonempty fresh selected family.  The high conclusion is exactly
the actual-occurrence prefix produced by the greedy dichotomy. -/
theorem exists_fresh_katzTaoParameter_bound_or_actualHighOccurrencePrefix
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (hKTP : KatzTaoAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (A : ENNReal)
    (hdelta0 : delta / 8 <= delta0)
    (hdensityBudget :
      (((delta / 8 : NNReal) : ENNReal) ^ eta) *
          (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) <=
        D.shading.shadingDensity)
    (hcoefficient :
      128 * A <= ((delta / 8 : NNReal) : ENNReal) ^ (-eta)) :
    (exists selectedLow : Finset iota,
        exists selectedFresh : Finset {i // i ∈ selectedLow},
          selectedFresh.Nonempty /\
          selectedFresh.card <= selectedLow.card /\
          D.shading.averageMultiplicity <=
            (2 * (sourceKatzTaoFreshLoss A : ENNReal)) *
              katzTaoMultiplicityRHS
                (delta / 8) selectedFresh.card epsilon beta) \/
      exists P : GreedyDensityPartition D.family.bodyFamily
          (hullCandidates (Finset.univ : Finset iota))
          (hullContainer D.family.bodyFamily) Finset.univ,
        exists selected : Finset iota,
          D.shading.shadingMass <= 2 *
            (restrictActualTubeDatum D selected).shading.shadingMass /\
          D.shading.averageMultiplicity <= 2 *
            (restrictActualTubeDatum D selected).shading.averageMultiplicity /\
          (restrictActualTubeDatum D selected).IsAdmissible /\
          ∀ i ∈ selected,
            exists q : Fin (blocks D.family.bodyFamily P).length,
              i ∈ (blockAt D.family.bodyFamily P q).fiber /\
              ActualHighConcentrationOccurrence D P A q := by
  rcases exists_factorTwo_lowKatzTaoRestriction_or_actualHighOccurrencePrefix
      D hD A with hlow | hhigh
  · obtain ⟨selectedLow, hmass, _haverage, hDlow, hKTlow⟩ := hlow
    left
    refine ⟨selectedLow, ?_⟩
    exact exists_fresh_katzTaoParameter_bound_of_factorTwo_lowRestriction
      hKTP D selectedLow hmass hDlow hKTlow hdelta0 hdensityBudget
        hcoefficient
  · exact Or.inr hhigh

#print axioms
  exists_fresh_katzTaoParameter_bound_or_actualHighOccurrencePrefix

end
end Family8GreedyLowFreshParameterOrActualHighOccurrenceV1
