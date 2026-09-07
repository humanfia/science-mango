import Family8Grounding.Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1

/-!
# Retain the literal core-high greedy prefix

This module exposes the first-low dichotomy before any occurrence, dyadic
label, or container is selected on the high branch.  The high payload keeps
the greedy partition and prefix selected by the original dichotomy together
with its literal factor-two source-mass certificate and pointwise occurrence
cover.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8TauActiveParentGreedyRetainedHighPrefixSplitV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The unrefined high-prefix datum returned by the core first-low split.
It retains exactly the original partition, selected prefix, factor-two mass
bound, and pointwise high-occurrence cover.  In particular it stores no
chosen occurrence or dyadic label. -/
abbrev CoreHighPrefixWithFirstHitMass
    (D : ActualTubeDatum delta index) (A : ENNReal) : Prop :=
  exists P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ,
    exists selected : Finset index,
      D.shading.shadingMass <= 2 *
          (restrictActualTubeDatum D selected).shading.shadingMass /\
        forall i, i ∈ selected ->
          exists q : Fin (blocks D.family.bodyFamily P).length,
            i ∈ (blockAt D.family.bodyFamily P q).fiber /\
              CoreHighConcentrationOccurrence D P A q

/-- The core first-low split with its high branch packaged before every
subsequent occurrence or label selection. -/
theorem exists_factorTwo_lowKatzTaoRestriction_or_coreHighPrefixWithFirstHitMass
    (D : ActualTubeDatum delta index) (A : ENNReal) :
    (exists selected : Finset index,
        D.shading.shadingMass <= 2 *
          (restrictActualTubeDatum D selected).shading.shadingMass /\
        IsKatzTao A
          (restrictActualTubeDatum D selected).family.bodyFamily) \/
      CoreHighPrefixWithFirstHitMass D A := by
  exact
    exists_factorTwo_lowKatzTaoRestriction_or_coreHighOccurrencePrefix D A

end
end Family8TauActiveParentGreedyRetainedHighPrefixSplitV1
