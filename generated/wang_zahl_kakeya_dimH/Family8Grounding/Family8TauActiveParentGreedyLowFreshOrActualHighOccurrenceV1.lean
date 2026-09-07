import Family8Grounding.Family8GreedyLowFreshParameterOrActualHighOccurrenceV1
import Family8Grounding.Family8TauActiveParentActualDatumAdmissibilityV1
import Mathlib.Tactic

/-!
# Literal tau-active parent greedy low/high connector

The canonical tau geometry makes the literal active-parent datum admissible.
This file feeds that exact datum into the honest greedy low/high assembly.  No
datum equality, reindexing map, or selected-family transport is exposed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8TauActiveParentGreedyLowFreshOrActualHighOccurrenceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighPrefixActualOccurrenceV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1
open Family8GreedyLowFreshParameterOrActualHighOccurrenceV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8TauActiveParentActualDatumAdmissibilityV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth N : Nat} {epsilonLong : Real} {etaLong : Nat -> Real}

/-- On the literal `tauScaleCover`, the greedy split either gives a fresh
Katz--Tao parameter bound for the original tau-parent datum or returns the
same actual high-occurrence prefix.  Source-scale positivity is the weakest
extra input needed to construct parent admissibility. -/
theorem exists_tauActiveParent_fresh_katzTaoParameter_bound_or_actualHighOccurrencePrefix
    {betaKT epsilonKT etaKT : Real} {delta0 : NNReal}
    (hKTP : KatzTaoAtParameters betaKT epsilonKT etaKT delta0)
    (D : ActualTubeDatum delta iota) (hdeltaPos : 0 < delta)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness
      D.family C N epsilonLong etaLong S)
    (A : ENNReal)
    (htauHalf : S.tau W.m <= (2 : NNReal)⁻¹)
    (hgeometry : TauActiveCoarseAdmissibility D C S W)
    (hdelta0 : S.tau W.m / 8 <= delta0)
    (hdensityBudget :
      (((S.tau W.m / 8 : NNReal) : ENNReal) ^ etaKT) *
          (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) <=
        (activeParentActualTubeDatum
          (tauScaleCover D C S W) D.shading).shading.shadingDensity)
    (hcoefficient :
      128 * A <=
        ((S.tau W.m / 8 : NNReal) : ENNReal) ^ (-etaKT)) :
    (exists selectedLow : Finset
          {k // k ∈ (tauScaleCover D C S W).activeCoarse},
        exists selectedFresh : Finset {k // k ∈ selectedLow},
          selectedFresh.Nonempty /\
          selectedFresh.card <= selectedLow.card /\
          (activeParentActualTubeDatum
              (tauScaleCover D C S W) D.shading).shading.averageMultiplicity <=
            (2 * (sourceKatzTaoFreshLoss A : ENNReal)) *
              katzTaoMultiplicityRHS
                (S.tau W.m / 8) selectedFresh.card epsilonKT betaKT) \/
      exists P : GreedyDensityPartition
          (activeParentActualTubeDatum
            (tauScaleCover D C S W) D.shading).family.bodyFamily
          (hullCandidates (Finset.univ : Finset
            {k // k ∈ (tauScaleCover D C S W).activeCoarse}))
          (hullContainer
            (activeParentActualTubeDatum
              (tauScaleCover D C S W) D.shading).family.bodyFamily)
          Finset.univ,
        exists selected : Finset
            {k // k ∈ (tauScaleCover D C S W).activeCoarse},
          (activeParentActualTubeDatum
              (tauScaleCover D C S W) D.shading).shading.shadingMass <=
            2 * (restrictActualTubeDatum
              (activeParentActualTubeDatum
                (tauScaleCover D C S W) D.shading)
              selected).shading.shadingMass /\
          (activeParentActualTubeDatum
              (tauScaleCover D C S W) D.shading).shading.averageMultiplicity <=
            2 * (restrictActualTubeDatum
              (activeParentActualTubeDatum
                (tauScaleCover D C S W) D.shading)
              selected).shading.averageMultiplicity /\
          (restrictActualTubeDatum
            (activeParentActualTubeDatum
              (tauScaleCover D C S W) D.shading)
            selected).IsAdmissible /\
          ∀ k ∈ selected,
            exists q : Fin (blocks
              (activeParentActualTubeDatum
                (tauScaleCover D C S W) D.shading).family.bodyFamily P).length,
              k ∈ (blockAt
                (activeParentActualTubeDatum
                  (tauScaleCover D C S W) D.shading).family.bodyFamily
                P q).fiber /\
              ActualHighConcentrationOccurrence
                (activeParentActualTubeDatum
                  (tauScaleCover D C S W) D.shading)
                P A q := by
  have hparentAdmissible :
      (activeParentActualTubeDatum
        (tauScaleCover D C S W) D.shading).IsAdmissible :=
    activeParentActualTubeDatum_tauScaleCover_isAdmissible
      D hdeltaPos C S W htauHalf hgeometry
  exact exists_fresh_katzTaoParameter_bound_or_actualHighOccurrencePrefix
    hKTP
    (activeParentActualTubeDatum (tauScaleCover D C S W) D.shading)
    hparentAdmissible A hdelta0 hdensityBudget hcoefficient

#print axioms
  exists_tauActiveParent_fresh_katzTaoParameter_bound_or_actualHighOccurrencePrefix

end
end Family8TauActiveParentGreedyLowFreshOrActualHighOccurrenceV1
