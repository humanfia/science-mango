import Family8Grounding.Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
import Family8Grounding.Family8FullRefinementActualDatumV1
import Mathlib.Tactic

/-!
# Full-refinement mass identity for the shading-aware long core

The canonical buffered global cover is active on the refinement set.  On the
full-refinement datum that set is the whole finite index type, so the active
shading mass used by the logarithmic selector is exactly the original total
shading mass.  In particular the selector's nonzero-mass input follows from
the source Frostman lower bound without a callback.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreShadingAwareFullRefinementMassV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FullRefinementActualDatumV1
open Family8AllFrostmanStickyUnionProducerV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma etaF : Real}

/-- On the full-refinement datum, the mass seen by the canonical
shading-aware selector is exactly the original source shading mass. -/
theorem coreShadingAwareActiveShadingMass_fullRefinement
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon ≤ 1 / 2) :
    coreShadingAwareActiveShadingMass
        (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        C Sseq P W hepsilonHalf =
      D.shading.shadingMass := by
  unfold coreShadingAwareActiveShadingMass shadingMassOn
  rw [(canonicalBufferedGlobalCover W hD.delta_pos
      P.epsilon_pos.le hepsilonHalf).activeFine_eq_refined,
    fullRefinementDatum_refined]
  simp only [Shading.shadingMass, fullRefinementDatum_shading_carrier]

/-- The Frostman mass floor supplies the nonzero input required by the
shading-aware logarithmic selector on the full-refinement datum. -/
theorem coreShadingAwareActiveShadingMass_ne_zero_of_fullRefinement
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hF : FrostmanHypotheses D etaF) :
    coreShadingAwareActiveShadingMass
        (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        C Sseq P W hepsilonHalf ≠ 0 := by
  rw [coreShadingAwareActiveShadingMass_fullRefinement
    D hD C Sseq P W hepsilonHalf]
  have hfloor : (delta : ENNReal) ^ (2 * etaF) ≤ D.shading.shadingMass :=
    delta_rpow_two_eta_le_shadingMass_of_frostman D hD hF
  have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
    ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top
  exact ne_of_gt (hpositive.trans_le hfloor)

#print axioms coreShadingAwareActiveShadingMass_fullRefinement
#print axioms coreShadingAwareActiveShadingMass_ne_zero_of_fullRefinement

end

end Family8NormalizedLongCoreShadingAwareFullRefinementMassV2
