import Family8Grounding.Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
import Family8Grounding.Family8NormalizedCrossingSourceTauShadingV2
import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import Mathlib.Tactic

/-!
# Basic tau-active transports on the normalized long core, V2

These are the three structural transports needed before constructing the
bounded `tau -> b` assembly: nonzero restricted mass, the active-fine average
identity, and native Katz--Tao inheritance.  They read no outside upper field
of an identified witness.  V1 omitted the restrict-to-universe namespace and
is not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8NormalizedLongCoreTauActiveBasicTransportsV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Nonzero mass on the source-to-`tau` active restriction survives the
literal parent aggregation and then the full active restriction of the
`tau -> b` cover. -/
theorem canonicalBufferedTauActiveCover_restrictedMass_ne_zero
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hsourceTau :
      (IndexedShadingRefinement.restrictTo D.shading
        (tauScaleCover D C S W).activeFine).shading.shadingMass ≠ 0) :
    (IndexedShadingRefinement.restrictTo
      (tauActiveCoarseDatum D C S W).shading
      (canonicalBufferedTauActiveCover
        D hD C S W P.epsilon_pos.le hepsilonHalf).activeFine).shading.shadingMass ≠
        0 := by
  rw [canonicalBufferedTauActiveCover_activeFine,
    restrictTo_univ_shadingMass]
  exact parentAggregatedShading_shadingMass_ne_zero_of_restrictTo
    (tauScaleCover D C S W) D.shading hsourceTau

/-- Since the core-native `tau -> b` cover has every tau parent active, its
active-fine shading has exactly the tau-parent average multiplicity. -/
theorem canonicalBufferedTauActiveCover_activeFine_averageMultiplicity
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2) :
    let U := canonicalBufferedTauActiveCover
      D hD C S W P.epsilon_pos.le hepsilonHalf
    (activeFineShading U
      (tauActiveCoarseDatum D C S W).shading).averageMultiplicity =
      (tauActiveCoarseDatum D C S W).shading.averageMultiplicity := by
  dsimp only
  unfold Shading.averageMultiplicity
  rw [Family8AllFrostmanStickyUnionProducerV1.activeFineShading_shadingMass_eq_of_activeFine_eq_univ
      _ _ (canonicalBufferedTauActiveCover_activeFine
        D hD C S W P.epsilon_pos.le hepsilonHalf),
    Family8AllFrostmanStickyUnionProducerV1.activeFineShading_shadedUnion_eq_of_activeFine_eq_univ
      _ _ (canonicalBufferedTauActiveCover_activeFine
        D hD C S W P.epsilon_pos.le hepsilonHalf)]

/-- Native Katz--Tao control restricts from the actual tau cover's active
coarse family to the core-native tau-parent datum definitionally. -/
theorem tauActiveCoarseDatum_isKatzTao_of_tauScaleCover
    (D : ActualTubeDatum delta index)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S)
    {CKT : ENNReal}
    (hKT : (tauScaleCover D C S W).IsKatzTaoAtScale CKT) :
    IsKatzTao CKT
      (tauActiveCoarseDatum D C S W).family.bodyFamily := by
  have hfamily :
      (tauActiveCoarseDatum D C S W).family.bodyFamily =
        (tauScaleCover D C S W).activeCoarseFamily := by
    funext k
    rfl
  apply isKatzTao_iff_concentration_le.mpr
  intro K
  rw [hfamily]
  exact hKT K

#print axioms canonicalBufferedTauActiveCover_restrictedMass_ne_zero
#print axioms canonicalBufferedTauActiveCover_activeFine_averageMultiplicity
#print axioms tauActiveCoarseDatum_isKatzTao_of_tauScaleCover

end
end Family8NormalizedLongCoreTauActiveBasicTransportsV2
