import Family8Grounding.Family8NormalizedCrossingSourceTauActualAverageV2
import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3
import Family8Grounding.Family8FullRefinementActualDatumV1
import Family8Grounding.Family8ParameterLadderV1
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8IdentifiedDividingWitnessSourceTauFrozenProductV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedCrossingSourceTauActualAverageV2
open Family8FullRefinementActualDatumV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
# One identified witness supplies one source-tau frozen product

The normalized-crossing assembly and the identified dividing witness used
different public names for the same two coherent covers.  This module closes
that naming seam.  At the canonical buffered radius of one identified
witness, the source-to-tau parent average is retained on the same actual
refinement whose average is bounded by the product of its frozen coarse and
surviving fibre averages.

This is a structural product statement only.  It does not estimate either
visible factor and does not state a final Frostman bound.
-/

/-- Compose the two scalar retention inequalities without changing any of
the actual data that produced them. -/
theorem sourceAverage_le_fourLoss_mul_outerFiber
    {source refinement outer fiber loss : ENNReal}
    (hSource : source <= loss * refinement)
    (hRefinement : refinement <= 4 * (outer * fiber)) :
    source <= (4 * loss) * (outer * fiber) := by
  calc
    source <= loss * refinement := hSource
    _ <= loss * (4 * (outer * fiber)) := mul_le_mul' le_rfl hRefinement
    _ = (4 * loss) * (outer * fiber) := by ac_rfl

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The source-to-tau cover in the normalized-crossing path is literally the
tau cover attached to the identified witness. -/
theorem sourceTauCover_eq_tauScaleCover
    (D : ActualTubeDatum delta index)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family C P.N P.epsilon P.eta S) :
    sourceTauCover D C S W.m =
      Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness.tauScaleCover
        D C S W := by
  rfl

/-- The buffered interval used by the normalized assembly is the canonical
buffered interval of the same witness. -/
theorem bufferedIntervalCover_eq_canonicalBufferedIntervalCover
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2) :
    bufferedIntervalCover D hD C S P.epsilon P.epsilon_pos.le W.m
        (Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius W)
        (Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius_isBuffered
          W hD.delta_pos P.epsilon_pos.le hepsilonHalf) =
      Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedIntervalCover
        W hD.delta_pos P.epsilon_pos.le hepsilonHalf := by
  rfl

/-- Full refinement metadata makes the actual source-to-tau active mass equal
to the original nonzero shading mass. -/
theorem fullRefinement_sourceTau_activeMass_ne_zero
    (D : ActualTubeDatum delta index)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth) (m : Fin depth)
    (hmass : D.shading.shadingMass ≠ 0) :
    (IndexedShadingRefinement.restrictTo
      (fullRefinementDatum D).shading
      (sourceTauCover (fullRefinementDatum D) C S m).activeFine).shading.shadingMass ≠
        0 := by
  rw [(sourceTauCover (fullRefinementDatum D) C S m).activeFine_eq_refined]
  simpa only [fullRefinementDatum_restricted_shadingMass] using hmass

/-- Canonical-buffered frozen assembly attached to one identified witness.
The witness stage is therefore immediately available as the endpoint stage,
while the two displayed inequalities live on one literal assembly. -/
theorem exists_canonicalBuffered_sourceTau_frozenAssembly
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hsourceTau :
      (IndexedShadingRefinement.restrictTo D.shading
        (sourceTauCover D C S W.m).activeFine).shading.shadingMass ≠ 0) :
    let rho :=
      Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius W
    let hbuffered : S.IsBuffered P.epsilon W.m rho :=
      Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius_isBuffered
        W hD.delta_pos P.epsilon_pos.le hepsilonHalf
    let Y := sourceTauFullShading D C S W.m
    let U := bufferedIntervalCover D hD C S P.epsilon
      P.epsilon_pos.le W.m rho hbuffered
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 :=
      sourceTauFullShading_restrictedMass_ne_zero
        D hD C S P.epsilon P.epsilon_pos.le W.m rho hbuffered hsourceTau
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (sourceMassCoarseTubePartition U
          (actualDatum_tau_le_of_isBuffered
            D hD S P.epsilon_pos.le W.m rho hbuffered) Y hsource).asConvexFactorization
          Y 1,
      A.loss = frozenComparableLoss (bufferedLowerIndex D C S W.m)
        (Fin U.coarseCard) /\
      (parentAggregatedShading (sourceTauCover D C S W.m)
          D.shading).averageMultiplicity <=
        (frozenComparableLoss (bufferedLowerIndex D C S W.m)
          (Fin U.coarseCard) : ENNReal) *
          (actualRefinementShading A).averageMultiplicity /\
      ∃ k : Fin U.coarseCard, k ∈ U.activeCoarse /\
        0 < volume (finalFiberShading A k).shadedUnion /\
        (actualRefinementShading A).averageMultiplicity <=
          4 * (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) := by
  dsimp only
  exact exists_frozenComparableAssembly_with_sourceTau_actualAverage
    D hD C S P.epsilon P.epsilon_pos.le W.m
      (Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius W)
      (Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius_isBuffered
        W hD.delta_pos P.epsilon_pos.le hepsilonHalf)
      1 (by norm_num) hsourceTau

#print axioms sourceAverage_le_fourLoss_mul_outerFiber
#print axioms sourceTauCover_eq_tauScaleCover
#print axioms bufferedIntervalCover_eq_canonicalBufferedIntervalCover
#print axioms fullRefinement_sourceTau_activeMass_ne_zero
#print axioms exists_canonicalBuffered_sourceTau_frozenAssembly

end Witness

end

end Family8IdentifiedDividingWitnessSourceTauFrozenProductV3
