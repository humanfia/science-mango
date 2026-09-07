import Family8Grounding.Family8IdentifiedDividingWitnessTauActivePowerProductV3
import Family8Grounding.Family8IdentifiedDividingWitnessSourceTauFrozenProductV3
import Family8Grounding.Family8FullRefinementActualDatumV1
import Family8Grounding.Family8KatzTaoDoubledFiberActiveIndexCapV3
import FamilyStickyGrounding.FamilyStickyKatzTaoParentAggregatedMultiplicityConsumerV1
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8IdentifiedDividingWitnessFirstOuterParentTransportV1

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
open FamilyStickyKatzTaoParentAggregatedMultiplicityConsumerV1
open Family8AllFrostmanStickyUnionProducerV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8KatzTaoDoubledFiberActiveIndexCapV3.StickyScaleCover
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8IdentifiedDividingWitnessActiveLogLossV3.Witness
open Family8IdentifiedDividingWitnessTauActivePowerProductV3.Witness
open Family8NormalizedCrossingSourceTauShadingV2
open Family8IdentifiedDividingWitnessSourceTauFrozenProductV3.Witness
open Family8FullRefinementActualDatumV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-!
# First outer transport on the identified source-to-tau cover

Full refinement makes the active fine set of the literal source-to-`tau`
cover the whole original index type.  Thus the parent-aggregation consumer
transports the original average multiplicity to the actual active `tau`
parent shading with exactly one fibre-cardinality cap.

The final theorem composes this exact transport with the existing
callback-free tau-active frozen product.  It supplies the literal
three-factor decomposition needed by the Section 8 scalar orchestration;
only analytic estimates for the three displayed factors remain.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- On the full-refinement copy, the active fine shading of the genuine
source-to-`tau_m` cover has exactly the original average multiplicity. -/
theorem fullRefinement_sourceTau_activeFine_averageMultiplicity
    (D : ActualTubeDatum delta index)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth) (m : Fin depth) :
    (activeFineShading
      (sourceTauCover (fullRefinementDatum D) C S m)
      (fullRefinementDatum D).shading).averageMultiplicity =
        D.shading.averageMultiplicity := by
  have hactive :
      (sourceTauCover (fullRefinementDatum D) C S m).activeFine =
        Finset.univ := by
    rw [(sourceTauCover (fullRefinementDatum D) C S m).activeFine_eq_refined,
      fullRefinementDatum_refined]
  unfold Shading.averageMultiplicity
  rw [activeFineShading_shadingMass_eq_of_activeFine_eq_univ _ _ hactive,
    activeFineShading_shadedUnion_eq_of_activeFine_eq_univ _ _ hactive]
  rw [fullRefinementDatum_shadingMass, fullRefinementDatum_shadedUnion]

/-- The exact deterministic first-outer transport.  No Katz--Tao estimate is
needed here: any honest uniform parent-fibre cap is retained literally. -/
theorem fullRefinement_averageMultiplicity_le_nsmul_sourceTauParent
    (D : ActualTubeDatum delta index)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth) (m : Fin depth)
    (M : Nat)
    (hM : forall k : {k // k ∈
        (sourceTauCover (fullRefinementDatum D) C S m).activeCoarse},
      ((activeIndexFactorization
        (sourceTauCover (fullRefinementDatum D) C S m)).fiber k).card <= M) :
    D.shading.averageMultiplicity <=
      M • (parentAggregatedShading
        (sourceTauCover (fullRefinementDatum D) C S m)
        (fullRefinementDatum D).shading).averageMultiplicity := by
  rw [← fullRefinement_sourceTau_activeFine_averageMultiplicity D C S m]
  exact activeFineShading_averageMultiplicity_le_nsmul_parent
    (sourceTauCover (fullRefinementDatum D) C S m)
    (fullRefinementDatum D).shading M hM

/-- Source Katz--Tao non-concentration supplies the exact natural fibre cap
consumed by the preceding parent transport. -/
theorem fullRefinement_averageMultiplicity_le_katzTaoCap_mul_sourceTauParent
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth) (m : Fin depth)
    {A : ENNReal} (hAfinite : A ≠ ∞)
    (hKT : IsKatzTao A D.family.bodyFamily) :
    D.shading.averageMultiplicity <=
      (katzTaoDoubledFiberNatCap delta (S.tau m) A : ENNReal) *
        (parentAggregatedShading
          (sourceTauCover (fullRefinementDatum D) C S m)
          (fullRefinementDatum D).shading).averageMultiplicity := by
  have hKTFull :
      IsKatzTao A (fullRefinementDatum D).family.bodyFamily := by
    exact hKT
  have hcap :=
    activeIndexFiber_card_le_katzTaoDoubledFiberNatCap
      (sourceTauCover (fullRefinementDatum D) C S m)
      hD.delta_pos hD.delta_le_half
      (CoherentStickyMultiscaleCover.tau_le_one S m)
      hAfinite hKTFull
  simpa only [nsmul_eq_mul] using
    (fullRefinement_averageMultiplicity_le_nsmul_sourceTauParent
      D C S m (katzTaoDoubledFiberNatCap delta (S.tau m) A) hcap)

/-- Direct specialization of the exact cap to the public
`KatzTaoHypotheses` input. -/
theorem fullRefinement_averageMultiplicity_le_hypothesisCap_mul_sourceTauParent
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth) (m : Fin depth)
    {etaKT : Real} (hKT : KatzTaoHypotheses D etaKT) :
    D.shading.averageMultiplicity <=
      (katzTaoDoubledFiberNatCap delta (S.tau m)
          ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
        (parentAggregatedShading
          (sourceTauCover (fullRefinementDatum D) C S m)
          (fullRefinementDatum D).shading).averageMultiplicity := by
  apply fullRefinement_averageMultiplicity_le_katzTaoCap_mul_sourceTauParent
    D hD C S m
  · exact ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.coe_ne_zero.mpr hD.delta_pos.ne') ENNReal.coe_ne_top
  · exact (maximalConcentration_le_iff_isKatzTao).1 hKT.2

/-- The full-refinement source average is bounded by the literal product of
the exact first fibre cap, the log-loss-weighted frozen coarse average, and
one surviving final-fibre average, all on one tau-active assembly. -/
theorem exists_fullRefinement_tauActive_firstOuter_frozenPowerProduct
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hmass : D.shading.shadingMass ≠ 0)
    {etaKT lossEta : Real}
    (hKT : KatzTaoHypotheses D etaKT)
    (hlossEta : 0 < lossEta)
    (hdelta : delta <=
      Family8ActiveFrozenComparableLogLossAbsorptionV4.activeFrozenComparableLossAbsorptionThreshold lossEta) :
    let E := fullRefinementDatum D
    let U := canonicalBufferedTauActiveCover
      E (fullRefinementDatum_isAdmissible hD) C S W
        P.epsilon_pos.le hepsilonHalf
    let hscale : S.tau W.m <= canonicalBufferedRadius W :=
      tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
    let Y := (tauActiveCoarseDatum E C S W).shading
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 :=
      canonicalBufferedTauActiveCover_restrictedMass_ne_zero
        E (fullRefinementDatum_isAdmissible hD) C S P W hepsilonHalf
          (fullRefinement_sourceTau_activeMass_ne_zero
            D C S W.m hmass)
    exists A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (sourceMassCoarseTubePartition
          (activeFineRestrictedScaleCover U) hscale
          (activeFineRestrictedShading U Y)
          (activeFineRestrictedSourceMass_ne_zero U Y hsource)).asConvexFactorization
        (activeFineRestrictedShading U Y) 1,
      A.loss = frozenComparableLoss {i // i ∈ U.activeFine}
        (Fin U.activeCoarse.card) /\
      exists k : Fin U.activeCoarse.card,
        0 < volume (finalFiberShading A k).shadedUnion /\
        D.shading.averageMultiplicity <=
          (katzTaoDoubledFiberNatCap delta (S.tau W.m)
              ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
            (((4 * (delta : ENNReal) ^ (-lossEta)) *
                A.frozenCoarse.averageMultiplicity) *
              (finalFiberShading A k).averageMultiplicity) := by
  dsimp only
  have hsourceTau :
      (IndexedShadingRefinement.restrictTo
        (fullRefinementDatum D).shading
        (tauScaleCover (fullRefinementDatum D) C S W).activeFine).shading.shadingMass ≠
          0 :=
    fullRefinement_sourceTau_activeMass_ne_zero D C S W.m hmass
  obtain ⟨A, hLoss, k, hFiberVolume, hProduct⟩ :=
    exists_canonicalBuffered_tauActive_frozenPowerProduct
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      C S P W hepsilonHalf hsourceTau hlossEta hdelta
  refine ⟨A, hLoss, k, hFiberVolume, ?_⟩
  have hFirst :=
    fullRefinement_averageMultiplicity_le_hypothesisCap_mul_sourceTauParent
      D hD C S W.m hKT
  calc
    D.shading.averageMultiplicity <=
        (katzTaoDoubledFiberNatCap delta (S.tau W.m)
            ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
          (tauActiveCoarseDatum (fullRefinementDatum D) C S W).shading.averageMultiplicity :=
      hFirst
    _ <=
        (katzTaoDoubledFiberNatCap delta (S.tau W.m)
            ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
          ((4 * (delta : ENNReal) ^ (-lossEta)) *
            (A.frozenCoarse.averageMultiplicity *
              (finalFiberShading A k).averageMultiplicity)) :=
      mul_le_mul' le_rfl hProduct
    _ =
        (katzTaoDoubledFiberNatCap delta (S.tau W.m)
            ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
          (((4 * (delta : ENNReal) ^ (-lossEta)) *
              A.frozenCoarse.averageMultiplicity) *
            (finalFiberShading A k).averageMultiplicity) := by
      ac_rfl

#print axioms fullRefinement_sourceTau_activeFine_averageMultiplicity
#print axioms fullRefinement_averageMultiplicity_le_nsmul_sourceTauParent
#print axioms
  fullRefinement_averageMultiplicity_le_katzTaoCap_mul_sourceTauParent
#print axioms
  fullRefinement_averageMultiplicity_le_hypothesisCap_mul_sourceTauParent
#print axioms exists_fullRefinement_tauActive_firstOuter_frozenPowerProduct

end Witness

end

end Family8IdentifiedDividingWitnessFirstOuterParentTransportV1
