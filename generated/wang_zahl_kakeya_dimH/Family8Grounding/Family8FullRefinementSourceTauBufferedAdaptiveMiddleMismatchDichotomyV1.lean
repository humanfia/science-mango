import Family8Grounding.Family8FullRefinementSourceTauAdaptiveCardWeightedBudgetDichotomyV1
import Family8Grounding.Family8PaperEq45MaxWitnessBufferedAdaptiveCardWeightedThickLossEndpointV1
import Family8Grounding.Family8BufferedEq45Eq46MiddleMismatchAlgebraV1
import Mathlib.Tactic

/-!
# Low-beta source-tau buffered Equation (45)/(46) middle mismatch

In the non-hull-thin branch, the callback-free source-tau budget dichotomy
feeds the literal card-weighted Equation (46) budget into the buffered
same-selected Equation (45) endpoint.  The exact algebraic identity then
rewrites its remainder times inner factor as the Section 8 middle factor
times the sole explicit mismatch coefficient.

This module performs no numerical absorption and assumes no target-valued
scalar comparison.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8FullRefinementSourceTauBufferedAdaptiveMiddleMismatchDichotomyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8BufferedCommonScaleTubePlankV1
open Family8BufferedEq45Eq46MiddleMismatchAlgebraV1
open Family8CardWeightedEq46CoefficientPowerEnvelopeV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8FullRefinementActualDatumV1
open Family8FullRefinementSourceTauAdaptiveCardWeightedBudgetDichotomyV1
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV13
open Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV17
open Family8PaperEq45MaxWitnessBufferedAdaptiveCardWeightedThickLossEndpointV1
open Family8PaperEq45MaxWitnessBufferedCanonicalV1
open Family8PaperEq45MaxWitnessBufferedCanonicalV1.PaperEq45MaxWitnessBufferedInput
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedParentAdaptiveScaleReservePowerLowerV1
open Family8SelectedParentCardWeightedProp66AInnerV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8SelectedParentSourceTauAdaptiveGlobalPowerResidualV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8ThreeScaleFrostmanFactorAlgebraV2
open Family8UniqueOwnerLocalDeltaMaxThickControlV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 30000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat → Real}

/-- Callback-free low-`beta` endpoint nearest to the Section 8 middle
comparison: either an actual occupied bucket is paper hull-thin, or the
actual full-refinement average is bounded by the genuine outer/thick loss,
the sole scalar mismatch, and the literal Section 8 middle count factor. -/
theorem fullRefinement_sourceTau_paperHullThin_or_bufferedOuterThickMismatch_mul_middleFactor
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N
        stoppingEpsilon stoppingEta Sseq)
    (hstoppingEpsilon : 0 < stoppingEpsilon)
    {sigma : NNReal}
    (U : StickyScaleCover
      ((tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).coarse.restrictTo
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarse)
      sigma)
    (Pgreedy : GreedyDensityPartition
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily
      (hullCandidates (Finset.univ : Finset
        (ActiveParentIndex
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W))))
      (hullContainer
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily)
      Finset.univ)
    {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W) Pgreedy)
      (parentAggregatedShading
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
        (fullRefinementDatum D).shading) loss)
    {conflictLoss : ENNReal}
    (Wouter : DoubledParentConflictWeightedSelection U
      (occurrenceMaxOwnerMass U
        (canonicalUpperPartition
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W) U Pgreedy)
        A.refinement.shading Finset.univ) conflictLoss)
    (I : PaperEq45MaxWitnessBufferedInput U
      A.refinement.shading Finset.univ conflictLoss Wouter)
    (r : NNReal) (hr : 0 < r)
    (hsource :
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          (fullRefinementDatum D).shading)
        (greedyParentFactorization
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          Pgreedy).index.fine).shading.shadingMass ≠ 0)
    (KT adaptiveC CKT : ENNReal)
    (hKT : IsKatzTao KT
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily)
    {etaF etaKT lossEta absorbEta epsilon beta : Real}
    {lossExponent coarseKTExponent innerKTExponent
      constantAbsorbExponent : Real}
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT)
    (htauExponent : 0 ≤ lossEta + absorbEta)
    (hloss : (loss : ENNReal) ≤
      (delta : ENNReal) ^ (-lossExponent))
    (hCKTPower : CKT ≤ (delta : ENNReal) ^ (-coarseKTExponent))
    (hKTPower : KT ≤ (delta : ENNReal) ^ (-innerKTExponent))
    (hconstantAbsorbExponent : 0 < constantAbsorbExponent)
    (hfixedSmall : delta ≤
      cardWeightedEq46FixedConstantThreshold constantAbsorbExponent)
    (hFsource : FrostmanHypotheses D etaF)
    (hKTsource : KatzTaoHypotheses D etaKT)
    (hetaF : 0 ≤ etaF) (hepsilon : 0 ≤ epsilon)
    (hbetaStrict : beta < 2 / 3)
    (hetaKT : 0 < etaKT) (hlossEta : 0 < lossEta)
    (habsorbEta : 0 < absorbEta)
    (hlossExponent : 0 ≤ lossExponent)
    (hcoarseKTExponent : 0 ≤ coarseKTExponent)
    (hinnerKTExponent : 0 ≤ innerKTExponent)
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices
        (canonicalUpperPartition
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W) U Pgreedy)
        (selected U I)} beta)
    (lemmaEpsilon : Real) (hlemmaEpsilon : 0 < lemmaEpsilon)
    (htauHalf : Sseq.tau W.m ≤ (2 : NNReal)⁻¹)
    (htauThreshold :
      Sseq.tau W.m ≤
        selectedParentLogarithmicSideBucketAbsorptionThreshold
          ((2 : ENNReal) * (2304 : ENNReal) ^ 3) absorbEta)
    (hsideThreshold :
      Sseq.tau W.m ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (lossEta / 2))
    (hangleThreshold :
      Sseq.tau W.m / 2 ≤
        selectedParentLogarithmicSideBucketAbsorptionThreshold
          (4 * certifiedPlankThresholdedAngleScaleCap 576)
          (lossEta / 4))
    (hscaleSmall : delta ≤
      adaptiveScaleReserveFlatConstantThreshold beta
        constantAbsorbExponent) :
    let coefficientExponent := etaKT + (lossEta + absorbEta) +
      lossExponent + coarseKTExponent + innerKTExponent +
        constantAbsorbExponent
    let paperTau := selectedParentSourceTauEq46PaperTau stoppingEpsilon
      epsilon beta constantAbsorbExponent coefficientExponent etaF
    (∃ k : Fin (blocks
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily
          Pgreedy).length,
      ∃ label : Fin 3 → Int,
        ActualSelectedParentBucketOccupied
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
          Pgreedy k r hr label ∧
        hullShortestSide
          (selectedParentGreedyBlockJohnFrame
            (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
            (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
            Pgreedy k) ≤
          Sseq.tau W.m ^ (1 - paperTau)) ∨
      (∃ eta : Real, ∃ b0 : NNReal,
        0 < eta ∧ 0 < b0 ∧
        ∀ (_hw : 0 < bufferedCommonWidth (Sseq.tau W.m)),
          bufferedCommonWidth (Sseq.tau W.m) ≤ b0 →
          (bufferedCommonWidth (Sseq.tau W.m) : ENNReal) ^ eta ≤
            (datum U I).shading.shadingDensity →
          ∃ a b : NNReal,
            0 < a ∧ a ≤ b ∧ b ≤ 1 ∧
            A.refinement.shading.averageMultiplicity ≤
              (((((I.fibreCardCap : ENNReal) * conflictLoss) *
                    (I.fibreCardCap : ENNReal)) *
                  (thickM U I : ENNReal) ^ (beta / 2)) *
                (bufferedEq45Eq46MiddleMismatch
                    (Sseq.tau W.m) (bufferedCommonWidth (Sseq.tau W.m))
                    a b I.frostmanConstant lemmaEpsilon epsilon beta *
                  sectionEightScaleCountFrostmanFactor
                    (Sseq.tau W.m) 1
                    (plankCount U I *
                      centeredAdaptiveGlobalFullFiberNatCap
                        (tauScaleCover
                          (fullRefinementDatum D) Cmulti Sseq W)
                        (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
                        Pgreedy r hr adaptiveC)
                    beta))) := by
  dsimp only
  obtain hthin | hbudget :=
    fullRefinement_sourceTau_exists_occupied_paperHullThin_or_forall_cardWeightedBudget
      D hD Cmulti Sseq W hstoppingEpsilon Pgreedy r hr A KT adaptiveC CKT
      hKTEvery htauExponent hloss hCKTPower hKTPower
      hconstantAbsorbExponent hfixedSmall hFsource hKTsource
      hetaF hepsilon hbetaStrict hetaKT hlossEta habsorbEta
      hlossExponent hcoarseKTExponent hinnerKTExponent htauHalf
      htauThreshold hscaleSmall
  · exact Or.inl hthin
  · right
    let E := fullRefinementDatum D
    let S := tauScaleCover E Cmulti Sseq W
    let htau : 0 < Sseq.tau W.m :=
      hD.delta_pos.trans_le (Sseq.delta_le_tau W.m)
    obtain ⟨eta, b0, heta, hb0, hmain⟩ :=
      exists_family6Parameters_refinementAverage_le_bufferedThickLossEq45_mul_cardWeightedEq46
        E S U Pgreedy A Wouter I (fullRefinementDatum_isAdmissible hD)
        htau (CoherentStickyMultiscaleCover.tau_le_one Sseq W.m)
        htauHalf r hr hsource KT hKT
        (centeredAdaptiveGlobalFullFiberNatCap S htau
          Pgreedy r hr adaptiveC)
        H lemmaEpsilon epsilon hlemmaEpsilon hlossEta
        hsideThreshold hangleThreshold (by
          intro k label hoccupied
          exact hbudget k label (by
            simpa only [E, S, htau] using hoccupied))
    refine ⟨eta, b0, heta, hb0, ?_⟩
    intro hw hwb0 hdensity
    obtain ⟨a, b, ha, hab, hb, haverage⟩ := hmain hw hwb0 hdensity
    refine ⟨a, b, ha, hab, hb, haverage.trans ?_⟩
    let w := bufferedCommonWidth (Sseq.tau W.m)
    let plankN := plankCount U I
    let capM := centeredAdaptiveGlobalFullFiberNatCap S htau
      Pgreedy r hr adaptiveC
    let outerLoss : ENNReal :=
      ((I.fibreCardCap : ENNReal) * conflictLoss) *
        (I.fibreCardCap : ENNReal)
    have hremainder :
        bufferedCommonWitnessFamily6Remainder U I lemmaEpsilon beta =
          bufferedIsotropicEq45Remainder w plankN I.frostmanConstant
            lemmaEpsilon beta := by
      unfold bufferedCommonWitnessFamily6Remainder
        bufferedIsotropicEq45Remainder
      simp only [w, plankN]
      rw [ENNReal.div_self]
      · simp
      · exact ENNReal.coe_ne_zero.mpr hw.ne'
      · exact ENNReal.coe_ne_top
    have hfactor :=
      bufferedIsotropicEq45Remainder_mul_inner_eq_mismatch_mul_sectionEight
        (rho := Sseq.tau W.m) (w := w) (a := a) (b := b)
        (plankCount := plankN) (tubesPerPlank := capM)
        (CF := I.frostmanConstant) (lemmaEpsilon := lemmaEpsilon)
        (epsilon := epsilon) (beta := beta)
        htau hw ha (hbetaStrict.le.trans (by norm_num))
    have hmiddle :
        bufferedCommonWitnessFamily6Remainder U I lemmaEpsilon beta *
            proposition66AInnerFactor
              (Sseq.tau W.m) a b capM epsilon beta =
          bufferedEq45Eq46MiddleMismatch
              (Sseq.tau W.m) w a b I.frostmanConstant
              lemmaEpsilon epsilon beta *
            sectionEightScaleCountFrostmanFactor
              (Sseq.tau W.m) 1 (plankN * capM) beta := by
      rw [hremainder]
      exact hfactor
    have halgebra :
        outerLoss *
            ((thickM U I : ENNReal) ^ (beta / 2) *
              bufferedCommonWitnessFamily6Remainder U I
                lemmaEpsilon beta) *
          proposition66AInnerFactor
            (Sseq.tau W.m) a b capM epsilon beta =
        (outerLoss * (thickM U I : ENNReal) ^ (beta / 2)) *
          (bufferedEq45Eq46MiddleMismatch
              (Sseq.tau W.m) w a b I.frostmanConstant
              lemmaEpsilon epsilon beta *
            sectionEightScaleCountFrostmanFactor
              (Sseq.tau W.m) 1 (plankN * capM) beta) := by
      calc
        outerLoss *
              ((thickM U I : ENNReal) ^ (beta / 2) *
                bufferedCommonWitnessFamily6Remainder U I
                  lemmaEpsilon beta) *
            proposition66AInnerFactor
              (Sseq.tau W.m) a b capM epsilon beta =
            (outerLoss * (thickM U I : ENNReal) ^ (beta / 2)) *
              (bufferedCommonWitnessFamily6Remainder U I
                  lemmaEpsilon beta *
                proposition66AInnerFactor
                  (Sseq.tau W.m) a b capM epsilon beta) := by ac_rfl
        _ = _ := by rw [hmiddle]
    exact_mod_cast halgebra.le

#print axioms
  fullRefinement_sourceTau_paperHullThin_or_bufferedOuterThickMismatch_mul_middleFactor

end
end Family8FullRefinementSourceTauBufferedAdaptiveMiddleMismatchDichotomyV1
