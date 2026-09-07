import Family8Grounding.Family8DoubledParentConflictKatzTaoWeightedDef212FrostmanV2
import Family8Grounding.Family8ExactConflictDensityBudgetV1
import Family8Grounding.Family8FrostmanWeightedSelectedDirectBaseBudgetV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalExactWeightedDef212FrostmanEndpointV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedRestrictedCoverEndpointV2.ScaleCover
open Family8DoubledParentConflictWeightedDef212EndpointV1.ScaleCover
open Family8DoubledParentConflictWeightedShadingMassBridgeV2.ScaleCover
open Family8DoubledParentConflictWeightedFrostmanConnectorV2.ScaleCover
open Family8DoubledParentConflictKatzTaoWeightedDef212FrostmanV2
open Family8PaperConflictOwnerActiveOwnerKatzTaoExactIncidenceDegreeV3
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV14
open Family8CanonicalLowerBufferedScaleV4
open Family8ExactConflictDensityBudgetV1
open Family8FrostmanWeightedSelectedDirectBaseBudgetV3
open Family8FrostmanWeightedSelectedDirectBaseBudgetV3.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Canonical exact-degree weighted Def. 2.12/Frostman endpoint

This is the short replacement chain for the fixed-John degree-fifteen greedy
loss.  The exact Katz--Tao doubled-parent incidence degree constructs the
weighted selected endpoint.  Its density input is discharged by the exact
degree power envelope, and its base input is discharged directly from the
source Frostman shading mass.  No desired multiplicity bound, selected
density bound, or base scalar is accepted as a callback.
-/

namespace ScaleCover

theorem exists_canonicalExactWeightedDef212_frostmanEndpoint
    {beta frostmanEpsilon frostmanEta sourceExponent : Real}
    {delta0 delta theta : NNReal}
    {index : Type} [Fintype index] [DecidableEq index]
    (hF : FrostmanAtParameters beta frostmanEpsilon frostmanEta delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hSource : FrostmanHypotheses D sourceExponent)
    {scaleEpsilon katzTaoExponent degreeAbsorbExponent
      volumeAbsorbExponent : Real}
    {A : ENNReal} {Cnn : NNReal}
    (S : StickyScaleCover D.family
      (canonicalLowerBufferedScale delta theta scaleEpsilon))
    (hactive : S.activeFine = Finset.univ)
    (huniform : IsCUniform S (Cnn : ENNReal))
    (hpaper : Set.Pairwise (Set.univ : Set index) fun i j =>
      PaperEssentiallyDistinct (D.family.tubes i) (D.family.tubes j))
    (R : UnitRescalingGeometry S)
    (hCWA : R.FibresSatisfyCWA (Cnn : ENNReal))
    (hdeltaTheta : delta <= theta) (hthetaOne : theta <= 1)
    (hscaleEpsilon : 0 <= scaleEpsilon)
    (hdegreeAbsorb : 0 < degreeAbsorbExponent)
    (hvolumeAbsorb : 0 < volumeAbsorbExponent)
    (hdegreeThreshold :
      delta <= activeOwnerExactDegreeSmallDeltaThreshold degreeAbsorbExponent)
    (hvolumeThreshold :
      delta <= directSelectedBaseVolumeSmallDeltaThreshold
        volumeAbsorbExponent)
    (hAone : 1 <= A)
    (hA : A <= (delta : ENNReal) ^ (-katzTaoExponent))
    (hKT : IsKatzTao A D.family.bodyFamily)
    (hrhoSmall :
      canonicalLowerBufferedScale delta theta scaleEpsilon <=
        (1 / 16 : NNReal))
    (hdelta0 : delta <= delta0)
    (hdensityExponent :
      sourceExponent <= frostmanEta -
        activeOwnerExactDegreePowerEnvelope scaleEpsilon
          katzTaoExponent degreeAbsorbExponent)
    (hbaseExponent :
      2 * sourceExponent +
          directSelectedBasePowerLoss scaleEpsilon katzTaoExponent
            degreeAbsorbExponent volumeAbsorbExponent <= frostmanEta) :
    ∃ E : WeightedDef212ScaleEndpoint S
        (parentShadingWeight S D.shading)
        (katzTaoDoubledParentConflictBudget delta
          (canonicalLowerBufferedScale delta theta scaleEpsilon) A)
        (Cnn : ENNReal),
      (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading E.base.selection)).IsAdmissible ∧
      D.shading.averageMultiplicity <=
        katzTaoDoubledParentConflictBudget delta
            (canonicalLowerBufferedScale delta theta scaleEpsilon) A *
          (restrictActualTubeDatum D
            (weightedSelectedFineIndices D.shading
              E.base.selection)).shading.averageMultiplicity ∧
      D.shading.averageMultiplicity <=
        katzTaoDoubledParentConflictBudget delta
            (canonicalLowerBufferedScale delta theta scaleEpsilon) A *
          frostmanMultiplicityRHS delta
            (restrictActualTubeDatum D
              (weightedSelectedFineIndices D.shading
                E.base.selection)).actualFamilyVolume
            frostmanEpsilon beta := by
  let B : ENNReal := katzTaoDoubledParentConflictBudget delta
    (canonicalLowerBufferedScale delta theta scaleEpsilon) A
  have hAfinite : A ≠ ∞ := by
    apply ne_top_of_le_ne_top _ hA
    exact ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.coe_ne_zero.mpr hD.delta_pos.ne') ENNReal.coe_ne_top
  have hdegree : ClosedDoubledParentConflictDegreeBound S B := by
    simpa only [B, katzTaoDoubledParentConflictBudget] using
      (closedDoubledParentConflictDegreeBound_katzTao
        S hD.delta_pos hD.delta_le_half hrhoSmall hAfinite hKT)
  obtain ⟨E⟩ := exists_weightedDef212ScaleEndpoint
    S (parentShadingWeight S D.shading) B (Cnn : ENNReal)
      hdegree huniform hpaper R hCWA
  have hadmissible :
      (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading E.base.selection)).IsAdmissible :=
    Family8GeneralizedKatzTaoMultiplicityV1.ActualTubeDatum.IsAdmissible.restrictTo
      hD _
  have havg : D.shading.averageMultiplicity <=
      B * (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading
          E.base.selection)).shading.averageMultiplicity :=
    source_averageMultiplicity_le_mul_weightedSelected
      D E.base.selection hactive
  have hdensity : (delta : ENNReal) ^ frostmanEta <=
      D.shading.shadingDensity / B := by
    simpa only [B] using
      (canonicalLowerBufferedScale_exactConflict_densityBudget_of_frostman
        D hSource hD.delta_pos hdeltaTheta hthetaOne hscaleEpsilon
        hdegreeAbsorb hdegreeThreshold hAone hA hdensityExponent)
  have hbase : A * volume (unitBallBody : Set Space) <=
      (delta : ENNReal) ^ (-frostmanEta) *
        (restrictActualTubeDatum D
          (weightedSelectedFineIndices D.shading
            E.base.selection)).actualFamilyVolume := by
    simpa only [B] using
      (canonicalLowerBufferedScale_weightedSelected_baseBudget_of_frostman
        D hD hSource E.base.selection hactive hdeltaTheta hthetaOne
        hscaleEpsilon hdegreeAbsorb hvolumeAbsorb hdegreeThreshold
        hvolumeThreshold hAone hA hbaseExponent)
  have hfrostman : D.shading.averageMultiplicity <=
      B * frostmanMultiplicityRHS delta
        (restrictActualTubeDatum D
          (weightedSelectedFineIndices D.shading
            E.base.selection)).actualFamilyVolume
        frostmanEpsilon beta :=
    source_averageMultiplicity_le_mul_frostmanRHS_of_weightedSelection
      hF D hD E.base.selection hactive hdelta0 hKT hdensity hbase
  refine ⟨E, hadmissible, ?_, ?_⟩
  · simpa only [B] using havg
  · simpa only [B] using hfrostman

#print axioms exists_canonicalExactWeightedDef212_frostmanEndpoint

end ScaleCover
end
end Family8CanonicalExactWeightedDef212FrostmanEndpointV2
