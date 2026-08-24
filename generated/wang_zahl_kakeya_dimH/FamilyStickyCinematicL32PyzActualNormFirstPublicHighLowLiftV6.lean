import FamilyStickyCinematicL32PyzActualNormFirstHighOrLowMomentFinalV3
import FamilyStickyCinematicL32PyzFixedBandBinLossCompressionCleanV1
import FamilyStickyCinematicL32PyzSelectionMeasureTelescopeV1
import FamilyStickyCinematicL32CriticalSingleDyadicBinFactorPositiveV1

set_option autoImplicit false
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstPublicHighLowLiftV6

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32PyzActualCenteredHalfLocalizedSupportActualCleanV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyCinematicL32PyzQuasiProductFrostmanBoundV1
open FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualCanonicalPayloadLocalEstimateV5
open FamilyStickyCinematicL32PyzActualNormFirstHighOrLowMomentFinalV3
open FamilyStickyCinematicL32PyzFixedBandBinLossCompressionCleanV1
open FamilyStickyCinematicL32PyzCriticalBinUniformityV1
open FamilyStickyCinematicL32PyzSelectionMeasureTelescopeV1
open FamilyStickyCinematicL32CriticalSingleDyadicBinFactorPositiveV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Lift the selected-norm-scale high/low endpoint to the original band

This layer only restores the initial norm-selection loss in the low branch
and compresses the three fixed-band dyadic losses.  The high payload is passed
through unchanged.
-/

theorem exists_actualNormFirst_highPayload_or_lowOriginalBandMoment
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {E : Set (Real × Real)} {alpha : Real} {C : ENNReal}
    (Q : PyzCarrierQuasiProduct E
      (pyzFrostmanIntervalBound (radius : Real) alpha C))
    (S : WZL3UniformTubeSource radius iota)
    (ambient : Finset iota) (hambient : ambient ⊆ S.source)
    (hunit : ∀ i, i ∈ ambient →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (f : Real → Real) (hfContinuous : Continuous f)
    (f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (hparameter : ∀ z, z ∈ Icc outerA outerB → |z| ≤ 1)
    (halpha : 0 ≤ alpha) (halphaOne : alpha ≤ 1)
    (hfun : ∀ z, z ∈ Icc outerA outerB → |f z| ≤ 2)
    (hfun1 : ∀ z, z ∈ Icc outerA outerB → |f1 z| ≤ 2)
    {Y : Shading S.family.bodyFamily}
    {parallelLoss : Nat} {extremalEpsilon extremalSigma : Real}
    (G : EpsilonExtremalTubeFamily S.family Y ambient parallelLoss
      extremalEpsilon extremalSigma)
    (bucket : Int)
    (hbucket : ∀ i, i ∈ ambient →
      actualProjectedTubeCBucket ((radius : Real) / 2)
        (S.family.tubes i) = bucket)
    (normExponent tangencyExponent : Real)
    (logCount lower upper multiplicity : Nat)
    (hradius : 0 < radius)
    (hradiusSixteen : (radius : Real) ≤ 16)
    (hnormExponent : 0 ≤ normExponent)
    (htangencyExponent : 0 ≤ tangencyExponent)
    (hsourcePos : 0 < volume
      ((actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
        physicalBase hphysicalBase f hfContinuous outerA outerB).multiplicityBand
          lower upper))
    (hbandSubsetE :
      (actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
        physicalBase hphysicalBase f hfContinuous outerA outerB).multiplicityBand
          lower upper ⊆ E)
    (hmultiplicity : 0 < multiplicity)
    (hlower : 3 * multiplicity ≤ lower)
    (hloss : actualHalfScaleCoefficientCoverLoss * parallelLoss ≤
      multiplicity)
    (hslack : pyzCriticalBinUniformSlack (radius : Real) ≤ logCount) :
    let physical := actualProjectedNormFirstSixteenthPhysicalShading
      S.family ambient physicalBase hphysicalBase f hfContinuous outerA outerB
    let normScale := actualProjectedAmbientNormScale S.family physical 16
      normExponent
    ∃ normLabel ∈ Finset.Icc (dyadicCeilBucket (radius : Real))
        (dyadicCeilBucket 16),
      let E_norm := continuumCriticalSingleDyadicCell
        (physical.multiplicityBand lower upper) normScale normLabel
      let globalScale := dyadicCeilUpper normLabel
      volume (physical.multiplicityBand lower upper) /
          (continuumCriticalSingleDyadicBinFactor (radius : Real) 16 :
            ENNReal) ≤ volume E_norm ∧
      0 < volume E_norm ∧ MeasurableSet E_norm ∧
      E_norm ⊆ physical.multiplicityBand lower upper ∧
      0 < globalScale ∧ (radius : Real) ≤ globalScale ∧
      globalScale ≤ 32 ∧
      ((∃ globalCenter : Tube radius, ∃ base : Set (Real × Real),
          ∃ hbase : MeasurableSet base,
          0 < volume base ∧ base ⊆ E_norm ∧
          ∃ payload : ActualPositiveCenterCanonicalPayload volume base hbase
              S.family physical f f1 f2 outerA outerB hOuter hf hf1
              globalScale globalCenter tangencyExponent,
            24 * logCount ≤ pyzE2DegreeLower payload.finalLabel) ∨
        actualCanonicalPayloadGlobalWeight lower globalScale normExponent
            tangencyExponent *
              volume (physical.multiplicityBand lower upper) ≤
          ((logCount : ENNReal) ^ 2 *
              (continuumCriticalSingleDyadicBinFactor 1
                (ambient.card : Real) : ENNReal)) *
            actualCanonicalPayloadUniformMomentCost radius multiplicity
              logCount normExponent tangencyExponent alpha C *
            ((19 ^ 3 * ambient.card : Nat) : ENNReal)) := by
  dsimp only
  let physical := actualProjectedNormFirstSixteenthPhysicalShading S.family
    ambient physicalBase hphysicalBase f hfContinuous outerA outerB
  obtain ⟨normLabel, hnormLabel, hnormMeasure, hnormPos, hnormMeasurable,
      hnormSubset, hglobalScale, hradiusGlobalScale, hglobalScaleUpper,
      hresult⟩ :=
    exists_actualNormFirst_highPayload_or_lowMoment Q S ambient hambient hunit
      physicalBase hphysicalBase f hfContinuous f1 f2 outerA outerB hOuter hf
      hf1 hparameter halpha halphaOne hfun hfun1 G bucket hbucket normExponent
      tangencyExponent logCount lower upper multiplicity hradius
      hradiusSixteen hnormExponent htangencyExponent hsourcePos hbandSubsetE
      hmultiplicity hlower hloss
  let normScale := actualProjectedAmbientNormScale S.family physical 16
    normExponent
  let E_norm := continuumCriticalSingleDyadicCell
    (physical.multiplicityBand lower upper) normScale normLabel
  let globalScale := dyadicCeilUpper normLabel
  refine ⟨normLabel, hnormLabel, hnormMeasure, hnormPos, hnormMeasurable,
    hnormSubset, hglobalScale, hradiusGlobalScale, hglobalScaleUpper, ?_⟩
  rcases hresult with hhigh | hlow
  · exact Or.inl hhigh
  · apply Or.inr
    have hradiusTangency : (radius : Real) ≤ 36 * globalScale := by
      have hscale36 : globalScale ≤ 36 * globalScale := by
        nlinarith
      exact hradiusGlobalScale.trans hscale36
    have hnormLossZero :
        (continuumCriticalSingleDyadicBinFactor (radius : Real) 16 :
          ENNReal) ≠ 0 :=
      continuumCriticalSingleDyadicBinFactor_cast_ne_zero
        (by exact_mod_cast hradius) hradiusSixteen
    have hnormLossTop :
        (continuumCriticalSingleDyadicBinFactor (radius : Real) 16 :
          ENNReal) ≠ ⊤ :=
      continuumCriticalSingleDyadicBinFactor_cast_ne_top
        (radius : Real) 16
    have hnormRetention :
        volume (physical.multiplicityBand lower upper) ≤
          volume E_norm *
            (continuumCriticalSingleDyadicBinFactor (radius : Real) 16 :
              ENNReal) :=
      div_retention_to_mul_upper hnormLossZero hnormLossTop hnormMeasure
    have hthreeLoss :=
      actualFixedBandThreeBinLoss_le_logCount_sq_mul_final
        hradius hradiusTangency hglobalScaleUpper hslack
        (ambientCard := ambient.card)
    calc
      actualCanonicalPayloadGlobalWeight lower globalScale normExponent
            tangencyExponent *
          volume (physical.multiplicityBand lower upper) ≤
        actualCanonicalPayloadGlobalWeight lower globalScale normExponent
            tangencyExponent *
          (volume E_norm *
            (continuumCriticalSingleDyadicBinFactor (radius : Real) 16 :
              ENNReal)) :=
        mul_le_mul_right hnormRetention _
      _ = (continuumCriticalSingleDyadicBinFactor (radius : Real) 16 :
            ENNReal) *
          (actualCanonicalPayloadGlobalWeight lower globalScale normExponent
            tangencyExponent * volume E_norm) := by
        ac_rfl
      _ ≤ (continuumCriticalSingleDyadicBinFactor (radius : Real) 16 :
            ENNReal) *
          (actualCanonicalPayloadCommonCost radius globalScale ambient.card
              multiplicity logCount normExponent tangencyExponent alpha C *
            ((19 ^ 3 * ambient.card : Nat) : ENNReal)) :=
        mul_le_mul_right hlow _
      _ = actualFixedBandThreeBinLoss radius globalScale ambient.card *
          actualCanonicalPayloadUniformMomentCost radius multiplicity
            logCount normExponent tangencyExponent alpha C *
          ((19 ^ 3 * ambient.card : Nat) : ENNReal) := by
        unfold actualCanonicalPayloadCommonCost actualFixedBandThreeBinLoss
        ac_rfl
      _ ≤ ((logCount : ENNReal) ^ 2 *
              (continuumCriticalSingleDyadicBinFactor 1
                (ambient.card : Real) : ENNReal)) *
            actualCanonicalPayloadUniformMomentCost radius multiplicity
              logCount normExponent tangencyExponent alpha C *
            ((19 ^ 3 * ambient.card : Nat) : ENNReal) := by
        exact mul_le_mul_left (mul_le_mul_left hthreeLoss _) _

#print axioms exists_actualNormFirst_highPayload_or_lowOriginalBandMoment

end

end FamilyStickyCinematicL32PyzActualNormFirstPublicHighLowLiftV6
