import Family6Grounding.Family6Lemma69DeltaBCThresholdedBudgetV1
import Family8Grounding.Family8ActualFamilyVolumePackingV1
import Family8Grounding.Family8Prop66AFrostmanUnionVolumeAverageAdapterV1

/-!
# Thresholded normalized `delta x b x c` Lemma 6.9 to Equation (32)

This file keeps the normalization Jacobian exactly.  The canonical thresholded
angle rows produce the overlap budget for the affine image shading with union
floor `J * L`, where `J` is the Jacobian of scalar normalization by `c`.
The actual-tube volume upper bound is transported by the same `J`, and affine
invariance of average multiplicity returns the resulting estimate to the
original shading.

Thus angle labels, row containers, pair-overlap estimates, and row-scale
comparisons do not occur in the interface.  The two remaining numerical seams
are the canonical thresholded scalar absorption and the raw tube-volume upper
payment.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Lemma69ActualTubeDeltaBCThresholdedEq32ComposerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffineConvexVolumeCoreV1
open Family6Lemma69DeltaBCPlankGeometryV1
open Family6Lemma69DeltaBCThresholdedBudgetV1
open Family8ActualFamilyVolumePackingV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AFrostmanUnionVolumeAverageAdapterV1
open Family8SelectedParentAffineShadingTransportV4

noncomputable section

/-- Same-datum Equation (32) composer using the canonical thresholded rows of
the honestly normalized `delta x b x c` family.  The normalized union floor is
the literal Jacobian multiple of the requested raw floor; no volume-preserving
normalization is assumed.  The zero-mass branch is discharged directly, so no
extra nonzero-mass premise is exposed. -/
theorem actualTube_eq32_of_lemma69_deltaBCThresholded_normalizedScalarPayments
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index)
    {geometryC plankB plankC : NNReal}
    (cert : ∀ i,
      DeltaBCDimensionsCertificate geometryC delta plankB plankC
        (D.family.bodyFamily i))
    (hplankC : 0 < plankC)
    (a b : NNReal)
    (CF externalLoss rawUnionFloor KT : ENNReal)
    (epsilon beta : Real)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hKT : IsKatzTao KT D.family.bodyFamily)
    (hscalar :
      DeltaBCThresholdedScalarAbsorption cert hplankC D.shading KT
        (affineJacobian (deltaBCNormalizationEquiv plankC hplankC) *
          rawUnionFloor))
    (hupperScalar :
      (Fintype.card index : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) ≤
        (externalLoss * proposition66AFrostmanFactor delta a b
          (Fintype.card index) CF epsilon beta) * rawUnionFloor) :
    D.shading.averageMultiplicity ≤
      externalLoss * proposition66AFrostmanFactor delta a b
        (Fintype.card index) CF epsilon beta := by
  let e : Space ≃ᵃ[Real] Space :=
    deltaBCNormalizationEquiv plankC hplankC
  let J : ENNReal := affineJacobian e
  let Yn := deltaBCNormalizedShading plankC hplankC D.shading
  let rhs : ENNReal :=
    externalLoss * proposition66AFrostmanFactor delta a b
      (Fintype.card index) CF epsilon beta
  by_cases hmassZero : D.shading.shadingMass = 0
  · have havgZero : D.shading.averageMultiplicity = 0 := by
      unfold Shading.averageMultiplicity
      rw [hmassZero]
      exact ENNReal.zero_div
    rw [havgZero]
    exact bot_le
  · have hmassTransport :
        Yn.shadingMass = J * D.shading.shadingMass := by
      simpa only [Yn, J, e, deltaBCNormalizedShading] using
        affineImageShading_shadingMass
          (deltaBCNormalizationEquiv plankC hplankC) D.shading
    have hmassNormalized : Yn.shadingMass ≠ 0 := by
      rw [hmassTransport]
      exact mul_ne_zero
        (affineJacobian_pos e).ne' hmassZero
    have hbudgetNormalized :
        (J * rawUnionFloor) *
            (∑ i, ∑ j, volume (Yn.carrier i ∩ Yn.carrier j)) ≤
          Yn.shadingMass ^ 2 := by
      simpa only [Yn, J, e] using
        lemma69_normalized_overlapBudget_of_deltaBCThresholded
          D.shading cert hplankC KT
            (affineJacobian
              (deltaBCNormalizationEquiv plankC hplankC) * rawUnionFloor)
            hKT hscalar
    have hunionNormalizedDirect :
        J * rawUnionFloor ≤ volume Yn.shadedUnion :=
      lemma69_union_of_overlapBudget Yn hmassNormalized hbudgetNormalized
    have hunionTransport :
        volume Yn.shadedUnion =
          J * volume D.shading.shadedUnion := by
      simpa only [Yn, J, e, deltaBCNormalizedShading] using
        affineImageShading_shadedUnion_volume
          (deltaBCNormalizationEquiv plankC hplankC) D.shading
    have hunionRaw :
        rawUnionFloor ≤ volume D.shading.shadedUnion := by
      apply (ENNReal.mul_le_mul_iff_right
        (affineJacobian_pos e).ne' (affineJacobian_ne_top e)).mp
      simpa only [J, hunionTransport] using hunionNormalizedDirect
    have hunionNormalized :
        J * rawUnionFloor ≤ volume Yn.shadedUnion := by
      calc
        J * rawUnionFloor ≤
            J * volume D.shading.shadedUnion :=
          mul_le_mul' le_rfl hunionRaw
        _ = volume Yn.shadedUnion := hunionTransport.symm
    have hmassRaw : D.shading.shadingMass ≤ rhs * rawUnionFloor := by
      calc
        D.shading.shadingMass ≤ D.actualFamilyVolume := by
          simpa only [ActualTubeDatum.actualFamilyVolume] using
            D.shading.shadingMass_le_familyVolume
        _ ≤ (Fintype.card index : ENNReal) *
              (8 * (delta : ENNReal) ^ 2) :=
          actualFamilyVolume_le_card_mul_eight_sq D hdeltaHalf
        _ ≤ rhs * rawUnionFloor := by
          simpa only [rhs] using hupperScalar
    have hmassNormalizedUpper :
        Yn.shadingMass ≤ rhs * (J * rawUnionFloor) := by
      rw [hmassTransport]
      calc
        J * D.shading.shadingMass ≤ J * (rhs * rawUnionFloor) := by
          exact mul_le_mul' le_rfl hmassRaw
        _ = rhs * (J * rawUnionFloor) := by ac_rfl
    have havgNormalized : Yn.averageMultiplicity ≤ rhs :=
      averageMultiplicity_le_of_shadingMass_le_rhs_mul_unionVolumeFloor
        Yn hunionNormalized hmassNormalizedUpper
    have havgTransport : Yn.averageMultiplicity =
        D.shading.averageMultiplicity := by
      simpa only [Yn, e, deltaBCNormalizedShading] using
        affineImageShading_averageMultiplicity
          (deltaBCNormalizationEquiv plankC hplankC) D.shading
    rw [havgTransport] at havgNormalized
    simpa only [rhs] using havgNormalized

#print axioms
  actualTube_eq32_of_lemma69_deltaBCThresholded_normalizedScalarPayments

end
end Family8Lemma69ActualTubeDeltaBCThresholdedEq32ComposerV1
