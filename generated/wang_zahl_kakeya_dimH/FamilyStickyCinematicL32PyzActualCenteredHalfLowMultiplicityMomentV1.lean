import FamilyStickyCinematicL32PyzActualCenteredHalfY1QuasiProductMassV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32PyzActualCenteredHalfLowMultiplicityMomentV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzQuasiProductFrostmanBoundV1
open FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1
open FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1
open FamilyStickyCinematicL32PyzActualCenteredHalfY1QuasiProductMassV1
open FamilyStickyCinematicL32PyzLowMultiplicityRestrictedThreeHalfV1
open FamilyStickyCinematicL32PyzLowMultiplicityE2MomentSandwichV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyY1E2AfterNormCoverV1
open FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1

noncomputable section

/-!
# Faithful low-multiplicity moment after centered-half tangency selection

This endpoint combines the strict low-degree gate with the separate-base
centered-half `Y₁` and the quasi-product carrier mass theorem.  It is
denominator-free.  It does not identify the physical and selected bases and
does not absorb the later `μ → μ₁ → μ₂` scale losses.
-/

theorem actual_centeredHalf_lowMultiplicity_degreeLower_rpow_mul_E2Volume_le
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    {E : Set (Real × Real)} {alpha : Real} {C : ENNReal}
    (Q : PyzCarrierQuasiProduct E
      (pyzFrostmanIntervalBound (radius : Real) alpha C))
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (hbaseSubset : base ⊆ E)
    (f : Real → Real) (hfContinuous : Continuous f)
    (f1 f2 : Real → Real) (A B : Real) (hAB : A ≤ B)
    (hfDeriv : ∀ z, HasDerivAt f (f1 z) z)
    (hf1Deriv : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyCeiling tangencyExponent tangencyThreshold : Real)
    (label : Int) (logCount : Nat)
    (hactive : ∀ x,
      x ∈ projectedPositiveMultiplicityDyadicCell
        (actualProjectedNormFirstSixteenthCenteredHalfY1 fine ambient
          physicalBase hphysicalBase base hbase f hfContinuous f1 f2 A B hAB
          hfDeriv hf1Deriv globalScale globalCenter tangencyCeiling
          tangencyExponent tangencyThreshold) label →
      ((actualProjectedNormFirstSixteenthCenteredHalfY1 fine ambient
          physicalBase hphysicalBase base hbase f hfContinuous f1 f2 A B hAB
          hfDeriv hf1Deriv globalScale globalCenter tangencyCeiling
          tangencyExponent tangencyThreshold).activeAtPoint x).Nonempty)
    (hlow : pyzE2DegreeLower label < 24 * logCount) :
    (pyzE2DegreeLower label : ENNReal) ^ (3 / 2 : Real) *
        volume (projectedPositiveMultiplicityDyadicCell
          (actualProjectedNormFirstSixteenthCenteredHalfY1 fine ambient
            physicalBase hphysicalBase base hbase f hfContinuous f1 f2 A B
            hAB hfDeriv hf1Deriv globalScale globalCenter tangencyCeiling
            tangencyExponent tangencyThreshold) label) ≤
      ((48 * logCount : Nat) : ENNReal) ^ (1 / 2 : Real) *
        ((ambient.card : ENNReal) *
          pyzActualCenteredHalfY1FrostmanPieceMass radius alpha C A B) := by
  let Z := actualProjectedNormFirstSixteenthCenteredHalfY1 fine ambient
    physicalBase hphysicalBase base hbase f hfContinuous f1 f2 A B hAB
    hfDeriv hf1Deriv globalScale globalCenter tangencyCeiling
    tangencyExponent tangencyThreshold
  have hactiveZ : ∀ x, x ∈ projectedPositiveMultiplicityDyadicCell Z label →
      (Z.activeAtPoint x).Nonempty := by
    simpa only [Z] using hactive
  have hmass : ∀ i ∈ Z.ambient,
      volume (pyzE2RestrictedCarrier Z label i) ≤
        pyzActualCenteredHalfY1FrostmanPieceMass radius alpha C A B := by
    intro i _hi
    exact volume_actualCenteredHalfY1_restrictedCarrier_le_frostmanPieceMass
      Q fine ambient physicalBase hphysicalBase base hbase hbaseSubset f
      hfContinuous f1 f2 A B hAB hfDeriv hf1Deriv globalScale globalCenter
      tangencyCeiling tangencyExponent tangencyThreshold label i
  have hbound := degreeLower_rpow_mul_measure_le_lowCap_card_mul_pieceMass
    volume Z label logCount
    (pyzActualCenteredHalfY1FrostmanPieceMass radius alpha C A B)
    hactiveZ hlow hmass
  simpa only [Z, actualProjectedNormFirstSixteenthCenteredHalfY1,
    actualProjectedCenteredHalfTangencyY1,
    finiteIncidenceLocalizedTangencyY1,
    actualProjectedNormFirstSixteenthPhysicalShading,
    finiteProjectedTubeShading] using hbound

end
end FamilyStickyCinematicL32PyzActualCenteredHalfLowMultiplicityMomentV1
