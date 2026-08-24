import FamilyStickyCinematicL32PyzActualCenteredHalfLocalizedSupportActualCleanV1

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32PyzActualCenteredHalfLocalizedMomentRunV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzQuasiProductFrostmanBoundV1
open FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1
open FamilyStickyCinematicL32PyzActualCenteredHalfY1QuasiProductMassV1
open FamilyStickyCinematicL32PyzLowMultiplicityRestrictedThreeHalfV1
open FamilyStickyCinematicL32PyzLowMultiplicityE2MomentSandwichV1
open FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1
open FamilyStickyCinematicL32PyzActualCenteredHalfLocalizedSupportActualCleanV1

noncomputable section

/-!
# Low-multiplicity moment with the actual `F_B` cardinality

The full ambient carrier sum has literal zero terms outside the fixed
coefficient `3B`.  Consequently the one-carrier quasi-product estimate
costs `#F_B`, not the cardinality of the global source family.  This is the
faithful local summand needed before summing over the bounded-overlap norm
cover in PYZ Section 5.
-/

/-- The full ambient restricted-carrier sum is exactly supported on the
actual fixed global `3B` index family. -/
theorem sum_volume_restrictedCarrier_eq_sum_threeBall
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (f : Real → Real) (hfContinuous : Continuous f)
    (f1 f2 : Real → Real) (A B : Real) (hAB : A ≤ B)
    (hfDeriv : ∀ z, HasDerivAt f (f1 z) z)
    (hf1Deriv : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyCeiling tangencyExponent tangencyThreshold : Real)
    (label : Int) :
    let Z := actualProjectedNormFirstSixteenthCenteredHalfY1 fine ambient
      physicalBase hphysicalBase base hbase f hfContinuous f1 f2 A B hAB
      hfDeriv hf1Deriv globalScale globalCenter tangencyCeiling
      tangencyExponent tangencyThreshold
    ∑ i ∈ ambient, volume (pyzE2RestrictedCarrier Z label i) =
      ∑ i ∈ actualProjectedNormThreeBallIndices fine ambient
          globalScale globalCenter,
        volume (pyzE2RestrictedCarrier Z label i) := by
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hiAmbient hiNot
  rw [pyzE2RestrictedCarrier_eq_empty_of_not_mem_threeBall fine ambient
    physicalBase hphysicalBase base hbase f hfContinuous f1 f2 A B hAB
    hfDeriv hf1Deriv globalScale globalCenter tangencyCeiling
    tangencyExponent tangencyThreshold label i hiAmbient hiNot]
  simp

/-- The exact restricted-carrier sum is bounded by the cardinality of the
actual `F_B`, rather than by the full ambient cardinality. -/
theorem sum_volume_restrictedCarrier_le_threeBallCard_mul_pieceMass
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
    (label : Int) :
    let Z := actualProjectedNormFirstSixteenthCenteredHalfY1 fine ambient
      physicalBase hphysicalBase base hbase f hfContinuous f1 f2 A B hAB
      hfDeriv hf1Deriv globalScale globalCenter tangencyCeiling
      tangencyExponent tangencyThreshold
    ∑ i ∈ ambient, volume (pyzE2RestrictedCarrier Z label i) ≤
      ((actualProjectedNormThreeBallIndices fine ambient globalScale
          globalCenter).card : ENNReal) *
        pyzActualCenteredHalfY1FrostmanPieceMass radius alpha C A B := by
  dsimp only
  rw [sum_volume_restrictedCarrier_eq_sum_threeBall fine ambient physicalBase
    hphysicalBase base hbase f hfContinuous f1 f2 A B hAB hfDeriv hf1Deriv
    globalScale globalCenter tangencyCeiling tangencyExponent
    tangencyThreshold label]
  calc
    ∑ i ∈ actualProjectedNormThreeBallIndices fine ambient globalScale
          globalCenter,
        volume (pyzE2RestrictedCarrier
          (actualProjectedNormFirstSixteenthCenteredHalfY1 fine ambient
            physicalBase hphysicalBase base hbase f hfContinuous f1 f2 A B
            hAB hfDeriv hf1Deriv globalScale globalCenter tangencyCeiling
            tangencyExponent tangencyThreshold) label i) ≤
        ∑ _i ∈ actualProjectedNormThreeBallIndices fine ambient
          globalScale globalCenter,
          pyzActualCenteredHalfY1FrostmanPieceMass radius alpha C A B := by
      apply Finset.sum_le_sum
      intro i _hi
      exact volume_actualCenteredHalfY1_restrictedCarrier_le_frostmanPieceMass
        Q fine ambient physicalBase hphysicalBase base hbase hbaseSubset f
        hfContinuous f1 f2 A B hAB hfDeriv hf1Deriv globalScale globalCenter
        tangencyCeiling tangencyExponent tangencyThreshold label i
    _ = ((actualProjectedNormThreeBallIndices fine ambient globalScale
          globalCenter).card : ENNReal) *
        pyzActualCenteredHalfY1FrostmanPieceMass radius alpha C A B := by
      simp

/-- Faithful low-degree moment for one norm-cover cell.  The right-hand
cardinality is the literal local family `F_B`; no centre-count loss or
global-family cardinality has been introduced. -/
theorem actual_centeredHalf_lowMultiplicity_localized_degreeLower_rpow_mul_E2Volume_le
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
        (((actualProjectedNormThreeBallIndices fine ambient globalScale
            globalCenter).card : ENNReal) *
          pyzActualCenteredHalfY1FrostmanPieceMass radius alpha C A B) := by
  let Z := actualProjectedNormFirstSixteenthCenteredHalfY1 fine ambient
    physicalBase hphysicalBase base hbase f hfContinuous f1 f2 A B hAB
    hfDeriv hf1Deriv globalScale globalCenter tangencyCeiling
    tangencyExponent tangencyThreshold
  have hbaseMoment :=
    degreeLower_rpow_mul_measure_le_lowCap_sum_restricted_measure
      volume Z label logCount (by simpa only [Z] using hactive) hlow
  have hsum :=
    sum_volume_restrictedCarrier_le_threeBallCard_mul_pieceMass Q fine ambient
      physicalBase hphysicalBase base hbase hbaseSubset f hfContinuous f1 f2
      A B hAB hfDeriv hf1Deriv globalScale globalCenter tangencyCeiling
      tangencyExponent tangencyThreshold label
  have hsum' :
      ∑ i ∈ Z.ambient, volume (pyzE2RestrictedCarrier Z label i) ≤
        ((actualProjectedNormThreeBallIndices fine ambient globalScale
            globalCenter).card : ENNReal) *
          pyzActualCenteredHalfY1FrostmanPieceMass radius alpha C A B := by
    rw [show Z.ambient = ambient by rfl]
    simpa only [Z] using hsum
  have hfinal := hbaseMoment.trans
    (mul_le_mul_right hsum'
      (((48 * logCount : Nat) : ENNReal) ^ (1 / 2 : Real)))
  simpa only [Z] using hfinal

#print axioms sum_volume_restrictedCarrier_eq_sum_threeBall
#print axioms sum_volume_restrictedCarrier_le_threeBallCard_mul_pieceMass
#print axioms actual_centeredHalf_lowMultiplicity_localized_degreeLower_rpow_mul_E2Volume_le

end
end FamilyStickyCinematicL32PyzActualCenteredHalfLocalizedMomentRunV1
