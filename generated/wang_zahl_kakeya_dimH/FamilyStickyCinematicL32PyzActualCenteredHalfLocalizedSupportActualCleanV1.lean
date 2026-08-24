import FamilyStickyCinematicL32PyzActualCenteredHalfLowMultiplicityMomentV1
import FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32PyzActualCenteredHalfLocalizedSupportActualCleanV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1
open FamilyStickyCinematicL32PyzLowMultiplicityRestrictedThreeHalfV1

noncomputable section

/-!
# The actual global `3B` support of one centered-half norm cell

PYZ Section 5 does not pay the cardinality of the full source family for
each norm-cover cell.  Once a global coefficient centre is fixed, every
literal active carrier is supported on the paper family `F_B = F ∩ 3B`.
This module records that support before any summation or numerical
absorption.  It is the first half of the bounded-overlap replacement for
the non-faithful product `centres.card * ambient.card`.
-/

/-- Ambient indices whose actual tubes belong to the coefficient `3B`
around one fixed global norm centre. -/
def actualProjectedNormThreeBallIndices
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (globalScale : Real) (globalCenter : Tube radius) : Finset iota :=
  ambient.filter fun i =>
    projectedTubePairCoefficientDistance (fine.tubes i) globalCenter ≤
      3 * globalScale

/-- Every literal active index of the centered-half `Y₁` lies in the
fixed global `3B` index family. -/
theorem activeAtPoint_subset_actualProjectedNormThreeBallIndices
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
    (q : Real × Real) :
    let Z := actualProjectedNormFirstSixteenthCenteredHalfY1 fine ambient
      physicalBase hphysicalBase base hbase f hfContinuous f1 f2 A B hAB
      hfDeriv hf1Deriv globalScale globalCenter tangencyCeiling
      tangencyExponent tangencyThreshold
    Z.activeAtPoint q ⊆
      actualProjectedNormThreeBallIndices fine ambient globalScale
        globalCenter := by
  dsimp only
  intro i hi
  let physical := actualProjectedNormFirstSixteenthPhysicalShading fine
    ambient physicalBase hphysicalBase f hfContinuous A B
  have hi' : i ∈
      (actualProjectedCenteredHalfTangencyY1 base hbase fine physical
        f f1 f2 A B hAB hfDeriv hf1Deriv globalScale globalCenter
        tangencyCeiling tangencyExponent tangencyThreshold).activeAtPoint q := by
    simpa only [physical,
      actualProjectedNormFirstSixteenthCenteredHalfY1] using hi
  have hdata := mem_actualProjectedCenteredHalfTangencyY1_data base hbase
    fine physical f f1 f2 A B hAB hfDeriv hf1Deriv globalScale globalCenter
    tangencyCeiling tangencyExponent tangencyThreshold q i hi'
  have hiAmbientPhysical : i ∈ physical.ambient :=
    (physical.mem_activeAtPoint q i).mp hdata.1 |>.1
  have hiAmbient : i ∈ ambient := by
    change i ∈ ambient at hiAmbientPhysical
    exact hiAmbientPhysical
  have hiDistance :
      projectedTubePairCoefficientDistance (fine.tubes i) globalCenter ≤
        3 * globalScale := by
    have hlocalized := hdata.2.1
    rw [finiteIncidenceNormLocalizedFamilyValue,
      finiteGlobalNormLocalizedFamily, finiteFamilyMetricBall,
      Finset.mem_filter] at hlocalized
    exact hlocalized.2
  exact Finset.mem_filter.mpr ⟨hiAmbient, hiDistance⟩

/-- For an ambient index outside the fixed global `3B`, the literal
centered-half restricted carrier is empty. -/
theorem pyzE2RestrictedCarrier_eq_empty_of_not_mem_threeBall
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
    (label : Int) (i : iota) (hiAmbient : i ∈ ambient)
    (hi : i ∉ actualProjectedNormThreeBallIndices fine ambient globalScale
      globalCenter) :
    let Z := actualProjectedNormFirstSixteenthCenteredHalfY1 fine ambient
      physicalBase hphysicalBase base hbase f hfContinuous f1 f2 A B hAB
      hfDeriv hf1Deriv globalScale globalCenter tangencyCeiling
      tangencyExponent tangencyThreshold
    pyzE2RestrictedCarrier Z label i = ∅ := by
  dsimp only
  ext q
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hq
  let Z := actualProjectedNormFirstSixteenthCenteredHalfY1 fine ambient
    physicalBase hphysicalBase base hbase f hfContinuous f1 f2 A B hAB
    hfDeriv hf1Deriv globalScale globalCenter tangencyCeiling
    tangencyExponent tangencyThreshold
  have hiAmbientZ : i ∈ Z.ambient := by
    change i ∈ ambient
    exact hiAmbient
  have hiActive : i ∈ Z.activeAtPoint q :=
    (FiniteProjectedShading.mem_activeAtPoint Z q i).mpr
      ⟨hiAmbientZ, hq.2⟩
  exact hi (activeAtPoint_subset_actualProjectedNormThreeBallIndices fine
    ambient physicalBase hphysicalBase base hbase f hfContinuous f1 f2 A B
    hAB hfDeriv hf1Deriv globalScale globalCenter tangencyCeiling
    tangencyExponent tangencyThreshold q (by simpa only [Z] using hiActive))

#print axioms actualProjectedNormThreeBallIndices
#print axioms activeAtPoint_subset_actualProjectedNormThreeBallIndices
#print axioms pyzE2RestrictedCarrier_eq_empty_of_not_mem_threeBall

end
end FamilyStickyCinematicL32PyzActualCenteredHalfLocalizedSupportActualCleanV1
