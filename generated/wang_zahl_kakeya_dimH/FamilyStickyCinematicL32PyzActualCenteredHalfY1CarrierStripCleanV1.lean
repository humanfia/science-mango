import FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
import FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
import FamilyStickyCinematicL32FiniteLocalizedTangencyCarrierSubsetV1
import FamilyStickyCinematicL32ProjectedTubeVerticalCarrierStripV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyY1E2AfterNormCoverV1
open FamilyStickyCinematicL32FiniteLocalizedTangencyCarrierSubsetV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
open FamilyStickyCinematicL32ProjectedTubeVerticalCarrierStripV1
open FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1

noncomputable section

/-!
Faithful carrier transport for the centered-half tangency stage in the low
multiplicity branch.  The physical shading base and the selected tangency
base remain separate: this is the distinction used in the Section 5
construction, and is deliberately not identified by this adapter.
-/

theorem actualProjectedCenteredHalfTangencyY1_carrier_subset_physical
    {point : Type*} [MeasurableSpace point]
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) (i : iota) :
    (actualProjectedCenteredHalfTangencyY1 base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
      exponent threshold).carrier i ⊆ physical.carrier i := by
  intro x hx
  have hsource := finiteIncidenceLocalizedTangencyCarrier_subset_incidence
    physical.ambient (fun i x => x ∈ physical.carrier i)
    (actualProjectedAmbientCriticalFamily fine physical.ambient)
    projectedTubePairCoefficientDistance globalScale globalCenter
    (actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
      hOuter hf hf1)
    fine.tubes (radius : Real) ceiling exponent threshold i
  apply hsource
  simpa only [actualProjectedCenteredHalfTangencyY1,
    finiteIncidenceLocalizedTangencyY1] using hx

noncomputable def actualProjectedNormFirstSixteenthCenteredHalfY1
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (f : Real → Real) (hfContinuous : Continuous f)
    (f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) :
    FiniteProjectedShading (Real × Real) iota :=
  actualProjectedCenteredHalfTangencyY1 base hbase fine
    (actualProjectedNormFirstSixteenthPhysicalShading fine ambient
      physicalBase hphysicalBase f hfContinuous outerA outerB)
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
    exponent threshold

theorem actualProjectedNormFirstSixteenthCenteredHalfY1_carrier_subset_strip
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (f : Real → Real) (hfContinuous : Continuous f)
    (f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) (i : iota) :
    (actualProjectedNormFirstSixteenthCenteredHalfY1 fine ambient
      physicalBase hphysicalBase base hbase f hfContinuous f1 f2 outerA
      outerB hOuter hf hf1 globalScale globalCenter ceiling exponent
      threshold).carrier i ⊆
    pyzCarrierGraphStrip
      (centeredFractionLeft outerA outerB (1 / 16 : Real))
      (centeredFractionRight outerA outerB (1 / 16 : Real))
      (projectedTubeCinematicTrace f (fine.tubes i)) (radius : Real) := by
  intro q hq
  have hp := actualProjectedCenteredHalfTangencyY1_carrier_subset_physical
    base hbase fine
    (actualProjectedNormFirstSixteenthPhysicalShading fine ambient
      physicalBase hphysicalBase f hfContinuous outerA outerB)
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
    exponent threshold i hq
  change q ∈ projectedTubeVerticalCarrier f
    (centeredFractionIcc outerA outerB (1 / 16 : Real)) (radius : Real)
    (fine.tubes i) at hp
  rw [centeredFractionIcc,
    projectedTubeVerticalCarrier_Icc_eq_pyzCarrierGraphStrip] at hp
  exact hp

end
end FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1
