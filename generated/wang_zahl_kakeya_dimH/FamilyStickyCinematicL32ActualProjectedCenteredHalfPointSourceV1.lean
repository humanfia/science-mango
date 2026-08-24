import FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
import FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CenteredFractionIntervalsV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TubePairTraceV1
import FamilyStickyCinematicL32ActualTubeCoefficientMetricV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteIncidenceCanonicalCriticalCenterV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u v

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Literal point source for the centered-half tangency stage

The physical carrier is still the outer-sixteenth radius-delta carrier.  Its
tangency centre, however, is the centre selected with the attained metric on
the centered half.  Thus outer carrier geometry and inner minimization scope
are represented by separate arguments and cannot be accidentally identified.
-/

/-- Actual physical projected shading on the outer sixteenth. -/
noncomputable def actualProjectedNormFirstOuterSixteenthPhysicalShading
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (f : Real → Real) (hf : Continuous f)
    (outerA outerB : Real) : FiniteProjectedShading (Real × Real) iota :=
  finiteProjectedTubeShading fine ambient base hbase f hf
    (centeredFractionIcc outerA outerB (1 / 16 : Real)) measurableSet_Icc
    (radius : Real)

/-- The four literal point-rectangle fields used by Lemma 5.5. -/
structure ActualCenteredHalfPointRectangleSource
    {radius : NNReal} (E : Set (Real × Real))
    (centerTube : Tube radius) (tubeAt : Real × Real → Tube radius)
    (f : Real → Real) (outerA outerB tGlobal : Real) : Prop where
  hpointTheta : ∀ q, q ∈ E →
    q.2 ∈ centeredFractionIcc outerA outerB (1 / 16 : Real)
  hpointTube : ∀ q, q ∈ E →
    |q.1 - cinematicTraceValue f
      (tubeGraphA (tubeAt q)) (tubeGraphB (tubeAt q))
      (tubeGraphC (tubeAt q)) (tubeGraphD (tubeAt q)) q.2| ≤
        (radius : Real)
  hcBucket : ∀ q, q ∈ E →
    |tubeGraphC centerTube - tubeGraphC (tubeAt q)| ≤
      (radius : Real) / 2
  hcoefficientUpper : ∀ q, q ∈ E →
    tubePairCoefficientDistance centerTube (tubeAt q) ≤ 6 * tGlobal

/-- The centered-half selector's total centre belongs to the literal
norm-localized family whenever that family is nonempty. -/
theorem actualProjectedCenteredHalfTangencyCenterTubeAt_mem
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent : Real) (x : point)
    (hlocalized : (finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine physical.ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter
      (physical.activeAtPoint x)).Nonempty) :
    actualProjectedCenteredHalfTangencyCenterTubeAt fine physical f f1 f2
        outerA outerB hOuter hf hf1 globalScale globalCenter ceiling exponent x ∈
      finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily fine physical.ambient)
        projectedTubePairCoefficientDistance globalScale globalCenter
        (physical.activeAtPoint x) := by
  let familyOfActive :=
    actualProjectedAmbientCriticalFamily fine physical.ambient
  let tangencyDistance : Finset iota → Tube radius → Tube radius → Real :=
    actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
      hOuter hf hf1
  have hlocalizedFinite :
      (finiteIncidenceNormLocalizedFamilyValue familyOfActive
        projectedTubePairCoefficientDistance globalScale globalCenter
        (finiteIncidenceActiveAtPoint physical.ambient
          (fun i x => x ∈ physical.carrier i) x)).Nonempty := by
    simpa only [familyOfActive, FiniteProjectedShading.activeAtPoint] using
      hlocalized
  obtain ⟨center, hcenterSome, hcenterMem⟩ :=
    finiteIncidenceCriticalCenter_exists_mem_of_nonempty physical.ambient
      (fun i x => x ∈ physical.carrier i)
      (finiteIncidenceNormLocalizedFamilyValue familyOfActive
        projectedTubePairCoefficientDistance globalScale globalCenter)
      tangencyDistance (radius : Real) ceiling exponent x hlocalizedFinite
  have htubeAt : actualProjectedCenteredHalfTangencyCenterTubeAt fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      ceiling exponent x = center := by
    change (finiteIncidenceLocalizedTangencyCenter physical.ambient
      (fun i x => x ∈ physical.carrier i) familyOfActive
      projectedTubePairCoefficientDistance globalScale globalCenter
      tangencyDistance (radius : Real) ceiling exponent x).getD
        globalCenter = center
    rw [finiteIncidenceLocalizedTangencyCenter, hcenterSome]
    rfl
  rw [htubeAt]
  simpa only [familyOfActive, FiniteProjectedShading.activeAtPoint] using
    hcenterMem

/-- Outer-sixteenth physical incidence, the actual centered-half selector,
and an ambient half-c bucket produce every point-rectangle source field. -/
theorem actualCenteredHalfPointRectangleSource_of_outerSixteenthPhysical
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (f : Real → Real) (hfContinuous : Continuous f)
    (outerA outerB : Real) (f1 f2 : Real → Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (hglobalScale : 0 < globalScale)
    (globalCenter : Tube radius)
    (hglobalCenter : globalCenter ∈ finiteMetricCoverCenters
      (activeTubeImage fine ambient) projectedTubePairCoefficientDistance
      globalScale (fun T U => projectedTubePairCoefficientDistance_comm T U))
    (ceiling exponent : Real) (E : Set (Real × Real))
    (hlocalized : ∀ q, q ∈ E →
      let physical := actualProjectedNormFirstOuterSixteenthPhysicalShading
        fine ambient physicalBase hphysicalBase f hfContinuous outerA outerB
      (finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily fine physical.ambient)
        projectedTubePairCoefficientDistance globalScale globalCenter
        (physical.activeAtPoint q)).Nonempty)
    (hambientCBucket : ∀ i, i ∈ ambient → ∀ j, j ∈ ambient →
      |tubeGraphC (fine.tubes i) - tubeGraphC (fine.tubes j)| ≤
        (radius : Real) / 2) :
    let physical := actualProjectedNormFirstOuterSixteenthPhysicalShading
      fine ambient physicalBase hphysicalBase f hfContinuous outerA outerB
    let tubeAt := actualProjectedCenteredHalfTangencyCenterTubeAt fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      ceiling exponent
    ActualCenteredHalfPointRectangleSource E globalCenter tubeAt f
      outerA outerB globalScale := by
  dsimp only
  let physical := actualProjectedNormFirstOuterSixteenthPhysicalShading fine
    ambient physicalBase hphysicalBase f hfContinuous outerA outerB
  let tubeAt := actualProjectedCenteredHalfTangencyCenterTubeAt fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
    exponent
  have hglobalAmbientImage : globalCenter ∈ activeTubeImage fine ambient :=
    finiteMetricCoverCenters_subset (activeTubeImage fine ambient)
      projectedTubePairCoefficientDistance globalScale
      (fun T U => projectedTubePairCoefficientDistance_comm T U)
      hglobalCenter
  obtain ⟨centerIndex, hcenterIndex, hcenterEq⟩ :=
    (mem_activeTubeImage_iff fine ambient globalCenter).mp
      hglobalAmbientImage
  have htubeAtData : ∀ q, q ∈ E →
      ∃ activeIndex, activeIndex ∈ physical.activeAtPoint q ∧
        fine.tubes activeIndex = tubeAt q ∧
        q.2 ∈ centeredFractionIcc outerA outerB (1 / 16 : Real) ∧
        |q.1 - cinematicTraceValue f
          (tubeGraphA (tubeAt q)) (tubeGraphB (tubeAt q))
          (tubeGraphC (tubeAt q)) (tubeGraphD (tubeAt q)) q.2| ≤
            (radius : Real) ∧
        projectedTubePairCoefficientDistance (tubeAt q) globalCenter ≤
          3 * globalScale := by
    intro q hq
    have htubeLocalized :=
      actualProjectedCenteredHalfTangencyCenterTubeAt_mem fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        ceiling exponent q (hlocalized q hq)
    have htubeLocalizedData :
        tubeAt q ∈ actualProjectedAmbientCriticalFamily fine physical.ambient
            (physical.activeAtPoint q) ∧
          projectedTubePairCoefficientDistance (tubeAt q) globalCenter ≤
            3 * globalScale := by
      simpa only [finiteIncidenceNormLocalizedFamilyValue,
        finiteGlobalNormLocalizedFamily, finiteFamilyMetricBall,
        Finset.mem_filter, physical, tubeAt] using htubeLocalized
    have htubeCritical : tubeAt q ∈
        actualProjectedCriticalFamily fine (physical.activeAtPoint q) := by
      rw [← actualProjectedAmbientCriticalFamily_eq_activeAtPoint
        fine physical q]
      exact htubeLocalizedData.1
    have htubeImage : tubeAt q ∈ activeTubeImage fine
        (physical.activeAtPoint q) :=
      selectedTubes_subset
        (activeTubeImage fine (physical.activeAtPoint q)) (radius : Real)
        htubeCritical
    obtain ⟨activeIndex, hactiveIndex, hactiveEq⟩ :=
      (mem_activeTubeImage_iff fine (physical.activeAtPoint q)
        (tubeAt q)).mp htubeImage
    have hcarrier := (physical.mem_activeAtPoint q activeIndex).mp
      hactiveIndex |>.2
    change q ∈ projectedTubeVerticalCarrier f
      (centeredFractionIcc outerA outerB (1 / 16 : Real)) (radius : Real)
      (fine.tubes activeIndex) at hcarrier
    refine ⟨activeIndex, hactiveIndex, hactiveEq, hcarrier.1, ?_,
      htubeLocalizedData.2⟩
    rw [← hactiveEq]
    have hpoint := hcarrier.2
    change |q.1 - cinematicTraceValue f (tubeGraphA (fine.tubes activeIndex)) (tubeGraphB (fine.tubes activeIndex)) (tubeGraphC (fine.tubes activeIndex)) (tubeGraphD (fine.tubes activeIndex)) q.2| ≤ (radius : Real) at hpoint
    exact hpoint
  refine
    { hpointTheta := by
        intro q hq
        obtain ⟨_i, _hi, _heq, htheta, _hpoint, _hcoeff⟩ := htubeAtData q hq
        exact htheta
      hpointTube := by
        intro q hq
        obtain ⟨_i, _hi, _heq, _htheta, hpoint, _hcoeff⟩ :=
          htubeAtData q hq
        exact hpoint
      hcBucket := by
        intro q hq
        obtain ⟨activeIndex, hactiveIndex, hactiveEq, _htheta,
          _hpoint, _hcoefficient⟩ := htubeAtData q hq
        have hactiveAmbient : activeIndex ∈ ambient :=
          (physical.mem_activeAtPoint q activeIndex).mp hactiveIndex |>.1
        change |tubeGraphC globalCenter - tubeGraphC (tubeAt q)| ≤ (radius : Real) / 2
        rw [← hactiveEq, ← hcenterEq]
        exact hambientCBucket centerIndex hcenterIndex activeIndex
          hactiveAmbient
      hcoefficientUpper := by
        intro q hq
        obtain ⟨_activeIndex, _hactiveIndex, _hactiveEq, _htheta,
          _hpoint, hcoefficient⟩ := htubeAtData q hq
        rw [projectedTubePairCoefficientDistance_comm] at hcoefficient
        change tubePairCoefficientDistance globalCenter (tubeAt q) ≤
          6 * globalScale
        exact hcoefficient.trans (by nlinarith [hglobalScale]) }

#print axioms actualProjectedNormFirstOuterSixteenthPhysicalShading
#print axioms ActualCenteredHalfPointRectangleSource
#print axioms actualProjectedCenteredHalfTangencyCenterTubeAt_mem
#print axioms actualCenteredHalfPointRectangleSource_of_outerSixteenthPhysical

end

end FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
