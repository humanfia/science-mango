import FamilyStickyCinematicL32ActualProjectedNormLocalizedTangencyY1E2V1
import FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CenteredFractionIntervalsV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TubePairTraceV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32FiniteIncidenceCanonicalCriticalCenterV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Literal point source for the norm-localized tangency centre

The physical family is the actual radius-delta vertical trace carrier on the
centered sixteenth interval.  The tangency centre is selected from `F_B(x)`.
Membership in `F_B(x)` supplies its coefficient distance to the fixed norm-
cover centre; membership in the actual critical family supplies a genuine
active tube index and hence the literal point-carrier bounds.
-/

universe u

/-- Clean physical projected family used by the norm-first route. -/
noncomputable def actualProjectedNormFirstSixteenthPhysicalShading
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (f : Real → Real) (hf : Continuous f)
    (A B : Real) : FiniteProjectedShading (Real × Real) iota :=
  finiteProjectedTubeShading fine ambient base hbase f hf
    (centeredFractionIcc A B (1 / 16 : Real)) measurableSet_Icc
    (radius : Real)

/-- Total actual tangency centre after norm localization. -/
noncomputable def actualProjectedNormLocalizedTangencyCenterTubeAt
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real → Real) (TA TB : Real) (hTAB : TA ≤ TB)
    (hfDeriv : ∀ z, z ∈ Icc TA TB → HasDerivAt f (f1 z) z)
    (hf1Deriv : ∀ z, z ∈ Icc TA TB → HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyCeiling tangencyExponent : Real) :
    Real × Real → Tube radius :=
  fun q => (finiteIncidenceLocalizedTangencyCenter physical.ambient
    (fun i x => x ∈ physical.carrier i)
    (actualProjectedAmbientCriticalFamily fine physical.ambient)
    projectedTubePairCoefficientDistance globalScale globalCenter
    (actualProjectedTangencyDistance f f1 f2 TA TB hTAB
      hfDeriv hf1Deriv)
    (radius : Real) tangencyCeiling tangencyExponent q).getD globalCenter

/-- The four literal fields consumed by the Lemma 5.5 point-rectangle
selection. -/
structure ActualNormLocalizedPointRectangleSource
    {radius : NNReal} (E : Set (Real × Real))
    (centerTube : Tube radius) (tubeAt : Real × Real → Tube radius)
    (f : Real → Real) (A B tGlobal : Real) : Prop where
  hpointTheta : ∀ q, q ∈ E →
    q.2 ∈ centeredFractionIcc A B (1 / 16 : Real)
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

/-- On a retained point, the total centre is an actual member of `F_B(x)`. -/
theorem actualProjectedNormLocalizedTangencyCenterTubeAt_mem
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real → Real) (TA TB : Real) (hTAB : TA ≤ TB)
    (hfDeriv : ∀ z, z ∈ Icc TA TB → HasDerivAt f (f1 z) z)
    (hf1Deriv : ∀ z, z ∈ Icc TA TB → HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyCeiling tangencyExponent : Real) (q : Real × Real)
    (hlocalized :
      (finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily fine physical.ambient)
        projectedTubePairCoefficientDistance globalScale globalCenter
        (physical.activeAtPoint q)).Nonempty) :
    actualProjectedNormLocalizedTangencyCenterTubeAt fine physical
        f f1 f2 TA TB hTAB hfDeriv hf1Deriv globalScale globalCenter
        tangencyCeiling tangencyExponent q ∈
      finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily fine physical.ambient)
        projectedTubePairCoefficientDistance globalScale globalCenter
        (physical.activeAtPoint q) := by
  let familyOfActive :=
    actualProjectedAmbientCriticalFamily fine physical.ambient
  let tangencyDistance : Finset iota → Tube radius → Tube radius → Real :=
    actualProjectedTangencyDistance f f1 f2 TA TB hTAB hfDeriv hf1Deriv
  have hlocalizedFinite :
      (finiteIncidenceNormLocalizedFamilyValue familyOfActive
        projectedTubePairCoefficientDistance globalScale globalCenter
        (finiteIncidenceActiveAtPoint physical.ambient
          (fun i x => x ∈ physical.carrier i) q)).Nonempty := by
    simpa only [familyOfActive, FiniteProjectedShading.activeAtPoint] using
      hlocalized
  obtain ⟨center, hcenterSome, hcenterMem⟩ :=
    finiteIncidenceCriticalCenter_exists_mem_of_nonempty physical.ambient
      (fun i x => x ∈ physical.carrier i)
      (finiteIncidenceNormLocalizedFamilyValue familyOfActive
        projectedTubePairCoefficientDistance globalScale globalCenter)
      tangencyDistance (radius : Real) tangencyCeiling tangencyExponent q
      hlocalizedFinite
  have htubeAt :
      actualProjectedNormLocalizedTangencyCenterTubeAt fine physical
          f f1 f2 TA TB hTAB hfDeriv hf1Deriv globalScale globalCenter
          tangencyCeiling tangencyExponent q = center := by
    change (finiteIncidenceCriticalCenter physical.ambient
      (fun i x => x ∈ physical.carrier i)
      (finiteIncidenceNormLocalizedFamilyValue familyOfActive
        projectedTubePairCoefficientDistance globalScale globalCenter)
      tangencyDistance (radius : Real) tangencyCeiling tangencyExponent q).getD
        globalCenter = center
    rw [hcenterSome]
    rfl
  rw [htubeAt]
  simpa only [familyOfActive, FiniteProjectedShading.activeAtPoint] using
    hcenterMem

/-- Actual ambient half-c localization plus membership in the norm-localized
family produce every point-rectangle source field. -/
theorem actualNormLocalizedPointRectangleSource_of_sixteenthPhysical
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (f : Real → Real) (hf : Continuous f) (A B : Real)
    (f1 f2 : Real → Real) (TA TB : Real) (hTAB : TA ≤ TB)
    (hfDeriv : ∀ z, z ∈ Icc TA TB → HasDerivAt f (f1 z) z)
    (hf1Deriv : ∀ z, z ∈ Icc TA TB → HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (hglobalScale : 0 < globalScale)
    (globalCenter : Tube radius)
    (hglobalCenter : globalCenter ∈ finiteMetricCoverCenters
      (activeTubeImage fine ambient) projectedTubePairCoefficientDistance
      globalScale (fun T U => projectedTubePairCoefficientDistance_comm T U))
    (tangencyCeiling tangencyExponent : Real)
    (E : Set (Real × Real))
    (hlocalized : ∀ q, q ∈ E →
      let physical := actualProjectedNormFirstSixteenthPhysicalShading
        fine ambient base hbase f hf A B
      (finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily fine physical.ambient)
        projectedTubePairCoefficientDistance globalScale globalCenter
        (physical.activeAtPoint q)).Nonempty)
    (hambientCBucket : ∀ i, i ∈ ambient → ∀ j, j ∈ ambient →
      |tubeGraphC (fine.tubes i) - tubeGraphC (fine.tubes j)| ≤
        (radius : Real) / 2) :
    let physical := actualProjectedNormFirstSixteenthPhysicalShading
      fine ambient base hbase f hf A B
    let tubeAt := actualProjectedNormLocalizedTangencyCenterTubeAt
      fine physical f f1 f2 TA TB hTAB hfDeriv hf1Deriv globalScale
      globalCenter tangencyCeiling tangencyExponent
    ActualNormLocalizedPointRectangleSource E globalCenter tubeAt f A B
      globalScale := by
  dsimp only
  let physical := actualProjectedNormFirstSixteenthPhysicalShading
    fine ambient base hbase f hf A B
  let tubeAt := actualProjectedNormLocalizedTangencyCenterTubeAt
    fine physical f f1 f2 TA TB hTAB hfDeriv hf1Deriv globalScale
    globalCenter tangencyCeiling tangencyExponent
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
        q.2 ∈ centeredFractionIcc A B (1 / 16 : Real) ∧
        |q.1 - cinematicTraceValue f
          (tubeGraphA (tubeAt q)) (tubeGraphB (tubeAt q))
          (tubeGraphC (tubeAt q)) (tubeGraphD (tubeAt q)) q.2| ≤
            (radius : Real) ∧
        projectedTubePairCoefficientDistance (tubeAt q) globalCenter ≤
          3 * globalScale := by
    intro q hq
    have htubeLocalized :=
      actualProjectedNormLocalizedTangencyCenterTubeAt_mem fine physical
        f f1 f2 TA TB hTAB hfDeriv hf1Deriv globalScale globalCenter
        tangencyCeiling tangencyExponent q (hlocalized q hq)
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
    have htubeImage : tubeAt q ∈
        activeTubeImage fine (physical.activeAtPoint q) :=
      selectedTubes_subset
        (activeTubeImage fine (physical.activeAtPoint q)) (radius : Real)
        htubeCritical
    obtain ⟨activeIndex, hactiveIndex, hactiveEq⟩ :=
      (mem_activeTubeImage_iff fine (physical.activeAtPoint q)
        (tubeAt q)).mp htubeImage
    have hcarrier := (physical.mem_activeAtPoint q activeIndex).mp
      hactiveIndex |>.2
    change q ∈ projectedTubeVerticalCarrier f
      (centeredFractionIcc A B (1 / 16 : Real)) (radius : Real)
      (fine.tubes activeIndex) at hcarrier
    refine ⟨activeIndex, hactiveIndex, hactiveEq, hcarrier.1, ?_,
      htubeLocalizedData.2⟩
    rw [← hactiveEq]
    exact hcarrier.2
  refine
    { hpointTheta := by
        intro q hq
        obtain ⟨_activeIndex, _hactiveIndex, _hactiveEq, htheta,
          _hpoint, _hcoefficient⟩ := htubeAtData q hq
        exact htheta
      hpointTube := by
        intro q hq
        obtain ⟨_activeIndex, _hactiveIndex, _hactiveEq, _htheta,
          hpoint, _hcoefficient⟩ := htubeAtData q hq
        exact hpoint
      hcBucket := by
        intro q hq
        obtain ⟨activeIndex, hactiveIndex, hactiveEq, _htheta,
          _hpoint, _hcoefficient⟩ := htubeAtData q hq
        have hactiveAmbient : activeIndex ∈ ambient :=
          (physical.mem_activeAtPoint q activeIndex).mp hactiveIndex |>.1
        have htubeAtEq : fine.tubes activeIndex =
            actualProjectedNormLocalizedTangencyCenterTubeAt fine
              (actualProjectedNormFirstSixteenthPhysicalShading fine ambient
                base hbase f hf A B) f f1 f2 TA TB hTAB hfDeriv hf1Deriv
              globalScale globalCenter tangencyCeiling tangencyExponent q := by
          simpa only [tubeAt, physical] using hactiveEq
        rw [← htubeAtEq, ← hcenterEq]
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

#print axioms actualProjectedNormFirstSixteenthPhysicalShading
#print axioms actualProjectedNormLocalizedTangencyCenterTubeAt
#print axioms ActualNormLocalizedPointRectangleSource
#print axioms actualProjectedNormLocalizedTangencyCenterTubeAt_mem
#print axioms actualNormLocalizedPointRectangleSource_of_sixteenthPhysical

end

end FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
