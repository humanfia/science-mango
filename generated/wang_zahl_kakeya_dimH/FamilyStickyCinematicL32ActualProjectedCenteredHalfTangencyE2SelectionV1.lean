import FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
import FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyE2SelectionV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteIncidenceCanonicalCriticalCenterV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyY1E2AfterNormCoverV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

noncomputable section

universe u v

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-! # Positive multiplicity `E₂` for the centered-half tangency stage -/

theorem setNonempty_of_measure_pos
    {point : Type v} [MeasurableSpace point]
    (mu : Measure point) {E : Set point} (hE : 0 < mu E) : E.Nonempty := by
  by_contra hEmpty
  have hEq : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hEmpty
  rw [hEq] at hE
  simp at hE

/-- The canonical centered-half tangency centre itself supplies one literal
active `Y₁` index. -/
theorem activeAtPoint_actualProjectedCenteredHalfTangencyY1_nonempty
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) (hthreshold : 0 ≤ threshold)
    (x : point)
    (hlocalized : (finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine physical.ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter
      (physical.activeAtPoint x)).Nonempty) :
    ((actualProjectedCenteredHalfTangencyY1 base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
      exponent threshold).activeAtPoint x).Nonempty := by
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
  have hcenterData : center ∈
      actualProjectedAmbientCriticalFamily fine physical.ambient
          (physical.activeAtPoint x) ∧
        projectedTubePairCoefficientDistance center globalCenter ≤
          3 * globalScale := by
    simpa only [finiteIncidenceNormLocalizedFamilyValue,
      finiteGlobalNormLocalizedFamily, finiteFamilyMetricBall,
      Finset.mem_filter, familyOfActive,
      FiniteProjectedShading.activeAtPoint] using hcenterMem
  have hcenterSelected : center ∈
      actualProjectedCriticalFamily fine (physical.activeAtPoint x) := by
    rw [← actualProjectedAmbientCriticalFamily_eq_activeAtPoint
      fine physical x]
    exact hcenterData.1
  have hcenterImage : center ∈ activeTubeImage fine
      (physical.activeAtPoint x) :=
    selectedTubes_subset
      (activeTubeImage fine (physical.activeAtPoint x)) (radius : Real)
      hcenterSelected
  obtain ⟨i, hiActive, hiCenter⟩ :=
    (mem_activeTubeImage_iff fine (physical.activeAtPoint x) center).mp
      hcenterImage
  have hiAmbient : i ∈ physical.ambient :=
    (physical.mem_activeAtPoint x i).mp hiActive |>.1
  refine ⟨i, (FiniteProjectedShading.mem_activeAtPoint
    (actualProjectedCenteredHalfTangencyY1 base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
      exponent threshold) x i).mpr ⟨hiAmbient, ?_⟩⟩
  change finiteIncidenceLocalizedTangencyCarrierAccept familyOfActive
    projectedTubePairCoefficientDistance globalScale globalCenter
    tangencyDistance fine.tubes threshold i
    (finiteIncidenceActiveAtPoint physical.ambient
      (fun i x => x ∈ physical.carrier i) x)
    (finiteIncidenceLocalizedTangencyCenter physical.ambient
      (fun i x => x ∈ physical.carrier i) familyOfActive
      projectedTubePairCoefficientDistance globalScale globalCenter
      tangencyDistance (radius : Real) ceiling exponent x)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [FiniteProjectedShading.activeAtPoint] using hiActive
  · simpa only [FiniteProjectedShading.activeAtPoint, hiCenter,
      familyOfActive] using hcenterMem
  · rw [finiteIncidenceLocalizedTangencyCenter, hcenterSome, hiCenter]
    exact (actualProjectedCenteredHalfTangencyDistance_self f f1 f2
      outerA outerB hOuter hf hf1
      (finiteIncidenceActiveAtPoint physical.ambient
        (fun i x => x ∈ physical.carrier i) x) center).le.trans hthreshold

/-- Positive measurable `E₂` selection for the faithful centered-half `Y₁`.
The lower and upper multiplicity-bin bounds are conclusions. -/
theorem exists_actualProjectedCenteredHalfTangencyE2
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure point) (base : Set point) (hbase : MeasurableSet base)
    (hbasePos : 0 < mu base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) (hthreshold : 0 ≤ threshold)
    (hlocalized : ∀ x, x ∈ base →
      (finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily fine physical.ambient)
        projectedTubePairCoefficientDistance globalScale globalCenter
        (physical.activeAtPoint x)).Nonempty) :
    let Y1 := actualProjectedCenteredHalfTangencyY1 base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
      exponent threshold
    ∃ label ∈ Finset.Icc (dyadicCeilBucket 1)
        (dyadicCeilBucket (Y1.ambient.card : Real)),
      let E2 := projectedPositiveMultiplicityDyadicCell Y1 label
      mu base /
          (continuumCriticalSingleDyadicBinFactor 1
            (Y1.ambient.card : Real) : ENNReal) ≤ mu E2 ∧
      0 < mu E2 ∧ E2.Nonempty ∧ MeasurableSet E2 ∧ E2 ⊆ base ∧
      (∀ x, x ∈ E2 → (Y1.activeAtPoint x).Nonempty) ∧
      0 < dyadicCeilUpper label ∧
      ∀ x ∈ E2,
        dyadicCeilUpper label / 2 < projectedActiveMultiplicity Y1 x ∧
          projectedActiveMultiplicity Y1 x ≤ dyadicCeilUpper label := by
  dsimp only
  let Y1 := actualProjectedCenteredHalfTangencyY1 base hbase fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
    exponent threshold
  have hbaseNonempty : base.Nonempty := setNonempty_of_measure_pos mu hbasePos
  have hactive : ∀ x, x ∈ Y1.base →
      (Y1.activeAtPoint x).Nonempty := by
    intro x hx
    apply activeAtPoint_actualProjectedCenteredHalfTangencyY1_nonempty
      base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent threshold hthreshold x
    change x ∈ base at hx
    exact hlocalized x hx
  have hY1Base : Y1.base = base := rfl
  obtain ⟨label, hlabel, hmeasure, hlabelPos, hmeasurable, hsubset,
      hbin⟩ :=
    exists_projectedPositiveMultiplicityDyadicCell mu Y1
      (by simpa [hY1Base] using hbaseNonempty) hactive
  let E2 := projectedPositiveMultiplicityDyadicCell Y1 label
  have hquotPos :
      0 < mu Y1.base /
        (continuumCriticalSingleDyadicBinFactor 1
          (Y1.ambient.card : Real) : ENNReal) :=
    ENNReal.div_pos (ne_of_gt (by simpa [hY1Base] using hbasePos))
      (ENNReal.natCast_ne_top _)
  have hE2Pos : 0 < mu E2 :=
    hquotPos.trans_le (by simpa [E2] using hmeasure)
  refine ⟨label, hlabel, ?_, hE2Pos, setNonempty_of_measure_pos mu hE2Pos,
    ?_, ?_, ?_, hlabelPos, ?_⟩
  · simpa [E2, hY1Base] using hmeasure
  · simpa [E2] using hmeasurable
  · intro x hx
    have hxY1 : x ∈ Y1.base := hsubset (by simpa [E2] using hx)
    simpa [hY1Base] using hxY1
  · intro x hx
    exact hactive x (hsubset (by simpa [E2] using hx))
  · simpa [E2] using hbin

#print axioms activeAtPoint_actualProjectedCenteredHalfTangencyY1_nonempty
#print axioms exists_actualProjectedCenteredHalfTangencyE2

end

end FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyE2SelectionV1
