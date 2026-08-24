import FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CenteredFractionNestingV1
open FamilyStickyCinematicL32Lemma57TubeTangencyDistanceV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Active geometry of the faithful centered-half `Y₁`

Every estimate is unpacked from the literal three-conjunct `Y₁` carrier and
the outer-sixteenth physical carrier.  In particular, the last field is the
actual attained minimum on `J/2`; no interval-comparison premise occurs.
-/

theorem tubePairCoefficientDistance_eq_projected
    {radius : NNReal} (T U : Tube radius) :
    tubePairCoefficientDistance T U =
      projectedTubePairCoefficientDistance T U := by
  rfl

/-- Unpack physical activity, norm localization, and centered-half attained
tangency from one literal `Y₁` active index. -/
theorem mem_actualProjectedCenteredHalfTangencyY1_data
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) (q : Real × Real) (i : iota)
    (hi : i ∈ (actualProjectedCenteredHalfTangencyY1 base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      ceiling exponent threshold).activeAtPoint q) :
    i ∈ physical.activeAtPoint q ∧
      fine.tubes i ∈ finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily fine physical.ambient)
        projectedTubePairCoefficientDistance globalScale globalCenter
        (physical.activeAtPoint q) ∧
      tubePairAttainedTangencyDistance (fine.tubes i)
          (actualProjectedCenteredHalfTangencyCenterTubeAt fine physical
            f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
            ceiling exponent q)
          f f1 f2
          (centeredFractionLeft outerA outerB (1 / 2 : Real))
          (centeredFractionRight outerA outerB (1 / 2 : Real))
          (centered_half_and_quarter_endpoints_ordered hOuter).1
          (fun z _hz => hf z) (fun z _hz => hf1 z) ≤ threshold := by
  let familyOfActive :=
    actualProjectedAmbientCriticalFamily fine physical.ambient
  let tangencyDistance : Finset iota → Tube radius → Tube radius → Real :=
    actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
      hOuter hf hf1
  have hiCarrier :=
    (FiniteProjectedShading.mem_activeAtPoint
      (actualProjectedCenteredHalfTangencyY1 base hbase fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
        exponent threshold) q i).mp hi |>.2
  change finiteIncidenceLocalizedTangencyCarrierAccept familyOfActive
    projectedTubePairCoefficientDistance globalScale globalCenter
    tangencyDistance fine.tubes threshold i
    (finiteIncidenceActiveAtPoint physical.ambient
      (fun i q => q ∈ physical.carrier i) q)
    (finiteIncidenceLocalizedTangencyCenter physical.ambient
      (fun i q => q ∈ physical.carrier i) familyOfActive
      projectedTubePairCoefficientDistance globalScale globalCenter
      tangencyDistance (radius : Real) ceiling exponent q) at hiCarrier
  rcases hiCarrier with ⟨hiPhysical, hiLocalized, hiTangency⟩
  have hiPhysical' : i ∈ physical.activeAtPoint q := by
    simpa only [FiniteProjectedShading.activeAtPoint] using hiPhysical
  have hiLocalized' : fine.tubes i ∈
      finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily fine physical.ambient)
        projectedTubePairCoefficientDistance globalScale globalCenter
        (physical.activeAtPoint q) := by
    simpa only [familyOfActive, FiniteProjectedShading.activeAtPoint] using
      hiLocalized
  let selected := finiteIncidenceLocalizedTangencyCenter physical.ambient
    (fun i q => q ∈ physical.carrier i) familyOfActive
    projectedTubePairCoefficientDistance globalScale globalCenter
    tangencyDistance (radius : Real) ceiling exponent q
  cases hselected : selected with
  | none =>
      simp only [selected, hselected] at hiTangency
  | some center =>
      have hselectedFull : finiteIncidenceLocalizedTangencyCenter
          physical.ambient (fun i q => q ∈ physical.carrier i)
          familyOfActive projectedTubePairCoefficientDistance globalScale
          globalCenter tangencyDistance (radius : Real) ceiling exponent q =
          some center := by
        simpa only [selected] using hselected
      have htubeAt : actualProjectedCenteredHalfTangencyCenterTubeAt fine
          physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
          globalCenter ceiling exponent q = center := by
        change (finiteIncidenceLocalizedTangencyCenter physical.ambient
          (fun i q => q ∈ physical.carrier i) familyOfActive
          projectedTubePairCoefficientDistance globalScale globalCenter
          tangencyDistance (radius : Real) ceiling exponent q).getD
            globalCenter = center
        rw [hselectedFull]
        rfl
      have hiAttained : tangencyDistance
          (finiteIncidenceActiveAtPoint physical.ambient
            (fun i q => q ∈ physical.carrier i) q)
          (fine.tubes i) center ≤ threshold := by
        simpa only [selected, hselected] using hiTangency
      refine ⟨hiPhysical', hiLocalized', ?_⟩
      rw [htubeAt]
      simpa only [tangencyDistance,
        actualProjectedCenteredHalfTangencyDistance] using hiAttained

/-- The selected centered-half centre has a literal physical active index. -/
theorem exists_physical_active_index_eq_centeredHalfCenter
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent : Real) (q : Real × Real)
    (hlocalized : (finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine physical.ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter
      (physical.activeAtPoint q)).Nonempty) :
    ∃ j, j ∈ physical.activeAtPoint q ∧
      fine.tubes j = actualProjectedCenteredHalfTangencyCenterTubeAt fine
        physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
        globalCenter ceiling exponent q := by
  let tubeAt := actualProjectedCenteredHalfTangencyCenterTubeAt fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
    exponent
  have htubeLocalized :=
    actualProjectedCenteredHalfTangencyCenterTubeAt_mem fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
      exponent q hlocalized
  have htubeCritical : tubeAt q ∈
      actualProjectedCriticalFamily fine (physical.activeAtPoint q) := by
    rw [← actualProjectedAmbientCriticalFamily_eq_activeAtPoint
      fine physical q]
    exact (Finset.mem_filter.mp htubeLocalized).1
  have htubeImage : tubeAt q ∈ activeTubeImage fine
      (physical.activeAtPoint q) :=
    selectedTubes_subset (activeTubeImage fine (physical.activeAtPoint q))
      (radius : Real) htubeCritical
  simpa only [tubeAt] using
    (mem_activeTubeImage_iff fine (physical.activeAtPoint q) (tubeAt q)).mp
      htubeImage

/-- The active estimates consumed by the actual q=10 geometry constructor. -/
structure ActualCenteredHalfY1ActiveGeometryFacts
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (E : Set (Real × Real))
    (activeAtPoint : Real × Real → Finset iota)
    (tubeAt : Real × Real → Tube radius)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real) : Prop where
  hactivePhysical : ∀ q, q ∈ E → ∀ i, i ∈ activeAtPoint q →
    i ∈ physical.activeAtPoint q
  hactiveCBucket : ∀ q, q ∈ E → ∀ i, i ∈ activeAtPoint q →
    |tubeGraphC (fine.tubes i) - tubeGraphC (tubeAt q)| ≤
      (radius : Real) / 2
  hactiveFullWitness : ∀ q, q ∈ E → ∀ i, i ∈ activeAtPoint q →
    |cinematicTraceValue f
        (tubeGraphA (fine.tubes i)) (tubeGraphB (fine.tubes i))
        (tubeGraphC (fine.tubes i)) (tubeGraphD (fine.tubes i)) q.2 -
      cinematicTraceValue f
        (tubeGraphA (tubeAt q)) (tubeGraphB (tubeAt q))
        (tubeGraphC (tubeAt q)) (tubeGraphD (tubeAt q)) q.2| ≤
      2 * (radius : Real)
  hactiveCoefficientUpper : ∀ q, q ∈ E → ∀ i,
    i ∈ activeAtPoint q →
    tubePairCoefficientDistance (fine.tubes i) (tubeAt q) ≤ 6 * tGlobal
  hactiveTangencyUpper : ∀ q, q ∈ E → ∀ i,
    i ∈ activeAtPoint q →
    tubePairAttainedTangencyDistance (fine.tubes i) (tubeAt q)
        f f1 f2
        (centeredFractionLeft outerA outerB (1 / 2 : Real))
        (centeredFractionRight outerA outerB (1 / 2 : Real))
        (centered_half_and_quarter_endpoints_ordered hOuter).1
        (fun z _hz => hf z) (fun z _hz => hf1 z) + (radius : Real) ≤
      2 * globalDelta

/-- Produce all active estimates from the actual outer-sixteenth physical
shading and the centered-half `Y₁`. -/
theorem actualCenteredHalfY1ActiveGeometryFacts
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (f f1 f2 : Real → Real) (hfContinuous : Continuous f)
    (outerA outerB : Real) (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) (E : Set (Real × Real))
    (hambientCBucket : ∀ i, i ∈ ambient → ∀ j, j ∈ ambient →
      |tubeGraphC (fine.tubes i) - tubeGraphC (fine.tubes j)| ≤
        (radius : Real) / 2)
    (hdeltaThreshold : (radius : Real) ≤ threshold) :
    let physical := actualProjectedNormFirstOuterSixteenthPhysicalShading
      fine ambient physicalBase hphysicalBase f hfContinuous outerA outerB
    let Y1 := actualProjectedCenteredHalfTangencyY1 base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
      exponent threshold
    let tubeAt := actualProjectedCenteredHalfTangencyCenterTubeAt fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      ceiling exponent
    ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      Y1.activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale threshold := by
  dsimp only
  let physical := actualProjectedNormFirstOuterSixteenthPhysicalShading fine
    ambient physicalBase hphysicalBase f hfContinuous outerA outerB
  let Y1 := actualProjectedCenteredHalfTangencyY1 base hbase fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
    exponent threshold
  let tubeAt := actualProjectedCenteredHalfTangencyCenterTubeAt fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
    exponent
  have hdata : ∀ q i, i ∈ Y1.activeAtPoint q →
      i ∈ physical.activeAtPoint q ∧
        fine.tubes i ∈ finiteIncidenceNormLocalizedFamilyValue
          (actualProjectedAmbientCriticalFamily fine physical.ambient)
          projectedTubePairCoefficientDistance globalScale globalCenter
          (physical.activeAtPoint q) ∧
        tubePairAttainedTangencyDistance (fine.tubes i) (tubeAt q)
          f f1 f2
          (centeredFractionLeft outerA outerB (1 / 2 : Real))
          (centeredFractionRight outerA outerB (1 / 2 : Real))
          (centered_half_and_quarter_endpoints_ordered hOuter).1
          (fun z _hz => hf z) (fun z _hz => hf1 z) ≤ threshold := by
    intro q i hi
    simpa only [Y1, tubeAt] using
      mem_actualProjectedCenteredHalfTangencyY1_data base hbase fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
        exponent threshold q i hi
  have hcenterIndex : ∀ q i, i ∈ Y1.activeAtPoint q →
      ∃ j, j ∈ physical.activeAtPoint q ∧ fine.tubes j = tubeAt q := by
    intro q i hi
    exact exists_physical_active_index_eq_centeredHalfCenter fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
      exponent q ⟨fine.tubes i, (hdata q i hi).2.1⟩
  refine
    { hactivePhysical := by
        intro q _hq i hi
        exact (hdata q i hi).1
      hactiveCBucket := ?_
      hactiveFullWitness := ?_
      hactiveCoefficientUpper := ?_
      hactiveTangencyUpper := ?_ }
  · intro q _hq i hi
    obtain ⟨j, hj, hjEq⟩ := hcenterIndex q i hi
    have hiAmbient := (physical.mem_activeAtPoint q i).mp
      (hdata q i hi).1 |>.1
    have hjAmbient := (physical.mem_activeAtPoint q j).mp hj |>.1
    simpa only [physical, hjEq] using
      hambientCBucket i hiAmbient j hjAmbient
  · intro q _hq i hi
    obtain ⟨j, hj, hjEq⟩ := hcenterIndex q i hi
    have hiCarrier := (physical.mem_activeAtPoint q i).mp
      (hdata q i hi).1 |>.2
    have hjCarrier := (physical.mem_activeAtPoint q j).mp hj |>.2
    change q ∈ projectedTubeVerticalCarrier f
      (centeredFractionIcc outerA outerB (1 / 16 : Real)) (radius : Real)
      (fine.tubes i) at hiCarrier
    change q ∈ projectedTubeVerticalCarrier f
      (centeredFractionIcc outerA outerB (1 / 16 : Real)) (radius : Real)
      (fine.tubes j) at hjCarrier
    have hiError : |q.1 - cinematicTraceValue f
        (tubeGraphA (fine.tubes i)) (tubeGraphB (fine.tubes i))
        (tubeGraphC (fine.tubes i)) (tubeGraphD (fine.tubes i)) q.2| ≤
        (radius : Real) := by
      have hiError' := hiCarrier.2
      change |q.1 - cinematicTraceValue f
        (tubeGraphA (fine.tubes i)) (tubeGraphB (fine.tubes i))
        (tubeGraphC (fine.tubes i)) (tubeGraphD (fine.tubes i)) q.2| ≤
        (radius : Real) at hiError'
      exact hiError'
    have hjError : |q.1 - cinematicTraceValue f
        (tubeGraphA (tubeAt q)) (tubeGraphB (tubeAt q))
        (tubeGraphC (tubeAt q)) (tubeGraphD (tubeAt q)) q.2| ≤
        (radius : Real) := by
      have hjError' := hjCarrier.2
      change |q.1 - cinematicTraceValue f
        (tubeGraphA (fine.tubes j)) (tubeGraphB (fine.tubes j))
        (tubeGraphC (fine.tubes j)) (tubeGraphD (fine.tubes j)) q.2| ≤
        (radius : Real) at hjError'
      rw [hjEq] at hjError'
      exact hjError'
    calc
      |_ - _| ≤ |q.1 - cinematicTraceValue f
          (tubeGraphA (fine.tubes i)) (tubeGraphB (fine.tubes i))
          (tubeGraphC (fine.tubes i)) (tubeGraphD (fine.tubes i)) q.2| +
        |q.1 - cinematicTraceValue f
          (tubeGraphA (tubeAt q)) (tubeGraphB (tubeAt q))
          (tubeGraphC (tubeAt q)) (tubeGraphD (tubeAt q)) q.2| := by
            rw [abs_sub_comm q.1]
            exact abs_sub_le _ _ _
      _ ≤ 2 * (radius : Real) := by linarith
  · intro q _hq i hi
    have hiNorm := (Finset.mem_filter.mp (hdata q i hi).2.1).2
    have hjLocalized :=
      actualProjectedCenteredHalfTangencyCenterTubeAt_mem fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
        exponent q ⟨fine.tubes i, (hdata q i hi).2.1⟩
    have hjNorm := (Finset.mem_filter.mp hjLocalized).2
    rw [projectedTubePairCoefficientDistance_comm] at hjNorm
    have htriangle := projectedTubePairCoefficientDistance_triangle
      (fine.tubes i) globalCenter (tubeAt q)
    rw [tubePairCoefficientDistance_eq_projected]
    exact htriangle.trans (by linarith)
  · intro q _hq i hi
    exact (add_le_add (hdata q i hi).2.2 hdeltaThreshold).trans
      (by ring_nf; exact le_rfl)

#print axioms mem_actualProjectedCenteredHalfTangencyY1_data
#print axioms exists_physical_active_index_eq_centeredHalfCenter
#print axioms ActualCenteredHalfY1ActiveGeometryFacts
#print axioms actualCenteredHalfY1ActiveGeometryFacts

end

end FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
