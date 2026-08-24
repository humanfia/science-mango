import FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
import FamilyStickyCinematicL32ActualTubeSeparatedSelectionIdentityV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32ActualProjectedCenteredHalfRetainedTubeFamilyV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteIncidenceCanonicalCriticalCenterV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1
open FamilyStickyCinematicL32ActualTubeSeparatedSelectionIdentityV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Literal retained tube family of the centered-half `Y₁`

This module identifies the image of the final active indices with the exact
tangency filter of the norm-localized actual tube family.  It also proves
that the downstream `selectedTubes` operation is the identity: the source
localized family was already selected at coefficient scale `delta`.
-/

/-- The exact tube-level family retained by the centered-half threshold. -/
noncomputable def actualProjectedCenteredHalfRetainedTubeFamily
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) (q : Real × Real) :
    Finset (Tube radius) :=
  let localized := finiteIncidenceNormLocalizedFamilyValue
    (actualProjectedAmbientCriticalFamily fine physical.ambient)
    projectedTubePairCoefficientDistance globalScale globalCenter
    (physical.activeAtPoint q)
  let center := actualProjectedCenteredHalfTangencyCenterTubeAt fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
    exponent q
  localized.filter fun T =>
    actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
      hOuter hf hf1 (physical.activeAtPoint q) T center ≤ threshold

/-- The actual active-index image is exactly the retained tube filter. -/
theorem activeTubeImage_centeredHalfY1_eq_retained
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) (q : Real × Real)
    (hlocalized : (finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine physical.ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter
      (physical.activeAtPoint q)).Nonempty) :
    let Y1 := actualProjectedCenteredHalfTangencyY1 base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
      exponent threshold
    activeTubeImage fine (Y1.activeAtPoint q) =
      actualProjectedCenteredHalfRetainedTubeFamily fine physical f f1 f2
        outerA outerB hOuter hf hf1 globalScale globalCenter ceiling exponent
        threshold q := by
  dsimp only
  let Y1 := actualProjectedCenteredHalfTangencyY1 base hbase fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
    exponent threshold
  let localized := finiteIncidenceNormLocalizedFamilyValue
    (actualProjectedAmbientCriticalFamily fine physical.ambient)
    projectedTubePairCoefficientDistance globalScale globalCenter
    (physical.activeAtPoint q)
  let tangencyDistance : Finset iota → Tube radius → Tube radius → Real :=
    actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
      hOuter hf hf1
  let tubeAt := actualProjectedCenteredHalfTangencyCenterTubeAt fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
    exponent
  apply Finset.Subset.antisymm
  · intro T hT
    obtain ⟨i, hi, hiEq⟩ :=
      (mem_activeTubeImage_iff fine (Y1.activeAtPoint q) T).mp hT
    have hdata := mem_actualProjectedCenteredHalfTangencyY1_data base hbase
      fine physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
      globalCenter ceiling exponent threshold q i hi
    rw [actualProjectedCenteredHalfRetainedTubeFamily, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · simpa only [localized, hiEq] using hdata.2.1
    · simpa only [actualProjectedCenteredHalfTangencyDistance,
        tangencyDistance, tubeAt, hiEq] using hdata.2.2
  · intro T hT
    rw [actualProjectedCenteredHalfRetainedTubeFamily,
      Finset.mem_filter] at hT
    have hTSource : T ∈ actualProjectedAmbientCriticalFamily fine
        physical.ambient (physical.activeAtPoint q) := by
      exact (Finset.mem_filter.mp hT.1).1
    have hTImage : T ∈ activeTubeImage fine (physical.activeAtPoint q) := by
      have hTSelected : T ∈ actualProjectedCriticalFamily fine
          (physical.activeAtPoint q) := by
        rw [← actualProjectedAmbientCriticalFamily_eq_activeAtPoint
          fine physical q]
        exact hTSource
      exact selectedTubes_subset _ _ hTSelected
    obtain ⟨i, hiPhysical, hiEq⟩ :=
      (mem_activeTubeImage_iff fine (physical.activeAtPoint q) T).mp hTImage
    let familyOfActive :=
      actualProjectedAmbientCriticalFamily fine physical.ambient
    obtain ⟨center, hcenterSome, _hcenterMem⟩ :=
      finiteIncidenceCriticalCenter_exists_mem_of_nonempty physical.ambient
        (fun i q => q ∈ physical.carrier i)
        (finiteIncidenceNormLocalizedFamilyValue familyOfActive
          projectedTubePairCoefficientDistance globalScale globalCenter)
        tangencyDistance (radius : Real) ceiling exponent q
        (by simpa only [familyOfActive, FiniteProjectedShading.activeAtPoint]
          using hlocalized)
    have htubeAt : tubeAt q = center := by
      change (finiteIncidenceLocalizedTangencyCenter physical.ambient
        (fun i q => q ∈ physical.carrier i) familyOfActive
        projectedTubePairCoefficientDistance globalScale globalCenter
        tangencyDistance (radius : Real) ceiling exponent q).getD
          globalCenter = center
      rw [finiteIncidenceLocalizedTangencyCenter, hcenterSome]
      rfl
    apply (mem_activeTubeImage_iff fine (Y1.activeAtPoint q) T).mpr
    refine ⟨i, ?_, hiEq⟩
    apply (FiniteProjectedShading.mem_activeAtPoint Y1 q i).mpr
    have hiAmbient := (physical.mem_activeAtPoint q i).mp hiPhysical |>.1
    refine ⟨hiAmbient, ?_⟩
    change finiteIncidenceLocalizedTangencyCarrierAccept familyOfActive
      projectedTubePairCoefficientDistance globalScale globalCenter
      tangencyDistance fine.tubes threshold i
      (finiteIncidenceActiveAtPoint physical.ambient
        (fun i q => q ∈ physical.carrier i) q)
      (finiteIncidenceLocalizedTangencyCenter physical.ambient
        (fun i q => q ∈ physical.carrier i) familyOfActive
        projectedTubePairCoefficientDistance globalScale globalCenter
        tangencyDistance (radius : Real) ceiling exponent q)
    refine ⟨?_, ?_, ?_⟩
    · simpa only [FiniteProjectedShading.activeAtPoint] using hiPhysical
    · simpa only [familyOfActive, FiniteProjectedShading.activeAtPoint,
        hiEq] using hT.1
    · rw [finiteIncidenceLocalizedTangencyCenter, hcenterSome]
      simpa only [FiniteProjectedShading.activeAtPoint,
        tangencyDistance, tubeAt, hiEq, htubeAt] using hT.2

/-- Every retained tube family is still pairwise coefficient-separated. -/
theorem retainedTubeFamily_pairwise_separated
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) (q : Real × Real) :
    ∀ T, T ∈ actualProjectedCenteredHalfRetainedTubeFamily fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
        exponent threshold q →
      ∀ U, U ∈ actualProjectedCenteredHalfRetainedTubeFamily fine physical
          f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
          ceiling exponent threshold q →
        T ≠ U → (radius : Real) ≤
          projectedTubePairCoefficientDistance T U := by
  intro T hT U hU hTU
  have hTSource : T ∈ actualProjectedAmbientCriticalFamily fine
      physical.ambient (physical.activeAtPoint q) := by
    exact (Finset.mem_filter.mp hT).1 |> Finset.mem_filter.mp |>.1
  have hUSource : U ∈ actualProjectedAmbientCriticalFamily fine
      physical.ambient (physical.activeAtPoint q) := by
    exact (Finset.mem_filter.mp hU).1 |> Finset.mem_filter.mp |>.1
  rw [actualProjectedAmbientCriticalFamily_eq_activeAtPoint fine physical q]
    at hTSource hUSource
  exact selectedTubes_pairwise_separated
    (activeTubeImage fine (physical.activeAtPoint q)) (radius : Real)
    T hTSource U hUSource hTU

/-- The downstream coefficient selection of the final active image is
definitionally lossless. -/
theorem selectedTubes_activeTubeImage_centeredHalfY1_eq_retained
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) (q : Real × Real)
    (hlocalized : (finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine physical.ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter
      (physical.activeAtPoint q)).Nonempty) :
    let Y1 := actualProjectedCenteredHalfTangencyY1 base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
      exponent threshold
    selectedTubes (activeTubeImage fine (Y1.activeAtPoint q))
        (radius : Real) =
      actualProjectedCenteredHalfRetainedTubeFamily fine physical f f1 f2
        outerA outerB hOuter hf hf1 globalScale globalCenter ceiling exponent
        threshold q := by
  dsimp only
  rw [activeTubeImage_centeredHalfY1_eq_retained base hbase fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
    exponent threshold q hlocalized]
  exact selectedTubes_eq_self_of_pairwise_separated _ _
    (retainedTubeFamily_pairwise_separated fine physical f f1 f2 outerA
      outerB hOuter hf hf1 globalScale globalCenter ceiling exponent
      threshold q)

#print axioms actualProjectedCenteredHalfRetainedTubeFamily
#print axioms activeTubeImage_centeredHalfY1_eq_retained
#print axioms retainedTubeFamily_pairwise_separated
#print axioms selectedTubes_activeTubeImage_centeredHalfY1_eq_retained

end

end FamilyStickyCinematicL32ActualProjectedCenteredHalfRetainedTubeFamilyV1
