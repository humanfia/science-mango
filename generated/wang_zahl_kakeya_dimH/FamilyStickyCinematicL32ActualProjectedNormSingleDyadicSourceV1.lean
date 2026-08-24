import FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
import FamilyStickyCinematicL32FiniteIncidenceCriticalScaleMeasurabilityV1
import FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32FiniteIncidenceCriticalScaleMeasurabilityV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1

noncomputable section

/-!
# Actual norm-scale dyadic source before the global function-space cover

The selected norm scale is a finite-pattern function of the literal projected
incidences.  A positive-measure multiplicity slice therefore has one positive-
measure dyadic cell.  On that cell the global scale is the dyadic upper
endpoint, so both its positivity and every pointwise norm-scale upper bound
are conclusions.
-/

universe u v

/-- Total actual norm critical scale, with the honest lower-endpoint fallback
on incidence patterns whose normalized family is empty. -/
noncomputable def actualProjectedAmbientNormScale
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (physical : FiniteProjectedShading point iota)
    (normCeiling normExponent : Real) : point → Real :=
  finiteIncidenceCriticalScale physical.ambient
    (fun i x => x ∈ physical.carrier i)
    (actualProjectedAmbientCriticalFamily fine physical.ambient)
    (fun _active => projectedTubePairCoefficientDistance)
    (delta : Real) normCeiling normExponent

theorem measurable_actualProjectedAmbientNormScale
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (physical : FiniteProjectedShading point iota)
    (normCeiling normExponent : Real) :
    Measurable
      (actualProjectedAmbientNormScale fine physical normCeiling
        normExponent) := by
  exact measurable_finiteIncidenceCriticalScale physical.ambient
    (fun i x => x ∈ physical.carrier i)
    (fun i hi => physical.measurable_carrier i hi)
    (actualProjectedAmbientCriticalFamily fine physical.ambient)
    (fun _active => projectedTubePairCoefficientDistance)
    (delta : Real) normCeiling normExponent

/-- On an actual nonempty incidence pattern the total norm scale is the
canonical maximizer scale and lies in its compact source interval. -/
theorem actualProjectedAmbientNormScale_bounds
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (physical : FiniteProjectedShading point iota)
    {normCeiling normExponent : Real}
    (hnormCeiling : (delta : Real) ≤ normCeiling)
    (x : point)
    (hfamily :
      (actualProjectedAmbientCriticalFamily fine physical.ambient
        (physical.activeAtPoint x)).Nonempty) :
    (delta : Real) ≤
        actualProjectedAmbientNormScale fine physical normCeiling
          normExponent x ∧
      actualProjectedAmbientNormScale fine physical normCeiling
          normExponent x ≤ normCeiling := by
  have hfamilyFinite :
      (actualProjectedAmbientCriticalFamily fine physical.ambient
        (finiteIncidenceActiveAtPoint physical.ambient
          (fun i x => x ∈ physical.carrier i) x)).Nonempty := by
    simpa only [FiniteProjectedShading.activeAtPoint] using hfamily
  rw [actualProjectedAmbientNormScale, finiteIncidenceCriticalScale,
    finiteIncidenceCriticalScaleValue, dif_pos hfamilyFinite]
  exact finiteCriticalMaximizerScale_bounds
    (actualProjectedAmbientCriticalFamily fine physical.ambient
      (finiteIncidenceActiveAtPoint physical.ambient
        (fun i x => x ∈ physical.carrier i) x))
    projectedTubePairCoefficientDistance hfamilyFinite hnormCeiling

/-- Positive measure gives a genuine point; this elementary measure fact is
kept in the clean norm-first closure. -/
theorem nonempty_of_measure_pos
    {point : Type v} [MeasurableSpace point]
    (mu : Measure point) {E : Set point} (hE : 0 < mu E) : E.Nonempty := by
  by_contra hEmpty
  have hEq : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hEmpty
  rw [hEq] at hE
  simp at hE

/-- The actual positive-measure norm single-dyadic cell.  Its nonemptiness,
measurability, source containment, and pointwise scale upper bound are all
produced, not assumed. -/
theorem exists_actualProjectedAmbientNorm_singleDyadicSource
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure point)
    (fine : UniformTubeFamily delta iota)
    (physical : FiniteProjectedShading point iota)
    {lower upper multiplicity : Nat}
    (normCeiling normExponent : Real)
    (hdelta : 0 < delta)
    (hnormCeiling : (delta : Real) ≤ normCeiling)
    (hsourcePos : 0 < mu (physical.multiplicityBand lower upper))
    (hmultiplicity : 0 < multiplicity)
    (hlower : 3 * multiplicity ≤ lower)
    (hpair : ∀ x, x ∈ physical.multiplicityBand lower upper →
      Set.Pairwise (physical.activeAtPoint x : Set iota) fun i j =>
        EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (hactiveCap : ∀ x, x ∈ physical.multiplicityBand lower upper →
      ∀ center,
        center ∈ actualProjectedCriticalFamily fine
          (physical.activeAtPoint x) →
        (activeNearCoefficientIndices fine (physical.activeAtPoint x) center
          (delta : Real)).card ≤ multiplicity) :
    let scale := actualProjectedAmbientNormScale fine physical normCeiling
      normExponent
    ∃ label ∈ Finset.Icc (dyadicCeilBucket (delta : Real))
        (dyadicCeilBucket normCeiling),
      let E_norm := continuumCriticalSingleDyadicCell
        (physical.multiplicityBand lower upper) scale label
      mu (physical.multiplicityBand lower upper) /
          (continuumCriticalSingleDyadicBinFactor (delta : Real)
            normCeiling : ENNReal) ≤ mu E_norm ∧
      0 < mu E_norm ∧ E_norm.Nonempty ∧ MeasurableSet E_norm ∧
      E_norm ⊆ physical.multiplicityBand lower upper ∧
      0 < dyadicCeilUpper label ∧
      ∀ x ∈ E_norm,
        dyadicCeilUpper label / 2 < scale x ∧
        scale x ≤ dyadicCeilUpper label := by
  dsimp only
  let hfamily :=
    actualProjectedAmbientCriticalFamily_nonempty_on_multiplicityBand
      fine physical hdelta hmultiplicity hlower hpair hactiveCap
  let scale := actualProjectedAmbientNormScale fine physical normCeiling
    normExponent
  have hscaleBounds : ∀ x ∈ physical.multiplicityBand lower upper,
      (delta : Real) ≤ scale x ∧ scale x ≤ normCeiling := by
    intro x hx
    exact actualProjectedAmbientNormScale_bounds fine physical hnormCeiling x
      (hfamily x hx)
  obtain ⟨label, hlabel, hmeasure, hlabelPos, hbin⟩ :=
    exists_continuumCritical_single_dyadic_selection mu scale
      (FiniteProjectedShading.measurableSet_multiplicityBand physical
        lower upper)
      (by exact_mod_cast hdelta) hnormCeiling
      (measurable_actualProjectedAmbientNormScale fine physical
        normCeiling normExponent)
      hscaleBounds
  let E_norm := continuumCriticalSingleDyadicCell
    (physical.multiplicityBand lower upper) scale label
  have hquotPos :
      0 < mu (physical.multiplicityBand lower upper) /
        (continuumCriticalSingleDyadicBinFactor (delta : Real)
          normCeiling : ENNReal) :=
    ENNReal.div_pos (ne_of_gt hsourcePos) (ENNReal.natCast_ne_top _)
  have hcellPos : 0 < mu E_norm := hquotPos.trans_le hmeasure
  refine ⟨label, hlabel, hmeasure, hcellPos,
    nonempty_of_measure_pos mu hcellPos, ?_, ?_, hlabelPos, hbin⟩
  · exact measurableSet_continuumCriticalSingleDyadicCell
      (FiniteProjectedShading.measurableSet_multiplicityBand physical
        lower upper)
      (measurable_actualProjectedAmbientNormScale fine physical
        normCeiling normExponent) label
  · intro x hx
    exact hx.1

#print axioms actualProjectedAmbientNormScale
#print axioms measurable_actualProjectedAmbientNormScale
#print axioms actualProjectedAmbientNormScale_bounds
#print axioms nonempty_of_measure_pos
#print axioms exists_actualProjectedAmbientNorm_singleDyadicSource

end

end FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
