import Family8Grounding.Family8Family7ProjectedCriticalFamilyNonemptyWithoutCapV1
import FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
import Mathlib.Tactic

/-!
# Actual projected norm single-dyadic source without a near-fibre cap, V2

This clean successor makes both multiplicity endpoints explicit when applying
the cap-free critical-family nonemptiness theorem.  V1 is not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ActualProjectedNormSingleDyadicSourceCapFreeV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Family7ProjectedCriticalFamilyNonemptyWithoutCapV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32FiniteIncidenceCriticalScaleMeasurabilityV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

noncomputable section

universe u v

/-- A positive lower multiplicity endpoint alone supplies the nonempty
critical families needed to select one positive norm-scale dyadic cell. -/
theorem exists_actualProjectedAmbientNorm_singleDyadicSource_capFree
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure point)
    (fine : UniformTubeFamily delta iota)
    (physical : FiniteProjectedShading point iota)
    {lower upper : Nat}
    (normCeiling normExponent : Real)
    (hdelta : 0 < delta)
    (hnormCeiling : (delta : Real) ≤ normCeiling)
    (hsourcePos : 0 < mu (physical.multiplicityBand lower upper))
    (hlowerPos : 0 < lower) :
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
    actualProjectedAmbientCriticalFamily_nonempty_on_multiplicityBand_of_lower_pos
      fine physical (lower := lower) (upper := upper) hlowerPos
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

#print axioms exists_actualProjectedAmbientNorm_singleDyadicSource_capFree

end
end Family8ActualProjectedNormSingleDyadicSourceCapFreeV2
