import Family8Grounding.Family8ActualProjectedNormSingleDyadicSourceCapFreeV2
import FamilyStickyCinematicL32ActualProjectedNormCellRadiusDominanceV1
import FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
import FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
import FamilyStickyCinematicL32FiniteIncidenceCriticalScaleMeasurabilityV1
import FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverAllCellsRunV1
import FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
import FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
import Mathlib.Tactic

/-!
# Norm-first all-centre cells without a near-fibre cap, V3

Clean successor of the frozen V2 draft with direct imports for every
all-centre cover primitive and an explicit decidable equality on tubes.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ActualProjectedNormFirstAllCenterCellsCapFreeV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8ActualProjectedNormSingleDyadicSourceCapFreeV2
open Family8Family7ProjectedCriticalFamilyNonemptyWithoutCapV1
open FamilyStickyCinematicL32ActualProjectedNormCellRadiusDominanceV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
open FamilyStickyCinematicL32FiniteIncidenceCriticalScaleMeasurabilityV1
open FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverAllCellsRunV1
open FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverCellV1
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1

noncomputable section

universe u v

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-- Cap-free all-centre norm-cell partition and localization on the same
physical datum. -/
theorem exists_actualProjectedNormFirst_allCenterCells_capFree
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure point)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    {lower upper : Nat}
    (normCeiling normExponent : Real)
    (hdelta : 0 < radius)
    (hnormCeiling : (radius : Real) ≤ normCeiling)
    (hsourcePos : 0 < mu (physical.multiplicityBand lower upper))
    (hlowerPos : 0 < lower) :
    let normScale := actualProjectedAmbientNormScale fine physical
      normCeiling normExponent
    ∃ normLabel ∈ Finset.Icc (dyadicCeilBucket (radius : Real))
        (dyadicCeilBucket normCeiling),
      let E_norm := continuumCriticalSingleDyadicCell
        (physical.multiplicityBand lower upper) normScale normLabel
      let globalScale := dyadicCeilUpper normLabel
      let familyOfActive :=
        actualProjectedAmbientCriticalFamily fine physical.ambient
      let normDistance := projectedTubePairCoefficientDistance
      mu (physical.multiplicityBand lower upper) /
          (continuumCriticalSingleDyadicBinFactor (radius : Real)
            normCeiling : ENNReal) ≤ mu E_norm ∧
      0 < mu E_norm ∧ E_norm.Nonempty ∧ MeasurableSet E_norm ∧
      E_norm ⊆ physical.multiplicityBand lower upper ∧
      0 < globalScale ∧ (radius : Real) ≤ globalScale ∧
      (∀ x ∈ E_norm,
        globalScale / 2 < normScale x ∧ normScale x ≤ globalScale) ∧
      ∃ fallback : FiniteMetricMember (activeTubeImage fine physical.ambient),
        let centers := finiteMetricCoverCenters
          (activeTubeImage fine physical.ambient) normDistance globalScale
          (fun T U ↦ projectedTubePairCoefficientDistance_comm T U)
        let label := finiteIncidenceNormGlobalCoverLabel physical.ambient
          (fun i x ↦ x ∈ physical.carrier i)
          (activeTubeImage fine physical.ambient) fallback familyOfActive
          normDistance (radius : Real) normCeiling normExponent globalScale
          (fun T U ↦ projectedTubePairCoefficientDistance_comm T U)
        mu E_norm = ∑ center ∈ centers,
            mu (measurableLabelCell E_norm label center) ∧
        (∀ x ∈ E_norm, label x ∈ centers) ∧
        ∀ center, center ∈ centers →
          MeasurableSet (measurableLabelCell E_norm label center) ∧
          measurableLabelCell E_norm label center ⊆ E_norm ∧
          ∀ x, x ∈ measurableLabelCell E_norm label center →
            let active := physical.activeAtPoint x
            let localFamily := familyOfActive active
            ∃ hlocalFamily : localFamily.Nonempty,
              let localBall := finiteNormCriticalBall localFamily normDistance
                (radius : Real) normCeiling normExponent hlocalFamily
              let localized := finiteGlobalNormLocalizedFamily localFamily
                normDistance globalScale center
              localBall ⊆ localized ∧
                localBall.card ≤ localized.card := by
  dsimp only
  obtain ⟨normLabel, hnormLabel, hnormMeasure, hnormPos,
      hnormNonempty, hnormMeasurable, hnormSubset, hglobalScale,
      hnormBin⟩ :=
    exists_actualProjectedAmbientNorm_singleDyadicSource_capFree
      mu fine physical normCeiling normExponent hdelta hnormCeiling
        hsourcePos hlowerPos
  let normScale := actualProjectedAmbientNormScale fine physical
    normCeiling normExponent
  let E_norm := continuumCriticalSingleDyadicCell
    (physical.multiplicityBand lower upper) normScale normLabel
  let globalScale := dyadicCeilUpper normLabel
  let familyOfActive :=
    actualProjectedAmbientCriticalFamily fine physical.ambient
  let normDistance : Tube radius → Tube radius → Real :=
    projectedTubePairCoefficientDistance
  let hfamilyBand :=
    actualProjectedAmbientCriticalFamily_nonempty_on_multiplicityBand_of_lower_pos
      fine physical (lower := lower) (upper := upper) hlowerPos
  have hfamilyFinite : ∀ x ∈ E_norm,
      (familyOfActive (finiteIncidenceActiveAtPoint physical.ambient
        (fun i x ↦ x ∈ physical.carrier i) x)).Nonempty := by
    intro x hx
    have hxBand : x ∈ physical.multiplicityBand lower upper := hnormSubset hx
    simpa only [familyOfActive, FiniteProjectedShading.activeAtPoint] using
      hfamilyBand x hxBand
  have hnormUpperFromBin : ∀ x, ∀ hx : x ∈ E_norm,
      finiteCriticalMaximizerScale
          (familyOfActive (finiteIncidenceActiveAtPoint physical.ambient
            (fun i x ↦ x ∈ physical.carrier i) x))
          normDistance (radius : Real) normCeiling normExponent
          (hfamilyFinite x hx) ≤ globalScale := by
    intro x hx
    have hupper := (hnormBin x hx).2
    simpa only [normScale, globalScale, familyOfActive, normDistance,
      actualProjectedAmbientNormScale, finiteIncidenceCriticalScale,
      finiteIncidenceCriticalScaleValue, dif_pos (hfamilyFinite x hx)] using
      hupper
  have hradiusGlobalScale : (radius : Real) ≤ globalScale := by
    apply radius_le_dyadicUpper_of_nonempty_actual_norm_cell
      fine physical normCeiling normExponent hnormCeiling normLabel E_norm
      hnormNonempty
    · intro x hx
      exact hfamilyBand x (hnormSubset hx)
    · intro x hx
      exact (hnormBin x hx).2
  obtain ⟨fallback, hpartition, hlabelRange, hcells⟩ :=
    exists_normGlobalCoverAllCells_with_local_retention
      mu E_norm hnormMeasurable hnormNonempty physical.ambient
      (fun i x ↦ x ∈ physical.carrier i)
      (fun i hi ↦ physical.measurable_carrier i hi)
      (activeTubeImage fine physical.ambient) familyOfActive normDistance
      hfamilyFinite
      (fun active ↦ actualProjectedAmbientCriticalFamily_subset fine
        physical.ambient active)
      (fun T U ↦ projectedTubePairCoefficientDistance_comm T U)
      (fun T U V ↦ projectedTubePairCoefficientDistance_triangle T U V)
      (fun T _hT ↦ projectedTubePairCoefficientDistance_self T)
      (by exact_mod_cast hdelta.le) hnormCeiling hglobalScale
      hnormUpperFromBin
  refine ⟨normLabel, hnormLabel, hnormMeasure, hnormPos, hnormNonempty,
    hnormMeasurable, hnormSubset, hglobalScale, hradiusGlobalScale,
    hnormBin, fallback, ?_, ?_, ?_⟩
  · simpa [E_norm, globalScale, familyOfActive, normDistance] using hpartition
  · simpa [E_norm, globalScale, familyOfActive, normDistance] using hlabelRange
  · simpa only [E_norm, globalScale, familyOfActive, normDistance,
      FiniteProjectedShading.activeAtPoint] using hcells

#print axioms exists_actualProjectedNormFirst_allCenterCells_capFree

end
end Family8ActualProjectedNormFirstAllCenterCellsCapFreeV3
