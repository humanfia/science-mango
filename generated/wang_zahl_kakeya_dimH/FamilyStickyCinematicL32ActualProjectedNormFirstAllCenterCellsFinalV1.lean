import FamilyStickyCinematicL32ActualProjectedNormCellRadiusDominanceV1
import FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
import FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverAllCellsRunV1

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32ActualProjectedNormFirstAllCenterCellsFinalV1

open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32FiniteIncidenceCriticalScaleMeasurabilityV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ActualProjectedNormCellRadiusDominanceV1
open FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverCellV1
open FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverAllCellsRunV1

noncomputable section

universe u v

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Norm-first selection with every global-cover cell retained

The norm dyadic scale is still selected once.  At that fixed scale, however,
the measurable norm-cover cells are kept as an exact partition and every
cell receives its automatically derived critical-ball localization.  There
is no centre-cardinality pigeonhole loss.
-/

theorem exists_actualProjectedNormFirst_allCenterCells
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure point)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    {lower upper multiplicity : Nat}
    (normCeiling normExponent : Real)
    (hdelta : 0 < radius)
    (hnormCeiling : (radius : Real) ≤ normCeiling)
    (hsourcePos : 0 < mu (physical.multiplicityBand lower upper))
    (hmultiplicity : 0 < multiplicity)
    (hlower : 3 * multiplicity ≤ lower)
    (hpair : ∀ x, x ∈ physical.multiplicityBand lower upper →
      Set.Pairwise (physical.activeAtPoint x : Set iota) fun i j ↦
        EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (hactiveCap : ∀ x, x ∈ physical.multiplicityBand lower upper →
      ∀ center,
        center ∈ actualProjectedCriticalFamily fine
          (physical.activeAtPoint x) →
        (activeNearCoefficientIndices fine (physical.activeAtPoint x) center
          (radius : Real)).card ≤ multiplicity) :
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
    exists_actualProjectedAmbientNorm_singleDyadicSource mu fine physical
      normCeiling normExponent hdelta hnormCeiling hsourcePos hmultiplicity
      hlower hpair hactiveCap
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
    actualProjectedAmbientCriticalFamily_nonempty_on_multiplicityBand
      fine physical hdelta hmultiplicity hlower hpair hactiveCap
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

#print axioms exists_actualProjectedNormFirst_allCenterCells

end

end FamilyStickyCinematicL32ActualProjectedNormFirstAllCenterCellsFinalV1
