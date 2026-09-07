import Family8Grounding.Family8ActualProjectedNormFirstAllCenterCellsCapFreeV3
import Family8Grounding.Family8Family7LowerBucketGenericNativeBranchCoreV1
import FamilyStickyCinematicL32ActualProjectedContinuumCriticalCellBoundsV1
import FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
import FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
import FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
import Mathlib.Tactic

/-!
# Lower-bucket generic native core without a coefficient cap

The cap-free all-centre selector only needs a positive measured active-card
band.  Specializing it to the lower-fibre physical datum preserves the
literal positive fibre floor while removing the unrelated extremal-family,
pairwise-distinctness, and `3m` coefficient-cap inputs.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7LowerBucketGenericNativeBranchCoreCapFreeV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8ActualProjectedNormFirstAllCenterCellsCapFreeV3
open Family8Family7LowerBucketGenericNativeBranchCoreV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open FamilyStickyCinematicL32ActualProjectedContinuumCriticalCellBoundsV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
open FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverCellV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-- A positive lower-fibre active-card band produces the literal native core
without any extremal or near-coefficient cap premise. -/
theorem exists_lowerBucket_genericNativeBranchCore_capFree
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily) (active : Finset iota)
    (f : Real -> Real) (hfContinuous : Continuous f)
    (X : Set (Real × Real)) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (fibreFloor : ENNReal)
    (f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (normExponent tangencyExponent : Real)
    (logCount lower upper : Nat)
    (hradius : 0 < radius)
    (hradiusSixteen : (radius : Real) <= 16)
    (hnormExponent : 0 <= normExponent)
    (hsourcePos : 0 < volume
      ((shadingAwareProjectedPhysicalLowerBucket Y active f
        hfContinuous.measurable X hX I hI fibreFloor).multiplicityBand
          lower upper))
    (hlowerPos : 0 < lower) :
    let physical := shadingAwareProjectedPhysicalLowerBucket Y active f
      hfContinuous.measurable X hX I hI fibreFloor
    let normScale := actualProjectedAmbientNormScale S.family physical 16
      normExponent
    ∃ normLabel ∈ Finset.Icc (dyadicCeilBucket (radius : Real))
        (dyadicCeilBucket 16),
      let E_norm := continuumCriticalSingleDyadicCell
        (physical.multiplicityBand lower upper) normScale normLabel
      exists D : LowerBucketNativeBranchCore S Y active f hfContinuous
          X hX I hI fibreFloor,
        D.globalScale = dyadicCeilUpper normLabel /\
        volume E_norm = D.sourceMass /\
        volume (physical.multiplicityBand lower upper) /
            (continuumCriticalSingleDyadicBinFactor (radius : Real) 16 :
              ENNReal) <= D.sourceMass /\
        0 < D.sourceMass /\
        D.globalScale <= 32 := by
  dsimp only
  let physical := shadingAwareProjectedPhysicalLowerBucket Y active f
    hfContinuous.measurable X hX I hI fibreFloor
  obtain ⟨normLabel, hnormLabel, hnormMeasure, hnormPos,
      _hnormNonempty, _hnormMeasurable, _hnormSubset, hglobalScale,
      hradiusGlobalScale, _hnormBin, fallback, hpartition, _hlabelRange,
      hcellData⟩ :=
    exists_actualProjectedNormFirst_allCenterCells_capFree
      volume S.family physical 16 normExponent hradius hradiusSixteen
        hsourcePos hlowerPos
  let normScale := actualProjectedAmbientNormScale S.family physical 16
    normExponent
  let E_norm := continuumCriticalSingleDyadicCell
    (physical.multiplicityBand lower upper) normScale normLabel
  let globalScale := dyadicCeilUpper normLabel
  let centers := finiteMetricCoverCenters
    (activeTubeImage S.family physical.ambient)
    projectedTubePairCoefficientDistance globalScale
    (fun T U => projectedTubePairCoefficientDistance_comm T U)
  let label := finiteIncidenceNormGlobalCoverLabel physical.ambient
    (fun i x => x ∈ physical.carrier i)
    (activeTubeImage S.family physical.ambient) fallback
    (actualProjectedAmbientCriticalFamily S.family physical.ambient)
    projectedTubePairCoefficientDistance (radius : Real) 16 normExponent
    globalScale (fun T U => projectedTubePairCoefficientDistance_comm T U)
  let cell := fun center => measurableLabelCell E_norm label center
  have hcellMeasurable : forall center, center ∈ centers ->
      MeasurableSet (cell center) := fun center hcenter =>
    (hcellData center hcenter).1
  have hradiusTangency : (radius : Real) <= 36 * globalScale := by
    have hscale36 : globalScale <= 36 * globalScale := by nlinarith
    exact hradiusGlobalScale.trans hscale36
  have hlocalized : forall center, center ∈ centers ->
      forall x, x ∈ cell center ->
        (finiteIncidenceNormLocalizedFamilyValue
          (actualProjectedAmbientCriticalFamily S.family physical.ambient)
          projectedTubePairCoefficientDistance globalScale center
          (physical.activeAtPoint x)).Nonempty := by
    intro center hcenter x hx
    obtain ⟨hlocalFamily, hballSubset, _hcard⟩ :=
      (hcellData center hcenter).2.2 x hx
    have hballNonempty := finiteNormCriticalBall_nonempty
      (exponent := normExponent)
      (actualProjectedAmbientCriticalFamily S.family physical.ambient
        (physical.activeAtPoint x))
      projectedTubePairCoefficientDistance hlocalFamily
      (fun T _hT => by
        rw [projectedTubePairCoefficientDistance_self]
        exact_mod_cast hradius.le)
      hradiusSixteen
    exact hballNonempty.mono hballSubset
  have hglobalScaleUpper : globalScale <= 32 := by
    have hbounds := dyadicCeilUpper_bounds_of_mem_Icc
      (by exact_mod_cast hradius) hradiusSixteen hnormLabel
    norm_num at hbounds ⊢
    exact hbounds.2
  let D : LowerBucketNativeBranchCore S Y active f hfContinuous
      X hX I hI fibreFloor :=
    { f1 := f1
      f2 := f2
      outerA := outerA
      outerB := outerB
      hOuter := hOuter
      hf := hf
      hf1 := hf1
      globalScale := globalScale
      hglobalScale := hglobalScale
      cell := cell
      tangencyExponent := tangencyExponent
      normExponent := normExponent
      logCount := logCount
      hradius := hradius
      hradiusSixteen := hradiusSixteen
      hradiusTangency := hradiusTangency
      hnormExponent := hnormExponent
      hcellMeasurable := by
        simpa only [GenericNativeBranchCore.centers, genericNativeCenters,
          centers] using hcellMeasurable
      hlocalized := by
        simpa only [GenericNativeBranchCore.physicalDatum,
          GenericNativeBranchCore.centers, genericNativeCenters, centers,
          physical] using hlocalized }
  have hsourceEq : volume E_norm = D.sourceMass := by
    simpa only [D, GenericNativeBranchCore.sourceMass,
      GenericNativeBranchCore.centers, genericNativeCenters, centers,
      E_norm, cell, label, normScale, globalScale, physical] using hpartition
  refine ⟨normLabel, hnormLabel, D, rfl, hsourceEq, ?_, ?_, ?_⟩
  · rw [← hsourceEq]
    exact hnormMeasure
  · rw [← hsourceEq]
    exact hnormPos
  · simpa only [D] using hglobalScaleUpper

#print axioms exists_lowerBucket_genericNativeBranchCore_capFree

end
end Family8Family7LowerBucketGenericNativeBranchCoreCapFreeV1
