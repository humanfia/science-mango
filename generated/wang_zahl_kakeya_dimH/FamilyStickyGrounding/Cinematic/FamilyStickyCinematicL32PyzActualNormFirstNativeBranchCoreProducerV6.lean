import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
import FamilyStickyCinematicL32PyzActualNormFirstAllCenterPayloadDichotomyFinalCleanV2
import FamilyStickyCinematicL32PyzCriticalBinUniformityV1
import FamilyStickyCinematicL32ActualProjectedContinuumCriticalCellBoundsV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstNativeBranchCoreProducerV6

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyCinematicL32ActualProjectedContinuumCriticalCellBoundsV1
open FamilyStickyCinematicL32ActualProjectedNormFirstAllCenterCellsFinalV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
open FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverCellV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterPayloadDichotomyFinalCleanV2
open FamilyStickyCinematicL32PyzActualNormFirstExtremalPublicInputsV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32PyzCriticalBinUniformityV1
open FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Constructing the native branch core from the actual norm-first partition

The native high/low branch core is not an abstract callback.  The existing
norm-first selector constructs a measurable partition of one literal dyadic
cell.  This module packages that constructed partition as the exact
`NativeBranchCore` consumed by the later concrete-Q/P branch.

The result records the genuine source-mass identity, the initial norm-bin
retention, the actual extremal pairwise-essential-distinctness, and the
automatic bound `globalScale <= 32`.  It does not construct
`NativeHighGeometry` or assert any high-branch conclusion.
-/

/-- Actual norm-first data construct a native branch core with no cell,
payload, source-mass, scale, or pairwise-distinctness callback. -/
theorem exists_actualNormFirst_nativeBranchCore
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (ambient : Finset iota) (hambient : ambient ⊆ S.source)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (f : Real → Real) (hfContinuous : Continuous f)
    (f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    {Y : Shading S.family.bodyFamily}
    {parallelLoss : Nat} {extremalEpsilon extremalSigma : Real}
    (G : EpsilonExtremalTubeFamily S.family Y ambient parallelLoss
      extremalEpsilon extremalSigma)
    (bucket : Int)
    (hbucket : ∀ i, i ∈ ambient →
      actualProjectedTubeCBucket ((radius : Real) / 2)
        (S.family.tubes i) = bucket)
    (normExponent tangencyExponent : Real)
    (logCount lower upper multiplicity : Nat)
    (hradius : 0 < radius)
    (hradiusSixteen : (radius : Real) ≤ 16)
    (hnormExponent : 0 ≤ normExponent)
    (hsourcePos : 0 < volume
      ((actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
        physicalBase hphysicalBase f hfContinuous outerA outerB).multiplicityBand
          lower upper))
    (hmultiplicity : 0 < multiplicity)
    (hlower : 3 * multiplicity ≤ lower)
    (hloss : actualHalfScaleCoefficientCoverLoss * parallelLoss ≤
      multiplicity) :
    let physical := actualProjectedNormFirstSixteenthPhysicalShading
      S.family ambient physicalBase hphysicalBase f hfContinuous outerA outerB
    let normScale := actualProjectedAmbientNormScale S.family physical 16
      normExponent
    ∃ normLabel ∈ Finset.Icc (dyadicCeilBucket (radius : Real))
        (dyadicCeilBucket 16),
      let E_norm := continuumCriticalSingleDyadicCell
        (physical.multiplicityBand lower upper) normScale normLabel
      ∃ D : NativeBranchCore radius iota,
        D.S = S ∧
        D.ambient = ambient ∧
        D.physical = physical ∧
        D.globalScale = dyadicCeilUpper normLabel ∧
        D.sourceMass = volume E_norm ∧
        volume (physical.multiplicityBand lower upper) /
            (continuumCriticalSingleDyadicBinFactor (radius : Real) 16 :
              ENNReal) ≤ D.sourceMass ∧
        0 < D.sourceMass ∧
        D.globalScale ≤ 32 ∧
        Set.Pairwise (D.ambient : Set iota) (fun i j =>
          EssentiallyDistinct (D.S.family.tubes i) (D.S.family.tubes j)) := by
  dsimp only
  let physical := actualProjectedNormFirstSixteenthPhysicalShading S.family
    ambient physicalBase hphysicalBase f hfContinuous outerA outerB
  obtain ⟨hambientPairwise, _hbandPairwise, _hactiveCap⟩ :=
    actualNormFirst_public_inputs_of_extremal_bucket (lower := lower)
      (upper := upper) S ambient hambient physicalBase hphysicalBase f
      hfContinuous outerA outerB G bucket hbucket hloss
  obtain ⟨normLabel, hnormLabel, hnormMeasure, hnormPos, _hnormNonempty,
      _hnormMeasurable, _hnormSubset, hglobalScale, hradiusGlobalScale,
      _hnormBin, fallback, hcellData, hpartition, _hlabelRange,
      _hdichotomy⟩ :=
    exists_actualNormFirst_allCenterPayload_high_or_all_low S ambient hambient
      physicalBase hphysicalBase f hfContinuous f1 f2 outerA outerB hOuter hf
      hf1 G bucket hbucket normExponent tangencyExponent logCount lower upper
      multiplicity hradius hradiusSixteen hsourcePos hmultiplicity hlower hloss
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
  have hcellMeasurable : ∀ center, center ∈ centers →
      MeasurableSet (cell center) := fun center hcenter =>
    (hcellData center hcenter).1
  have hradiusTangency : (radius : Real) ≤ 36 * globalScale := by
    have hscale36 : globalScale ≤ 36 * globalScale := by nlinarith
    exact hradiusGlobalScale.trans hscale36
  have hlocalized : ∀ center, center ∈ centers → ∀ x, x ∈ cell center →
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
  have hglobalScaleUpper : globalScale ≤ 32 := by
    have hbounds := dyadicCeilUpper_bounds_of_mem_Icc
      (by exact_mod_cast hradius) hradiusSixteen hnormLabel
    norm_num at hbounds ⊢
    exact hbounds.2
  let D : NativeBranchCore radius iota :=
    { S := S
      ambient := ambient
      physicalBase := physicalBase
      hphysicalBase := hphysicalBase
      f := f
      hfContinuous := hfContinuous
      f1 := f1
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
        simpa only [NativeBranchCore.centers, nativeCenters, centers, physical,
          actualProjectedNormFirstSixteenthPhysicalShading,
          finiteProjectedTubeShading] using hcellMeasurable
      hlocalized := by
        simpa only [NativeBranchCore.physical, nativePhysical,
          NativeBranchCore.centers, nativeCenters, centers, physical,
          actualProjectedNormFirstSixteenthPhysicalShading,
          finiteProjectedTubeShading, globalScale] using hlocalized
      sourceMass := volume E_norm
      hsourceMass := by
        simpa only [NativeBranchCore.centers, nativeCenters, centers,
          E_norm, cell, label, normScale, globalScale, physical,
          actualProjectedNormFirstSixteenthPhysicalShading,
          finiteProjectedTubeShading] using hpartition }
  refine ⟨normLabel, hnormLabel, D, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rfl
  · simpa only [D] using hnormMeasure
  · simpa only [D] using hnormPos
  · simpa only [D] using hglobalScaleUpper
  · simpa only [D] using hambientPairwise

/-- On every automatically produced core, the radius-dependent tangency-bin
part of the post-norm loss is bounded by the canonical critical-bin slack.
The final ambient-card bin is left exact. -/
theorem actualAllCenterPostNormBinLoss_le_of_globalScale_le_32
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (hglobalScaleUpper : D.globalScale ≤ 32) :
    actualAllCenterPostNormBinLoss radius D.globalScale
        D.physical.ambient.card ≤
      (pyzCriticalBinUniformSlack (radius : Real) : ENNReal) *
        (continuumCriticalSingleDyadicBinFactor 1
          (D.physical.ambient.card : Real) : ENNReal) := by
  have htangency :=
    (norm_and_tangencyCriticalBinFactors_cast_le_uniformSlack
      (by exact_mod_cast D.hradius) D.hradiusTangency
        hglobalScaleUpper).2
  unfold actualAllCenterPostNormBinLoss
  exact mul_le_mul_left htangency _

#print axioms exists_actualNormFirst_nativeBranchCore
#print axioms actualAllCenterPostNormBinLoss_le_of_globalScale_le_32

end

end FamilyStickyCinematicL32PyzActualNormFirstNativeBranchCoreProducerV6
