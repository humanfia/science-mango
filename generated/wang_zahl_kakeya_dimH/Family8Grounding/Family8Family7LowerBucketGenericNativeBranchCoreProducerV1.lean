import Family8Grounding.Family8Family7LowerBucketGenericNativeBranchCoreV1
import FamilyStickyCinematicL32ActualProjectedContinuumCriticalCellBoundsV1
import FamilyStickyCinematicL32ActualProjectedNormFirstAllCenterCellsFinalV1
import FamilyStickyCinematicL32ActualProjectedSourceExtremalCoefficientCapV1
import FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
import FamilyStickyCinematicL32PyzCriticalBinUniformityV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7LowerBucketGenericNativeBranchCoreProducerV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8Family7LowerBucketGenericNativeBranchCoreV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyCinematicL32ActualProjectedContinuumCriticalCellBoundsV1
open FamilyStickyCinematicL32ActualProjectedNormFirstAllCenterCellsFinalV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedSourceAmbientDistinctSelectionV1
open FamilyStickyCinematicL32ActualProjectedSourceExtremalCoefficientCapV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
open FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverCellV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32PyzCriticalBinUniformityV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Actual lower-bucket norm-first core producer

The arbitrary-physical all-centre selector already constructs the dyadic
norm cell, its measurable centre partition, and every localization fact.
For the literal lower-fibre physical datum, the primitive extremal record and
one actual half-radius `c` bucket automatically provide the remaining
pairwise-distinctness and coefficient-cap hypotheses.  Thus no cell,
partition, localization, or active-cap callback is exposed here.

The sole source-side premise is positive mass in the displayed lower-bucket
multiplicity band.  Quantitative retention of such a band is deliberately
not asserted by this construction theorem.
-/

theorem exists_lowerBucket_genericNativeBranchCore
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily) (active : Finset iota)
    (hactiveSource : active ⊆ S.source)
    (f : Real → Real) (hfContinuous : Continuous f)
    (X : Set (Real × Real)) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (fibreFloor : ENNReal)
    (f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    {parallelLoss : Nat} {extremalEpsilon extremalSigma : Real}
    (G : EpsilonExtremalTubeFamily S.family Y active parallelLoss
      extremalEpsilon extremalSigma)
    (bucket : Int)
    (hbucket : ∀ i, i ∈ active →
      actualProjectedTubeCBucket ((radius : Real) / 2)
        (S.family.tubes i) = bucket)
    (normExponent tangencyExponent : Real)
    (logCount lower upper multiplicity : Nat)
    (hradius : 0 < radius)
    (hradiusSixteen : (radius : Real) ≤ 16)
    (hnormExponent : 0 ≤ normExponent)
    (hsourcePos : 0 < volume
      ((shadingAwareProjectedPhysicalLowerBucket Y active f
        hfContinuous.measurable X hX I hI fibreFloor).multiplicityBand
          lower upper))
    (hmultiplicity : 0 < multiplicity)
    (hlower : 3 * multiplicity ≤ lower)
    (hloss : actualHalfScaleCoefficientCoverLoss * parallelLoss ≤
      multiplicity) :
    let physical := shadingAwareProjectedPhysicalLowerBucket Y active f
      hfContinuous.measurable X hX I hI fibreFloor
    let normScale := actualProjectedAmbientNormScale S.family physical 16
      normExponent
    ∃ normLabel ∈ Finset.Icc (dyadicCeilBucket (radius : Real))
        (dyadicCeilBucket 16),
      let E_norm := continuumCriticalSingleDyadicCell
        (physical.multiplicityBand lower upper) normScale normLabel
      ∃ D : LowerBucketNativeBranchCore S Y active f hfContinuous
          X hX I hI fibreFloor,
        D.globalScale = dyadicCeilUpper normLabel ∧
        volume E_norm = D.sourceMass ∧
        volume (physical.multiplicityBand lower upper) /
            (continuumCriticalSingleDyadicBinFactor (radius : Real) 16 :
              ENNReal) ≤ D.sourceMass ∧
        0 < D.sourceMass ∧
        D.globalScale ≤ 32 := by
  dsimp only
  let physical := shadingAwareProjectedPhysicalLowerBucket Y active f
    hfContinuous.measurable X hX I hI fibreFloor
  have hambientPairwise : Set.Pairwise (physical.ambient : Set iota)
      (fun i j ↦ EssentiallyDistinct (S.family.tubes i)
        (S.family.tubes j)) := by
    simpa only [physical, shadingAwareProjectedPhysicalLowerBucket] using
      G.essentially_distinct
  have hpair : ∀ x, x ∈ physical.multiplicityBand lower upper →
      Set.Pairwise (physical.activeAtPoint x : Set iota)
        (fun i j ↦ EssentiallyDistinct (S.family.tubes i)
          (S.family.tubes j)) := by
    have hpointwise := essentiallyDistinct_activeAtPoint_of_ambient
      S.family physical hambientPairwise
    exact fun x _hx ↦ hpointwise x
  have hvertical : ∀ i, i ∈ physical.ambient →
      (S.family.tubes i).axis.direction 2 ≠ 0 := by
    intro i hi hzero
    have hhalf := S.source_direction_final_half i
      (hactiveSource (by
        simpa only [physical, shadingAwareProjectedPhysicalLowerBucket]
          using hi))
    rw [hzero, abs_zero] at hhalf
    norm_num at hhalf
  have hcBucket : ∀ i, i ∈ physical.ambient →
      ∀ j, j ∈ physical.ambient →
        |projectedTubeGraphC (S.family.tubes i) -
          projectedTubeGraphC (S.family.tubes j)| ≤ (radius : Real) / 2 := by
    intro i hi j hj
    apply abs_projectedTubeGraphC_sub_le_of_bucket_eq
    · exact div_pos (by exact_mod_cast hradius) (by norm_num)
    · exact
        (hbucket i (by
          simpa only [physical, shadingAwareProjectedPhysicalLowerBucket]
            using hi)).trans
          (hbucket j (by
            simpa only [physical, shadingAwareProjectedPhysicalLowerBucket]
              using hj)).symm
  have hactiveCap : ∀ x, x ∈ physical.multiplicityBand lower upper →
      ∀ center,
        center ∈ actualProjectedCriticalFamily S.family
          (physical.activeAtPoint x) →
        (activeNearCoefficientIndices S.family (physical.activeAtPoint x)
          center (radius : Real)).card ≤ multiplicity := by
    exact activeNearCoefficientIndices_cap_on_band_of_extremal
      physical G hvertical hcBucket hloss
  obtain ⟨normLabel, hnormLabel, hnormMeasure, hnormPos,
      _hnormNonempty, _hnormMeasurable, _hnormSubset, hglobalScale,
      hradiusGlobalScale, _hnormBin, fallback, hpartition, _hlabelRange,
      hcellData⟩ :=
    exists_actualProjectedNormFirst_allCenterCells volume S.family physical
      16 normExponent hradius hradiusSixteen hsourcePos hmultiplicity hlower
        hpair hactiveCap
  let normScale := actualProjectedAmbientNormScale S.family physical 16
    normExponent
  let E_norm := continuumCriticalSingleDyadicCell
    (physical.multiplicityBand lower upper) normScale normLabel
  let globalScale := dyadicCeilUpper normLabel
  let centers := finiteMetricCoverCenters
    (activeTubeImage S.family physical.ambient)
    projectedTubePairCoefficientDistance globalScale
    (fun T U ↦ projectedTubePairCoefficientDistance_comm T U)
  let label := finiteIncidenceNormGlobalCoverLabel physical.ambient
    (fun i x ↦ x ∈ physical.carrier i)
    (activeTubeImage S.family physical.ambient) fallback
    (actualProjectedAmbientCriticalFamily S.family physical.ambient)
    projectedTubePairCoefficientDistance (radius : Real) 16 normExponent
    globalScale (fun T U ↦ projectedTubePairCoefficientDistance_comm T U)
  let cell := fun center ↦ measurableLabelCell E_norm label center
  have hcellMeasurable : ∀ center, center ∈ centers →
      MeasurableSet (cell center) := fun center hcenter ↦
    (hcellData center hcenter).1
  have hradiusTangency : (radius : Real) ≤ 36 * globalScale := by
    have hscale36 : globalScale ≤ 36 * globalScale := by nlinarith
    exact hradiusGlobalScale.trans hscale36
  have hlocalized : ∀ center, center ∈ centers →
      ∀ x, x ∈ cell center →
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
      (fun T _hT ↦ by
        rw [projectedTubePairCoefficientDistance_self]
        exact_mod_cast hradius.le)
      hradiusSixteen
    exact hballNonempty.mono hballSubset
  have hglobalScaleUpper : globalScale ≤ 32 := by
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

#print axioms exists_lowerBucket_genericNativeBranchCore

end

end Family8Family7LowerBucketGenericNativeBranchCoreProducerV1
