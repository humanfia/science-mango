import Family8Grounding.Family8Family7CoordinateToVerticalExtremalCoefficientCapV1
import Family8Grounding.Family8Family7LowerBucketGenericNativeBranchCoreFromCapV1
import Family8Grounding.Family8Family7CoordinateToVerticalWeightedChartSourceV2
import FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7CoordinateExtremalLowerBucketCoreV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8GeneralizedFrostmanMultiplicityV1
open Family8Family7CoordinateToVerticalTubeTransportV1
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7CoordinateToVerticalWeightedChartSourceV2
open Family8Family7CoordinateToVerticalExtremalCoefficientCapV1
open Family8Family7LowerBucketGenericNativeBranchCoreV1
open Family8Family7LowerBucketGenericNativeBranchCoreFromCapV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedSourceAmbientDistinctSelectionV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32PyzCriticalBinUniformityV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-!
# Native lower-bucket core from a transported upstream extremal family

The selected graph-c subfamily is not asserted to be extremal.  Its
distinctness and coefficient cap are inherited from one upstream extremal
ambient through the common coordinate permutation and active inclusion.
-/

theorem exists_coordinateExtremal_lowerBucket_genericNativeBranchCore
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily radius iota}
    {Y0 : Shading fine.bodyFamily} {ambient : Finset iota}
    {parallelLoss : Nat} {extremalEpsilon extremalSigma : Real}
    (G : EpsilonExtremalTubeFamily fine Y0 ambient parallelLoss
      extremalEpsilon extremalSigma)
    (axis : Fin 3) (chartSource : Finset iota)
    (Y : Shading
      (coordinateToVerticalChartSourceV2 axis fine chartSource).family.bodyFamily)
    (active : Finset iota)
    (hactiveSource : active ⊆
      (coordinateToVerticalChartSourceV2 axis fine chartSource).source)
    (hactiveAmbient : active ⊆ ambient)
    (f : Real -> Real) (hfContinuous : Continuous f)
    (X : Set (Real × Real)) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (fibreFloor : ENNReal)
    (f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (bucket : Int)
    (hbucket : forall i, i ∈ active ->
      actualProjectedTubeCBucket ((radius : Real) / 2)
        ((coordinateToVerticalChartSourceV2 axis fine chartSource).family.tubes i) =
          bucket)
    (normExponent tangencyExponent : Real)
    (logCount lower upper multiplicity : Nat)
    (hradius : 0 < radius)
    (hradiusSixteen : (radius : Real) <= 16)
    (hnormExponent : 0 <= normExponent)
    (hsourcePos : 0 < volume
      ((shadingAwareProjectedPhysicalLowerBucket Y active f
        hfContinuous.measurable X hX I hI fibreFloor).multiplicityBand
          lower upper))
    (hmultiplicity : 0 < multiplicity)
    (hlower : 3 * multiplicity <= lower)
    (hloss : actualHalfScaleCoefficientCoverLoss * parallelLoss <=
      multiplicity) :
    let VS := coordinateToVerticalChartSourceV2 axis fine chartSource
    let physical := shadingAwareProjectedPhysicalLowerBucket Y active f
      hfContinuous.measurable X hX I hI fibreFloor
    let normScale := actualProjectedAmbientNormScale VS.family physical 16
      normExponent
    ∃ normLabel ∈ Finset.Icc (dyadicCeilBucket (radius : Real))
        (dyadicCeilBucket 16),
      let E_norm := continuumCriticalSingleDyadicCell
        (physical.multiplicityBand lower upper) normScale normLabel
      ∃ D : LowerBucketNativeBranchCore VS Y active f hfContinuous
          X hX I hI fibreFloor,
        D.globalScale = dyadicCeilUpper normLabel ∧
        volume E_norm = D.sourceMass ∧
        volume (physical.multiplicityBand lower upper) /
            (continuumCriticalSingleDyadicBinFactor (radius : Real) 16 :
              ENNReal) <= D.sourceMass ∧
        0 < D.sourceMass ∧
        D.globalScale <= 32 := by
  dsimp only
  let VS := coordinateToVerticalChartSourceV2 axis fine chartSource
  let physical := shadingAwareProjectedPhysicalLowerBucket Y active f
    hfContinuous.measurable X hX I hI fibreFloor
  have hambientPairwise : Set.Pairwise (physical.ambient : Set iota)
      (fun i j => EssentiallyDistinct (VS.family.tubes i)
        (VS.family.tubes j)) := by
    intro i hi j hj hij
    change i ∈ active at hi
    change j ∈ active at hj
    change EssentiallyDistinct
      (rigidTube (coordinateToVerticalRigidMotion axis) (fine.tubes i))
      (rigidTube (coordinateToVerticalRigidMotion axis) (fine.tubes j))
    rw [essentiallyDistinct_rigidTube_iff]
    exact G.essentially_distinct (hactiveAmbient hi)
      (hactiveAmbient hj) hij
  have hpair : forall x, x ∈ physical.multiplicityBand lower upper ->
      Set.Pairwise (physical.activeAtPoint x : Set iota)
        (fun i j => EssentiallyDistinct (VS.family.tubes i)
          (VS.family.tubes j)) := by
    have hpointwise := essentiallyDistinct_activeAtPoint_of_ambient
      VS.family physical hambientPairwise
    exact fun x _hx => hpointwise x
  have hvertical : forall i, i ∈ physical.ambient ->
      (VS.family.tubes i).axis.direction 2 ≠ 0 := by
    intro i hi hzero
    have hhalf := VS.source_direction_final_half i
      (hactiveSource (by
        simpa only [physical, shadingAwareProjectedPhysicalLowerBucket]
          using hi))
    rw [hzero, abs_zero] at hhalf
    norm_num at hhalf
  have hcBucket : forall i, i ∈ physical.ambient ->
      forall j, j ∈ physical.ambient ->
        |projectedTubeGraphC (VS.family.tubes i) -
          projectedTubeGraphC (VS.family.tubes j)| <= (radius : Real) / 2 := by
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
  have hactiveCap : forall x,
      x ∈ physical.multiplicityBand lower upper -> forall center,
        center ∈ actualProjectedCriticalFamily VS.family
          (physical.activeAtPoint x) ->
        (activeNearCoefficientIndices VS.family (physical.activeAtPoint x)
          center (radius : Real)).card <= multiplicity := by
    exact activeNearCoefficientIndices_cap_on_band_of_coordinateExtremal
      G axis physical
      (by
        intro i hi
        exact hactiveAmbient (by
          simpa only [physical, shadingAwareProjectedPhysicalLowerBucket]
            using hi))
      hvertical hcBucket hloss
  exact exists_lowerBucket_genericNativeBranchCore_of_pairwise_cap
    VS Y active f hfContinuous X hX I hI fibreFloor f1 f2 outerA outerB
      hOuter hf hf1 normExponent tangencyExponent logCount lower upper
      multiplicity hradius hradiusSixteen hnormExponent hsourcePos
      hmultiplicity hlower hpair hactiveCap

#print axioms exists_coordinateExtremal_lowerBucket_genericNativeBranchCore

end

end Family8Family7CoordinateExtremalLowerBucketCoreV1
