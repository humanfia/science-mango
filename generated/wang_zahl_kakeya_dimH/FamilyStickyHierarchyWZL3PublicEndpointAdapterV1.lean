import Submission.Kakeya.ConvexFactoring.MultiscaleTubeHierarchy
import FamilyStickyCinematicL32PyzActualNormFirstPublicHighLowLiftV6

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyHierarchyWZL3PublicEndpointAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyCinematicL32PyzQuasiProductFrostmanBoundV1
open FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualCanonicalPayloadLocalEstimateV5
open FamilyStickyCinematicL32PyzCriticalBinUniformityV1
open FamilyStickyCinematicL32CriticalSingleDyadicBinFactorPositiveV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1
open FamilyStickyCinematicL32PyzActualNormFirstPublicHighLowLiftV6

noncomputable section

universe u

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)

/-!
# The hierarchy's level-zero chart bucket as a genuine WZ `L_3` source

The public cinematic endpoint and the hierarchy cannot currently be imported
through the large `FamilyStickyGrounding` aggregate: tracked root and
Grounding modules expose two copies of
`FamilyStickyTubeParentDirectionCoherenceV1`.  This module therefore uses the
canonical hierarchy definition directly and states the analytic chart bucket
with the public endpoint's literal bucket function.

The resulting subtype retains both facts needed by the norm-first chain:
the genuine fixed-`L_3` inequality `1 / 2 <= |direction 2|`, and a constant
half-radius graph-`c` bucket.  It does not manufacture a shading, extremality,
quasi-product structure, or cinematic slope function; those remain explicit
inputs to the final theorem below.
-/

/-- The literal level-zero fixed-vertical-chart / graph-`c` bucket in the
analytic API. -/
def levelZeroAnalyticChartBucket (label : Int) : Finset (Index 0) :=
  (fixedVerticalChartIndices (H.effectiveFamily 0)
      (H.family 0).refinement.refined).filter fun i =>
    actualProjectedTubeCBucket
      (((H.effectiveRadius 0 : NNReal) : Real) / 2)
      ((H.effectiveFamily 0).tubes i) = label

/-- The selected hierarchy bucket is a genuine WZ `L_3` source, not merely a
family with a nonzero final direction coordinate. -/
def levelZeroChartBucketWZL3Source (label : Int) :
    WZL3UniformTubeSource (H.effectiveRadius 0)
      {i // i ∈ levelZeroAnalyticChartBucket H label} where
  family := (H.effectiveFamily 0).restrictTo
    (levelZeroAnalyticChartBucket H label)
  source := Finset.univ
  source_direction_final_half := by
    intro i _hi
    have hchart := (Finset.mem_filter.mp i.2).1
    simpa using vertical_half_of_mem_fixedVerticalChartIndices
      (H.effectiveFamily 0) (H.family 0).refinement.refined hchart

@[simp]
theorem levelZeroChartBucketWZL3Source_source (label : Int) :
    (levelZeroChartBucketWZL3Source H label).source = Finset.univ :=
  rfl

/-- Every member carries the selected literal analytic bucket label. -/
@[simp]
theorem levelZeroChartBucketWZL3Source_bucket
    (label : Int)
    (i : {i // i ∈ levelZeroAnalyticChartBucket H label}) :
    actualProjectedTubeCBucket
        (((H.effectiveRadius 0 : NNReal) : Real) / 2)
        ((levelZeroChartBucketWZL3Source H label).family.tubes i) = label :=
  (Finset.mem_filter.mp i.2).2

/-- The public norm-first high/low theorem on the literal hierarchy bucket.

This discharges the WZ `L_3` provenance, source inclusion, the redundant
unit-ball premise, and graph-`c` bucket constancy.  Extremality, shading,
quasi-product geometry, and the cinematic function remain genuine analytic
inputs. -/
theorem exists_levelZeroChartBucket_highPayload_or_lowOriginalBandMoment
    (label : Int)
    {E : Set (Real × Real)} {alpha : Real} {C : ENNReal}
    (Q : PyzCarrierQuasiProduct E
      (pyzFrostmanIntervalBound
        ((H.effectiveRadius 0 : NNReal) : Real) alpha C))
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (f : Real -> Real) (hfContinuous : Continuous f)
    (f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (halpha : 0 <= alpha) (halphaOne : alpha <= 1)
    (hfun : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfun1 : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    {Y : Shading (levelZeroChartBucketWZL3Source H label).family.bodyFamily}
    {parallelLoss : Nat} {extremalEpsilon extremalSigma : Real}
    (G : EpsilonExtremalTubeFamily
      (levelZeroChartBucketWZL3Source H label).family Y Finset.univ
      parallelLoss extremalEpsilon extremalSigma)
    (normExponent tangencyExponent : Real)
    (logCount lower upper multiplicity : Nat)
    (hradiusSixteen :
      ((H.effectiveRadius 0 : NNReal) : Real) <= 16)
    (hnormExponent : 0 <= normExponent)
    (htangencyExponent : 0 <= tangencyExponent)
    (hsourcePos : 0 < volume
      ((actualProjectedNormFirstSixteenthPhysicalShading
        (levelZeroChartBucketWZL3Source H label).family Finset.univ
        physicalBase hphysicalBase f hfContinuous outerA outerB).multiplicityBand
          lower upper))
    (hbandSubsetE :
      (actualProjectedNormFirstSixteenthPhysicalShading
        (levelZeroChartBucketWZL3Source H label).family Finset.univ
        physicalBase hphysicalBase f hfContinuous outerA outerB).multiplicityBand
          lower upper ⊆ E)
    (hmultiplicity : 0 < multiplicity)
    (hlower : 3 * multiplicity <= lower)
    (hloss : actualHalfScaleCoefficientCoverLoss * parallelLoss <=
      multiplicity)
    (hslack : pyzCriticalBinUniformSlack
      (((H.effectiveRadius 0 : NNReal) : Real)) <= logCount) :
    let S := levelZeroChartBucketWZL3Source H label
    let ambient : Finset {i // i ∈ levelZeroAnalyticChartBucket H label} :=
      Finset.univ
    let physical := actualProjectedNormFirstSixteenthPhysicalShading
      S.family ambient physicalBase hphysicalBase f hfContinuous outerA outerB
    let normScale := actualProjectedAmbientNormScale S.family physical 16
      normExponent
    ∃ normLabel ∈ Finset.Icc
        (dyadicCeilBucket (((H.effectiveRadius 0 : NNReal) : Real)))
        (dyadicCeilBucket 16),
      let E_norm := continuumCriticalSingleDyadicCell
        (physical.multiplicityBand lower upper) normScale normLabel
      let globalScale := dyadicCeilUpper normLabel
      volume (physical.multiplicityBand lower upper) /
          (continuumCriticalSingleDyadicBinFactor
            (((H.effectiveRadius 0 : NNReal) : Real)) 16 : ENNReal) <=
          volume E_norm ∧
      0 < volume E_norm ∧ MeasurableSet E_norm ∧
      E_norm ⊆ physical.multiplicityBand lower upper ∧
      0 < globalScale ∧
      (((H.effectiveRadius 0 : NNReal) : Real)) <= globalScale ∧
      globalScale <= 32 ∧
      ((∃ globalCenter : Tube (H.effectiveRadius 0),
          ∃ base : Set (Real × Real),
          ∃ hbase : MeasurableSet base,
          0 < volume base ∧ base ⊆ E_norm ∧
          ∃ payload : ActualPositiveCenterCanonicalPayload volume base
              hbase S.family physical f f1 f2 outerA outerB hOuter hf hf1
              globalScale globalCenter tangencyExponent,
            24 * logCount <= pyzE2DegreeLower payload.finalLabel) ∨
        actualCanonicalPayloadGlobalWeight lower globalScale normExponent
            tangencyExponent *
              volume (physical.multiplicityBand lower upper) <=
          ((logCount : ENNReal) ^ 2 *
              (continuumCriticalSingleDyadicBinFactor 1
                (ambient.card : Real) : ENNReal)) *
            actualCanonicalPayloadUniformMomentCost
              (H.effectiveRadius 0) multiplicity logCount normExponent
              tangencyExponent alpha C *
            ((19 ^ 3 * ambient.card : Nat) : ENNReal)) := by
  dsimp only
  exact exists_actualNormFirst_highPayload_or_lowOriginalBandMoment
    Q (levelZeroChartBucketWZL3Source H label) Finset.univ
    (by intro i hi; exact hi)
    (fun i hi => G.contained_in_unit_ball i hi)
    physicalBase hphysicalBase f hfContinuous f1 f2 outerA outerB hOuter hf
    hf1 hparameter halpha halphaOne hfun hfun1 G label
    (fun i _hi => levelZeroChartBucketWZL3Source_bucket H label i)
    normExponent tangencyExponent logCount lower upper multiplicity G.delta_pos
    hradiusSixteen hnormExponent htangencyExponent hsourcePos hbandSubsetE
    hmultiplicity hlower hloss hslack

#print axioms levelZeroChartBucketWZL3Source
#print axioms levelZeroChartBucketWZL3Source_bucket
#print axioms exists_levelZeroChartBucket_highPayload_or_lowOriginalBandMoment

end
end FamilyStickyHierarchyWZL3PublicEndpointAdapterV1
