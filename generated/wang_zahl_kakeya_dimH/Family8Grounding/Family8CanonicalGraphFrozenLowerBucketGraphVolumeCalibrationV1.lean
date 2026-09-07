import Family8Grounding.Family8CanonicalGraphFrozenLowerBucketSameGraphShadingMassPaymentV1
import Family8Grounding.Family8ExactAssemblyActualAverageBridgeV1
import Mathlib.Tactic

/-!
# Same-graph volume calibration for a displayed coefficient

The lower-bucket norm cell pays directly into the shading mass of the graph
frozen by `R`.  Consequently the weakest remaining scalar comparison is
against the shaded-union volume of that very graph; no source-family volume
or assembly-selection loss is needed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenLowerBucketGraphVolumeCalibrationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenLowerBucketSameGraphShadingMassPaymentV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7LowerBucketGenericNativeBranchCoreV1
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- The automatic part of the same-graph payment, after division by the
literal graph-union volume. -/
theorem lowerBucketNormCellPayment_div_shadedUnion_le_graphAverage
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (n : Nat) (hn : 1 <= n) (fibreFloor : ENNReal) (normLabel : Int)
    (D :
      let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
      let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
        VS R.label
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      let f0 : Real -> Real := fun _ => 0
      let hf0 : Continuous f0 := continuous_const
      LowerBucketNativeBranchCore VS Z graph f0 hf0
        Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ fibreFloor)
    (hsourceEq :
      let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
      let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
        VS R.label
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      let f0 : Real -> Real := fun _ => 0
      let physical := shadingAwareProjectedPhysicalLowerBucket Z graph f0
        measurable_const Set.univ MeasurableSet.univ Set.univ
          MeasurableSet.univ fibreFloor
      let normScale := actualProjectedAmbientNormScale VS.family physical 16 0
      let E_norm := continuumCriticalSingleDyadicCell
        (physical.multiplicityBand n n) normScale normLabel
      volume E_norm = D.sourceMass) :
    let Z := firstCrossingFamilyGraphBucketShading
      R.axis R.label F P R.A R.k
    (fibreFloor * D.sourceMass) / volume Z.shadedUnion <= R.graphAverage := by
  dsimp only
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  have hpayment : fibreFloor * D.sourceMass <= Z.shadingMass := by
    simpa only [Z] using
      lowerBucketNormCellPayment_le_sameGraphShadingMass
        R n hn fibreFloor normLabel D hsourceEq
  simpa only [SameAssemblyFullCoefficientGraphIdentity.graphAverage,
    Shading.averageMultiplicity, Z] using
      ENNReal.div_le_div_right hpayment (volume Z.shadedUnion)

/-- A displayed coefficient is bounded by the average multiplicity of the
literal graph once it pays only the volume of that same graph. -/
theorem displayed_le_graphAverage_of_sameGraph_volumeCalibration
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (n : Nat) (hn : 1 <= n) (fibreFloor : ENNReal) (normLabel : Int)
    (D :
      let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
      let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
        VS R.label
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      let f0 : Real -> Real := fun _ => 0
      let hf0 : Continuous f0 := continuous_const
      LowerBucketNativeBranchCore VS Z graph f0 hf0
        Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ fibreFloor)
    (hsourceEq :
      let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
      let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
        VS R.label
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      let f0 : Real -> Real := fun _ => 0
      let physical := shadingAwareProjectedPhysicalLowerBucket Z graph f0
        measurable_const Set.univ MeasurableSet.univ Set.univ
          MeasurableSet.univ fibreFloor
      let normScale := actualProjectedAmbientNormScale VS.family physical 16 0
      let E_norm := continuumCriticalSingleDyadicCell
        (physical.multiplicityBand n n) normScale normLabel
      volume E_norm = D.sourceMass)
    (displayed : ENNReal)
    (hCalibration :
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      displayed * volume Z.shadedUnion <= fibreFloor * D.sourceMass) :
    displayed <= R.graphAverage := by
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let Q := Classical.choice R.graphCertificate
  have hgraphMass : Z.shadingMass ≠ 0 := by
    simpa only [Z] using Q.graph_mass_ne_zero
  have hvolume0 : volume Z.shadedUnion ≠ 0 :=
    volume_shadedUnion_ne_zero_of_shadingMass_ne_zero Z hgraphMass
  have hvolumeTop : volume Z.shadedUnion ≠ ∞ :=
    volume_shadedUnion_ne_top Z
  have hpayment : fibreFloor * D.sourceMass <= Z.shadingMass := by
    simpa only [Z] using
      lowerBucketNormCellPayment_le_sameGraphShadingMass
        R n hn fibreFloor normLabel D hsourceEq
  have hCalibration' :
      displayed * volume Z.shadedUnion <= fibreFloor * D.sourceMass := by
    simpa only [Z] using hCalibration
  have hmul : displayed * volume Z.shadedUnion <= Z.shadingMass :=
    hCalibration'.trans hpayment
  have hdiv : displayed <= Z.shadingMass / volume Z.shadedUnion :=
    (ENNReal.le_div_iff_mul_le
      (Or.inl hvolume0) (Or.inl hvolumeTop)).2 hmul
  simpa only [SameAssemblyFullCoefficientGraphIdentity.graphAverage,
    Shading.averageMultiplicity, Z] using hdiv

#print axioms displayed_le_graphAverage_of_sameGraph_volumeCalibration
#print axioms lowerBucketNormCellPayment_div_shadedUnion_le_graphAverage

end
end Family8CanonicalGraphFrozenLowerBucketGraphVolumeCalibrationV1
