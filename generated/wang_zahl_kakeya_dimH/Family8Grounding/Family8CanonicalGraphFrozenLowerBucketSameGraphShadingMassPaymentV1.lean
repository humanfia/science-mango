import Family8Grounding.Family8CanonicalGraphFrozenLowerBucketSourceDensityPaymentV1
import Mathlib.Tactic

/-!
# Exact lower-bucket payment into the same frozen graph

The source-density payment already proves this inequality internally before
passing to the larger source shading and dividing by the assembly losses.
This file exposes that strongest same-object intermediate endpoint: the
selected norm cell pays its literal fibre floor directly into the shading
mass of the graph selected by the same `R`.

No displayed coefficient, tail budget, or comparison with a reselected
graph is assumed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenLowerBucketSameGraphShadingMassPaymentV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenLowerBucketSourceDensityPaymentV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7LowerBucketGenericNativeBranchCoreV1
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- The norm cell selected inside the quantitative lower bucket pays directly
into the shading mass of the literal graph frozen by the same identity `R`.
This is the pre-quotient graph-mass inequality hidden inside the existing
source-density payment. -/
theorem lowerBucketNormCellPayment_le_sameGraphShadingMass
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
    fibreFloor * D.sourceMass <=
      (firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k).shadingMass := by
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
  have hEmeasurable : MeasurableSet E_norm := by
    exact measurableSet_continuumCriticalSingleDyadicCell
      (physical.measurableSet_multiplicityBand n n)
      (measurable_actualProjectedAmbientNormScale
        VS.family physical 16 0) normLabel
  have hEsubset : E_norm ⊆ physical.multiplicityBand n n := by
    intro x hx
    exact hx.1
  have hpaySum :=
    fibreFloor_mul_volume_le_activeWindowShadingMass_of_band
      Z graph f0 measurable_const Set.univ MeasurableSet.univ
        Set.univ MeasurableSet.univ fibreFloor n n hn E_norm
          hEmeasurable hEsubset
  have hwindow : forall i,
      (shadingWindowRestriction Z f0 measurable_const
        Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ).carrier i =
          Z.carrier i := by
    intro i
    simp [shadingWindowRestriction, shadingProjectionWindow, f0]
  have hsumEq :
      (∑ i ∈ graph,
        volume ((shadingWindowRestriction Z f0 measurable_const
          Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ).carrier i)) =
        Z.shadingMass := by
    simp_rw [hwindow]
    change (∑ i ∈ graph,
      volume (((IndexedShadingRefinement.restrictTo
        (firstCrossingFamilyVerticalShading R.axis F P R.A R.k) graph).shading
          ).carrier i)) =
      (IndexedShadingRefinement.restrictTo
        (firstCrossingFamilyVerticalShading R.axis F P R.A R.k) graph).shading.shadingMass
    rw [shadingMass_restrictTo_eq_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [IndexedShadingRefinement.restrictTo_carrier, if_pos hi]
  change fibreFloor * D.sourceMass <= Z.shadingMass
  rw [← hsourceEq]
  exact hpaySum.trans_eq hsumEq

#print axioms lowerBucketNormCellPayment_le_sameGraphShadingMass

end
end Family8CanonicalGraphFrozenLowerBucketSameGraphShadingMassPaymentV1
