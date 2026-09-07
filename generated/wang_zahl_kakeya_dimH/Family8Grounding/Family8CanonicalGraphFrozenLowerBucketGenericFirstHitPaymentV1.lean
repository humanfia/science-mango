import Family8Grounding.Family8CanonicalGraphFrozenGraphActiveLowerBucketNativeCoreCapFreeV1
import Family8Grounding.Family8Family7GenericNativeHighGeometryOfBucketV1
import Family8Grounding.Family8Family7GenericNativeHighOccurrenceSourceRetentionSumV1
import Family8Grounding.Family8Family7WeightedVerticalGraphCBucketActualBridgeV1
import Mathlib.Tactic

/-!
# Native generic first-hit payment on the literal frozen graph lower bucket

The lower-bucket physical datum is fixed before the native all-centre
selection.  We then build the minimal generic high geometry from the very
same graph-c bucket.  In the genuine high alternative the canonical payload
retains half of the selected source mass in its literal E2 active-pattern
sources.  The low alternative is returned unchanged.

No old `NativeBranchCore`, physical equality, or reselected outcome occurs in
this construction.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenLowerBucketGenericFirstHitPaymentV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenGraphActiveLowerBucketNativeCoreCapFreeV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7GenericNativeHighGeometryOfBucketV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7GenericNativeHighOccurrenceSourceRetentionSumV1
open Family8Family7LowerBucketGenericNativeBranchCoreV1
open Family8Family7WeightedVerticalGraphCBucketActualBridgeV1
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

universe u

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- Selection-first high/low payment on the literal same-R lower-bucket
physical datum.  In particular, the high branch is a producer for the E2
mass payment; it is not accepted as a premise. -/
theorem exists_sameGraph_zeroWindow_lowerBucket_genericFirstHitPayment_capFree
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau : 0 < tau) (htauSixteen : (tau : Real) <= 16) :
    let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
    let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
      VS R.label
    let Z := firstCrossingFamilyGraphBucketShading
      R.axis R.label F P R.A R.k
    let f0 : Real -> Real := fun _ => 0
    let hf0 : Continuous f0 := continuous_const
    let X0 : Set (Real × Real) := Set.univ
    let hX0 : MeasurableSet X0 := MeasurableSet.univ
    let I0 : Set Real := Set.univ
    let hI0 : MeasurableSet I0 := MeasurableSet.univ
    exists n : Nat, 1 <= n /\ n <= graph.card /\
      exists fibreFloor : ENNReal, 0 < fibreFloor /\
        let physical := shadingAwareProjectedPhysicalLowerBucket Z graph f0
          hf0.measurable X0 hX0 I0 hI0 fibreFloor
        let normScale := actualProjectedAmbientNormScale VS.family physical 16 0
        ∃ normLabel ∈ Finset.Icc (dyadicCeilBucket (tau : Real))
            (dyadicCeilBucket 16),
          let E_norm := continuumCriticalSingleDyadicCell
            (physical.multiplicityBand n n) normScale normLabel
          exists D : LowerBucketNativeBranchCore VS Z graph f0 hf0
              X0 hX0 I0 hI0 fibreFloor,
            D.globalScale = dyadicCeilUpper normLabel /\
            volume E_norm = D.sourceMass /\
            volume (physical.multiplicityBand n n) /
                (continuumCriticalSingleDyadicBinFactor (tau : Real) 16 :
                  ENNReal) <= D.sourceMass /\
            0 < D.sourceMass /\
            D.globalScale <= 32 /\
            exists G : GenericNativeHighGeometry D,
              (D.sourceMass / 2 <=
                  ∑ c ∈ D.low, volume (D.cell c.1)) \/
                D.sourceMass / 2 <=
                  actualAllCenterPostNormBinLoss tau D.globalScale
                      physical.ambient.card *
                    ∑ c : D.HighCenter,
                      volume (genericNativeHighActivePatternSource D G c) := by
  dsimp only
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real -> Real := fun _ => 0
  let hf0 : Continuous f0 := continuous_const
  let X0 : Set (Real × Real) := Set.univ
  let hX0 : MeasurableSet X0 := MeasurableSet.univ
  let I0 : Set Real := Set.univ
  let hI0 : MeasurableSet I0 := MeasurableSet.univ
  obtain ⟨n, hnOne, hnCard, fibreFloor, hfibreFloor, normLabel,
      hnormLabel, D, hglobalScale, hsourceEq, hbandRetention,
      hsourcePos, hglobalUpper⟩ :=
    exists_sameGraph_zeroWindow_lowerBucketNativeCore_capFree
      R htau htauSixteen
  refine ⟨n, hnOne, hnCard, fibreFloor, hfibreFloor, normLabel,
    hnormLabel, D, hglobalScale, hsourceEq, hbandRetention,
    hsourcePos, hglobalUpper, ?_⟩
  have hbucket : forall i, i ∈ graph ->
      actualProjectedTubeCBucket ((tau : Real) / 2)
        (VS.family.tubes i) = R.label := by
    intro i hi
    exact actualProjectedTubeCBucket_eq_of_mem_verticalSourceGraphCBucketFiber
      ((tau : Real) / 2) VS R.label hi
  let G : GenericNativeHighGeometry D :=
    genericNativeHighGeometryOfBucket D R.label (by
      intro i hi
      apply hbucket i
      simpa only [shadingAwareProjectedPhysicalLowerBucket] using hi)
  refine ⟨G, ?_⟩
  rcases (GenericNativeBranchCore.payloadAt_spec D).2.1 with hhigh | hlow
  · exact Or.inr
      (sourceMass_half_le_postNormBinLoss_mul_sum_genericActivePatternSource
        D G hhigh)
  · exact Or.inl hlow

#print axioms
  exists_sameGraph_zeroWindow_lowerBucket_genericFirstHitPayment_capFree

end
end Family8CanonicalGraphFrozenLowerBucketGenericFirstHitPaymentV1
