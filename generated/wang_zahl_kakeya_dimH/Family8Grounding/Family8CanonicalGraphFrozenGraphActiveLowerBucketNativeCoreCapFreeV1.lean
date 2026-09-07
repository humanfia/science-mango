import Family8Grounding.Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
import Family8Grounding.Family8Family7FirstCrossingFamilyGraphBucketExactCardBandV1
import Family8Grounding.Family8Family7LowerBucketGenericNativeBranchCoreCapFreeV1
import Family8Grounding.Family8Family7PositiveBandLowerFibreFloorV1
import Mathlib.Tactic

/-!
# Cap-free native lower bucket on the frozen canonical graph

The graph certificate already gives nonzero mass on its literal graph
shading.  Exact-card selection and qualitative fibre-floor selection are
therefore performed after `R` is fixed.  The cap-free all-centre producer
then constructs a native core on exactly the same graph and shading, without
an extremal-family or coefficient-cap premise.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenGraphActiveLowerBucketNativeCoreCapFreeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8Family7FirstCrossingFamilyGraphBucketExactCardBandV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8Family7LowerBucketGenericNativeBranchCoreCapFreeV1
open Family8Family7LowerBucketGenericNativeBranchCoreV1
open Family8Family7PositiveBandLowerFibreFloorV1
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- The same frozen graph automatically produces a cap-free lower-bucket
native core.  All analytic windows are the canonical zero/universal choice;
the exact-card band, positive fibre floor, and retained native source mass
are outputs. -/
theorem exists_sameGraph_zeroWindow_lowerBucketNativeCore_capFree
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
            D.globalScale <= 32 := by
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
  let Q := Classical.choice R.graphCertificate
  have hgraphMass : Z.shadingMass ≠ 0 := by
    simpa only [Z] using Q.graph_mass_ne_zero
  obtain ⟨n, hnOne, hnCard, hband⟩ :=
    exists_firstCrossingFamilyGraphBucket_positiveExactCardBand
      R.axis R.label F P R.A R.k hgraphMass
  obtain ⟨fibreFloor, hfibreFloor, hlowerBand⟩ :=
    exists_positive_fibreFloor_preserving_multiplicityBand
      Z graph f0 hf0.measurable X0 hX0 I0 hI0 n n
        (by
          simpa only [firstCrossingFamilyGraphBucketZeroPhysical,
            VS, graph, Z, f0, X0, I0] using hband)
  have hf : forall z, HasDerivAt f0 (f0 z) z := by
    intro z
    simpa only [f0] using (hasDerivAt_const z (0 : Real))
  have hnative := exists_lowerBucket_genericNativeBranchCore_capFree
    VS Z graph f0 hf0 X0 hX0 I0 hI0 fibreFloor
      f0 f0 0 0 le_rfl hf hf 0 0 1 n n htau htauSixteen
      (by norm_num)
      (by simpa only [VS, graph, Z, f0, hf0, X0, hX0, I0, hI0]
        using hlowerBand)
      hnOne
  refine ⟨n, hnOne, ?_, fibreFloor, hfibreFloor, ?_⟩
  · simpa only [VS, graph] using hnCard
  · simpa only [VS, graph, Z, f0, hf0, X0, hX0, I0, hI0] using hnative

#print axioms exists_sameGraph_zeroWindow_lowerBucketNativeCore_capFree

end
end Family8CanonicalGraphFrozenGraphActiveLowerBucketNativeCoreCapFreeV1
