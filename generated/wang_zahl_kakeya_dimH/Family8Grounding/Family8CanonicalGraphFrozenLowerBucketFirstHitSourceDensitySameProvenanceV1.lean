import Family8Grounding.Family8CanonicalGraphFrozenLowerBucketSourceDensityPaymentV1
import Family8Grounding.Family8NativeToGenericWeightedFirstHitPaymentAdapterV1
import Family8Grounding.Family8CanonicalGraphFrozenLowerBucketGenericFirstHitPaymentV1
import Mathlib.Tactic

/-!
# Same-provenance lower-bucket first-hit and source-density payments

The old native-to-generic adapter retains a genuine weighted first-hit
payment, but its physical datum is the old sixteenth-trace physical.  It
therefore cannot be identified with the graph-frozen lower-bucket physical.
The generic producer imported above instead performs the high/low split on
the literal lower-bucket datum.

This file records the maximal honest common interface: the norm cell, native
source mass, generic high/low payment, and source-density payment all use the
same `R`, graph, lower-bucket physical, label, and generic core `D`.  No
displayed-coefficient calibration is assumed or manufactured here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenLowerBucketFirstHitSourceDensitySameProvenanceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenLowerBucketGenericFirstHitPaymentV1
open Family8CanonicalGraphFrozenLowerBucketSourceDensityPaymentV1
open Family8CanonicalGraphFrozenDisplayedGraphLowerProducerV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7CoordinateToVerticalWeightedChartSourceV2
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7LowerBucketGenericNativeBranchCoreV1
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8ShadingAwareGenericNativeBranchCoreV2
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-! ## The honest division-free calibration seam -/

/-- The weakest scalar input which turns the retained lower-bucket payment
into a lower bound for a displayed coefficient.  The three factors on the
left are the literal source-family volume, frozen-assembly/coarse-card loss,
and graph-bucket loss attached to the same `R`.  In particular, this
predicate does not follow merely from positivity of `fibreFloor` or from
volume retention of a fibre-level selector. -/
def SameGraphLowerBucketDisplayedCalibration
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (fibreFloor : ENNReal)
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
    (displayed : ENNReal) : Prop :=
  displayed *
      (familyVolume (sourceActiveFineFamily P) *
        (((R.A.loss : ENNReal) *
            (P.index.coarse.card : ENNReal)) * R.graphLoss)) <=
    fibreFloor * D.sourceMass

/-- A division-free calibration for the literal lower-bucket source mass
feeds the source-density quotient and hence the average multiplicity of the
same frozen graph.  All denominator nondegeneracy is proved from the graph
certificate; it is not exposed as an extra premise. -/
theorem displayed_le_graphAverage_of_sameGraph_lowerBucketCalibration
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau : 0 < tau)
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
    (hCalibration : SameGraphLowerBucketDisplayedCalibration
      R fibreFloor D displayed) :
    displayed <= R.graphAverage := by
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let Q := Classical.choice R.graphCertificate
  have hgraphMass : Z.shadingMass ≠ 0 := by
    simpa only [Z] using Q.graph_mass_ne_zero
  have hsourceMass : (sourceActiveFineShading P Y).shadingMass ≠ 0 := by
    apply bot_lt_iff_ne_bot.mp
    exact (bot_lt_iff_ne_bot.mpr hgraphMass).trans_le
      (by simpa only [Z] using graphShadingMass_le_sourceActiveFineShadingMass R)
  have hsourceVolume : familyVolume (sourceActiveFineFamily P) ≠ 0 := by
    intro hzero
    apply hsourceMass
    exact le_antisymm
      ((sourceActiveFineShading P Y).shadingMass_le_familyVolume.trans_eq
        hzero)
      bot_le
  have hloss0 : (R.A.loss : ENNReal) ≠ 0 := by
    intro hzero
    apply hsourceMass
    apply le_antisymm
    · have hretained :=
        sourceActiveFineShading_mass_le_loss_mul_actualRefinementShading R.A
      simpa only [hzero, zero_mul] using hretained
    · exact bot_le
  obtain ⟨i, hiGraph⟩ := Q.graph_nonempty
  have hiSource : i ∈ VS.source :=
    (mem_verticalSourceGraphCBucketFiber_iff
      ((tau : Real) / 2) VS R.label i).mp hiGraph |>.1
  have hiFiber : i ∈ P.index.fiber R.k := by
    change i ∈ verticalSourceDirectionChartFiber
      F (P.index.fiber R.k) R.axis at hiSource
    exact (mem_verticalSourceDirectionChartFiber_iff
      F (P.index.fiber R.k) R.axis i).mp hiSource |>.1
  have hiFine : i ∈ P.index.fine :=
    (P.index.mem_fiber i R.k).mp hiFiber |>.1
  have hparent : P.index.parent i = R.k :=
    (P.index.mem_fiber i R.k).mp hiFiber |>.2
  have hkCoarse : R.k ∈ P.index.coarse := by
    simpa only [hparent] using P.index.parent_mem i hiFine
  have hcard0 : (P.index.coarse.card : ENNReal) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨R.k, hkCoarse⟩
  have heta : 0 < ((tau : Real) / 2) := by
    exact div_pos (NNReal.coe_pos.mpr htau) (by norm_num)
  have hcandidate :
      verticalGraphCBucket
          ((tau : Real) / 2) (VS.family.tubes i) ∈
        verticalGraphCBucketCandidateLabels ((tau : Real) / 2) :=
    verticalGraphCBucket_mem_candidates_of_vertical_half heta
      (VS.source_direction_final_half i hiSource)
  have hbucketLossPos :
      0 < verticalGraphCBucketLoss ((tau : Real) / 2) :=
    Finset.card_pos.mpr ⟨_, hcandidate⟩
  have hgraphLossNat :
      0 < 3 * verticalGraphCBucketLoss ((tau : Real) / 2) :=
    Nat.mul_pos (by norm_num) hbucketLossPos
  have hgraphLoss0 : R.graphLoss ≠ 0 := by
    unfold SameAssemblyFullCoefficientGraphIdentity.graphLoss
    exact_mod_cast hgraphLossNat.ne'
  let baseLoss : ENNReal :=
    (R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal)
  have hbase0 : baseLoss ≠ 0 := mul_ne_zero hloss0 hcard0
  have hbaseTop : baseLoss ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top R.A.loss)
      (ENNReal.natCast_ne_top P.index.coarse.card)
  have hgraphLossTop : R.graphLoss ≠ ∞ := by
    unfold SameAssemblyFullCoefficientGraphIdentity.graphLoss
    exact ENNReal.natCast_ne_top _
  have hdisplayPayment :
      displayed <=
        (((fibreFloor * D.sourceMass) /
            familyVolume (sourceActiveFineFamily P)) /
          baseLoss) / R.graphLoss := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hgraphLoss0) (Or.inl hgraphLossTop)).2
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hbase0) (Or.inl hbaseTop)).2
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hsourceVolume)
        (Or.inl (familyVolume_ne_top (sourceActiveFineFamily P)))).2
    simpa only [SameGraphLowerBucketDisplayedCalibration, baseLoss,
      mul_assoc, mul_left_comm, mul_comm] using hCalibration
  have hpayment := lowerBucketNormCellPayment_le_sourceDensityQuotient
    R n hn fibreFloor normLabel D hsourceEq
  have hsourceGraph := sourceDensityQuotient_le_graphAverage R
  simpa only [baseLoss] using hdisplayPayment.trans (hpayment.trans hsourceGraph)

/-- The same graph-frozen lower-bucket core simultaneously carries the
generic first-hit high/low payment and the retained source-density payment.
Every dependent object is selected once by the upstream generic producer.
-/
theorem exists_sameGraph_zeroWindow_lowerBucket_firstHit_and_sourceDensityPayment_capFree
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
            (((fibreFloor * D.sourceMass) /
                  familyVolume (sourceActiveFineFamily P)) /
                ((R.A.loss : ENNReal) *
                  (P.index.coarse.card : ENNReal))) /
                R.graphLoss <=
              ((sourceActiveFineShading P Y).shadingDensity /
                  ((R.A.loss : ENNReal) *
                    (P.index.coarse.card : ENNReal))) /
                R.graphLoss /\
            exists G : GenericNativeHighGeometry D,
              (D.sourceMass / 2 <=
                  ∑ c ∈ D.low, volume (D.cell c.1)) \/
                D.sourceMass / 2 <=
                  actualAllCenterPostNormBinLoss tau D.globalScale
                      physical.ambient.card *
                    ∑ c : D.HighCenter,
                      volume (genericNativeHighActivePatternSource D G c) := by
  dsimp only
  obtain ⟨n, hnOne, hnCard, fibreFloor, hfibreFloor, normLabel,
      hnormLabel, D, hglobalScale, hsourceEq, hbandRetention,
      hsourcePos, hglobalUpper, G, hbranch⟩ :=
    exists_sameGraph_zeroWindow_lowerBucket_genericFirstHitPayment_capFree
      R htau htauSixteen
  refine ⟨n, hnOne, hnCard, fibreFloor, hfibreFloor, normLabel,
    hnormLabel, D, hglobalScale, hsourceEq, hbandRetention,
    hsourcePos, hglobalUpper, ?_, G, hbranch⟩
  exact lowerBucketNormCellPayment_le_sourceDensityQuotient
    R n hnOne fibreFloor normLabel D hsourceEq

#print axioms
  exists_sameGraph_zeroWindow_lowerBucket_firstHit_and_sourceDensityPayment_capFree
#print axioms displayed_le_graphAverage_of_sameGraph_lowerBucketCalibration

end
end Family8CanonicalGraphFrozenLowerBucketFirstHitSourceDensitySameProvenanceV1
