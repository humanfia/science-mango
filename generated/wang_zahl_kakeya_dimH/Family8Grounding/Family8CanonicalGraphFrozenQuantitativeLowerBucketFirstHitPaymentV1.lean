import Family8Grounding.Family8CanonicalGraphFrozenLowerBucketFirstHitSourceDensitySameProvenanceV1
import Family8Grounding.Family8CanonicalGraphFrozenPositiveBandVolumeFiniteV1
import Family8Grounding.Family8Family7QuantitativeFibreFloorSelectionV2
import FamilyStickyCinematicL32CriticalSingleDyadicBinFactorPositiveV1
import Mathlib.Tactic

/-!
# Quantitative lower-bucket payment on the literal frozen graph

The graph, shading, exact-card band, dyadic fibre floor, norm cell, native
core, and generic high geometry are selected once.  The fibre selector keeps
half of the positive exact-card band's planar volume and the norm selector
keeps its usual exact dyadic-bin share.

These two automatic retentions do not produce an absolute lower scale for
the selected fibre floor.  The sole remaining analytic input is therefore
recorded as a division-free tail budget against the pre-floor positive band.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenQuantitativeLowerBucketFirstHitPaymentV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenLowerBucketFirstHitSourceDensitySameProvenanceV1
open Family8CanonicalGraphFrozenLowerBucketSourceDensityPaymentV1
open Family8CanonicalGraphFrozenPositiveBandVolumeFiniteV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8Family7FirstCrossingFamilyGraphBucketExactCardBandV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7GenericNativeHighGeometryOfBucketV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7GenericNativeHighOccurrenceSourceRetentionSumV1
open Family8Family7LowerBucketGenericNativeBranchCoreCapFreeV1
open Family8Family7LowerBucketGenericNativeBranchCoreV1
open Family8Family7WeightedVerticalGraphCBucketActualBridgeV1
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8ShadingAwareGenericNativeBranchCoreV2
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32CriticalSingleDyadicBinFactorPositiveV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- The exact automatic loss after the dyadic fibre-floor selector and the
existing norm-cell selector. -/
def quantitativeLowerBucketSelectionLoss (tau : NNReal) : ENNReal :=
  Family8Family7QuantitativeFibreFloorSelectionV2.fibreLevelBinLoss *
    (continuumCriticalSingleDyadicBinFactor (tau : Real) 16 : ENNReal)

theorem quantitativeLowerBucketSelectionLoss_ne_zero
    (htau : 0 < tau) (htauSixteen : (tau : Real) <= 16) :
    quantitativeLowerBucketSelectionLoss tau ≠ 0 := by
  unfold quantitativeLowerBucketSelectionLoss
  apply mul_ne_zero
  · norm_num [Family8Family7QuantitativeFibreFloorSelectionV2.fibreLevelBinLoss]
  · exact continuumCriticalSingleDyadicBinFactor_cast_ne_zero
      (NNReal.coe_pos.mpr htau) htauSixteen

theorem quantitativeLowerBucketSelectionLoss_ne_top (tau : NNReal) :
    quantitativeLowerBucketSelectionLoss tau ≠ ∞ := by
  unfold quantitativeLowerBucketSelectionLoss
  apply ENNReal.mul_ne_top
  · norm_num [Family8Family7QuantitativeFibreFloorSelectionV2.fibreLevelBinLoss]
  · exact continuumCriticalSingleDyadicBinFactor_cast_ne_top
      (tau : Real) 16

/-- The only non-automatic scalar left after quantitative fibre and norm
selection.  It compares the desired displayed coefficient, with every
literal graph-selection denominator restored, to the selected fibre floor
times the pre-floor positive exact-card band. -/
def SameGraphQuantitativeLowerBucketTailBudget
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (n : Nat) (fibreFloor displayed : ENNReal) : Prop :=
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real -> Real := fun _ => 0
  let positive := shadingAwareProjectedPhysical Z graph f0 measurable_const
    Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
  quantitativeLowerBucketSelectionLoss tau *
      (displayed *
        (familyVolume (sourceActiveFineFamily P) *
          (((R.A.loss : ENNReal) *
              (P.index.coarse.card : ENNReal)) * R.graphLoss))) <=
    fibreFloor * volume (positive.multiplicityBand n n)

/-- The automatic two-stage volume retention converts the residual tail
budget into the exact same-`D` calibration consumed by the source-density
payment adapter. -/
theorem sameGraphLowerBucketCalibration_of_quantitativeRetention
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau : 0 < tau) (htauSixteen : (tau : Real) <= 16)
    (n : Nat) (fibreFloor : ENNReal)
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
    (hretained :
      let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
      let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
        VS R.label
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      let f0 : Real -> Real := fun _ => 0
      let positive := shadingAwareProjectedPhysical Z graph f0 measurable_const
        Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
      volume (positive.multiplicityBand n n) <=
        quantitativeLowerBucketSelectionLoss tau * D.sourceMass)
    (displayed : ENNReal)
    (hTail : SameGraphQuantitativeLowerBucketTailBudget
      R n fibreFloor displayed) :
    SameGraphLowerBucketDisplayedCalibration R fibreFloor D displayed := by
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real -> Real := fun _ => 0
  let positive := shadingAwareProjectedPhysical Z graph f0 measurable_const
    Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
  let loss := quantitativeLowerBucketSelectionLoss tau
  have hfloorRetained :
      fibreFloor * volume (positive.multiplicityBand n n) <=
        loss * (fibreFloor * D.sourceMass) := by
    calc
      fibreFloor * volume (positive.multiplicityBand n n) <=
          fibreFloor * (loss * D.sourceMass) :=
        mul_le_mul_right
          (by simpa only [positive, loss] using hretained) fibreFloor
      _ = loss * (fibreFloor * D.sourceMass) := by ac_rfl
  have htail' :
      loss *
          (displayed *
            (familyVolume (sourceActiveFineFamily P) *
              (((R.A.loss : ENNReal) *
                (P.index.coarse.card : ENNReal)) * R.graphLoss))) <=
        fibreFloor * volume (positive.multiplicityBand n n) := by
    simpa only [SameGraphQuantitativeLowerBucketTailBudget, VS, graph,
      Z, f0, positive, loss] using hTail
  have hscaled :
      loss *
          (displayed *
            (familyVolume (sourceActiveFineFamily P) *
              (((R.A.loss : ENNReal) *
                (P.index.coarse.card : ENNReal)) * R.graphLoss))) <=
        loss * (fibreFloor * D.sourceMass) :=
    htail'.trans hfloorRetained
  have hcancel := (ENNReal.mul_le_mul_iff_right
    (quantitativeLowerBucketSelectionLoss_ne_zero htau htauSixteen)
    (quantitativeLowerBucketSelectionLoss_ne_top tau)).mp (by
      simpa only [loss] using hscaled)
  simpa only [SameGraphLowerBucketDisplayedCalibration] using hcancel

/-- Full quantitative same-provenance producer.  Besides the high/low
first-hit payment and the source-density payment, it exports the automatic
combined volume retention and a callback showing that the sole tail budget
implies the displayed graph-average bound. -/
theorem exists_sameGraph_zeroWindow_quantitativeLowerBucket_firstHitPayment
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
    let positive := shadingAwareProjectedPhysical Z graph f0 hf0.measurable
      X0 hX0 I0 hI0
    exists n : Nat, 1 <= n /\ n <= graph.card /\
      exists level : Nat,
        let fibreFloor :=
          Family8Family7QuantitativeFibreFloorSelectionV2.dyadicFibreFloor level
        let physical := shadingAwareProjectedPhysicalLowerBucket Z graph f0
          hf0.measurable X0 hX0 I0 hI0 fibreFloor
        0 < fibreFloor /\
        volume (positive.multiplicityBand n n) <=
          Family8Family7QuantitativeFibreFloorSelectionV2.fibreLevelBinLoss *
            volume (physical.multiplicityBand n n) /\
        ∃ normLabel ∈ Finset.Icc (dyadicCeilBucket (tau : Real))
            (dyadicCeilBucket 16),
          let normScale := actualProjectedAmbientNormScale
            VS.family physical 16 0
          let E_norm := continuumCriticalSingleDyadicCell
            (physical.multiplicityBand n n) normScale normLabel
          exists D : LowerBucketNativeBranchCore VS Z graph f0 hf0
              X0 hX0 I0 hI0 fibreFloor,
            D.globalScale = dyadicCeilUpper normLabel /\
            volume E_norm = D.sourceMass /\
            volume (physical.multiplicityBand n n) /
                (continuumCriticalSingleDyadicBinFactor
                  (tau : Real) 16 : ENNReal) <= D.sourceMass /\
            0 < D.sourceMass /\
            D.globalScale <= 32 /\
            volume (positive.multiplicityBand n n) <=
              quantitativeLowerBucketSelectionLoss tau * D.sourceMass /\
            (((fibreFloor * D.sourceMass) /
                  familyVolume (sourceActiveFineFamily P)) /
                ((R.A.loss : ENNReal) *
                  (P.index.coarse.card : ENNReal))) /
                R.graphLoss <=
              ((sourceActiveFineShading P Y).shadingDensity /
                  ((R.A.loss : ENNReal) *
                    (P.index.coarse.card : ENNReal))) /
                R.graphLoss /\
            (exists G : GenericNativeHighGeometry D,
              (D.sourceMass / 2 <=
                  ∑ c ∈ D.low, volume (D.cell c.1)) \/
                D.sourceMass / 2 <=
                  actualAllCenterPostNormBinLoss tau D.globalScale
                      physical.ambient.card *
                    ∑ c : D.HighCenter,
                      volume (genericNativeHighActivePatternSource D G c)) /\
            forall displayed : ENNReal,
              SameGraphQuantitativeLowerBucketTailBudget
                  R n fibreFloor displayed ->
                displayed <= R.graphAverage := by
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
  let positive := shadingAwareProjectedPhysical Z graph f0 hf0.measurable
    X0 hX0 I0 hI0
  let Q := Classical.choice R.graphCertificate
  have hgraphMass : Z.shadingMass ≠ 0 := by
    simpa only [Z] using Q.graph_mass_ne_zero
  obtain ⟨n, hnOne, hnCard, hband⟩ :=
    exists_firstCrossingFamilyGraphBucket_positiveExactCardBand
      R.axis R.label F P R.A R.k (by simpa only [Z] using hgraphMass)
  have hband' : 0 < volume (positive.multiplicityBand n n) := by
    simpa only [firstCrossingFamilyGraphBucketZeroPhysical,
      VS, graph, Z, f0, positive, X0, I0] using hband
  have hbandFinite :
      volume (positive.multiplicityBand n n) ≠ ∞ := by
    simpa only [VS, graph, Z, f0, hf0, X0, I0, positive] using
      sameGraph_zeroWindow_positiveExactCardBand_volume_ne_top R n hnOne
  obtain ⟨level, hfibreFloor, hfloorRetention⟩ :=
    Family8Family7QuantitativeFibreFloorSelectionV2.exists_dyadic_fibreFloor_half_multiplicityBand
      Z graph f0 hf0.measurable X0 hX0 I0 hI0 n n hband' hbandFinite
  let fibreFloor :=
    Family8Family7QuantitativeFibreFloorSelectionV2.dyadicFibreFloor level
  let physical := shadingAwareProjectedPhysicalLowerBucket Z graph f0
    hf0.measurable X0 hX0 I0 hI0 fibreFloor
  have hlowerBand : 0 < volume (physical.multiplicityBand n n) := by
    apply bot_lt_iff_ne_bot.mpr
    intro hzero
    have hzeroSource : volume (positive.multiplicityBand n n) <= 0 := by
      calc
        volume (positive.multiplicityBand n n) <=
            Family8Family7QuantitativeFibreFloorSelectionV2.fibreLevelBinLoss *
              volume (physical.multiplicityBand n n) := by
          simpa only [positive, physical, fibreFloor] using hfloorRetention
        _ = 0 := by simp [hzero]
    exact (not_le_of_gt hband') hzeroSource
  have hf : forall z, HasDerivAt f0 (f0 z) z := by
    intro z
    simpa only [f0] using (hasDerivAt_const z (0 : Real))
  obtain ⟨normLabel, hnormLabel, D, hglobalScale, hsourceEq,
      hnormRetention, hsourcePos, hglobalUpper⟩ :=
    exists_lowerBucket_genericNativeBranchCore_capFree
      VS Z graph f0 hf0 X0 hX0 I0 hI0 fibreFloor
      f0 f0 0 0 le_rfl hf hf 0 0 1 n n htau htauSixteen
      (by norm_num) (by simpa only [physical] using hlowerBand) hnOne
  let normLoss : ENNReal :=
    (continuumCriticalSingleDyadicBinFactor (tau : Real) 16 : ENNReal)
  have hnorm0 : normLoss ≠ 0 := by
    exact continuumCriticalSingleDyadicBinFactor_cast_ne_zero
      (NNReal.coe_pos.mpr htau) htauSixteen
  have hnormTop : normLoss ≠ ∞ :=
    continuumCriticalSingleDyadicBinFactor_cast_ne_top (tau : Real) 16
  have hlowerToSource :
      volume (physical.multiplicityBand n n) <=
        normLoss * D.sourceMass := by
    have hcross := (ENNReal.div_le_iff_le_mul
      (Or.inl hnorm0) (Or.inl hnormTop)).mp (by
        simpa only [normLoss] using hnormRetention)
    simpa only [mul_comm] using hcross
  have htotalRetention :
      volume (positive.multiplicityBand n n) <=
        quantitativeLowerBucketSelectionLoss tau * D.sourceMass := by
    calc
      volume (positive.multiplicityBand n n) <=
          Family8Family7QuantitativeFibreFloorSelectionV2.fibreLevelBinLoss *
            volume (physical.multiplicityBand n n) := by
        simpa only [positive, physical, fibreFloor] using hfloorRetention
      _ <= Family8Family7QuantitativeFibreFloorSelectionV2.fibreLevelBinLoss *
            (normLoss * D.sourceMass) :=
        mul_le_mul_right hlowerToSource _
      _ = quantitativeLowerBucketSelectionLoss tau * D.sourceMass := by
        simp only [quantitativeLowerBucketSelectionLoss, normLoss, mul_assoc]
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
      simpa only [physical,
        shadingAwareProjectedPhysicalLowerBucket] using hi)
  have hbranch :
      (D.sourceMass / 2 <= ∑ c ∈ D.low, volume (D.cell c.1)) \/
        D.sourceMass / 2 <=
          actualAllCenterPostNormBinLoss tau D.globalScale
              physical.ambient.card *
            ∑ c : D.HighCenter,
              volume (genericNativeHighActivePatternSource D G c) := by
    rcases (GenericNativeBranchCore.payloadAt_spec D).2.1 with hhigh | hlow
    · exact Or.inr
        (sourceMass_half_le_postNormBinLoss_mul_sum_genericActivePatternSource
          D G hhigh)
    · exact Or.inl hlow
  have hpayment := lowerBucketNormCellPayment_le_sourceDensityQuotient
    R n hnOne fibreFloor normLabel D (by
      simpa only [VS, graph, Z, f0, physical] using hsourceEq)
  refine ⟨n, hnOne, hnCard, level, hfibreFloor, ?_, normLabel,
    hnormLabel, D, hglobalScale, hsourceEq, hnormRetention, hsourcePos,
    hglobalUpper, htotalRetention, hpayment, ⟨G, hbranch⟩, ?_⟩
  · simpa only [positive, physical, fibreFloor] using hfloorRetention
  · intro displayed hTail
    apply displayed_le_graphAverage_of_sameGraph_lowerBucketCalibration
      R htau n hnOne fibreFloor normLabel D
        (by simpa only [VS, graph, Z, f0, physical] using hsourceEq)
        displayed
    exact sameGraphLowerBucketCalibration_of_quantitativeRetention
      R htau htauSixteen n fibreFloor D
        (by simpa only [VS, graph, Z, f0, positive] using htotalRetention)
        displayed hTail

#print axioms quantitativeLowerBucketSelectionLoss_ne_zero
#print axioms quantitativeLowerBucketSelectionLoss_ne_top
#print axioms sameGraphLowerBucketCalibration_of_quantitativeRetention
#print axioms
  exists_sameGraph_zeroWindow_quantitativeLowerBucket_firstHitPayment

end
end Family8CanonicalGraphFrozenQuantitativeLowerBucketFirstHitPaymentV1
