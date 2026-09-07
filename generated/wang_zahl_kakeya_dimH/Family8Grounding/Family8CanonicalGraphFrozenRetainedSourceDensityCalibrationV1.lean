import Family8Grounding.Family8CanonicalGraphFrozenDisplayedPaymentTerminalComposerV1
import Mathlib.Tactic

/-!
# Same-graph calibration from the retained source density

The actual ledger already retains a source-density numerator inside the
literal shading used by the frozen graph.  This file isolates the weakest
division-free comparison still needed to turn that retained numerator into
the displayed coefficient.  All denominator nondegeneracy is recovered from
the same graph certificate; no graph, assembly, or label is reselected.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalGraphFrozenRetainedSourceDensityCalibrationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenDisplayedGraphLowerProducerV1
open Family8CanonicalGraphFrozenLowerBucketSourceDensityPaymentV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8Family7CoordinateToVerticalWeightedChartSourceV2
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {tau rho delta : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- The retained source-density numerator pays the displayed coefficient
after restoring exactly the three denominator factors occurring in the
same-graph density quotient. -/
theorem displayed_le_sourceDensityQuotient_of_retainedSourceDensityBudget
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau : 0 < tau)
    (displayed sourceDensity densityRetentionLoss : ENNReal)
    (hSourceDensity : densityRetentionLoss * sourceDensity <=
      (sourceActiveFineShading P Y).shadingDensity)
    (hBudget :
      displayed *
          (((R.A.loss : ENNReal) *
            (P.index.coarse.card : ENNReal)) * R.graphLoss) <=
        densityRetentionLoss * sourceDensity) :
    displayed <=
      ((sourceActiveFineShading P Y).shadingDensity /
          ((R.A.loss : ENNReal) *
            (P.index.coarse.card : ENNReal))) /
        R.graphLoss := by
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
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl hgraphLoss0) (Or.inl hgraphLossTop)).2
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl hbase0) (Or.inl hbaseTop)).2
  calc
    displayed * R.graphLoss * baseLoss =
        displayed * (baseLoss * R.graphLoss) := by ac_rfl
    _ <= densityRetentionLoss * sourceDensity := by
      simpa only [baseLoss] using hBudget
    _ <= (sourceActiveFineShading P Y).shadingDensity := hSourceDensity

/-- Terminal graph-average form in the exact displayed scalar used by the
actual-ledger closure. -/
theorem actualLedgerClosure_displayedInput_of_retainedSourceDensityBudget
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau : 0 < tau)
    (X selectorLoss sourceDensity densityRetentionLoss : ENNReal)
    (outputEta : Real)
    (hSourceDensity : densityRetentionLoss * sourceDensity <=
      (sourceActiveFineShading P Y).shadingDensity)
    (hBudget :
      (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X)) *
          (((R.A.loss : ENNReal) *
            (P.index.coarse.card : ENNReal)) * R.graphLoss) <=
        densityRetentionLoss * sourceDensity) :
    selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) <=
      R.graphAverage := by
  exact
    (displayed_le_sourceDensityQuotient_of_retainedSourceDensityBudget
      R htau
        (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X))
        sourceDensity densityRetentionLoss hSourceDensity hBudget).trans
      (sourceDensityQuotient_le_graphAverage R)

#print axioms
  displayed_le_sourceDensityQuotient_of_retainedSourceDensityBudget
#print axioms
  actualLedgerClosure_displayedInput_of_retainedSourceDensityBudget

end
end Family8CanonicalGraphFrozenRetainedSourceDensityCalibrationV1
