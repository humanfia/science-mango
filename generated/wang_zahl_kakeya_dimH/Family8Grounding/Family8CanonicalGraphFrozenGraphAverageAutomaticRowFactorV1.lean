import Family8Grounding.Family8CanonicalGraphFrozenHRowSelectionFirstConnectorV1
import Family8Grounding.Family8ContractedJohnActualTubeProxyV1
import Family8Grounding.Family8Prop66RowAutomaticForwardThickeningConnectorV1
import Family8Grounding.Family8SelectedOccurrenceMaxWitnessCommonScaleV1
import Mathlib.Tactic

/-!
# The canonical graph average enters its own automatic H-row factor

The Eq. (66) collapsed prefix contains the selected graph average.  Its
third factor is the frozen coarse average and must not be substituted into
this row estimate.  This file connects the literal graph average to the
automatic Prop. 6.6 factor of the H-row selected from that same graph.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8CanonicalGraphFrozenGraphAverageAutomaticRowFactorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8BufferedCommonScaleTubePlankV1
open Family8CanonicalGraphFrozenHRowSelectionFirstConnectorV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8ContractedJohnActualTubeProxyV1
open Family8HRowSourceAverageRetentionFromOwnerSelectionV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8Prop66Eq66ComposerFromHRowFreshV1
open Family8Prop66RowAutomaticForwardThickeningConnectorV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8SquarePlankHRowSelectionFirstSetupV1
open Family8StickyGraphContractedJohnProxyDatumV2
open Family8StickyFiberContractedJohnProxyDatumV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The fixed one-eighth common-width buffer is at most one half. -/
theorem graphRow_bufferedCommonWidth_le_half (d : NNReal) :
    bufferedCommonWidth d ≤ (2 : NNReal)⁻¹ := by
  calc
    bufferedCommonWidth d = (8 : NNReal)⁻¹ * maxWitnessCommonWidth d := rfl
    _ ≤ (8 : NNReal)⁻¹ * 1 :=
      mul_le_mul' le_rfl (maxWitnessCommonWidth_le_one d)
    _ ≤ (2 : NNReal)⁻¹ := by
      apply NNReal.coe_le_coe.mp
      norm_num [NNReal.coe_mul, NNReal.coe_inv]

/-- For the H-row setup selected from the graph of `R`, the source average
is literally `R.graphAverage`.  Owner-bucket retention supplies `H.loss`,
and the automatic thickening theorem absorbs that same loss into the row
factor.  No displayed coefficient and no frozen-coarse comparison occurs. -/
theorem graphAverage_le_sameGraphAutomaticForwardProp66Factor
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    {fine : UniformTubeFamily tau fineIndex}
    {U : StickyScaleCover fine rho}
    {Q : ConvexFactorization fine.bodyFamily U.coarse.bodyFamily}
    {Y : Shading fine.bodyFamily} {fibreCF : ENNReal}
    (R : SameAssemblyFullCoefficientGraphIdentity fine U Q Y fibreCF)
    (htau : 0 < tau) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (htauRho : tau ≤ rho) (hk : R.k ∈ U.activeCoarse)
    (H : SquarePlankHRowSelectionFirstSetup
      (sameAssemblyGraphBufferedPlankDatum
        R htau hrho hrhoOne htauRho hk))
    {epsilonRow betaRow etaRow : Real}
    (B : HRowFreshPropertyBundle
      (sameAssemblyGraphBufferedPlankDatum
        R htau hrho hrhoOne htauRho hk)
      H.C H.q universalHRowCell universalHRowCell_measurable
      (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
        epsilonRow betaRow etaRow)
    (hepsilonRow : 0 ≤ epsilonRow)
    (hbetaRow0 : 0 ≤ betaRow) (hbetaRow2 : betaRow ≤ 2) :
    R.graphAverage ≤
      hRowFreshAutomaticForwardProp66Factor
        (sameAssemblyGraphBufferedPlankDatum
          R htau hrho hrhoOne htauRho hk)
        H.C H.q universalHRowCell universalHRowCell_measurable
        (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
        B (Fintype.card {i // i ∈ sameAssemblyGraph R} : NNReal) H.loss := by
  let Drow := sameAssemblyGraphBufferedPlankDatum
    R htau hrho hrhoOne htauRho hk
  letI : Nonempty {i // i ∈ sameAssemblyGraph R} :=
    Finset.nonempty_coe_sort.mpr
      (Classical.choice R.graphCertificate).graph_nonempty
  let M : NNReal := Fintype.card {i // i ∈ sameAssemblyGraph R}
  have ha : 0 < bufferedCommonWidth (contractedJohnProxyRadius tau rho) :=
    bufferedCommonWidth_pos
      (stickyFiberContractedJohnProxyDatum_delta_pos htau hrho)
  have hbHalf : bufferedCommonWidth (contractedJohnProxyRadius tau rho) ≤
      (2 : NNReal)⁻¹ :=
    graphRow_bufferedCommonWidth_le_half _
  have hthick : FrostmanThickenedPlankControl Drow M := by
    simpa only [Drow, M] using
      squarePlank_fintypeCard_frostmanThickenedPlankControl Drow ha
  have hcorrelationTop : H.loss ≠ (⊤ : ENNReal) := by
    unfold SquarePlankHRowSelectionFirstSetup.loss ownerBucketToHRowLoss
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _))
  have hThirdToRowAvg : HRowFreshActualThirdCorrelationObligation
      Drow H.C H.q universalHRowCell universalHRowCell_measurable
      (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
      B R.graphAverage H.loss := by
    unfold HRowFreshActualThirdCorrelationObligation
    simpa only [Drow] using
      graphAverage_le_setupLoss_mul_sameHRowAverage
        R htau hrho hrhoOne htauRho hk H B
  simpa only [Drow, M] using
    actualThirdAverage_le_automaticForwardProp66Factor
      Drow H.C H.q universalHRowCell universalHRowCell_measurable
      (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
      B M hthick R.graphAverage H.loss hcorrelationTop hThirdToRowAvg
      hbHalf ha le_rfl hepsilonRow hbetaRow0 hbetaRow2

#print axioms graphRow_bufferedCommonWidth_le_half
#print axioms graphAverage_le_sameGraphAutomaticForwardProp66Factor

end
end Family8CanonicalGraphFrozenGraphAverageAutomaticRowFactorV1
