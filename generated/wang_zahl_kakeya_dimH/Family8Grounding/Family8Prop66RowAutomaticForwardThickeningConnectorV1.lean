import Family8Grounding.Family8Prop66RowAugmentedFrostmanConstantConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8Prop66RowAutomaticForwardThickeningConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
open Family8Prop66Eq66ComposerFromHRowFreshV1
open Family8Prop66RowCrossScaleAggregationV1
open Family8Prop66RowAugmentedFrostmanConstantConnectorV1
open Family8FrostmanRHSScaleVolumeAlgebraV4
open Family8PlankFrostmanCopyLossAlgebraV2

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe v

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Automatic M enlargement for the remaining forward coefficient

For a finite correlation loss, the complete finite coefficient can be paid by
an honest larger thickening parameter.  The choice
`M+ = max M (effectiveLoss / (a/b))` remains a valid thick-control parameter
by monotonicity and gives `effectiveLoss <= M+ * (a/b)` by construction.
No row or fresh subtype is reselected.
-/

/-- Thickened-plank control is monotone in its numerical parameter. -/
theorem frostmanThickenedPlankControl_mono
    {D : ShadedConvexPlankFamily iota a b} {M M' : NNReal}
    (h : FrostmanThickenedPlankControl D M) (hMM' : M ≤ M') :
    FrostmanThickenedPlankControl D M' := by
  refine ⟨h.1.trans hMM', ?_⟩
  intro theta hratio htheta i
  exact (h.2 theta hratio htheta i).trans (by gcongr)

/-- Finiteness of the complete forward coefficient. -/
theorem hRowFreshEffectiveLoss_ne_top
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta)
    (correlationLoss : ENNReal) (hcorrelationTop : correlationLoss ≠ ∞)
    (hepsilon : 0 ≤ epsilon) (hbeta0 : 0 ≤ beta) :
    hRowFreshEffectiveLoss
      D C q cell hcell selectedCells hmass hactive B correlationLoss ≠ ∞ := by
  have hfresh : hRowFreshLoss
      D C q cell hcell selectedCells hmass hactive B.tau B.S ≠ ∞ := by
    unfold hRowFreshLoss
    simp
  have hepsilonTop : (8 : ENNReal) ^ epsilon ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hepsilon (by norm_num)
  have htwobeta : 0 ≤ 2 * beta := by positivity
  have hbetaTop : (8 : ENNReal) ^ (2 * beta) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg htwobeta (by norm_num)
  unfold hRowFreshEffectiveLoss
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top hcorrelationTop hfresh)
    (ENNReal.mul_ne_top hepsilonTop hbetaTop)

/-- The finite NNReal thickening parameter which automatically pays the
complete forward coefficient at the true plank aspect ratio. -/
def hRowFreshAutomaticForwardM
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta)
    (M : NNReal) (correlationLoss : ENNReal) : NNReal :=
  max M
    (hRowFreshEffectiveLoss
        D C q cell hcell selectedCells hmass hactive B correlationLoss /
      ((a / b : NNReal) : ENNReal)).toNNReal

/-- The original thick control transports to the automatic parameter. -/
theorem hRowFresh_frostmanThickenedPlankControl_automaticForwardM
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta)
    (M : NNReal) (hthick : FrostmanThickenedPlankControl D M)
    (correlationLoss : ENNReal) :
    FrostmanThickenedPlankControl D
      (hRowFreshAutomaticForwardM
        D C q cell hcell selectedCells hmass hactive B M correlationLoss) := by
  apply frostmanThickenedPlankControl_mono hthick
  unfold hRowFreshAutomaticForwardM
  exact le_max_left _ _

/-- By construction, the automatic parameter pays the complete forward loss
times the exact aspect ratio. -/
theorem hRowFresh_effectiveLoss_le_automaticForwardM_mul_aspect
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta)
    (M : NNReal) (correlationLoss : ENNReal)
    (hcorrelationTop : correlationLoss ≠ ∞)
    (ha : 0 < a) (hab : a ≤ b)
    (hepsilon : 0 ≤ epsilon) (hbeta0 : 0 ≤ beta) :
    hRowFreshEffectiveLoss
        D C q cell hcell selectedCells hmass hactive B correlationLoss ≤
      (hRowFreshAutomaticForwardM
          D C q cell hcell selectedCells hmass hactive B M correlationLoss : ENNReal) *
        ((a / b : NNReal) : ENNReal) := by
  have hb : 0 < b := ha.trans_le hab
  have haspectNN : 0 < a / b := div_pos ha hb
  have haspect0 : ((a / b : NNReal) : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr haspectNN.ne'
  have haspectTop : ((a / b : NNReal) : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have heffectiveTop := hRowFreshEffectiveLoss_ne_top
    D C q cell hcell selectedCells hmass hactive B correlationLoss
      hcorrelationTop hepsilon hbeta0
  have hratioTop : hRowFreshEffectiveLoss
        D C q cell hcell selectedCells hmass hactive B correlationLoss /
      ((a / b : NNReal) : ENNReal) ≠ ∞ :=
    ENNReal.div_ne_top heffectiveTop haspect0
  have hratio : hRowFreshEffectiveLoss
        D C q cell hcell selectedCells hmass hactive B correlationLoss /
        ((a / b : NNReal) : ENNReal) ≤
      (hRowFreshAutomaticForwardM
          D C q cell hcell selectedCells hmass hactive B M correlationLoss : ENNReal) := by
    rw [← ENNReal.coe_toNNReal hratioTop]
    exact ENNReal.coe_le_coe.mpr (le_max_right _ _)
  calc
    hRowFreshEffectiveLoss
          D C q cell hcell selectedCells hmass hactive B correlationLoss =
        (hRowFreshEffectiveLoss
            D C q cell hcell selectedCells hmass hactive B correlationLoss /
          ((a / b : NNReal) : ENNReal)) *
            ((a / b : NNReal) : ENNReal) :=
      (ENNReal.div_mul_cancel haspect0 haspectTop).symm
    _ ≤ (hRowFreshAutomaticForwardM
            D C q cell hcell selectedCells hmass hactive B M correlationLoss : ENNReal) *
          ((a / b : NNReal) : ENNReal) := mul_le_mul' hratio le_rfl

/-- The enlarged Frostman choice at the automatic thickening parameter. -/
def hRowFreshAutomaticForwardFrostmanConstant
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta)
    (M : NNReal) (correlationLoss : ENNReal) : ENNReal :=
  hRowFreshAugmentedFrostmanConstant
    D C q cell hcell selectedCells hmass hactive B
      (hRowFreshAutomaticForwardM
        D C q cell hcell selectedCells hmass hactive B M correlationLoss)

/-- The final factor using both monotone choices, `M+` and `CF+`. -/
def hRowFreshAutomaticForwardProp66Factor
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta)
    (M : NNReal) (correlationLoss : ENNReal) : ENNReal :=
  hRowFreshAugmentedProp66Factor
    D C q cell hcell selectedCells hmass hactive B
      (hRowFreshAutomaticForwardM
        D C q cell hcell selectedCells hmass hactive B M correlationLoss)

/-- The automatic Frostman choice remains valid on the literal same row. -/
theorem hRowFresh_isFrostmanIn_automaticForward
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta)
    (M : NNReal) (correlationLoss : ENNReal) :
    IsFrostmanIn
      (hRowFreshAutomaticForwardFrostmanConstant
        D C q cell hcell selectedCells hmass hactive B M correlationLoss)
      (HRowFreshPlankDatum
        D C q cell hcell selectedCells hmass hactive B.tau B.S).family
      (HRowFreshPlankDatum
        D C q cell hcell selectedCells hmass hactive B.tau B.S).ambient := by
  exact hRowFresh_isFrostmanIn_augmented
    D C q cell hcell selectedCells hmass hactive B
      (hRowFreshAutomaticForwardM
        D C q cell hcell selectedCells hmass hactive B M correlationLoss)

/-- The automatic M/CF choices prove the mixed power without `hForward`. -/
theorem hRowFresh_effectiveLoss_mul_two_rpow_le_aspect_automaticFrostmanMix
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta)
    (M : NNReal) (hthick : FrostmanThickenedPlankControl D M)
    (correlationLoss : ENNReal) (hcorrelationTop : correlationLoss ≠ ∞)
    (ha : 0 < a) (hab : a ≤ b)
    (hepsilon : 0 ≤ epsilon) (hbeta0 : 0 ≤ beta) (hbeta2 : beta ≤ 2) :
    hRowFreshEffectiveLoss
        D C q cell hcell selectedCells hmass hactive B correlationLoss *
        (2 : ENNReal) ^ (1 - beta / 2) ≤
      ((a / b : NNReal) : ENNReal) *
        (hRowFreshAutomaticForwardFrostmanConstant
              D C q cell hcell selectedCells hmass hactive B M correlationLoss ^
            (1 - beta / 2) *
          (hRowFreshAutomaticForwardM
              D C q cell hcell selectedCells hmass hactive B M correlationLoss : ENNReal) ^
            (beta / 2)) := by
  let Mplus := hRowFreshAutomaticForwardM
    D C q cell hcell selectedCells hmass hactive B M correlationLoss
  let CFplus := hRowFreshAutomaticForwardFrostmanConstant
    D C q cell hcell selectedCells hmass hactive B M correlationLoss
  have hthickPlus := hRowFresh_frostmanThickenedPlankControl_automaticForwardM
    D C q cell hcell selectedCells hmass hactive B M hthick correlationLoss
  have hMposNN : 0 < Mplus := lt_of_lt_of_le zero_lt_one hthickPlus.1
  have hM0 : (Mplus : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hMposNN.ne'
  have hMtop : (Mplus : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hp : 0 ≤ 1 - beta / 2 := by linarith
  have heffective := hRowFresh_effectiveLoss_le_automaticForwardM_mul_aspect
    D C q cell hcell selectedCells hmass hactive B M correlationLoss
      hcorrelationTop ha hab hepsilon hbeta0
  have hcopy := hRowFresh_augmented_copyFactorBudget
    D C q cell hcell selectedCells hmass hactive B Mplus hthickPlus
  have hcopyPow : (2 : ENNReal) ^ (1 - beta / 2) ≤
      (CFplus / (Mplus : ENNReal)) ^ (1 - beta / 2) :=
    ENNReal.rpow_le_rpow hcopy hp
  calc
    hRowFreshEffectiveLoss
          D C q cell hcell selectedCells hmass hactive B correlationLoss *
          (2 : ENNReal) ^ (1 - beta / 2) ≤
        ((Mplus : ENNReal) * ((a / b : NNReal) : ENNReal)) *
          (CFplus / (Mplus : ENNReal)) ^ (1 - beta / 2) :=
      mul_le_mul' heffective hcopyPow
    _ = ((a / b : NNReal) : ENNReal) *
          ((Mplus : ENNReal) *
            (CFplus / (Mplus : ENNReal)) ^ (1 - beta / 2)) := by ac_rfl
    _ = ((a / b : NNReal) : ENNReal) *
          (CFplus ^ (1 - beta / 2) *
            (Mplus : ENNReal) ^ (beta / 2)) := by
      rw [copyLoss_rpow_eq_frostmanMix CFplus (Mplus : ENNReal) beta
        hM0 hMtop hbeta0 hbeta2]
    _ = ((a / b : NNReal) : ENNReal) *
        (hRowFreshAutomaticForwardFrostmanConstant
              D C q cell hcell selectedCells hmass hactive B M correlationLoss ^
            (1 - beta / 2) *
          (hRowFreshAutomaticForwardM
              D C q cell hcell selectedCells hmass hactive B M correlationLoss : ENNReal) ^
            (beta / 2)) := by rfl

/-- Exact automatic cross-row endpoint; neither `hCopy` nor `hForward` is an
input.  The price is displayed honestly in the chosen `M+` and `CF+`. -/
theorem hRowFresh_automaticCrossRowAggregation
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta)
    (M : NNReal) (hthick : FrostmanThickenedPlankControl D M)
    (correlationLoss : ENNReal) (hcorrelationTop : correlationLoss ≠ ∞)
    (hbHalf : b ≤ (2 : NNReal)⁻¹)
    (ha : 0 < a) (hab : a ≤ b) (hepsilon : 0 ≤ epsilon)
    (hbeta0 : 0 ≤ beta) (hbeta2 : beta ≤ 2) :
    HRowFreshAugmentedCrossRowAggregationObligation
      D C q cell hcell selectedCells hmass hactive B
        (hRowFreshAutomaticForwardM
          D C q cell hcell selectedCells hmass hactive B M correlationLoss)
        correlationLoss := by
  let Mplus := hRowFreshAutomaticForwardM
    D C q cell hcell selectedCells hmass hactive B M correlationLoss
  let selectedVolume := (HRowFreshSelectedDatum
    D C q cell hcell selectedCells hmass hactive B.tau B.S
      B.freshSelected).actualFamilyVolume
  let cardScaleVolume := hRowFreshCardScaleVolume
    D C q cell hcell selectedCells hmass hactive B
  let freshLoss := hRowFreshLoss
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  have hvolume : selectedVolume ≤ (2 : ENNReal) * cardScaleVolume := by
    simpa only [selectedVolume, cardScaleVolume] using
      hRowFreshSelected_actualFamilyVolume_le_two_cardScale
        D C q cell hcell selectedCells hmass hactive B hbHalf
  have htransport :=
    loss_mul_frostmanMultiplicityRHS_div_eight_le_source
      (delta := b) (selectedVolume := selectedVolume)
      (sourceVolume := cardScaleVolume)
      (loss := correlationLoss * freshLoss)
      (copyVolumeFactor := (2 : ENNReal))
      (epsilon := epsilon) (gamma := beta) hbeta2 hvolume
  have hmixed :=
    hRowFresh_effectiveLoss_mul_two_rpow_le_aspect_automaticFrostmanMix
      D C q cell hcell selectedCells hmass hactive B M hthick
        correlationLoss hcorrelationTop ha hab hepsilon hbeta0 hbeta2
  have hscale :=
    hRowFresh_aspect_augmentedFrostmanMix_mul_cardScaleRHS_le_prop66Factor
      D C q cell hcell selectedCells hmass hactive B Mplus ha hab hepsilon
  unfold HRowFreshAugmentedCrossRowAggregationObligation
  calc
    correlationLoss *
          (hRowFreshLoss
              D C q cell hcell selectedCells hmass hactive B.tau B.S *
            frostmanMultiplicityRHS (b / 8) selectedVolume epsilon beta) =
        (correlationLoss * freshLoss) *
          frostmanMultiplicityRHS (b / 8) selectedVolume epsilon beta := by
      simp only [freshLoss]
      ac_rfl
    _ ≤ fixedJohnFrostmanTransportScalar
          (correlationLoss * freshLoss) 2 epsilon beta *
        frostmanMultiplicityRHS b cardScaleVolume epsilon beta := htransport
    _ = (hRowFreshEffectiveLoss
            D C q cell hcell selectedCells hmass hactive B correlationLoss *
          (2 : ENNReal) ^ (1 - beta / 2)) *
        frostmanMultiplicityRHS b cardScaleVolume epsilon beta := by
      unfold fixedJohnFrostmanTransportScalar hRowFreshEffectiveLoss
      simp only [freshLoss]
    _ ≤ (((a / b : NNReal) : ENNReal) *
          (hRowFreshAutomaticForwardFrostmanConstant
                D C q cell hcell selectedCells hmass hactive B M correlationLoss ^
              (1 - beta / 2) *
            (Mplus : ENNReal) ^ (beta / 2))) *
        frostmanMultiplicityRHS b cardScaleVolume epsilon beta :=
      mul_le_mul' hmixed le_rfl
    _ ≤ hRowFreshAugmentedProp66Factor
          D C q cell hcell selectedCells hmass hactive B Mplus := by
      simpa only [cardScaleVolume, Mplus,
        hRowFreshAutomaticForwardFrostmanConstant] using hscale

/-- Same-row actual-third conclusion with both scalar seams removed. -/
theorem actualThirdAverage_le_automaticForwardProp66Factor
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta)
    (M : NNReal) (hthick : FrostmanThickenedPlankControl D M)
    (actualThirdAverage correlationLoss : ENNReal)
    (hcorrelationTop : correlationLoss ≠ ∞)
    (hThirdToRowAvg : HRowFreshActualThirdCorrelationObligation
      D C q cell hcell selectedCells hmass hactive B
        actualThirdAverage correlationLoss)
    (hbHalf : b ≤ (2 : NNReal)⁻¹)
    (ha : 0 < a) (hab : a ≤ b) (hepsilon : 0 ≤ epsilon)
    (hbeta0 : 0 ≤ beta) (hbeta2 : beta ≤ 2) :
    actualThirdAverage ≤ hRowFreshAutomaticForwardProp66Factor
      D C q cell hcell selectedCells hmass hactive B M correlationLoss := by
  calc
    actualThirdAverage ≤ correlationLoss *
        (HRowFreshPlankDatum
          D C q cell hcell selectedCells hmass hactive B.tau B.S).shading.averageMultiplicity :=
      hThirdToRowAvg
    _ ≤ correlationLoss *
        (hRowFreshLoss
            D C q cell hcell selectedCells hmass hactive B.tau B.S *
          frostmanMultiplicityRHS (b / 8)
            (HRowFreshSelectedDatum
              D C q cell hcell selectedCells hmass hactive B.tau B.S
                B.freshSelected).actualFamilyVolume epsilon beta) := by
      gcongr
      exact B.row_average_le_frostman
    _ ≤ hRowFreshAutomaticForwardProp66Factor
          D C q cell hcell selectedCells hmass hactive B M correlationLoss := by
      simpa only [hRowFreshAutomaticForwardProp66Factor,
        HRowFreshAugmentedCrossRowAggregationObligation] using
        hRowFresh_automaticCrossRowAggregation
          D C q cell hcell selectedCells hmass hactive B M hthick
            correlationLoss hcorrelationTop hbHalf ha hab hepsilon hbeta0 hbeta2

#print axioms frostmanThickenedPlankControl_mono
#print axioms hRowFreshEffectiveLoss_ne_top
#print axioms hRowFresh_frostmanThickenedPlankControl_automaticForwardM
#print axioms hRowFresh_effectiveLoss_le_automaticForwardM_mul_aspect
#print axioms hRowFresh_isFrostmanIn_automaticForward
#print axioms
  hRowFresh_effectiveLoss_mul_two_rpow_le_aspect_automaticFrostmanMix
#print axioms hRowFresh_automaticCrossRowAggregation
#print axioms actualThirdAverage_le_automaticForwardProp66Factor

end
end Family8Prop66RowAutomaticForwardThickeningConnectorV1
