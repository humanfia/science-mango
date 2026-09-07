import Family8Grounding.Family8Prop66RowCrossScaleAggregationV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8Prop66RowAugmentedFrostmanConstantConnectorV1

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
open Family8FrostmanRHSScaleVolumeAlgebraV4
open Family8PlankFrostmanCopyLossAlgebraV2

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe v

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# M-aware enlarged Frostman choice for the same HRow fresh datum

The canonical Frostman constant is a geometric concentration ratio and is not
normalized relative to an arbitrary admissible thickening parameter `M`.
This connector makes the standard monotone choice
`max canonicalCF (2*M)`.  It proves Frostman validity, finiteness, and the
copy-factor budget, while retaining the exact same row and fresh subtype.
-/

/-- The smallest monotone enlargement which automatically pays the proved
selected-volume factor two. -/
def hRowFreshAugmentedFrostmanConstant
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
    (M : NNReal) : ENNReal :=
  max
    (hRowFreshCanonicalFrostmanConstant
      D C q cell hcell selectedCells hmass hactive B.tau B.S)
    ((2 : ENNReal) * (M : ENNReal))

/-- The enlarged choice remains a valid Frostman constant for the literal
same row family and ambient body. -/
theorem hRowFresh_isFrostmanIn_augmented
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
    (M : NNReal) :
    IsFrostmanIn
      (hRowFreshAugmentedFrostmanConstant
        D C q cell hcell selectedCells hmass hactive B M)
      (HRowFreshPlankDatum
        D C q cell hcell selectedCells hmass hactive B.tau B.S).family
      (HRowFreshPlankDatum
        D C q cell hcell selectedCells hmass hactive B.tau B.S).ambient := by
  apply B.canonical_frostman.mono
  unfold hRowFreshAugmentedFrostmanConstant
  exact le_max_left _ _

/-- The enlarged constant is finite. -/
theorem hRowFreshAugmentedFrostmanConstant_ne_top
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
    (M : NNReal) :
    hRowFreshAugmentedFrostmanConstant
      D C q cell hcell selectedCells hmass hactive B M ≠ ∞ := by
  unfold hRowFreshAugmentedFrostmanConstant
  apply max_ne_top
  · exact B.canonical_frostman_finite
  · exact ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top

/-- The enlarged choice automatically discharges the previous copy-factor
seam `2 <= CF/M`; only the inherited fact `1 <= M` is used to rule out zero. -/
theorem hRowFresh_augmented_copyFactorBudget
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
    (M : NNReal) (hthick : FrostmanThickenedPlankControl D M) :
    (2 : ENNReal) ≤
      hRowFreshAugmentedFrostmanConstant
          D C q cell hcell selectedCells hmass hactive B M /
        (M : ENNReal) := by
  have hMposNN : 0 < M := lt_of_lt_of_le zero_lt_one hthick.1
  have hM0 : (M : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hMposNN.ne'
  have hMtop : (M : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  apply (ENNReal.le_div_iff_mul_le (Or.inl hM0) (Or.inl hMtop)).2
  unfold hRowFreshAugmentedFrostmanConstant
  exact le_max_right _ _

/-- The Prop. 6.6 factor evaluated at the honest enlarged Frostman choice. -/
def hRowFreshAugmentedProp66Factor
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
    (M : NNReal) : ENNReal :=
  convexPlankFrostmanFactor
    (HRowFreshPlankDatum
      D C q cell hcell selectedCells hmass hactive B.tau B.S)
    epsilon beta
    (hRowFreshAugmentedFrostmanConstant
      D C q cell hcell selectedCells hmass hactive B M) M

/-- With the enlarged constant, the mixed `M` power follows from the forward
branching budget alone; no copy-factor hypothesis remains. -/
theorem hRowFresh_effectiveLoss_mul_two_rpow_le_aspect_augmentedFrostmanMix
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
    (hratio : a / b ≤ theta) (htheta : theta ≤ 1)
    (hthetaAspect : theta ≤ a / b)
    (hbeta0 : 0 ≤ beta) (hbeta2 : beta ≤ 2)
    (correlationLoss : ENNReal)
    (hForward : HRowFreshForwardPowerBudget
      D C q cell hcell selectedCells hmass hactive B correlationLoss) :
    hRowFreshEffectiveLoss
        D C q cell hcell selectedCells hmass hactive B correlationLoss *
        (2 : ENNReal) ^ (1 - beta / 2) ≤
      ((a / b : NNReal) : ENNReal) *
        (hRowFreshAugmentedFrostmanConstant
              D C q cell hcell selectedCells hmass hactive B M ^
            (1 - beta / 2) *
          (M : ENNReal) ^ (beta / 2)) := by
  let CF := hRowFreshAugmentedFrostmanConstant
    D C q cell hcell selectedCells hmass hactive B M
  have hMposNN : 0 < M := lt_of_lt_of_le zero_lt_one hthick.1
  have hM0 : (M : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hMposNN.ne'
  have hMtop : (M : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hp : 0 ≤ 1 - beta / 2 := by linarith
  have hbranchTheta := hRowFresh_branching_le_M_mul_clusteringScale
    D C q cell hcell selectedCells hmass hactive B M hthick hratio htheta
  have hbranchAspect : (ownerBucketBranching q : ENNReal) ≤
      (M : ENNReal) * ((a / b : NNReal) : ENNReal) := by
    apply hbranchTheta.trans
    gcongr
  have heffective : hRowFreshEffectiveLoss
        D C q cell hcell selectedCells hmass hactive B correlationLoss ≤
      (M : ENNReal) * ((a / b : NNReal) : ENNReal) :=
    hForward.trans hbranchAspect
  have hcopy := hRowFresh_augmented_copyFactorBudget
    D C q cell hcell selectedCells hmass hactive B M hthick
  have hcopyPow : (2 : ENNReal) ^ (1 - beta / 2) ≤
      (CF / (M : ENNReal)) ^ (1 - beta / 2) :=
    ENNReal.rpow_le_rpow hcopy hp
  calc
    hRowFreshEffectiveLoss
          D C q cell hcell selectedCells hmass hactive B correlationLoss *
          (2 : ENNReal) ^ (1 - beta / 2) ≤
        ((M : ENNReal) * ((a / b : NNReal) : ENNReal)) *
          (CF / (M : ENNReal)) ^ (1 - beta / 2) :=
      mul_le_mul' heffective hcopyPow
    _ = ((a / b : NNReal) : ENNReal) *
          ((M : ENNReal) *
            (CF / (M : ENNReal)) ^ (1 - beta / 2)) := by ac_rfl
    _ = ((a / b : NNReal) : ENNReal) *
          (CF ^ (1 - beta / 2) * (M : ENNReal) ^ (beta / 2)) := by
      rw [copyLoss_rpow_eq_frostmanMix CF (M : ENNReal) beta
        hM0 hMtop hbeta0 hbeta2]
    _ = ((a / b : NNReal) : ENNReal) *
          (hRowFreshAugmentedFrostmanConstant
                D C q cell hcell selectedCells hmass hactive B M ^
              (1 - beta / 2) *
            (M : ENNReal) ^ (beta / 2)) := by rfl

/-- The epsilon-scale transport for the enlarged constant. -/
theorem hRowFresh_aspect_augmentedFrostmanMix_mul_cardScaleRHS_le_prop66Factor
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
    (M : NNReal) (ha : 0 < a) (hab : a ≤ b) (hepsilon : 0 ≤ epsilon) :
    (((a / b : NNReal) : ENNReal) *
        (hRowFreshAugmentedFrostmanConstant
              D C q cell hcell selectedCells hmass hactive B M ^
            (1 - beta / 2) *
          (M : ENNReal) ^ (beta / 2))) *
        frostmanMultiplicityRHS b
          (hRowFreshCardScaleVolume
            D C q cell hcell selectedCells hmass hactive B) epsilon beta ≤
      hRowFreshAugmentedProp66Factor
        D C q cell hcell selectedCells hmass hactive B M := by
  have hb : 0 < b := ha.trans_le hab
  have hscaleNN : b ^ (-epsilon) ≤ a ^ (-epsilon) :=
    NNReal.rpow_le_rpow_of_nonpos ha hab (neg_nonpos.mpr hepsilon)
  have hscale : (b : ENNReal) ^ (-epsilon) ≤
      (a : ENNReal) ^ (-epsilon) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hb.ne' (-epsilon),
      ← ENNReal.coe_rpow_of_ne_zero ha.ne' (-epsilon)]
    exact ENNReal.coe_le_coe.mpr hscaleNN
  rw [ENNReal.coe_div hb.ne']
  unfold hRowFreshAugmentedProp66Factor convexPlankFrostmanFactor
  unfold frostmanMultiplicityRHS hRowFreshCardScaleVolume
  calc
    ((a : ENNReal) / (b : ENNReal) *
          (hRowFreshAugmentedFrostmanConstant
                D C q cell hcell selectedCells hmass hactive B M ^
              (1 - beta / 2) *
            (M : ENNReal) ^ (beta / 2))) *
        ((b : ENNReal) ^ (-epsilon) *
          (b : ENNReal) ^ (-2 * beta) *
          ((b : ENNReal) ^ 2 *
            (Fintype.card (HRowFreshOccurrence
              D C q cell hcell selectedCells hmass hactive B.tau B.S) : ENNReal)) ^
              (1 - beta / 2)) =
      (b : ENNReal) ^ (-epsilon) *
        (hRowFreshAugmentedFrostmanConstant
              D C q cell hcell selectedCells hmass hactive B M ^
            (1 - beta / 2) *
          (M : ENNReal) ^ (beta / 2) *
          ((a : ENNReal) / (b : ENNReal)) *
          (b : ENNReal) ^ (-2 * beta) *
          ((b : ENNReal) ^ 2 *
            (Fintype.card (HRowFreshOccurrence
              D C q cell hcell selectedCells hmass hactive B.tau B.S) : ENNReal)) ^
              (1 - beta / 2)) := by ac_rfl
    _ ≤ (a : ENNReal) ^ (-epsilon) *
        (hRowFreshAugmentedFrostmanConstant
              D C q cell hcell selectedCells hmass hactive B M ^
            (1 - beta / 2) *
          (M : ENNReal) ^ (beta / 2) *
          ((a : ENNReal) / (b : ENNReal)) *
          (b : ENNReal) ^ (-2 * beta) *
          ((b : ENNReal) ^ 2 *
            (Fintype.card (HRowFreshOccurrence
              D C q cell hcell selectedCells hmass hactive B.tau B.S) : ENNReal)) ^
              (1 - beta / 2)) := mul_le_mul' hscale le_rfl
    _ = (a : ENNReal) ^ (-epsilon) *
        hRowFreshAugmentedFrostmanConstant
              D C q cell hcell selectedCells hmass hactive B M ^
            (1 - beta / 2) *
          (M : ENNReal) ^ (beta / 2) *
          ((a : ENNReal) / (b : ENNReal)) *
          (b : ENNReal) ^ (-2 * beta) *
          ((b : ENNReal) ^ 2 *
            (Fintype.card (HRowFreshOccurrence
              D C q cell hcell selectedCells hmass hactive B.tau B.S) : ENNReal)) ^
              (1 - beta / 2) := by ac_rfl

/-- Exact cross-row conclusion at the valid enlarged Frostman choice. -/
def HRowFreshAugmentedCrossRowAggregationObligation
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
    (M : NNReal) (correlationLoss : ENNReal) : Prop :=
  correlationLoss *
      (hRowFreshLoss
          D C q cell hcell selectedCells hmass hactive B.tau B.S *
        frostmanMultiplicityRHS (b / 8)
          (HRowFreshSelectedDatum
            D C q cell hcell selectedCells hmass hactive B.tau B.S
              B.freshSelected).actualFamilyVolume epsilon beta) ≤
    hRowFreshAugmentedProp66Factor
      D C q cell hcell selectedCells hmass hactive B M

/-- The enlarged constant eliminates `hCopy` from the complete cross-row
producer.  The only remaining analytic aggregation input is `hForward`. -/
theorem hRowFresh_augmentedCrossRowAggregation_of_forwardPowerBudget
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
    (hratio : a / b ≤ theta) (htheta : theta ≤ 1)
    (hthetaAspect : theta ≤ a / b)
    (hbHalf : b ≤ (2 : NNReal)⁻¹)
    (ha : 0 < a) (hab : a ≤ b) (hepsilon : 0 ≤ epsilon)
    (hbeta0 : 0 ≤ beta) (hbeta2 : beta ≤ 2)
    (correlationLoss : ENNReal)
    (hForward : HRowFreshForwardPowerBudget
      D C q cell hcell selectedCells hmass hactive B correlationLoss) :
    HRowFreshAugmentedCrossRowAggregationObligation
      D C q cell hcell selectedCells hmass hactive B M correlationLoss := by
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
    hRowFresh_effectiveLoss_mul_two_rpow_le_aspect_augmentedFrostmanMix
      D C q cell hcell selectedCells hmass hactive B M hthick
        hratio htheta hthetaAspect hbeta0 hbeta2 correlationLoss hForward
  have hscale :=
    hRowFresh_aspect_augmentedFrostmanMix_mul_cardScaleRHS_le_prop66Factor
      D C q cell hcell selectedCells hmass hactive B M ha hab hepsilon
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
          (hRowFreshAugmentedFrostmanConstant
                D C q cell hcell selectedCells hmass hactive B M ^
              (1 - beta / 2) *
            (M : ENNReal) ^ (beta / 2))) *
        frostmanMultiplicityRHS b cardScaleVolume epsilon beta :=
      mul_le_mul' hmixed le_rfl
    _ ≤ hRowFreshAugmentedProp66Factor
          D C q cell hcell selectedCells hmass hactive B M := by
      simpa only [cardScaleVolume] using hscale

/-- Same-row actual-third endpoint with no copy-factor input. -/
theorem actualThirdAverage_le_augmentedProp66Factor_of_forwardPowerBudget
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
    (hratio : a / b ≤ theta) (htheta : theta ≤ 1)
    (hthetaAspect : theta ≤ a / b)
    (hbHalf : b ≤ (2 : NNReal)⁻¹)
    (ha : 0 < a) (hab : a ≤ b) (hepsilon : 0 ≤ epsilon)
    (hbeta0 : 0 ≤ beta) (hbeta2 : beta ≤ 2)
    (actualThirdAverage correlationLoss : ENNReal)
    (hThirdToRowAvg : HRowFreshActualThirdCorrelationObligation
      D C q cell hcell selectedCells hmass hactive B
        actualThirdAverage correlationLoss)
    (hForward : HRowFreshForwardPowerBudget
      D C q cell hcell selectedCells hmass hactive B correlationLoss) :
    actualThirdAverage ≤ hRowFreshAugmentedProp66Factor
      D C q cell hcell selectedCells hmass hactive B M := by
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
    _ ≤ hRowFreshAugmentedProp66Factor
          D C q cell hcell selectedCells hmass hactive B M :=
      hRowFresh_augmentedCrossRowAggregation_of_forwardPowerBudget
        D C q cell hcell selectedCells hmass hactive B M hthick
          hratio htheta hthetaAspect hbHalf ha hab hepsilon hbeta0 hbeta2
          correlationLoss hForward

#print axioms hRowFresh_isFrostmanIn_augmented
#print axioms hRowFreshAugmentedFrostmanConstant_ne_top
#print axioms hRowFresh_augmented_copyFactorBudget
#print axioms
  hRowFresh_effectiveLoss_mul_two_rpow_le_aspect_augmentedFrostmanMix
#print axioms
  hRowFresh_aspect_augmentedFrostmanMix_mul_cardScaleRHS_le_prop66Factor
#print axioms hRowFresh_augmentedCrossRowAggregation_of_forwardPowerBudget
#print axioms
  actualThirdAverage_le_augmentedProp66Factor_of_forwardPowerBudget

end
end Family8Prop66RowAugmentedFrostmanConstantConnectorV1
