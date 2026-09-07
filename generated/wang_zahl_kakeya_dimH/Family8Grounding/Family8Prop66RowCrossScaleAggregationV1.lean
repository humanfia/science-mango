import Family8Grounding.Family8Prop66Eq66ComposerFromHRowFreshV1
import Family8Grounding.Family8PlankFrostmanCopyLossAlgebraV2
import Family8Grounding.Family8FixedJohnSelfImprovementRHSBridgeV15
import Family8Grounding.Family8FrostmanRHSScaleVolumeAlgebraV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8Prop66RowCrossScaleAggregationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FixedJohnSelfImprovementRHSBridgeV15
open Family8FrostmanRHSScaleVolumeAlgebraV3
open Family8FrostmanRHSScaleVolumeAlgebraV4
open Family8PlankFrostmanCopyLossAlgebraV2
open Family8PlankCertificateLongTubeCoverV2
open Family8PlankLongTubeCenteredFreshV4
open Family8PlankLongTubeAmbientB2SupportV3
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
open Family8Prop66Eq66ComposerFromHRowFreshV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe v

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Same-row selected-volume and mixed-power seam for Proposition 6.6

All statements in this module retain the unique row and unique fresh subtype
stored in an existing `HRowFreshPropertyBundle`.  The selected-volume bound,
the branching bound, and the mixed `M` power are proved.  The two genuinely
analytic scalar inputs are exposed separately as `forwardPowerBudget` and
`copyFactorBudget`; neither is hidden inside a renamed final conclusion.
-/

/-- The row card-scale volume before the eighth normalization. -/
def hRowFreshCardScaleVolume
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
      D C q cell hcell selectedCells hmass hactive epsilon beta eta) : ENNReal :=
  (b : ENNReal) ^ 2 *
    (Fintype.card (HRowFreshOccurrence
      D C q cell hcell selectedCells hmass hactive B.tau B.S) : ENNReal)

/-- The actual selected normalized tube volume is at most twice the literal
row card-scale volume.  This is a proved consequence of the one centered copy,
the quarter-volume eighth normalization, and the long-tube `8 b^2` bound. -/
theorem hRowFreshSelected_actualFamilyVolume_le_two_cardScale
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
    (hbHalf : b ≤ (2 : NNReal)⁻¹) :
    (HRowFreshSelectedDatum
      D C q cell hcell selectedCells hmass hactive B.tau B.S
        B.freshSelected).actualFamilyVolume ≤
      2 * hRowFreshCardScaleVolume
        D C q cell hcell selectedCells hmass hactive B := by
  let P := HRowFreshPlankDatum
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  haveI : Nonempty (HRowFreshOccurrence
      D C q cell hcell selectedCells hmass hactive B.tau B.S) :=
    B.occurrence_nonempty
  let v : Unit → Space := fun _ ↦
    -(ambientPlankCertificate P).box.center
  have hnormalized :=
    normalizedIndexedTranslation_restrict_actualFamilyVolume_le
      v (plankLongTubeActualDatum P) hbHalf B.freshSelected
  have hlong := longTubeCover_familyVolume_le_card_mul_eight_sq P hbHalf
  calc
    (HRowFreshSelectedDatum
        D C q cell hcell selectedCells hmass hactive B.tau B.S
          B.freshSelected).actualFamilyVolume ≤
        (Fintype.card Unit : ENNReal) *
          ((1 / 4 : ENNReal) *
            (plankLongTubeActualDatum P).actualFamilyVolume) := by
      simpa only [HRowFreshSelectedDatum, HRowFreshSource,
        centeredPlankLongTubeActualDatum, P, v] using hnormalized
    _ ≤ (Fintype.card Unit : ENNReal) *
          ((1 / 4 : ENNReal) *
            ((Fintype.card (HRowFreshOccurrence
                D C q cell hcell selectedCells hmass hactive B.tau B.S) : ENNReal) *
              (8 * (b : ENNReal) ^ 2))) := by
      gcongr
      change familyVolume (plankLongTubeCoverFamily P).bodyFamily ≤ _
      simpa only [P, HRowFreshOccurrence] using hlong
    _ = 2 * hRowFreshCardScaleVolume
          D C q cell hcell selectedCells hmass hactive B := by
      simp only [Fintype.card_unit, Nat.cast_one, one_mul,
        hRowFreshCardScaleVolume]
      calc
        (1 / 4 : ENNReal) *
              ((Fintype.card (HRowFreshOccurrence
                  D C q cell hcell selectedCells hmass hactive B.tau B.S) : ENNReal) *
                (8 * (b : ENNReal) ^ 2)) =
            ((1 / 4 : ENNReal) * 8) *
              ((Fintype.card (HRowFreshOccurrence
                  D C q cell hcell selectedCells hmass hactive B.tau B.S) : ENNReal) *
                (b : ENNReal) ^ 2) := by ac_rfl
        _ = 2 * ((b : ENNReal) ^ 2 *
              (Fintype.card (HRowFreshOccurrence
                D C q cell hcell selectedCells hmass hactive B.tau B.S) : ENNReal)) := by
          rw [show (1 / 4 : ENNReal) * 8 = 2 by
            rw [div_eq_mul_inv, one_mul]
            have hfour : (4 : ENNReal)⁻¹ * 4 = 1 :=
              ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
            calc
              (4 : ENNReal)⁻¹ * 8 = (4 : ENNReal)⁻¹ * (4 * 2) := by
                norm_num
              _ = ((4 : ENNReal)⁻¹ * 4) * 2 := by ac_rfl
              _ = 2 := by rw [hfour, one_mul]]
          ac_rfl

/-- The exact coefficient left after correlation, fresh-row retention, and
conversion from scale `b/8` to scale `b`. -/
def hRowFreshEffectiveLoss
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
    (correlationLoss : ENNReal) : ENNReal :=
  correlationLoss *
    hRowFreshLoss
      D C q cell hcell selectedCells hmass hactive B.tau B.S *
    ((8 : ENNReal) ^ epsilon * (8 : ENNReal) ^ (2 * beta))

/-- First genuine aggregation input: the complete correlation/fresh/scale
loss must fit inside the actual selected-owner branching number. -/
def HRowFreshForwardPowerBudget
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
    (correlationLoss : ENNReal) : Prop :=
  hRowFreshEffectiveLoss
      D C q cell hcell selectedCells hmass hactive B correlationLoss ≤
    (ownerBucketBranching q : ENNReal)

/-- Second genuine aggregation input: the proved selected-volume copy factor
`2` has to fit under the canonical Frostman copies-per-thick-cluster budget. -/
def HRowFreshCopyFactorBudget
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
    (M : NNReal) : Prop :=
  (2 : ENNReal) ≤
    hRowFreshCanonicalFrostmanConstant
        D C q cell hcell selectedCells hmass hactive B.tau B.S /
      (M : ENNReal)

/-- The structural `N ≤ M theta` row bound and the two explicit earlier
power budgets give the exact mixed Frostman power.  In particular, this is
an actual use of the existing copy-loss identity, not an assumed mixed-power
conclusion. -/
theorem hRowFresh_effectiveLoss_mul_two_rpow_le_aspect_frostmanMix
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
      D C q cell hcell selectedCells hmass hactive B correlationLoss)
    (hCopy : HRowFreshCopyFactorBudget
      D C q cell hcell selectedCells hmass hactive B M) :
    hRowFreshEffectiveLoss
        D C q cell hcell selectedCells hmass hactive B correlationLoss *
        (2 : ENNReal) ^ (1 - beta / 2) ≤
      ((a / b : NNReal) : ENNReal) *
        (hRowFreshCanonicalFrostmanConstant
              D C q cell hcell selectedCells hmass hactive B.tau B.S ^
            (1 - beta / 2) *
          (M : ENNReal) ^ (beta / 2)) := by
  let CF := hRowFreshCanonicalFrostmanConstant
    D C q cell hcell selectedCells hmass hactive B.tau B.S
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
  have hcopyPow : (2 : ENNReal) ^ (1 - beta / 2) ≤
      (CF / (M : ENNReal)) ^ (1 - beta / 2) :=
    ENNReal.rpow_le_rpow hCopy hp
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
          (hRowFreshCanonicalFrostmanConstant
                D C q cell hcell selectedCells hmass hactive B.tau B.S ^
              (1 - beta / 2) *
            (M : ENNReal) ^ (beta / 2)) := by rfl

/-- Moving only the harmless epsilon power from scale `b` to the smaller
plank scale `a` turns the mixed-power times row card-scale RHS into the exact
`convexPlankFrostmanFactor`. -/
theorem hRowFresh_aspect_frostmanMix_mul_cardScaleRHS_le_prop66Factor
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
        (hRowFreshCanonicalFrostmanConstant
              D C q cell hcell selectedCells hmass hactive B.tau B.S ^
            (1 - beta / 2) *
          (M : ENNReal) ^ (beta / 2))) *
        frostmanMultiplicityRHS b
          (hRowFreshCardScaleVolume
            D C q cell hcell selectedCells hmass hactive B) epsilon beta ≤
      hRowFreshProp66Factor
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
  unfold hRowFreshProp66Factor convexPlankFrostmanFactor
  unfold frostmanMultiplicityRHS hRowFreshCardScaleVolume
  calc
    ((a : ENNReal) / (b : ENNReal) *
          (hRowFreshCanonicalFrostmanConstant
                D C q cell hcell selectedCells hmass hactive B.tau B.S ^
              (1 - beta / 2) *
            (M : ENNReal) ^ (beta / 2))) *
        ((b : ENNReal) ^ (-epsilon) *
          (b : ENNReal) ^ (-2 * beta) *
          ((b : ENNReal) ^ 2 *
            (Fintype.card (HRowFreshOccurrence
              D C q cell hcell selectedCells hmass hactive B.tau B.S) : ENNReal)) ^
              (1 - beta / 2)) =
      (b : ENNReal) ^ (-epsilon) *
        (hRowFreshCanonicalFrostmanConstant
              D C q cell hcell selectedCells hmass hactive B.tau B.S ^
            (1 - beta / 2) *
          (M : ENNReal) ^ (beta / 2) *
          ((a : ENNReal) / (b : ENNReal)) *
          (b : ENNReal) ^ (-2 * beta) *
          ((b : ENNReal) ^ 2 *
            (Fintype.card (HRowFreshOccurrence
              D C q cell hcell selectedCells hmass hactive B.tau B.S) : ENNReal)) ^
              (1 - beta / 2)) := by ac_rfl
    _ ≤ (a : ENNReal) ^ (-epsilon) *
        (hRowFreshCanonicalFrostmanConstant
              D C q cell hcell selectedCells hmass hactive B.tau B.S ^
            (1 - beta / 2) *
          (M : ENNReal) ^ (beta / 2) *
          ((a : ENNReal) / (b : ENNReal)) *
          (b : ENNReal) ^ (-2 * beta) *
          ((b : ENNReal) ^ 2 *
            (Fintype.card (HRowFreshOccurrence
              D C q cell hcell selectedCells hmass hactive B.tau B.S) : ENNReal)) ^
              (1 - beta / 2)) := mul_le_mul' hscale le_rfl
    _ = (a : ENNReal) ^ (-epsilon) *
        hRowFreshCanonicalFrostmanConstant
              D C q cell hcell selectedCells hmass hactive B.tau B.S ^
            (1 - beta / 2) *
          (M : ENNReal) ^ (beta / 2) *
          ((a : ENNReal) / (b : ENNReal)) *
          (b : ENNReal) ^ (-2 * beta) *
          ((b : ENNReal) ^ 2 *
            (Fintype.card (HRowFreshOccurrence
              D C q cell hcell selectedCells hmass hactive B.tau B.S) : ENNReal)) ^
              (1 - beta / 2) := by ac_rfl

/-- Final positive aggregation producer.  Its output is the exact composer
cross-row obligation.  The only unproved analytic inputs are the two earlier
and strictly simpler power budgets; selected volume, branching, scale change,
and the mixed `M^(beta/2)` factor are all produced here. -/
theorem hRowFresh_crossRowAggregation_of_powerBudgets
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
      D C q cell hcell selectedCells hmass hactive B correlationLoss)
    (hCopy : HRowFreshCopyFactorBudget
      D C q cell hcell selectedCells hmass hactive B M) :
    HRowFreshCrossRowAggregationObligation
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
    hRowFresh_effectiveLoss_mul_two_rpow_le_aspect_frostmanMix
      D C q cell hcell selectedCells hmass hactive B M hthick
        hratio htheta hthetaAspect hbeta0 hbeta2 correlationLoss hForward hCopy
  have hscale :=
    hRowFresh_aspect_frostmanMix_mul_cardScaleRHS_le_prop66Factor
      D C q cell hcell selectedCells hmass hactive B M ha hab hepsilon
  unfold HRowFreshCrossRowAggregationObligation
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
          (hRowFreshCanonicalFrostmanConstant
                D C q cell hcell selectedCells hmass hactive B.tau B.S ^
              (1 - beta / 2) *
            (M : ENNReal) ^ (beta / 2))) *
        frostmanMultiplicityRHS b cardScaleVolume epsilon beta :=
      mul_le_mul' hmixed le_rfl
    _ ≤ hRowFreshProp66Factor
          D C q cell hcell selectedCells hmass hactive B M := by
      simpa only [cardScaleVolume] using hscale

namespace Prop66Eq66ComposerFromHRowFresh

/-- Same-object final producer.  It reuses the supplied bundle exactly once,
uses `hThirdToRowAvg` as the sole actual-third correlation seam, and obtains
the cross-row field from the two earlier power budgets proved above. -/
def ofBundle_and_powerBudgets
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {cellIndex : Type v} {cell : cellIndex → Set Space}
    {hcell : ∀ p, MeasurableSet (cell p)} {selectedCells : Finset cellIndex}
    {hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0}
    {hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty}
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
      D C q cell hcell selectedCells hmass hactive B correlationLoss)
    (hCopy : HRowFreshCopyFactorBudget
      D C q cell hcell selectedCells hmass hactive B M) :
    Prop66Eq66ComposerFromHRowFresh
      D C q cell hcell selectedCells hmass hactive epsilon beta eta M
        actualThirdAverage correlationLoss :=
  Prop66Eq66ComposerFromHRowFresh.ofBundle
    hthick hratio htheta B hThirdToRowAvg
      (hRowFresh_crossRowAggregation_of_powerBudgets
        D C q cell hcell selectedCells hmass hactive B M hthick
          hratio htheta hthetaAspect hbHalf ha hab hepsilon hbeta0 hbeta2
          correlationLoss hForward hCopy)

/-- Scalar endpoint of the same-object producer. -/
theorem actualThirdAverage_le_prop66Factor_of_powerBudgets
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {cellIndex : Type v} {cell : cellIndex → Set Space}
    {hcell : ∀ p, MeasurableSet (cell p)} {selectedCells : Finset cellIndex}
    {hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0}
    {hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty}
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
      D C q cell hcell selectedCells hmass hactive B correlationLoss)
    (hCopy : HRowFreshCopyFactorBudget
      D C q cell hcell selectedCells hmass hactive B M) :
    actualThirdAverage ≤ hRowFreshProp66Factor
      D C q cell hcell selectedCells hmass hactive B M := by
  let Z := ofBundle_and_powerBudgets B M hthick hratio htheta hthetaAspect
    hbHalf ha hab hepsilon hbeta0 hbeta2 actualThirdAverage correlationLoss
    hThirdToRowAvg hForward hCopy
  exact Z.actualThirdAverage_le_prop66Factor

end Prop66Eq66ComposerFromHRowFresh

#print axioms hRowFreshSelected_actualFamilyVolume_le_two_cardScale
#print axioms hRowFresh_effectiveLoss_mul_two_rpow_le_aspect_frostmanMix
#print axioms hRowFresh_aspect_frostmanMix_mul_cardScaleRHS_le_prop66Factor
#print axioms hRowFresh_crossRowAggregation_of_powerBudgets
#print axioms Prop66Eq66ComposerFromHRowFresh.ofBundle_and_powerBudgets
#print axioms
  Prop66Eq66ComposerFromHRowFresh.actualThirdAverage_le_prop66Factor_of_powerBudgets

end
end Family8Prop66RowCrossScaleAggregationV1
