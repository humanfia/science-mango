import Family8Grounding.Family8FrozenComparableLogLossSourceCardTransferV2
import Family8Grounding.Family8Prop51JointOccurrenceWeightedSelectionV1
import Family8Grounding.Family8ShadingAwareSelectionLossPowerV1
import Family8Grounding.Family8StickySelectedParentGreedyBlockFrostmanV3
import Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
import Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
import Mathlib.Tactic

/-!
# Source-scale power envelope for the selected-occurrence Option loss

The exact-outer selected-occurrence assembly keeps the full greedy occurrence
index `Option (Fin (blocks _ P).length)`.  This file absorbs precisely its
two logarithmic frozen-comparable factors and the literal product factor
`4`.  No fibre-uniformity count loss or Section Eight coefficient is included.

The only non-automatic reserve is that the active-parent index is nonempty.
It is exposed explicitly: it is what permits the sharp comparison
`log₂ (blocks.length + 1) <= log₂ (2 * #activeParents)` without replacing the
source-card coefficient by a stronger one.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8SelectedOccurrenceOptionFrozenLossPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8CommonPointTubePackingV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableLogLossSourceCardTransferV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8ShadingAwareSelectionLossPowerV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- Before the finite coefficient is absorbed, the exact Option-block frozen
loss spends half of the requested exponent.  The extra factor `2` is exactly
the cost of the `Option.none` coarse label. -/
theorem selectedOccurrenceOptionFrozenComparableLoss_real_le
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (hactiveParent : 0 < Fintype.card (ActiveParentIndex S))
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hdeltaSmall : delta <= (1 / 100 : NNReal)) :
    (frozenComparableLoss (ActiveParentIndex S)
        (Option (Fin (blocks S.activeCoarseFamily P).length)) : Real) <=
      (2 * activeFrozenLogProductConstant lossEta) *
        (delta : Real) ^ (-(lossEta / 2)) := by
  have hdeltaOne : delta <= 1 :=
    hdeltaSmall.trans (div_le_one_of_le₀ (by norm_num) (by positivity))
  have hsource := sourceIndexCard_real_le_sourcePower D hD hdeltaSmall
  have hactiveNat :
      Fintype.card (ActiveParentIndex S) <= Fintype.card index := by
    simpa only [Fintype.card_coe] using
      (activeCoarse_card_le_activeFine_card S).trans
        (Finset.card_le_univ S.activeFine)
  have hactiveReal :
      (Fintype.card (ActiveParentIndex S) : Real) <=
        (2 * commonPointFamilyVolumeConstant).toReal *
          (delta : Real) ^ (-4 : Real) := by
    calc
      (Fintype.card (ActiveParentIndex S) : Real) <=
          (Fintype.card index : Real) := by exact_mod_cast hactiveNat
      _ <= (2 * commonPointFamilyVolumeConstant).toReal *
          (delta : Real) ^ (-4 : Real) := hsource
  have hfine := natLogFactor_real_le hD.delta_pos hdeltaOne
    hlossEta hactiveReal
  have hblocks :
      (blocks S.activeCoarseFamily P).length <=
        Fintype.card (ActiveParentIndex S) := by
    rw [blocks_length]
    simpa only [Finset.card_univ] using P.length_le_card
  have hparentNe : Fintype.card (ActiveParentIndex S) ≠ 0 :=
    Nat.ne_of_gt hactiveParent
  have hblockSucc :
      (blocks S.activeCoarseFamily P).length + 1 <=
        Fintype.card (ActiveParentIndex S) * 2 := by
    omega
  have hlogMono :
      Nat.log 2 ((blocks S.activeCoarseFamily P).length + 1) <=
        Nat.log 2 (Fintype.card (ActiveParentIndex S) * 2) :=
    Nat.log_mono_right hblockSucc
  rw [Nat.log_mul_base Nat.one_lt_two hparentNe] at hlogMono
  have hcoarseNat :
      Nat.log 2 ((blocks S.activeCoarseFamily P).length + 1) + 2 <=
        2 * (Nat.log 2 (Fintype.card (ActiveParentIndex S)) + 2) := by
    omega
  have hcoarse :
      ((Nat.log 2 ((blocks S.activeCoarseFamily P).length + 1) + 2 : Nat) :
          Real) <=
        2 * (activeFrozenLogFactorConstant lossEta *
          (delta : Real) ^ (-(lossEta / 4))) := by
    calc
      ((Nat.log 2 ((blocks S.activeCoarseFamily P).length + 1) + 2 : Nat) :
          Real) <=
        2 * ((Nat.log 2 (Fintype.card (ActiveParentIndex S)) + 2 : Nat) :
          Real) := by exact_mod_cast hcoarseNat
      _ <= 2 * (activeFrozenLogFactorConstant lossEta *
          (delta : Real) ^ (-(lossEta / 4))) :=
        mul_le_mul_of_nonneg_left hfine (by norm_num)
  have hfactorNonneg :
      0 <= activeFrozenLogFactorConstant lossEta *
        (delta : Real) ^ (-(lossEta / 4)) :=
    mul_nonneg (activeFrozenLogFactorConstant_pos hlossEta).le
      (Real.rpow_nonneg (by positivity) _)
  have hscale :
      ((delta : Real) ^ (-(lossEta / 4))) ^ 2 =
        (delta : Real) ^ (-(lossEta / 2)) := by
    rw [<- Real.rpow_natCast]
    rw [<- Real.rpow_mul (show 0 <= (delta : Real) by positivity)]
    congr 1
    ring
  unfold frozenComparableLoss activeFrozenLogProductConstant
  simp only [Fintype.card_option, Fintype.card_fin]
  rw [Nat.cast_mul]
  calc
    ((Nat.log 2 (Fintype.card (ActiveParentIndex S)) + 2 : Nat) : Real) *
        ((Nat.log 2 ((blocks S.activeCoarseFamily P).length + 1) + 2 : Nat) :
          Real) <=
      (activeFrozenLogFactorConstant lossEta *
          (delta : Real) ^ (-(lossEta / 4))) *
        (2 * (activeFrozenLogFactorConstant lossEta *
          (delta : Real) ^ (-(lossEta / 4)))) := by
      exact mul_le_mul hfine hcoarse (by positivity) hfactorNonneg
    _ = (2 * (activeFrozenLogFactorConstant lossEta) ^ 2) *
        ((delta : Real) ^ (-(lossEta / 4))) ^ 2 := by ring
    _ = (2 * (activeFrozenLogFactorConstant lossEta) ^ 2) *
        (delta : Real) ^ (-(lossEta / 2)) := by rw [hscale]

/-- Explicit threshold absorbing the finite coefficient left by the two
Option-block logarithms. -/
def selectedOccurrenceOptionFrozenLossThreshold (lossEta : Real) : NNReal :=
  min (1 / 100 : NNReal)
    (finiteConstantSmallDeltaThreshold
      (ENNReal.ofReal (2 * activeFrozenLogProductConstant lossEta))
      (lossEta / 2))

theorem selectedOccurrenceOptionFrozenLossThreshold_pos (lossEta : Real) :
    0 < selectedOccurrenceOptionFrozenLossThreshold lossEta := by
  unfold selectedOccurrenceOptionFrozenLossThreshold
  exact lt_min (by norm_num) (finiteConstantSmallDeltaThreshold_pos _ _)

/-- The literal exact-outer Option-block frozen loss is bounded by any
prescribed positive source-scale power. -/
theorem selectedOccurrenceOptionFrozenComparableLoss_le_rpow
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (hactiveParent : 0 < Fintype.card (ActiveParentIndex S))
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hdelta : delta <= selectedOccurrenceOptionFrozenLossThreshold lossEta) :
    (frozenComparableLoss (ActiveParentIndex S)
        (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal) <=
      (delta : ENNReal) ^ (-lossEta) := by
  have hdeltaSmall : delta <= (1 / 100 : NNReal) :=
    hdelta.trans (min_le_left _ _)
  have hreal := selectedOccurrenceOptionFrozenComparableLoss_real_le
    D hD S P hactiveParent hlossEta hdeltaSmall
  have hconstantNonneg :
      0 <= 2 * activeFrozenLogProductConstant lossEta := by
    unfold activeFrozenLogProductConstant
    positivity
  have hdeltaReal : 0 < (delta : Real) := by exact_mod_cast hD.delta_pos
  have hlossENN :
      (frozenComparableLoss (ActiveParentIndex S)
          (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal) <=
        ENNReal.ofReal (2 * activeFrozenLogProductConstant lossEta) *
          (delta : ENNReal) ^ (-(lossEta / 2)) := by
    rw [<- ENNReal.ofReal_natCast
      (frozenComparableLoss (ActiveParentIndex S)
        (Option (Fin (blocks S.activeCoarseFamily P).length)))]
    rw [show (delta : ENNReal) ^ (-(lossEta / 2)) =
        ENNReal.ofReal ((delta : Real) ^ (-(lossEta / 2))) by
      simpa using ENNReal.ofReal_rpow_of_pos hdeltaReal]
    rw [<- ENNReal.ofReal_mul hconstantNonneg]
    exact ENNReal.ofReal_le_ofReal hreal
  let K : ENNReal :=
    ENNReal.ofReal (2 * activeFrozenLogProductConstant lossEta)
  have hhalf : 0 < lossEta / 2 := by positivity
  have hKFinite : K ≠ ∞ := by
    dsimp only [K]
    exact ENNReal.ofReal_ne_top
  have hK : K <= (delta : ENNReal) ^ (-(lossEta / 2)) := by
    exact finiteConstant_le_delta_negativePower hKFinite hhalf hD.delta_pos
      (hdelta.trans (min_le_right _ _))
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  calc
    (frozenComparableLoss (ActiveParentIndex S)
        (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal) <=
      K * (delta : ENNReal) ^ (-(lossEta / 2)) := by
        simpa only [K] using hlossENN
    _ <= (delta : ENNReal) ^ (-(lossEta / 2)) *
        (delta : ENNReal) ^ (-(lossEta / 2)) := by gcongr
    _ = (delta : ENNReal) ^ (-lossEta) := by
      rw [<- ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
      congr 1
      ring

/-- Uniform threshold absorbing both the exact Option-block frozen loss and
the literal factor four from the actual-average product. -/
def selectedOccurrenceOptionFrozenLossFourThreshold
    (lossEta : Real) : NNReal :=
  min (1 / 100 : NNReal)
    (finiteConstantSmallDeltaThreshold
      (ENNReal.ofReal (8 * activeFrozenLogProductConstant lossEta))
      (lossEta / 2))

theorem selectedOccurrenceOptionFrozenLossFourThreshold_pos (lossEta : Real) :
    0 < selectedOccurrenceOptionFrozenLossFourThreshold lossEta := by
  unfold selectedOccurrenceOptionFrozenLossFourThreshold
  exact lt_min (by norm_num) (finiteConstantSmallDeltaThreshold_pos _ _)

/-- The weakest product needed by the exact-outer loss ledger: the genuine
Option-block frozen loss times `4`, with no count loss or Section Eight
coefficient folded into it. -/
theorem selectedOccurrenceOptionFrozenComparableLoss_mul_four_le_rpow
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (hactiveParent : 0 < Fintype.card (ActiveParentIndex S))
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hdelta : delta <=
      selectedOccurrenceOptionFrozenLossFourThreshold lossEta) :
    (frozenComparableLoss (ActiveParentIndex S)
        (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal) * 4 <=
      (delta : ENNReal) ^ (-lossEta) := by
  have hdeltaSmall : delta <= (1 / 100 : NNReal) :=
    hdelta.trans (min_le_left _ _)
  have hrealLoss := selectedOccurrenceOptionFrozenComparableLoss_real_le
    D hD S P hactiveParent hlossEta hdeltaSmall
  have hreal :
      (frozenComparableLoss (ActiveParentIndex S)
          (Option (Fin (blocks S.activeCoarseFamily P).length)) : Real) * 4 <=
        (8 * activeFrozenLogProductConstant lossEta) *
          (delta : Real) ^ (-(lossEta / 2)) := by
    calc
      (frozenComparableLoss (ActiveParentIndex S)
          (Option (Fin (blocks S.activeCoarseFamily P).length)) : Real) * 4 <=
        ((2 * activeFrozenLogProductConstant lossEta) *
          (delta : Real) ^ (-(lossEta / 2))) * 4 :=
        mul_le_mul_of_nonneg_right hrealLoss (by norm_num)
      _ = (8 * activeFrozenLogProductConstant lossEta) *
          (delta : Real) ^ (-(lossEta / 2)) := by ring
  have hconstantNonneg :
      0 <= 8 * activeFrozenLogProductConstant lossEta := by
    unfold activeFrozenLogProductConstant
    positivity
  have hdeltaReal : 0 < (delta : Real) := by exact_mod_cast hD.delta_pos
  have hpreNat :
      ((frozenComparableLoss (ActiveParentIndex S)
          (Option (Fin (blocks S.activeCoarseFamily P).length)) * 4 : Nat) :
          ENNReal) <=
        ENNReal.ofReal (8 * activeFrozenLogProductConstant lossEta) *
          (delta : ENNReal) ^ (-(lossEta / 2)) := by
    rw [<- ENNReal.ofReal_natCast
      (frozenComparableLoss (ActiveParentIndex S)
        (Option (Fin (blocks S.activeCoarseFamily P).length)) * 4)]
    rw [show (delta : ENNReal) ^ (-(lossEta / 2)) =
        ENNReal.ofReal ((delta : Real) ^ (-(lossEta / 2))) by
      simpa using ENNReal.ofReal_rpow_of_pos hdeltaReal]
    rw [<- ENNReal.ofReal_mul hconstantNonneg]
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hreal)
  have hpre :
      (frozenComparableLoss (ActiveParentIndex S)
          (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal) * 4 <=
        ENNReal.ofReal (8 * activeFrozenLogProductConstant lossEta) *
          (delta : ENNReal) ^ (-(lossEta / 2)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hpreNat
  let K : ENNReal :=
    ENNReal.ofReal (8 * activeFrozenLogProductConstant lossEta)
  have hhalf : 0 < lossEta / 2 := by positivity
  have hKFinite : K ≠ ∞ := by
    dsimp only [K]
    exact ENNReal.ofReal_ne_top
  have hK : K <= (delta : ENNReal) ^ (-(lossEta / 2)) := by
    exact finiteConstant_le_delta_negativePower hKFinite hhalf hD.delta_pos
      (hdelta.trans (min_le_right _ _))
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  calc
    (frozenComparableLoss (ActiveParentIndex S)
        (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal) * 4 <=
      K * (delta : ENNReal) ^ (-(lossEta / 2)) := by
        simpa only [K] using hpre
    _ <= (delta : ENNReal) ^ (-(lossEta / 2)) *
        (delta : ENNReal) ^ (-(lossEta / 2)) := by gcongr
    _ = (delta : ENNReal) ^ (-lossEta) := by
      rw [<- ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
      congr 1
      ring

/-- Threshold for the exact joint fibre/density bucket loss at its canonical
active-parent logarithmic depth. -/
def selectedOccurrenceCanonicalJointLossThreshold
    (lossEta : Real) : NNReal :=
  shadingAwareSelectionLossPowerThreshold (lossEta / 2)

theorem selectedOccurrenceCanonicalJointLossThreshold_pos (lossEta : Real) :
    0 < selectedOccurrenceCanonicalJointLossThreshold lossEta := by
  exact shadingAwareSelectionLossPowerThreshold_pos _

/-- The exact joint-bucket retention factor at
`M = log₂ (# active parents)` is a square of single logarithms and therefore
costs an arbitrary positive source-scale power. -/
theorem selectedOccurrenceCanonicalJointLoss_le_rpow
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hdelta : delta <=
      selectedOccurrenceCanonicalJointLossThreshold lossEta) :
    ((2 * prop51JointOccurrenceLoss (ActiveParentIndex S)
        (Nat.log 2 (Fintype.card (ActiveParentIndex S))) : Nat) : ENNReal) <=
      (delta : ENNReal) ^ (-lossEta) := by
  let sourceLoss : Nat := 2 * (Nat.log 2 (Fintype.card index) + 1)
  have hactiveNat :
      Fintype.card (ActiveParentIndex S) <= Fintype.card index := by
    simpa only [Fintype.card_coe] using
      (activeCoarse_card_le_activeFine_card S).trans
        (Finset.card_le_univ S.activeFine)
  have hlog :
      Nat.log 2 (Fintype.card (ActiveParentIndex S)) <=
        Nat.log 2 (Fintype.card index) :=
    Nat.log_mono_right hactiveNat
  have hfirstNat :
      2 * (Nat.log 2 (Fintype.card (ActiveParentIndex S)) + 1) <=
        sourceLoss := by
    dsimp only [sourceLoss]
    omega
  have hsecondNat :
      Nat.log 2 (Fintype.card (ActiveParentIndex S)) + 1 <=
        sourceLoss := by
    dsimp only [sourceLoss]
    omega
  have hjointNat :
      2 * prop51JointOccurrenceLoss (ActiveParentIndex S)
          (Nat.log 2 (Fintype.card (ActiveParentIndex S))) <=
        sourceLoss * sourceLoss := by
    unfold prop51JointOccurrenceLoss
    calc
      2 * ((Nat.log 2 (Fintype.card (ActiveParentIndex S)) + 1) *
          (Nat.log 2 (Fintype.card (ActiveParentIndex S)) + 1)) =
        (2 * (Nat.log 2 (Fintype.card (ActiveParentIndex S)) + 1)) *
          (Nat.log 2 (Fintype.card (ActiveParentIndex S)) + 1) := by ring
      _ <= sourceLoss * sourceLoss := Nat.mul_le_mul hfirstNat hsecondNat
  have hjointENNRaw :
      ((2 * prop51JointOccurrenceLoss (ActiveParentIndex S)
          (Nat.log 2 (Fintype.card (ActiveParentIndex S))) : Nat) : ENNReal) <=
        ((sourceLoss * sourceLoss : Nat) : ENNReal) := by
    exact_mod_cast hjointNat
  have hjointENN :
      ((2 * prop51JointOccurrenceLoss (ActiveParentIndex S)
          (Nat.log 2 (Fintype.card (ActiveParentIndex S))) : Nat) : ENNReal) <=
        (sourceLoss : ENNReal) * (sourceLoss : ENNReal) := by
    simpa only [Nat.cast_mul] using hjointENNRaw
  have hsingle : (sourceLoss : ENNReal) <=
      (delta : ENNReal) ^ (-(lossEta / 2)) := by
    exact shadingAwareSelectionLoss_le_delta_negativePower
      D hD (by positivity) (by
        simpa only [selectedOccurrenceCanonicalJointLossThreshold] using hdelta)
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  calc
    ((2 * prop51JointOccurrenceLoss (ActiveParentIndex S)
        (Nat.log 2 (Fintype.card (ActiveParentIndex S))) : Nat) : ENNReal) <=
      (sourceLoss : ENNReal) * (sourceLoss : ENNReal) := hjointENN
    _ <= (delta : ENNReal) ^ (-(lossEta / 2)) *
        (delta : ENNReal) ^ (-(lossEta / 2)) :=
      mul_le_mul' hsingle hsingle
    _ = (delta : ENNReal) ^ (-lossEta) := by
      rw [<- ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
      congr 1
      ring

/-- Uniform threshold for exactly the joint retention loss, the Option-block
frozen loss, and the literal product factor four. -/
def selectedOccurrenceJointFrozenExternalLossThreshold
    (lossEta : Real) : NNReal :=
  min (selectedOccurrenceCanonicalJointLossThreshold (lossEta / 2))
    (selectedOccurrenceOptionFrozenLossFourThreshold (lossEta / 2))

theorem selectedOccurrenceJointFrozenExternalLossThreshold_pos
    (lossEta : Real) :
    0 < selectedOccurrenceJointFrozenExternalLossThreshold lossEta := by
  exact lt_min (selectedOccurrenceCanonicalJointLossThreshold_pos _)
    (selectedOccurrenceOptionFrozenLossFourThreshold_pos _)

/-- Combined source-scale envelope for the exact external loss already
present before side selection.  In particular, the fibre count loss and all
Section Eight coefficients remain separate. -/
theorem selectedOccurrenceJointFrozenExternalLoss_le_rpow
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (hactiveParent : 0 < Fintype.card (ActiveParentIndex S))
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hdelta : delta <=
      selectedOccurrenceJointFrozenExternalLossThreshold lossEta) :
    (((2 * prop51JointOccurrenceLoss (ActiveParentIndex S)
        (Nat.log 2 (Fintype.card (ActiveParentIndex S))) : Nat) : ENNReal) *
      (frozenComparableLoss (ActiveParentIndex S)
        (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal)) * 4 <=
      (delta : ENNReal) ^ (-lossEta) := by
  have hjoint :
      ((2 * prop51JointOccurrenceLoss (ActiveParentIndex S)
          (Nat.log 2 (Fintype.card (ActiveParentIndex S))) : Nat) : ENNReal) <=
        (delta : ENNReal) ^ (-(lossEta / 2)) := by
    exact selectedOccurrenceCanonicalJointLoss_le_rpow
      D hD S (by positivity) (hdelta.trans (min_le_left _ _))
  have hfrozen :
      (frozenComparableLoss (ActiveParentIndex S)
          (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal) * 4 <=
        (delta : ENNReal) ^ (-(lossEta / 2)) := by
    exact selectedOccurrenceOptionFrozenComparableLoss_mul_four_le_rpow
      D hD S P hactiveParent (by positivity)
        (hdelta.trans (min_le_right _ _))
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  calc
    (((2 * prop51JointOccurrenceLoss (ActiveParentIndex S)
        (Nat.log 2 (Fintype.card (ActiveParentIndex S))) : Nat) : ENNReal) *
      (frozenComparableLoss (ActiveParentIndex S)
        (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal)) * 4 =
      ((2 * prop51JointOccurrenceLoss (ActiveParentIndex S)
        (Nat.log 2 (Fintype.card (ActiveParentIndex S))) : Nat) : ENNReal) *
        ((frozenComparableLoss (ActiveParentIndex S)
          (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal) * 4) :=
      by ac_rfl
    _ <= (delta : ENNReal) ^ (-(lossEta / 2)) *
        (delta : ENNReal) ^ (-(lossEta / 2)) :=
      mul_le_mul' hjoint hfrozen
    _ = (delta : ENNReal) ^ (-lossEta) := by
      rw [<- ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
      congr 1
      ring

#print axioms selectedOccurrenceOptionFrozenComparableLoss_real_le
#print axioms selectedOccurrenceOptionFrozenLossThreshold_pos
#print axioms selectedOccurrenceOptionFrozenComparableLoss_le_rpow
#print axioms selectedOccurrenceOptionFrozenLossFourThreshold_pos
#print axioms selectedOccurrenceOptionFrozenComparableLoss_mul_four_le_rpow
#print axioms selectedOccurrenceCanonicalJointLossThreshold_pos
#print axioms selectedOccurrenceCanonicalJointLoss_le_rpow
#print axioms selectedOccurrenceJointFrozenExternalLossThreshold_pos
#print axioms selectedOccurrenceJointFrozenExternalLoss_le_rpow

end
end Family8SelectedOccurrenceOptionFrozenLossPowerV1
