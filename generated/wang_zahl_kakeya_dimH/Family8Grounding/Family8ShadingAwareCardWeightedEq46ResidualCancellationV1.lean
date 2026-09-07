import Family8Grounding.Family8ShadingAwareLogPartitionSourceFactorFloorV1
import Family8Grounding.Family8SelectedParentCardWeightedFixedEnvelopeLogAbsorptionV1
import Family8Grounding.Family8SelectedParentCardWeightedProp66AInnerV1
import Family8Grounding.Family8FullRefinementSourceTauMassPopularEq46ExactCapV7
import Mathlib.Tactic

/-!
# Shading-aware selected source cancellation in Equation (46)

The logarithmic shading selector loses one finite factor in retained source
mass and its balanced partition loses one finite fibre factor.  This file
multiplies the one-count Cordoba core by their literal product, applies the
fixed-container/logarithmic envelope, and cancels that same positive natural
product against the actual selected-parent source factor.  No Equation (46)
conclusion is assumed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ShadingAwareCardWeightedEq46ResidualCancellationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CanonicalFullGreedyPartitionChoiceV4
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8FullRefinementSourceTauMassPopularEq46ExactCapV7
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCardWeightedCordobaCoreV2
open Family8SelectedParentCardWeightedFixedEnvelopeLogAbsorptionV1
open Family8SelectedParentCardWeightedProp66AInnerV1
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentMassPopularProp66AInnerV4
open Family8ShadingAwareLogPartitionSourceFactorFloorV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open Family8StickyShadingAwareCanonicalLogSelectedDatumV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

section

variable
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hrho : 0 < rho) (hscale : delta ≤ rho)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn D.shading S.activeFine ≠ 0)

local notation "P₀" =>
  shadingAwareLogPartition S D.shading (sourceA : ENNReal)
    (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
    hrho hscale hactive hmass

local notation "D₁" =>
  shadingAwareSelectedActualDatum D S (sourceA : ENNReal)
    (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
    hrho hactive hmass

local notation "S₁" => exactPartitionStickyCover P₀
local notation "G₁" => canonicalFullGreedyPartition S₁
local notation "selectionLoss" =>
  (2 * (Nat.log 2 (Fintype.card index) + 1) : Nat)
local notation "fiberCap" => (CoarseTubePartition.branchingLoss P₀ * CoarseTubePartition.branching P₀ : Nat)
local notation "sourceCap" => (selectionLoss * fiberCap : Nat)
local notation "sourceMass" => shadingMassOn D.shading S.activeFine

/-- The literal shading-selection and balanced-fibre losses cancel from the
card-weighted Equation (46) core.  The only numerical input is the preceding
coefficient/inner-factor comparison, before the source cancellation. -/
theorem shadingAwareLogPartition_cardWeightedCrossEq46Budget_of_residualEnvelope
    (hD : D.IsAdmissible) (hrhoOne : rho ≤ 1)
    (k : Fin (blocks (S₁).activeCoarseFamily G₁).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S₁ G₁)
      (parentAggregatedShading S₁ (D₁).shading) loss)
    (label : Fin 3 → Int) (KT : ENNReal) (tubesPerPlank : Nat)
    {lossEta absorbEta epsilon beta : Real}
    (habsorbEta : 0 < absorbEta)
    (hrhoThreshold :
      rho ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        ((2 : ENNReal) * (2304 : ENNReal) ^ 3) absorbEta)
    (hscalar :
      (sourceCap : ENNReal) *
          ((rho : ENNReal) ^ (-(lossEta + absorbEta)) *
            ((loss : ENNReal) *
              (Fintype.card (ActiveParentIndex S₁) : ENNReal) * KT)) ≤
        sourceMass *
          proposition66AInnerFactor rho
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta) :
    CardWeightedCrossEq46Budget D₁ S₁ hrho G₁ k r hr A label KT
      lossEta tubesPerPlank epsilon beta := by
  let J : ENNReal := affineJacobian
    (bucketNormalizedAffineEquiv
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S₁ hrho G₁ k) r hr)
      label)
  let core : ENNReal :=
    (rho : ENNReal) ^ (-lossEta) *
      selectedParentCardWeightedCordobaCoreBudget
        D₁ S₁ hrho G₁ k r A label KT
  let inner : ENNReal := proposition66AInnerFactor rho
    (bucketShortA label) (bucketShortB label)
    tubesPerPlank epsilon beta
  let sourceFloor : ENNReal :=
    (sourceMass / (selectionLoss : ENNReal)) / (fiberCap : ENNReal)
  have hselectionLossPos : 0 < selectionLoss := by
    omega
  have hfiberCapPos : 0 < fiberCap :=
    Nat.mul_pos (CoarseTubePartition.branchingLoss_pos P₀) (CoarseTubePartition.branching_pos P₀)
  have hsourceCapPos : 0 < sourceCap :=
    Nat.mul_pos hselectionLossPos hfiberCapPos
  have hselectionLoss0 : (selectionLoss : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hselectionLossPos
  have hselectionLossTop : (selectionLoss : ENNReal) ≠ ∞ :=
    ENNReal.coe_ne_top
  have hfiberCap0 : (fiberCap : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hfiberCapPos
  have hfiberCapTop : (fiberCap : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hcapFloor : (sourceCap : ENNReal) * sourceFloor = sourceMass := by
    dsimp only [sourceFloor]
    rw [Nat.cast_mul selectionLoss fiberCap]
    calc
      ((selectionLoss : ENNReal) * (fiberCap : ENNReal)) *
          ((sourceMass / (selectionLoss : ENNReal)) /
            (fiberCap : ENNReal)) =
        ((sourceMass / (selectionLoss : ENNReal)) /
            (fiberCap : ENNReal)) * (fiberCap : ENNReal) *
              (selectionLoss : ENNReal) := by ac_rfl
      _ = (sourceMass / (selectionLoss : ENNReal)) *
            (selectionLoss : ENNReal) := by
          rw [ENNReal.div_mul_cancel hfiberCap0 hfiberCapTop]
      _ = sourceMass :=
        ENNReal.div_mul_cancel hselectionLoss0 hselectionLossTop
  have hsource : J * sourceFloor ≤
      selectedParentMassPopularSourceFactor
        D₁ S₁ hrho G₁ k r hr label := by
    dsimp only [J, sourceFloor]
    exact
      shadingAwareLogPartition_selectedParentSourceFactor_floor
      D S (sourceA : ENNReal)
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
      hrho hscale hactive hmass k r hr label
  have hscaled : (sourceCap : ENNReal) * core ≤
      (J * sourceMass) * inner := by
    have hraw :=
      relativeScaled_cardWeightedCordobaCore_le_of_residualEnvelope
        D₁
        (Family8StickyShadingAwareCanonicalLogSelectedDatumV1.ActualTubeDatum.IsAdmissible.shadingAwareSelected hD S (sourceA : ENNReal)
          (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
          hrho hactive hmass)
        S₁ hrho hrhoOne G₁ k r hr A label KT tubesPerPlank
        (capBound := (sourceCap : ENNReal))
        (relativeSquare := 1) (sourcePower := sourceMass)
        (lossEta := lossEta) (absorbEta := absorbEta)
        (epsilon := epsilon) (beta := beta)
        habsorbEta hrhoThreshold (by
          rw [one_mul]
          exact hscalar)
    dsimp only [core, J, inner]
    convert hraw using 1; simp
    congr 1
  have hcross : (sourceCap : ENNReal) * core ≤
      (J * ((sourceCap : ENNReal) * sourceFloor)) * inner := by
    rw [hcapFloor]
    exact hscaled
  have hbudget := cancel_positive_nat_sourceCap sourceCap hsourceCapPos
    (core := core) (J := J) (sourceFloor := sourceFloor)
    (sourceFactor := selectedParentMassPopularSourceFactor
      D₁ S₁ hrho G₁ k r hr label) (inner := inner)
    hsource hcross
  simpa only [CardWeightedCrossEq46Budget, core, inner] using hbudget

#print axioms
  shadingAwareLogPartition_cardWeightedCrossEq46Budget_of_residualEnvelope

end

end
end Family8ShadingAwareCardWeightedEq46ResidualCancellationV1
