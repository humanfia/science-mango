import Family8Grounding.Family8SelectedFineFiberCardCapTransportV2
import Family8Grounding.Family8KatzTaoDoubledFiberRelativePowerEnvelopeV4
import Family8Grounding.Family8ContractedJohnMiddleActualVolumeEnvelopeV4
import Family8Grounding.Family8StickyFiberContractedJohnSourcePowerEnvelopeV4
import Family8Grounding.Family8StickySelectedFineAssemblyFiberBridgeV1
import Family8Grounding.Family8StickyBoundedFiberPartitionCoreV1
import Family8Grounding.Family8ContractedJohnNormalizedProxyScaleRatioV3
import Family8Grounding.Family8GeneralizedKatzTaoMultiplicityV1
import Mathlib.Tactic

/-!
# Same-assembly selected-fibre middle envelope, V2

For the literal selected fibre returned by the mass-popular construction,
this theorem combines the old-fibre cap, the exact doubled Katz--Tao cap
cancellation, the contracted-John source loss, and the actual tube-volume
comparison.  The output is the literal Section 8 `fine -> coarse` factor on
that same selected object.  V1 omitted the namespace containing the literal
actual-datum restriction and is not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedFineContractedJohnMiddleEnvelopeV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnMiddleActualVolumeEnvelopeV3
open Family8ContractedJohnMiddleActualVolumeEnvelopeV4
open Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
open Family8ContractedJohnNormalizedProxyScaleRatioV3
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoDoubledFiberRelativePowerEnvelopeV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8SelectedFineFiberCardCapTransportV2
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnSourcePowerEnvelopeV4
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The exact selected datum on an arbitrary master assembly satisfies the
relative Section 8 middle envelope. -/
theorem selectedFine_sameAssembly_contractedJohnMiddle_le_sectionEight
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (hscale : delta <= rho) (hcoarse : S.activeCoarse.Nonempty)
    {C : ENNReal} (hCone : 1 <= C) (hCfinite : C ≠ ∞)
    (hM : forall k, k ∈ S.activeCoarse ->
      (S.fiber k).card <= katzTaoDoubledFiberNatCap delta rho C)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (boundedFiberCoarseTubePartition S hscale hcoarse
        (katzTaoDoubledFiberNatCap delta rho C) hM
        ).asConvexFactorization Y r)
    (q : {q // q ∈
      (selectedFineScaleCover S A.refinement.indices
        (assembly_indices_subset_activeFine S Y r A)).activeCoarse})
    (selected : Finset {i // i ∈
      (selectedFineScaleCover S A.refinement.indices
        (assembly_indices_subset_activeFine S Y r A)).fiber q.1})
    (hselectedNonempty : selected.Nonempty)
    (hdelta : 0 < delta) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    {epsilon beta gamma p a : Real}
    (hbetaTwo : beta <= 2) (hgammaTwo : gamma <= 2)
    (hgap : 0 <= gamma - beta) (hp : 0 < p) (ha : 0 < a)
    (hsmallRatio : delta / rho <=
      contractedJohnSourceClosedLossThreshold a)
    (hCratio : C <=
      (((delta : ENNReal) / (rho : ENNReal)) ^ (-p))) :
    stickyFiberContractedJohnSourceClosedLoss C *
        frostmanMultiplicityRHS
          (contractedJohnProxyRadius delta rho / 8)
          (restrictActualTubeDatum
            (eighthNormalizedDatum
              (stickyFiberContractedJohnProxyDatum
                (selectedFineScaleCover S A.refinement.indices
                  (assembly_indices_subset_activeFine S Y r A))
                (selectedFineShading S A.refinement.indices
                  A.refinement.shading)
                hrho hrhoOne q)) selected).actualFamilyVolume
          epsilon beta <=
      contractedJohnMiddleActualFixedCoefficient
          ordinaryFiberNatCapFixedConstant epsilon beta gamma (p + a) *
        (((delta : ENNReal) / (rho : ENNReal)) ^
          contractedJohnMiddleRatioGain
            epsilon beta gamma (p + a) p) *
        sectionEightScaleCountFrostmanFactor
          delta rho selected.card gamma := by
  classical
  let hindices := assembly_indices_subset_activeFine S Y r A
  let T := selectedFineScaleCover S A.refinement.indices hindices
  let Z := selectedFineShading S A.refinement.indices A.refinement.shading
  let scale : NNReal := contractedJohnProxyRadius delta rho / 8
  let Dselected := restrictActualTubeDatum
    (eighthNormalizedDatum
      (stickyFiberContractedJohnProxyDatum T Z hrho hrhoOne q)) selected
  have hscalePos : 0 < scale := by
    dsimp only [scale]
    exact div_pos (contractedJohnProxyRadius_pos hdelta hrho) (by norm_num)
  have hproxyHalf : contractedJohnProxyRadius delta rho <= (2 : NNReal)⁻¹ :=
    stickyFiberContractedJohnProxyDatum_delta_le_half hscale hrho
  have hscaleHalf : scale <= (2 : NNReal)⁻¹ := by
    dsimp only [scale]
    calc
      contractedJohnProxyRadius delta rho / 8 <=
          (2 : NNReal)⁻¹ / 8 := by gcongr
      _ <= (2 : NNReal)⁻¹ := by
        rw [← NNReal.coe_le_coe]
        norm_num
  have hscaleOne : scale <= 1 := hscaleHalf.trans (by norm_num)
  have hfixedNN : (3 / 64 : NNReal) <= 1 := by
    rw [← NNReal.coe_le_coe]
    norm_num
  have hscaleSmall : scale <= contractedJohnSourceClosedLossThreshold a := by
    calc
      scale = (3 / 64 : NNReal) * (delta / rho) :=
        contractedJohnProxyRadius_div_eight_eq_fixed_mul_ratio hrho
      _ <= 1 * (delta / rho) := mul_le_mul' hfixedNN le_rfl
      _ = delta / rho := one_mul _
      _ <= contractedJohnSourceClosedLossThreshold a := hsmallRatio
  have hfixedPos : 0 < (3 / 64 : ENNReal) := by norm_num
  have hfixedOne : (3 / 64 : ENNReal) <= 1 := by
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
    norm_num
  have hfixedNegative : 1 <= (3 / 64 : ENNReal) ^ (-p) :=
    ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
      hfixedPos hfixedOne (by linarith)
  have hCscale : C <= (scale : ENNReal) ^ (-p) := by
    calc
      C <= ((delta : ENNReal) / (rho : ENNReal)) ^ (-p) := hCratio
      _ = 1 * ((delta : ENNReal) / (rho : ENNReal)) ^ (-p) := by
        rw [one_mul]
      _ <= (3 / 64 : ENNReal) ^ (-p) *
          ((delta : ENNReal) / (rho : ENNReal)) ^ (-p) :=
        mul_le_mul' hfixedNegative le_rfl
      _ = (scale : ENNReal) ^ (-p) := by
        simpa only [scale] using
          (contractedJohnProxyRadius_div_eight_rpow_eq
            (delta := delta) hrho (-p)).symm
  have hloss : stickyFiberContractedJohnSourceClosedLoss C <=
      (scale : ENNReal) ^ (-(p + a)) :=
    stickyFiberContractedJohnSourceClosedLoss_le_negativePower
      hscalePos hscaleOne hp ha hscaleSmall hCscale
  have hselectedCapNat : selected.card <=
      katzTaoDoubledFiberNatCap delta rho C :=
    selectedFineScaleCover_selected_card_le_parent_cap
      S A.refinement.indices hindices q.1 selected
        (katzTaoDoubledFiberNatCap delta rho C) hM
  have hselectedCap : (selected.card : ENNReal) <=
      (katzTaoDoubledFiberNatCap delta rho C : ENNReal) := by
    exact_mod_cast hselectedCapNat
  have hcapPower :
      (katzTaoDoubledFiberNatCap delta rho C : ENNReal) <=
        ordinaryFiberNatCapFixedConstant *
          (((delta : ENNReal) / (rho : ENNReal)) ^ (-(2 + p))) :=
    katzTaoDoubledFiberNatCap_le_fixed_mul_ratio_negativePower
      hdelta hscale hCone hCfinite hCratio
  have hcount : (Fintype.card {i // i ∈ selected} : ENNReal) <=
      ordinaryFiberNatCapFixedConstant *
        (((delta : ENNReal) / (rho : ENNReal)) ^ (-(2 + p))) := by
    simpa only [Fintype.card_coe] using hselectedCap.trans hcapPower
  have hcountPos : 0 < Fintype.card {i // i ∈ selected} := by
    simpa only [Fintype.card_coe] using hselectedNonempty.card_pos
  have hscaleEq : (scale : ENNReal) =
      (3 / 64 : ENNReal) *
        ((delta : ENNReal) / (rho : ENNReal)) := by
    simpa only [scale] using
      coe_contractedJohnProxyRadius_div_eight_eq_fixed_mul_ratio
        (delta := delta) hrho
  have hbound :=
    loss_mul_actualRHS_le_fixed_mul_ratioGain_mul_sectionEight_of_scale
      (D := Dselected)
      (loss := stickyFiberContractedJohnSourceClosedLoss C)
      (K := ordinaryFiberNatCapFixedConstant)
      (epsilon := epsilon) (beta := beta) (gamma := gamma)
      (lossExp := p + a) (kappa := p)
      hdelta hrho hscalePos hscaleHalf hbetaTwo hgammaTwo hgap
        hscaleEq hloss hcountPos hcount
  simpa only [Dselected, scale, T, Z, hindices, Fintype.card_coe]
    using hbound

#print axioms
  selectedFine_sameAssembly_contractedJohnMiddle_le_sectionEight

end
end Family8SelectedFineContractedJohnMiddleEnvelopeV2
