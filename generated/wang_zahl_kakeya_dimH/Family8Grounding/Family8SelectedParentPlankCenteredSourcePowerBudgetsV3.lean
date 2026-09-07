import Family8Grounding.Family8SelectedParentPlankCenteredSourcePowerEnvelopesV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankCenteredSourcePowerBudgetsV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8ContractedJohnActualTubeProxyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankCenteredHalfPostKatzTaoV1
open Family8SelectedParentPlankCenteredHalfPostMassDatumV2
open Family8SelectedParentPlankCenteredSourcePowerEnvelopesV4
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineMassProxyDatumV2
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyKatzTaoV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Pure-power source budgets for the centered selected-parent proxy

The only geometric premise is a power cap on the exact volume/Jacobian
quotient from V4. Together with source density and global Katz--Tao powers,
it produces all three literal power premises exposed by the V6 endpoint.
-/

def centeredHalfPostFreshLossFixedConstant : ENNReal :=
  480000 * 128 + 2

def centeredHalfPostFreshLossThreshold (absorbEta : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    centeredHalfPostFreshLossFixedConstant absorbEta

theorem centeredHalfPostFreshLossThreshold_pos (absorbEta : Real) :
    0 < centeredHalfPostFreshLossThreshold absorbEta :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem centeredHalfPostFreshLossFixedConstant_ne_top :
    centeredHalfPostFreshLossFixedConstant ≠ ∞ := by
  norm_num [centeredHalfPostFreshLossFixedConstant]

theorem centeredHalfPost_freshLoss_le_power_of_proxyPower
    {s : NNReal} {Cproxy : ENNReal} {coefficientEta absorbEta : Real}
    (hs : 0 < s) (hsOne : s ≤ 1)
    (hcoefficientEta : 0 ≤ coefficientEta)
    (hCproxy : Cproxy ≤ (s : ENNReal) ^ (-coefficientEta))
    (habsorbEta : 0 < absorbEta)
    (hsmall : s ≤ centeredHalfPostFreshLossThreshold absorbEta) :
    ((Nat.ceil ((480000 * (128 * Cproxy) : ENNReal).toReal) + 1 : Nat) :
        ENNReal) ≤
      (s : ENNReal) ^ (-(coefficientEta + absorbEta)) := by
  let d : ENNReal := (s : ENNReal)
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hs.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hdOne : d ≤ 1 := by
    dsimp only [d]
    exact_mod_cast hsOne
  have hpowerTop : d ^ (-coefficientEta) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero hd0 hdTop
  have hCfinite : Cproxy ≠ ∞ := by
    exact ne_top_of_le_ne_top hpowerTop hCproxy
  have hscaledFinite : (128 : ENNReal) * Cproxy ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCfinite
  have hclosed := fixedKatzTaoClosedLoss_coe_le_add_two hscaledFinite
  have hone : 1 ≤ d ^ (-coefficientEta) := by
    rw [← ENNReal.rpow_zero]
    exact ENNReal.rpow_le_rpow_of_exponent_ge hdOne (by linarith)
  have hfixed : centeredHalfPostFreshLossFixedConstant ≤
      d ^ (-absorbEta) := by
    exact finiteConstant_le_delta_negativePower
      centeredHalfPostFreshLossFixedConstant_ne_top habsorbEta hs
        (by simpa only [centeredHalfPostFreshLossThreshold] using hsmall)
  calc
    ((Nat.ceil ((480000 * (128 * Cproxy) : ENNReal).toReal) + 1 : Nat) :
        ENNReal) ≤ 480000 * (128 * Cproxy) + 2 := hclosed
    _ ≤ 480000 * (128 * d ^ (-coefficientEta)) +
          2 * d ^ (-coefficientEta) := by
      apply add_le_add
      · gcongr
      · calc
          (2 : ENNReal) = 2 * 1 := by norm_num
          _ ≤ 2 * d ^ (-coefficientEta) := by gcongr
    _ = centeredHalfPostFreshLossFixedConstant *
          d ^ (-coefficientEta) := by
      unfold centeredHalfPostFreshLossFixedConstant
      ring
    _ ≤ d ^ (-absorbEta) * d ^ (-coefficientEta) := by gcongr
    _ = d ^ (-(coefficientEta + absorbEta)) := by
      rw [show -(coefficientEta + absorbEta) =
        -absorbEta + -coefficientEta by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem selectedPlankFineSource_power_le_centeredDensity
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hradius : affineLinearOperatorNorm
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) *
        (delta : Real) ≤ (s : Real))
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hs : 0 < s) (hsHalf : s ≤ (2 : NNReal)⁻¹)
    {sourceEta geometricEta : Real}
    (hsource : (s : ENNReal) ^ sourceEta ≤
      (selectedPlankFineSourceShading
        Y e S B hrho label W).shadingDensity)
    (hgeometric : centeredHalfPostSelectedPlankFineProxyGeometricLoss
      s e S B hrho label hplank W ≤
        (s : ENNReal) ^ (-geometricEta)) :
    (s : ENNReal) ^ (sourceEta + geometricEta) ≤
      (centeredHalfPostSelectedPlankFineMassDatum
        s Y e S B hrho label hplank W hradius).shading.shadingDensity := by
  let d : ENNReal := (s : ENNReal)
  let loss := centeredHalfPostSelectedPlankFineProxyGeometricLoss
    s e S B hrho label hplank W
  let sourceDensity := (selectedPlankFineSourceShading
    Y e S B hrho label W).shadingDensity
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hs.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hratio0 : affineAxisProxyVolumeRatio delta s ≠ 0 := by
    apply ENNReal.div_ne_zero.mpr
    refine ⟨?_, ?_⟩
    · exact mul_ne_zero (by norm_num)
        (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hs.ne'))
    · exact ENNReal.div_ne_top
        (ENNReal.pow_ne_top ENNReal.coe_ne_top) (by norm_num)
  have hratioTop : affineAxisProxyVolumeRatio delta s ≠ ∞ := by
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    · exact ENNReal.div_ne_zero.mpr
        ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdeltaPos.ne'), by norm_num⟩
  have hJ0 : affineJacobian
      (centeredHalfPostBucketAffineEquiv
        e S B hrho label hplank W) ≠ 0 :=
    (affineJacobian_pos
      (centeredHalfPostBucketAffineEquiv
        e S B hrho label hplank W)).ne'
  have hJTop : affineJacobian
      (centeredHalfPostBucketAffineEquiv
        e S B hrho label hplank W) ≠ ∞ :=
    affineJacobian_ne_top
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W)
  have hloss0 : loss ≠ 0 := by
    dsimp only [loss, centeredHalfPostSelectedPlankFineProxyGeometricLoss]
    exact ENNReal.div_ne_zero.mpr ⟨hratio0, hJTop⟩
  have hlossTop : loss ≠ ∞ := by
    dsimp only [loss, centeredHalfPostSelectedPlankFineProxyGeometricLoss]
    exact ENNReal.div_ne_top hratioTop hJ0
  have hmul : d ^ (sourceEta + geometricEta) * loss ≤
      sourceDensity := by
    calc
      d ^ (sourceEta + geometricEta) * loss ≤
          d ^ (sourceEta + geometricEta) * d ^ (-geometricEta) := by
        gcongr
      _ = d ^ ((sourceEta + geometricEta) + (-geometricEta)) :=
        (ENNReal.rpow_add
          (sourceEta + geometricEta) (-geometricEta) hd0 hdTop).symm
      _ = d ^ sourceEta := by
        congr 1
        ring
      _ ≤ sourceDensity := hsource
  have hdiv : d ^ (sourceEta + geometricEta) ≤ sourceDensity / loss :=
    (ENNReal.le_div_iff_mul_le (Or.inl hloss0) (Or.inl hlossTop)).2 hmul
  exact hdiv.trans
    (selectedPlankFineSource_shadingDensity_div_geometricLoss_le_centered
      s Y e S B hrho label hplank W hradius hdeltaPos hdeltaHalf hs hsHalf)

/-- All three literal power premises required by the V6 endpoint, generated
from source-side powers and one honest geometric Jacobian-loss power. -/
theorem centeredHalfPost_source_power_budgets
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hradius : affineLinearOperatorNorm
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) *
        (delta : Real) ≤ (s : Real))
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hs : 0 < s) (hsHalf : s ≤ (2 : NNReal)⁻¹)
    {C : ENNReal}
    {sourceEta geometricEta globalEta freshAbsorbEta : Real}
    (hsource : (s : ENNReal) ^ sourceEta ≤
      (selectedPlankFineSourceShading
        Y e S B hrho label W).shadingDensity)
    (hgeometric : centeredHalfPostSelectedPlankFineProxyGeometricLoss
      s e S B hrho label hplank W ≤
        (s : ENNReal) ^ (-geometricEta))
    (hglobal : C ≤ (s : ENNReal) ^ (-globalEta))
    (hgeometricEta : 0 ≤ geometricEta) (hglobalEta : 0 ≤ globalEta)
    (hfreshAbsorbEta : 0 < freshAbsorbEta)
    (hsmall : s ≤ centeredHalfPostFreshLossThreshold freshAbsorbEta) :
    let Cproxy := centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
      s e S B hrho label hplank W C
    let loss := Nat.ceil ((480000 * (128 * Cproxy) : ENNReal).toReal) + 1
    ((loss : ENNReal) ≤
        (s : ENNReal) ^
          (-(geometricEta + globalEta + freshAbsorbEta))) ∧
      ((s : ENNReal) ^ (sourceEta + geometricEta) ≤
        (centeredHalfPostSelectedPlankFineMassDatum
          s Y e S B hrho label hplank W hradius).shading.shadingDensity) ∧
      (Cproxy ≤
        (s : ENNReal) ^ (-(geometricEta + globalEta))) := by
  dsimp only
  have hsOne : s ≤ 1 := hsHalf.trans (by norm_num)
  have hCproxy := centeredHalfPost_proxyKatzTaoConstant_le_power
    s e S B hrho label hplank W hs hgeometric hglobal
  refine ⟨?_, ?_, hCproxy⟩
  · exact centeredHalfPost_freshLoss_le_power_of_proxyPower
      hs hsOne (by linarith) hCproxy hfreshAbsorbEta hsmall
  · exact selectedPlankFineSource_power_le_centeredDensity
      s Y e S B hrho label hplank W hradius hdeltaPos hdeltaHalf
        hs hsHalf hsource hgeometric

#print axioms centeredHalfPostFreshLossThreshold_pos
#print axioms centeredHalfPostFreshLossFixedConstant_ne_top
#print axioms centeredHalfPost_freshLoss_le_power_of_proxyPower
#print axioms selectedPlankFineSource_power_le_centeredDensity
#print axioms centeredHalfPost_source_power_budgets

end
end Family8SelectedParentPlankCenteredSourcePowerBudgetsV3
