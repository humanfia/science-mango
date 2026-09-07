import Family8Grounding.Family8StickyShadingAwareSelectedBaseRatioPowerV3
import Family8Grounding.Family8StickyShadingAwareSelectedMassPopularFiberMassV1
import Mathlib.Tactic

/-!
# Same-witness shading mass and contracted-John base ratio with global powers

This successor performs the maximum-mass selection once.  The selected
parent retains both the strong source-to-fibre mass estimate and the base
ratio obtained by cancelling its finite mass coefficient.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyShadingAwareSelectedBaseRatioGlobalPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyBoundedMassPopularRelativePowerFactorV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyMassPopularFixedKatzTaoPowerEnvelopeV1
open Family8StickySelectedFineMassPopularScalarTransportV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareSelectedBaseCoefficientV2
open Family8StickyShadingAwareSelectedMassPopularFiberMassV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {globalDelta delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- One actual parent simultaneously retains source shading mass and satisfies
the fixed Katz--Tao base ratio. -/
theorem exists_shadingAwareSelected_massPopular_baseRatio_and_mass_of_globalPowerCaps
    {eta p a etaF lossExp xExp absorbExp scaleExp : Real}
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hglobal : 0 < globalDelta) (hglobalOne : globalDelta ≤ 1)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0)
    (hloss :
      (2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) ≤
        (globalDelta : ENNReal) ^ (-lossExp))
    (hX : (activeCoarseCardScaleMass S : ENNReal) ≤
      (globalDelta : ENNReal) ^ (-xExp))
    (hconstant : massPopularBaseFixedConstant eta p a ≤
      (globalDelta : ENNReal) ^ (-absorbExp))
    (hq : ((delta : ENNReal) / (rho : ENNReal)) ≤
      (globalDelta : ENNReal) ^ scaleExp)
    (hgain : 0 ≤ eta - (2 * p + a))
    (hbudget : 2 * etaF + lossExp + xExp + absorbExp ≤
      scaleExp * (eta - (2 * p + a)))
    (hsource : (globalDelta : ENNReal) ^ (2 * etaF) ≤
      shadingMassOn Y S.activeFine) :
    let selected := shadingAwareSelectedParents
      S Y A hA0 hAtop hrho hactive hmass
    let retention : Nat := 2 * (Nat.log 2 (Fintype.card index) + 1)
    let q : ENNReal := (delta : ENNReal) / (rho : ENNReal)
    let base : ENNReal :=
      (3 / 64 : ENNReal) ^ (-(2 * p + a)) * q ^ (-(2 * p + a))
    let scale : ENNReal := (3 / 64 : ENNReal) ^ (-eta) * q ^ (-eta)
    let unit : ENNReal :=
      ((3 / 64 : ENNReal) ^ (2 : Nat) * q ^ (2 : Nat)) / 2
    ∃ k ∈ selected,
      shadingMassOn Y S.activeFine ≤
          (retention : ENNReal) * (selected.card : ENNReal) *
            (stickyFiberSourceShading S Y k).shadingMass ∧
        base ≤ scale *
          ((Fintype.card {i // i ∈ S.fiber k} : ENNReal) * unit) := by
  dsimp only
  let selected := shadingAwareSelectedParents
    S Y A hA0 hAtop hrho hactive hmass
  let retention : Nat := 2 * (Nat.log 2 (Fintype.card index) + 1)
  let coefficient : ENNReal :=
    ((retention : ENNReal) * (selected.card : ENNReal)) *
      (8 * (delta : ENNReal) ^ 2)
  let envelopeCoefficient : ENNReal :=
    (retention : ENNReal) *
      (8 * ((activeCoarseCardScaleMass S : ENNReal) *
        (((delta : ENNReal) / (rho : ENNReal)) ^ 2)))
  let q : ENNReal := (delta : ENNReal) / (rho : ENNReal)
  let base : ENNReal :=
    (3 / 64 : ENNReal) ^ (-(2 * p + a)) * q ^ (-(2 * p + a))
  let scale : ENNReal := (3 / 64 : ENNReal) ^ (-eta) * q ^ (-eta)
  let unit : ENNReal :=
    ((3 / 64 : ENNReal) ^ (2 : Nat) * q ^ (2 : Nat)) / 2
  let source : ENNReal := shadingMassOn Y S.activeFine
  obtain ⟨k, hk, hstrongRaw⟩ :=
    exists_shadingAwareSelected_massPopular_wholeFiber_mass
      S Y A hA0 hAtop hrho hactive hmass
  have hk' : k ∈ selected := by simpa only [selected] using hk
  have hstrong : source ≤
      (retention : ENNReal) * (selected.card : ENNReal) *
        (stickyFiberSourceShading S Y k).shadingMass := by
    simpa only [source, retention, selected] using hstrongRaw
  let card : ENNReal := Fintype.card {i // i ∈ S.fiber k}
  have hvolume : familyVolume (S.fiberFamily k) ≤
      card * (8 * (delta : ENNReal) ^ 2) := by
    simpa only [card] using
      stickyFiber_familyVolume_le_card_mul_eight_sq S hdeltaHalf k
  have hfiberMass : (stickyFiberSourceShading S Y k).shadingMass ≤
      card * (8 * (delta : ENNReal) ^ 2) :=
    (stickyFiberSourceShading S Y k).shadingMass_le_familyVolume.trans hvolume
  have hupper : source ≤ coefficient * card := by
    calc
      source ≤ (retention : ENNReal) * (selected.card : ENNReal) *
          (stickyFiberSourceShading S Y k).shadingMass := hstrong
      _ ≤ (retention : ENNReal) * (selected.card : ENNReal) *
          (card * (8 * (delta : ENNReal) ^ 2)) :=
        mul_le_mul' le_rfl hfiberMass
      _ = coefficient * card := by
        dsimp only [coefficient]
        ring
  have hcoefficientEnvelope : coefficient ≤ envelopeCoefficient := by
    simpa only [coefficient, envelopeCoefficient, retention, selected] using
      shadingAwareSelected_cardCoefficient_le_relativeScaleEnvelope
        S Y A hA0 hAtop hrho hactive hmass
  have hq0 : q ≠ 0 := by
    dsimp only [q]
    exact ENNReal.div_ne_zero.mpr
      ⟨ENNReal.coe_ne_zero.mpr hdelta.ne', ENNReal.coe_ne_top⟩
  have hqTop : q ≠ ∞ := by
    dsimp only [q]
    exact ENNReal.div_ne_top ENNReal.coe_ne_top
      (ENNReal.coe_ne_zero.mpr hrho.ne')
  have hbaseEnvelope := baseEnvelope_of_powerCaps
    hglobal hglobalOne hq0 hqTop hloss hX hconstant hq hgain hbudget hsource
  have hlower : coefficient * base ≤ (scale * unit) * source := by
    calc
      coefficient * base ≤ envelopeCoefficient * base :=
        mul_le_mul' hcoefficientEnvelope le_rfl
      _ ≤ (scale * unit) * source := by
        simpa only [envelopeCoefficient, base, scale, unit, source,
          retention, q, mul_assoc] using hbaseEnvelope
  have hcoefficient0 : coefficient ≠ 0 := by
    intro hzero
    have hsourceZero : source = 0 := by
      apply bot_unique
      calc
        source ≤ coefficient * card := hupper
        _ = 0 := by rw [hzero, zero_mul]
    exact hmass (by simpa only [source] using hsourceZero)
  have hretentionTop : (retention : ENNReal) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  have hselectedTop : (selected.card : ENNReal) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  have hareaTop : 8 * (delta : ENNReal) ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hcoefficientTop : coefficient ≠ ∞ := by
    dsimp only [coefficient]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hretentionTop hselectedTop) hareaTop
  have hratio : base ≤ scale * (card * unit) :=
    baseRatio_of_mass_card_sandwich hcoefficient0 hcoefficientTop
      hlower hupper
  refine ⟨k, hk', ?_, ?_⟩
  · simpa only [source] using hstrong
  · simpa only [base, scale, unit, card, q] using hratio

#print axioms
  exists_shadingAwareSelected_massPopular_baseRatio_and_mass_of_globalPowerCaps

end
end Family8StickyShadingAwareSelectedBaseRatioGlobalPowerV1
