import Family8Grounding.Family8StickyShadingAwareSelectedBaseCoefficientV2
import Family8Grounding.Family8StickyMassPopularFixedKatzTaoPowerEnvelopeV1
import Mathlib.Tactic

/-!
# Shading-aware mass-popular base ratio from power inputs

This is the cancellation layer between the literal shading-aware selected
whole fibre and the fixed Katz--Tao base envelope. It selects one actual
parent, invokes the existing global power producer, and cancels the common
finite mass coefficient. No fibrewise target inequality is assumed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyShadingAwareSelectedBaseRatioPowerV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyBoundedMassPopularRelativePowerFactorV1
open Family8StickyMassPopularFixedKatzTaoPowerEnvelopeV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareSelectedBaseCoefficientV2
open Family8StickyShadingAwareSelectedMassPopularFiberV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- One literal parent of the shading-aware selected bucket satisfies the
fixed Katz--Tao base ratio, using only global power caps and the actual source
shading mass floor. -/
theorem exists_shadingAwareSelected_massPopular_baseRatio_of_powerCaps
    {eta p a etaF lossExp xExp absorbExp scaleExp : Real}
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0)
    (hloss :
      (2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) ≤
        (delta : ENNReal) ^ (-lossExp))
    (hX : (activeCoarseCardScaleMass S : ENNReal) ≤
      (delta : ENNReal) ^ (-xExp))
    (hconstant : massPopularBaseFixedConstant eta p a ≤
      (delta : ENNReal) ^ (-absorbExp))
    (hq : ((delta : ENNReal) / (rho : ENNReal)) ≤
      (delta : ENNReal) ^ scaleExp)
    (hgain : 0 ≤ eta - (2 * p + a))
    (hbudget : 2 * etaF + lossExp + xExp + absorbExp ≤
      scaleExp * (eta - (2 * p + a)))
    (hsource : (delta : ENNReal) ^ (2 * etaF) ≤
      shadingMassOn Y S.activeFine) :
    let selected := shadingAwareSelectedParents
      S Y A hA0 hAtop hrho hactive hmass
    let q : ENNReal := (delta : ENNReal) / (rho : ENNReal)
    let base : ENNReal :=
      (3 / 64 : ENNReal) ^ (-(2 * p + a)) * q ^ (-(2 * p + a))
    let scale : ENNReal := (3 / 64 : ENNReal) ^ (-eta) * q ^ (-eta)
    let unit : ENNReal :=
      ((3 / 64 : ENNReal) ^ (2 : Nat) * q ^ (2 : Nat)) / 2
    ∃ k ∈ selected,
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
  obtain ⟨k, hk, hupperRaw⟩ :=
    exists_shadingAwareSelected_massPopular_wholeFiber_card
      S Y A hA0 hAtop hrho hactive hmass hdeltaHalf
  have hk' : k ∈ selected := by simpa only [selected] using hk
  let card : ENNReal := Fintype.card {i // i ∈ S.fiber k}
  have hupper : source ≤ coefficient * card := by
    simpa only [source, coefficient, card, retention, selected] using hupperRaw
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
  have hdeltaOne : delta ≤ 1 := hdeltaHalf.trans (by norm_num)
  have hbaseEnvelope := baseEnvelope_of_powerCaps
    hdelta hdeltaOne hq0 hqTop hloss hX hconstant hq hgain hbudget hsource
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
  refine ⟨k, hk', ?_⟩
  simpa only [base, scale, unit, card, q] using hratio

#print axioms exists_shadingAwareSelected_massPopular_baseRatio_of_powerCaps

end
end Family8StickyShadingAwareSelectedBaseRatioPowerV3
