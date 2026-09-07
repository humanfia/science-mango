import Family8Grounding.Family8Prop66AUniformCountLossAlgebraV3
import Mathlib.Tactic

/-!
# Proposition 6.6 symmetric inner-scale mismatch

The Equation (45) outer family and the Equation (46) inner fibre may use
different dyadic side labels.  This file transports the inner factor to the
outer scales, retaining the outer Proposition 6.6 aspect gain.  The exact
scale ratio remains visible and is never asserted to be at most one.
-/

open scoped ENNReal NNReal

namespace Family8Prop66InnerScaleMismatchAbsorptionV1

open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8Prop66AUniformCountLossAlgebraV3

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-- Exact scale ratio for replacing an inner factor at
`(innerA, innerB)` by one at `(outerA, outerB)`.

The scale-dependent part of Equation (46) is
`a^(2 * beta - 1) * b^(beta - 1)`. -/
def prop66InnerScaleMismatchLoss
    (outerA outerB innerA innerB : NNReal) (beta : Real) : ENNReal :=
  (((outerA : ENNReal) / (innerA : ENNReal)) ^ (1 - 2 * beta)) *
    (((outerB : ENNReal) / (innerB : ENNReal)) ^ (1 - beta))

/-- The Equation (46) factors at two positive finite side pairs differ by
exactly `prop66InnerScaleMismatchLoss`.

All four side scales and `delta` are finite `NNReal` values.  Their explicit
positivity hypotheses provide every nonzero condition used below. -/
theorem proposition66AInnerFactor_eq_scaleMismatchLoss_mul
    {delta outerA outerB innerA innerB : NNReal} {tubesPerPlank : Nat}
    {epsilon beta : Real}
    (hdelta : 0 < delta)
    (houterA : 0 < outerA) (houterB : 0 < outerB)
    (hinnerA : 0 < innerA) (hinnerB : 0 < innerB)
    (hbetaOne : beta ≤ 1) :
    proposition66AInnerFactor delta innerA innerB tubesPerPlank epsilon beta =
      prop66InnerScaleMismatchLoss outerA outerB innerA innerB beta *
        proposition66AInnerFactor delta outerA outerB tubesPerPlank epsilon beta := by
  let D : ENNReal := delta
  let AO : ENNReal := outerA
  let BO : ENNReal := outerB
  let AI : ENNReal := innerA
  let BI : ENNReal := innerB
  let M : ENNReal := tubesPerPlank
  let p : Real := 1 - beta / 2
  let r : Real := 1 - 2 * beta
  let s : Real := 1 - beta
  let q : Real := 2 - 3 * beta
  have hp : 0 ≤ p := by
    dsimp only [p]
    linarith
  have hs : 0 ≤ s := by
    dsimp only [s]
    linarith
  have hD0 : D ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hAO0 : AO ≠ 0 := ENNReal.coe_ne_zero.mpr houterA.ne'
  have hBO0 : BO ≠ 0 := ENNReal.coe_ne_zero.mpr houterB.ne'
  have hAI0 : AI ≠ 0 := ENNReal.coe_ne_zero.mpr hinnerA.ne'
  have hBI0 : BI ≠ 0 := ENNReal.coe_ne_zero.mpr hinnerB.ne'
  have hDTop : D ≠ ∞ := ENNReal.coe_ne_top
  have hAOTop : AO ≠ ∞ := ENNReal.coe_ne_top
  have hBOTop : BO ≠ ∞ := ENNReal.coe_ne_top
  have hAITop : AI ≠ ∞ := ENNReal.coe_ne_top
  have hBITop : BI ≠ ∞ := ENNReal.coe_ne_top
  have hsquareCount (Y : ENNReal) (n : Nat) :
      ((Y ^ (2 : Nat)) * (n : ENNReal)) ^ p =
        Y ^ (2 * p) * (n : ENNReal) ^ p := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hnormalized (a b : NNReal) (ha : 0 < a) (hb : 0 < b) :
      proposition66AInnerFactor delta a b tubesPerPlank epsilon beta =
        (D ^ (-epsilon / 2) * D ^ q * M ^ p) *
          ((a : ENNReal) ^ (-r) * (b : ENNReal) ^ (-s)) := by
    let A : ENNReal := a
    let B : ENNReal := b
    let Y : ENNReal := D / A
    have hA0 : A ≠ 0 := ENNReal.coe_ne_zero.mpr ha.ne'
    have hB0 : B ≠ 0 := ENNReal.coe_ne_zero.mpr hb.ne'
    have hATop : A ≠ ∞ := ENNReal.coe_ne_top
    have hBTop : B ≠ ∞ := ENNReal.coe_ne_top
    have hY0 : Y ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hD0, hATop⟩
    have hYTop : Y ≠ ∞ := ENNReal.div_ne_top hDTop hA0
    have hYcombine : Y ^ (-2 * beta) * Y ^ (2 * p) = Y ^ q := by
      rw [← ENNReal.rpow_add (-2 * beta) (2 * p) hY0 hYTop]
      congr 1
      dsimp only [p, q]
      ring
    have hABpower : (A / B) ^ s = A ^ s * B ^ (-s) := by
      rw [ENNReal.div_rpow_of_nonneg A B hs, div_eq_mul_inv,
        ENNReal.rpow_neg]
    have hDApower : Y ^ q = D ^ q * A ^ (-q) := by
      dsimp only [Y]
      rw [div_eq_mul_inv,
        ENNReal.mul_rpow_of_ne_top hDTop (ENNReal.inv_ne_top.mpr hA0) q,
        ENNReal.inv_rpow, ← ENNReal.rpow_neg]
    have hAcombine : A ^ s * A ^ (-q) = A ^ (-r) := by
      rw [← ENNReal.rpow_add s (-q) hA0 hATop]
      congr 1
      dsimp only [r, s, q]
      ring
    unfold proposition66AInnerFactor
    change
      D ^ (-epsilon / 2) * (A / B) ^ s * Y ^ (-2 * beta) *
          ((Y ^ (2 : Nat)) * M) ^ p =
        (D ^ (-epsilon / 2) * D ^ q * M ^ p) *
          (A ^ (-r) * B ^ (-s))
    rw [hsquareCount Y tubesPerPlank]
    calc
      D ^ (-epsilon / 2) * (A / B) ^ s * Y ^ (-2 * beta) *
          (Y ^ (2 * p) * M ^ p) =
        (D ^ (-epsilon / 2) * M ^ p) *
          ((A / B) ^ s * (Y ^ (-2 * beta) * Y ^ (2 * p))) := by
            ac_rfl
      _ = (D ^ (-epsilon / 2) * M ^ p) *
          ((A / B) ^ s * Y ^ q) := by rw [hYcombine]
      _ = (D ^ (-epsilon / 2) * M ^ p) *
          ((A ^ s * B ^ (-s)) * (D ^ q * A ^ (-q))) := by
            rw [hABpower, hDApower]
      _ = (D ^ (-epsilon / 2) * D ^ q * M ^ p) *
          ((A ^ s * A ^ (-q)) * B ^ (-s)) := by
            ac_rfl
      _ = (D ^ (-epsilon / 2) * D ^ q * M ^ p) *
          (A ^ (-r) * B ^ (-s)) := by rw [hAcombine]
  have hratioInv (X Y : ENNReal)
      (hX0 : X ≠ 0) (hXTop : X ≠ ∞)
      (hY0 : Y ≠ 0) (hYTop : Y ≠ ∞) (t : Real) :
      (X / Y) ^ t * X ^ (-t) = Y ^ (-t) := by
    have hbase : (X / Y) * X⁻¹ = Y⁻¹ := by
      rw [div_eq_mul_inv]
      calc
        X * Y⁻¹ * X⁻¹ = (X * X⁻¹) * Y⁻¹ := by ac_rfl
        _ = Y⁻¹ := by rw [ENNReal.mul_inv_cancel hX0 hXTop, one_mul]
    have hXneg : X ^ (-t) = X⁻¹ ^ t := by
      rw [ENNReal.rpow_neg, ENNReal.inv_rpow]
    have hYneg : Y ^ (-t) = Y⁻¹ ^ t := by
      rw [ENNReal.rpow_neg, ENNReal.inv_rpow]
    rw [hXneg, hYneg,
      ← ENNReal.mul_rpow_of_ne_top
        (ENNReal.div_ne_top hXTop hY0) (ENNReal.inv_ne_top.mpr hX0) t,
      hbase]
  have hratioA : (AO / AI) ^ r * AO ^ (-r) = AI ^ (-r) :=
    hratioInv AO AI hAO0 hAOTop hAI0 hAITop r
  have hratioB : (BO / BI) ^ s * BO ^ (-s) = BI ^ (-s) :=
    hratioInv BO BI hBO0 hBOTop hBI0 hBITop s
  have hscale :
      AI ^ (-r) * BI ^ (-s) =
        ((AO / AI) ^ r * (BO / BI) ^ s) *
          (AO ^ (-r) * BO ^ (-s)) := by
    rw [← hratioA, ← hratioB]
    ac_rfl
  rw [hnormalized innerA innerB hinnerA hinnerB,
    hnormalized outerA outerB houterA houterB]
  unfold prop66InnerScaleMismatchLoss
  change
    (D ^ (-epsilon / 2) * D ^ q * M ^ p) *
        (AI ^ (-r) * BI ^ (-s)) =
      ((AO / AI) ^ r * (BO / BI) ^ s) *
        ((D ^ (-epsilon / 2) * D ^ q * M ^ p) *
          (AO ^ (-r) * BO ^ (-s)))
  rw [hscale]
  ac_rfl

/-- Exact-count product adapter with independent labels.  The final
Proposition 6.6 aspect gain is the one from the genuine outer bucket. -/
theorem proposition66AOuterFactor_mul_innerFactor_eq_innerScaleMismatch_mul_frostmanFactor
    {delta outerA outerB innerA innerB : NNReal}
    {plankCount tubesPerPlank totalCount : Nat}
    {CF : ENNReal} {epsilon beta : Real}
    (hdelta : 0 < delta)
    (houterA : 0 < outerA) (houterB : 0 < outerB)
    (hinnerA : 0 < innerA) (hinnerB : 0 < innerB)
    (hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (hcount : totalCount = plankCount * tubesPerPlank) :
    proposition66AOuterFactor delta outerA outerB plankCount CF epsilon beta *
        proposition66AInnerFactor delta innerA innerB tubesPerPlank epsilon beta =
      prop66InnerScaleMismatchLoss outerA outerB innerA innerB beta *
        proposition66AFrostmanFactor delta outerA outerB totalCount CF epsilon beta := by
  have hinnerScale := proposition66AInnerFactor_eq_scaleMismatchLoss_mul
    (delta := delta) (tubesPerPlank := tubesPerPlank)
    (epsilon := epsilon) (beta := beta)
    hdelta houterA houterB hinnerA hinnerB hbetaOne
  have hsame := proposition66AOuterFactor_mul_innerFactor_eq_frostmanFactor
    (CF := CF) (epsilon := epsilon) (beta := beta)
    hdelta houterA houterB hbeta hbetaOne hcount
  calc
    proposition66AOuterFactor delta outerA outerB plankCount CF epsilon beta *
        proposition66AInnerFactor delta innerA innerB tubesPerPlank epsilon beta =
      proposition66AOuterFactor delta outerA outerB plankCount CF epsilon beta *
        (prop66InnerScaleMismatchLoss outerA outerB innerA innerB beta *
          proposition66AInnerFactor delta outerA outerB tubesPerPlank epsilon beta) := by
            rw [hinnerScale]
    _ = prop66InnerScaleMismatchLoss outerA outerB innerA innerB beta *
        (proposition66AOuterFactor delta outerA outerB plankCount CF epsilon beta *
          proposition66AInnerFactor delta outerA outerB tubesPerPlank epsilon beta) := by
            ac_rfl
    _ = _ := by rw [hsame]

/-- Uniform-count-loss form of the symmetric product adapter. -/
theorem proposition66AOuterFactor_mul_innerFactor_le_innerScaleMismatch_countLoss_mul_frostmanFactor
    {delta outerA outerB innerA innerB : NNReal}
    {plankCount tubesPerPlank totalCount : Nat}
    {CF countLoss : ENNReal} {epsilon beta : Real}
    (hdelta : 0 < delta)
    (houterA : 0 < outerA) (houterB : 0 < outerB)
    (hinnerA : 0 < innerA) (hinnerB : 0 < innerB)
    (hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (hcount : ((plankCount * tubesPerPlank : Nat) : ENNReal) ≤
      countLoss * (totalCount : ENNReal)) :
    proposition66AOuterFactor delta outerA outerB plankCount CF epsilon beta *
        proposition66AInnerFactor delta innerA innerB tubesPerPlank epsilon beta ≤
      (prop66InnerScaleMismatchLoss outerA outerB innerA innerB beta *
        countLoss ^ (1 - beta / 2)) *
          proposition66AFrostmanFactor delta outerA outerB totalCount CF epsilon beta := by
  have hinnerScale := proposition66AInnerFactor_eq_scaleMismatchLoss_mul
    (delta := delta) (tubesPerPlank := tubesPerPlank)
    (epsilon := epsilon) (beta := beta)
    hdelta houterA houterB hinnerA hinnerB hbetaOne
  have hsame :=
    proposition66AOuterFactor_mul_innerFactor_le_countLoss_mul_frostmanFactor
      (CF := CF) (countLoss := countLoss) (epsilon := epsilon) (beta := beta)
      hdelta houterA houterB hbeta hbetaOne hcount
  calc
    proposition66AOuterFactor delta outerA outerB plankCount CF epsilon beta *
        proposition66AInnerFactor delta innerA innerB tubesPerPlank epsilon beta =
      proposition66AOuterFactor delta outerA outerB plankCount CF epsilon beta *
        (prop66InnerScaleMismatchLoss outerA outerB innerA innerB beta *
          proposition66AInnerFactor delta outerA outerB tubesPerPlank epsilon beta) := by
            rw [hinnerScale]
    _ = prop66InnerScaleMismatchLoss outerA outerB innerA innerB beta *
        (proposition66AOuterFactor delta outerA outerB plankCount CF epsilon beta *
          proposition66AInnerFactor delta outerA outerB tubesPerPlank epsilon beta) := by
            ac_rfl
    _ ≤ prop66InnerScaleMismatchLoss outerA outerB innerA innerB beta *
        (countLoss ^ (1 - beta / 2) *
          proposition66AFrostmanFactor delta outerA outerB totalCount CF epsilon beta) :=
      mul_le_mul' le_rfl hsame
    _ = (prop66InnerScaleMismatchLoss outerA outerB innerA innerB beta *
          countLoss ^ (1 - beta / 2)) *
        proposition66AFrostmanFactor delta outerA outerB totalCount CF epsilon beta := by
      ac_rfl

#print axioms prop66InnerScaleMismatchLoss
#print axioms proposition66AInnerFactor_eq_scaleMismatchLoss_mul
#print axioms
  proposition66AOuterFactor_mul_innerFactor_eq_innerScaleMismatch_mul_frostmanFactor
#print axioms
  proposition66AOuterFactor_mul_innerFactor_le_innerScaleMismatch_countLoss_mul_frostmanFactor

end
end Family8Prop66InnerScaleMismatchAbsorptionV1
