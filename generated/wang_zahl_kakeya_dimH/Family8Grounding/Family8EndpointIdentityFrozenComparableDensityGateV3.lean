import Family8Grounding.Family8ActiveFrozenComparableLogLossAbsorptionV4
import Mathlib.Tactic

/-!
# Canonical frozen-comparable reduction of the endpoint density gate, V3

For an arbitrary frozen-neighborhood assembly the natural-number field
`loss` is upward-closed and has no power bound.  The endpoint producer does,
however, identify the loss of its actual assembly with the literal
active-index `frozenComparableLoss`.  This module uses exactly that equality
and the proved logarithmic-loss absorption theorem.

The remaining premise is deliberately assembly-independent.  It is the real
scalar comparison between the radius/conflict target and the source density
floor; no such comparison is manufactured here.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8EndpointIdentityFrozenComparableDensityGateV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8FrozenComparableActualAverageMassDensityV1
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- Replace only the loss of the actual endpoint assembly, and keep the
genuine assembly-independent density exponent budget explicit. -/
theorem target_le_density_div_actualFrozenLoss_mul_branching
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    {lossExp : Real} (hlossExp : 0 < lossExp)
    (hsmallLoss : delta <=
      activeFrozenComparableLossAbsorptionThreshold lossExp)
    {actualLoss branchingLoss : Nat}
    (hactualLoss : actualLoss =
      frozenComparableLoss {i // i ∈ S.activeFine}
        (Fin S.activeCoarse.card))
    (hbranchingLoss : branchingLoss = 1)
    {target densityFloor density : ENNReal}
    (hdensity : densityFloor <= density)
    (hpower :
      target * ((delta : ENNReal) ^ (-lossExp) * 768) <= densityFloor) :
    target <= density /
      ((actualLoss : ENNReal) *
        (768 * (branchingLoss : ENNReal) ^ (2 : Nat))) := by
  have hactualPos : 0 < actualLoss := by
    rw [hactualLoss]
    unfold frozenComparableLoss
    positivity
  have hactual0 : (actualLoss : ENNReal) ≠ 0 := by
    exact_mod_cast hactualPos.ne'
  have hactualTop : (actualLoss : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hactualPower : (actualLoss : ENNReal) <=
      (delta : ENNReal) ^ (-lossExp) := by
    rw [hactualLoss]
    exact activeFrozenComparableLoss_le_rpow
      D hD S hlossExp hsmallLoss
  have hden0 : (actualLoss : ENNReal) * 768 ≠ 0 :=
    mul_ne_zero hactual0 (by norm_num)
  have hdenTop : (actualLoss : ENNReal) * 768 ≠ ∞ :=
    ENNReal.mul_ne_top hactualTop (by norm_num)
  have hgate : target <= density / ((actualLoss : ENNReal) * 768) := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hden0) (Or.inl hdenTop)).2
    calc
      target * ((actualLoss : ENNReal) * 768) <=
          target * ((delta : ENNReal) ^ (-lossExp) * 768) := by
        gcongr
      _ <= densityFloor := hpower
      _ <= density := hdensity
  simpa only [hbranchingLoss, Nat.cast_one, one_pow, mul_one] using hgate

#print axioms target_le_density_div_actualFrozenLoss_mul_branching

end
end Family8EndpointIdentityFrozenComparableDensityGateV3
