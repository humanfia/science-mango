import FamilyStickyGrounding.FamilyStickyScaleChainActualUnitCapProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainSelectedGlobalExponentProducerV1

open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainExponentProductBudgetV1
open FamilyStickyScaleChainActualStoppingUpstreamClosureV1
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainActualUnitCapProducerV1

noncomputable section

/-!
# Exact selected global exponent producer

The selected stopping interval needs the literal comparison
`actualGlobalProductAt <= requiredGlobalPowerAt`.  Separate unit caps are a
convenient sufficient condition, but they are not the quantitative statement
used by the stopping endpoint.

This module packages the paper-shaped alternative at exactly one selected
interval: pointwise powers for the actual buffered local factors, one power
for the telescoped endpoint ratio, and a one-sided exponent balance.  The
balance is deliberately an inequality.  Since `theta <= 1`, any total
exponent at least the required negative exponent is strong enough.

The exact comparison is decidable independently of any exponent
decomposition.  A legal enlargement of the stored dimensional envelope loss
can force its strict failure, showing that neither the buffered hierarchy nor
the scale sequence alone can manufacture the missing quantitative estimates.
-/

variable {delta : NNReal} {outerDepth chainDepth : Nat}
  {S : FiniteScaleSequence delta outerDepth}
  {profile : Nat -> Real} {stage : Nat}

/-! ## One-interval paper-style exponent estimates -/

/-- Pointwise exponent estimates at one selected interval.  This is weaker
than `GlobalExponentAllocation`: it has no obligations at unused intervals,
and its exponent accounting is the sharp one-sided balance needed when the
base `theta` is at most one. -/
structure SelectedGlobalExponentEstimates
    (B : BufferedChainFamily outerDepth chainDepth)
    (S : FiniteScaleSequence delta outerDepth)
    (profile : Nat -> Real) (stage : Nat)
    (m : Fin outerDepth) where
  localExponent : Nat -> Real
  endpointExponent : Real
  localFactor_upper : forall l, l < chainDepth ->
    FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.localFactor
        (B.hierarchy m) (B.datum m) l <=
      (S.theta m : ENNReal) ^ localExponent l
  endpointRatio_upper :
    actualGlobalEndpointRatioAt B m <=
      (S.theta m : ENNReal) ^ endpointExponent
  exponent_balance :
    -profile (stage - 1) <=
      (∑ l ∈ Finset.range chainDepth, localExponent l) +
        endpointExponent

/-- The selected pointwise factor estimates and one-sided balance produce the
literal global comparison, without passing through a unit cap.  Positivity of
`theta` is generated from the actual scale sequence and `0 < delta`. -/
theorem actualGlobalProductAt_le_requiredGlobalPowerAt
    (B : BufferedChainFamily outerDepth chainDepth)
    (m : Fin outerDepth) (delta_pos : 0 < delta)
    (E : SelectedGlobalExponentEstimates B S profile stage m) :
    actualGlobalProductAt B m <=
      requiredGlobalPowerAt S profile stage m := by
  have theta_pos : 0 < S.theta m :=
    ScaleSequence.theta_pos_of_delta_pos S delta_pos m
  have theta_ne_zero : (S.theta m : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr theta_pos.ne'
  have theta_ne_top : (S.theta m : ENNReal) ≠ ∞ :=
    ENNReal.coe_ne_top
  have theta_le_one : (S.theta m : ENNReal) <= 1 := by
    exact_mod_cast S.theta_le_one m
  have product_le :
      actualGlobalProductAt B m <=
        (S.theta m : ENNReal) ^
          ((∑ l ∈ Finset.range chainDepth, E.localExponent l) +
            E.endpointExponent) := by
    simpa [actualGlobalProductAt, actualGlobalEndpointRatioAt] using
      prod_mul_endpoint_le_rpow_sum_add
        (S.theta m : ENNReal) theta_ne_zero theta_ne_top
        (fun l =>
          FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.localFactor
            (B.hierarchy m) (B.datum m) l)
        E.localExponent chainDepth (actualGlobalEndpointRatioAt B m)
        E.endpointExponent E.localFactor_upper E.endpointRatio_upper
  calc
    actualGlobalProductAt B m <=
        (S.theta m : ENNReal) ^
          ((∑ l ∈ Finset.range chainDepth, E.localExponent l) +
            E.endpointExponent) := product_le
    _ <= (S.theta m : ENNReal) ^ (-profile (stage - 1)) :=
      ENNReal.rpow_le_rpow_of_exponent_ge theta_le_one E.exponent_balance
    _ = requiredGlobalPowerAt S profile stage m := by
      rfl

/-- The old all-interval allocation forgets to the strictly smaller selected
certificate. -/
def SelectedGlobalExponentEstimates.ofGlobalExponentAllocation
    (B : BufferedChainFamily outerDepth chainDepth)
    (E : GlobalExponentAllocation B S stage profile)
    (m : Fin outerDepth) :
    SelectedGlobalExponentEstimates B S profile stage m where
  localExponent := E.localExponent m
  endpointExponent := E.endpointExponent m
  localFactor_upper := E.localFactor_upper m
  endpointRatio_upper := by
    simpa [actualGlobalEndpointRatioAt] using E.endpointRatio_upper m
  exponent_balance := le_of_eq (E.exponent_balance m).symm

/-- The older exponent-budget API also forgets to the selected certificate;
its stored positivity field is not duplicated. -/
def SelectedGlobalExponentEstimates.ofExponentBudgetData
    (B : BufferedChainFamily outerDepth chainDepth)
    (E : FamilyStickyScaleChainExponentProductBudgetV1.BufferedChainFamily.ExponentBudgetData
      B S stage profile)
    (m : Fin outerDepth) :
    SelectedGlobalExponentEstimates B S profile stage m where
  localExponent := E.localExponent m
  endpointExponent := E.endpointExponent m
  localFactor_upper := E.localFactor_upper m
  endpointRatio_upper := by
    simpa [actualGlobalEndpointRatioAt] using E.endpointRatio_upper m
  exponent_balance := le_of_eq (E.exponent_balance m).symm

/-! ## First-non-large specialization -/

variable {epsilon : Real}

/-- At the computed first non-large interval, the sole analytic input is the
selected exponent-estimate certificate itself. -/
theorem firstNonLarge_actualGlobalProductAt_le_requiredGlobalPowerAt
    (B : BufferedChainFamily outerDepth chainDepth)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (delta_pos : 0 < delta)
    (E : SelectedGlobalExponentEstimates B S profile stage
      (firstNonLargeStep S epsilon not_all_large)) :
    actualGlobalProductAt B
        (firstNonLargeStep S epsilon not_all_large) <=
      requiredGlobalPowerAt S profile stage
        (firstNonLargeStep S epsilon not_all_large) :=
  actualGlobalProductAt_le_requiredGlobalPowerAt B
    (firstNonLargeStep S epsilon not_all_large) delta_pos E

/-! ## Exact diagnostic and obstruction -/

/-- The unique failure mode of the selected global comparison is its strict
reverse inequality. -/
inductive SelectedGlobalComparisonFailure
    (B : BufferedChainFamily outerDepth chainDepth)
    (S : FiniteScaleSequence delta outerDepth)
    (profile : Nat -> Real) (stage : Nat)
    (m : Fin outerDepth) : Type where
  | exceeded (failed :
      requiredGlobalPowerAt S profile stage m <
        actualGlobalProductAt B m)

/-- A proof-relevant decision of the literal global comparison, independent
of whether any exponent estimates have been supplied. -/
def selectedGlobalComparisonSearch
    (B : BufferedChainFamily outerDepth chainDepth)
    (S : FiniteScaleSequence delta outerDepth)
    (profile : Nat -> Real) (stage : Nat)
    (m : Fin outerDepth) :
    PLift (actualGlobalProductAt B m <=
      requiredGlobalPowerAt S profile stage m) ⊕
      SelectedGlobalComparisonFailure B S profile stage m := by
  by_cases ok : actualGlobalProductAt B m <=
      requiredGlobalPowerAt S profile stage m
  · exact Sum.inl ⟨ok⟩
  · exact Sum.inr (.exceeded (lt_of_not_ge ok))

/-- A strict literal failure rules out every selected paper-style exponent
certificate, not only the older equality-balanced allocation. -/
theorem no_selectedGlobalExponentEstimates_of_failure
    (B : BufferedChainFamily outerDepth chainDepth)
    (m : Fin outerDepth) (delta_pos : 0 < delta)
    (failed : requiredGlobalPowerAt S profile stage m <
      actualGlobalProductAt B m) :
    Not (Nonempty
      (SelectedGlobalExponentEstimates B S profile stage m)) := by
  rintro ⟨E⟩
  exact (not_le_of_gt failed)
    (actualGlobalProductAt_le_requiredGlobalPowerAt B m delta_pos E)

/-! ## Sharp non-automaticity under legal loss enlargement -/

/-- At positive chain depth and positive literal product, legal enlargement
of the dimensional envelope loss can exceed any finite target. -/
theorem exists_scaledFamily_target_lt_actualGlobalProductAt
    (B : BufferedChainFamily outerDepth chainDepth)
    (m : Fin outerDepth) (chainDepth_pos : 0 < chainDepth)
    (product_pos : 0 < actualGlobalProductAt B m)
    (target : ENNReal) (target_ne_top : target ≠ ∞) :
    ∃ (c : ENNReal) (one_le_c : (1 : ENNReal) <= c)
      (c_ne_top : c ≠ ∞),
      target < actualGlobalProductAt
        (scaleFamilyDimensionalLoss B c one_le_c c_ne_top) m := by
  have quotient_ne_top :
      target / actualGlobalProductAt B m ≠ ∞ :=
    ENNReal.div_ne_top target_ne_top product_pos.ne'
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt quotient_ne_top
  have n_pos : 0 < n := by
    have cast_pos : (0 : ENNReal) < (n : ENNReal) :=
      bot_le.trans_lt hn
    exact_mod_cast cast_pos
  have one_le_n : (1 : ENNReal) <= (n : ENNReal) := by
    exact_mod_cast n_pos
  have n_ne_top : (n : ENNReal) ≠ ∞ := ENNReal.natCast_ne_top n
  refine ⟨(n : ENNReal), one_le_n, n_ne_top, ?_⟩
  rw [actualGlobalProductAt_scaleFamilyDimensionalLoss]
  have linear_lt :
      target < (n : ENNReal) * actualGlobalProductAt B m :=
    (ENNReal.div_lt_iff (Or.inl product_pos.ne')
      (Or.inr target_ne_top)).1 hn
  have power_ge : (n : ENNReal) <= (n : ENNReal) ^ chainDepth := by
    calc
      (n : ENNReal) = (n : ENNReal) ^ 1 := by simp
      _ <= (n : ENNReal) ^ chainDepth :=
        pow_le_pow_right' one_le_n chainDepth_pos
  exact linear_lt.trans_le (by gcongr)

/-- In particular, the required profile power is finite when `delta > 0`, so
the same legal deformation can force the exact selected comparison to fail. -/
theorem exists_scaledFamily_requiredGlobalPower_lt_actualGlobalProductAt
    (B : BufferedChainFamily outerDepth chainDepth)
    (m : Fin outerDepth) (chainDepth_pos : 0 < chainDepth)
    (product_pos : 0 < actualGlobalProductAt B m)
    (delta_pos : 0 < delta) :
    ∃ (c : ENNReal) (one_le_c : (1 : ENNReal) <= c)
      (c_ne_top : c ≠ ∞),
      requiredGlobalPowerAt S profile stage m <
        actualGlobalProductAt
          (scaleFamilyDimensionalLoss B c one_le_c c_ne_top) m := by
  have theta_pos : 0 < S.theta m :=
    ScaleSequence.theta_pos_of_delta_pos S delta_pos m
  have target_ne_top :
      requiredGlobalPowerAt S profile stage m ≠ ∞ := by
    unfold requiredGlobalPowerAt
    exact ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.coe_ne_zero.mpr theta_pos.ne') ENNReal.coe_ne_top
  exact exists_scaledFamily_target_lt_actualGlobalProductAt B m
    chainDepth_pos product_pos
    (requiredGlobalPowerAt S profile stage m) target_ne_top

/-- The deformation therefore yields a legal buffered family for which no
selected exponent-estimate certificate exists. -/
theorem exists_scaledFamily_without_selectedGlobalExponentEstimates
    (B : BufferedChainFamily outerDepth chainDepth)
    (m : Fin outerDepth) (chainDepth_pos : 0 < chainDepth)
    (product_pos : 0 < actualGlobalProductAt B m)
    (delta_pos : 0 < delta) :
    ∃ (c : ENNReal) (one_le_c : (1 : ENNReal) <= c)
      (c_ne_top : c ≠ ∞),
      Not (Nonempty
        (SelectedGlobalExponentEstimates
          (scaleFamilyDimensionalLoss B c one_le_c c_ne_top)
          S profile stage m)) := by
  obtain ⟨c, one_le_c, c_ne_top, failed⟩ :=
    exists_scaledFamily_requiredGlobalPower_lt_actualGlobalProductAt
      B m chainDepth_pos product_pos delta_pos
  exact ⟨c, one_le_c, c_ne_top,
    no_selectedGlobalExponentEstimates_of_failure
      (scaleFamilyDimensionalLoss B c one_le_c c_ne_top)
      m delta_pos failed⟩

#print axioms actualGlobalProductAt_le_requiredGlobalPowerAt
#print axioms SelectedGlobalExponentEstimates.ofGlobalExponentAllocation
#print axioms SelectedGlobalExponentEstimates.ofExponentBudgetData
#print axioms firstNonLarge_actualGlobalProductAt_le_requiredGlobalPowerAt
#print axioms selectedGlobalComparisonSearch
#print axioms no_selectedGlobalExponentEstimates_of_failure
#print axioms exists_scaledFamily_target_lt_actualGlobalProductAt
#print axioms exists_scaledFamily_requiredGlobalPower_lt_actualGlobalProductAt
#print axioms exists_scaledFamily_without_selectedGlobalExponentEstimates

end
end FamilyStickyScaleChainSelectedGlobalExponentProducerV1
