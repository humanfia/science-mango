import FamilyStickyGrounding.FamilyStickyScaleChainConstantExponentLossEndpointV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainReservedExponentProfileV1

open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainConstantBearingStoppingEndpointV1
open FamilyStickyScaleChainConstantExponentLossEndpointV1

noncomputable section
set_option maxHeartbeats 3000000

/-!
# Reserving the exponent loss in the stopping profile

The constant-absorption adapter lowers the exponent only at the selected
stopping stage.  Its monotonicity seam asks that the adjacent profile gap pay
for `loss`.  That gap need not be supplied as an unrelated numerical fact:
starting with a monotone target profile, add `loss` from the intended stopping
stage onward.  The raised profile has the exact required gap, and lowering its
stopping entry recovers the original target exponent there.

The construction is explicit about its remaining cost.  A stopping theorem
run with the reserved profile needs the room
`eta stage + loss <= epsilon`, and absorbing the multiplicative constant still
needs the honest small-delta power budget from the preceding module.
-/

/-- Add the reserved loss at the stopping stage and every later stage. -/
def reserveTailLoss (eta : Nat -> Real) (stage : Nat) (loss : Real) :
    Nat -> Real :=
  fun j => eta j + if stage <= j then loss else 0

@[simp]
theorem reserveTailLoss_at
    (eta : Nat -> Real) (stage : Nat) (loss : Real) :
    reserveTailLoss eta stage loss stage = eta stage + loss := by
  simp [reserveTailLoss]

@[simp]
theorem reserveTailLoss_pred
    (eta : Nat -> Real) {stage : Nat} (stage_pos : 1 <= stage)
    (loss : Real) :
    reserveTailLoss eta stage loss (stage - 1) = eta (stage - 1) := by
  have hnot : ¬ (stage <= stage - 1) := by omega
  simp [reserveTailLoss, hnot]

/-- A nonnegative tail reserve preserves monotonicity of the original
profile. -/
theorem reserveTailLoss_monotone
    {eta : Nat -> Real} {stage : Nat} {loss : Real}
    (eta_monotone : Monotone eta) (loss_nonneg : 0 <= loss) :
    Monotone (reserveTailLoss eta stage loss) := by
  intro a b hab
  by_cases ha : stage <= a
  · have hb : stage <= b := ha.trans hab
    simp only [reserveTailLoss, if_pos ha, if_pos hb]
    simpa [add_comm] using add_le_add_right (eta_monotone hab) loss
  · by_cases hb : stage <= b
    · simp only [reserveTailLoss, if_neg ha, if_pos hb]
      exact add_le_add (eta_monotone hab) loss_nonneg
    · simp only [reserveTailLoss, if_neg ha, if_neg hb]
      simpa using eta_monotone hab

/-- The reserved profile automatically contains the precise adjacent gap
needed to lower the stopping exponent by `loss`. -/
theorem loss_le_reserveTailLoss_gap
    {eta : Nat -> Real} {stage : Nat} (stage_pos : 1 <= stage)
    {loss : Real} (eta_monotone : Monotone eta) :
    reserveTailLoss eta stage loss (stage - 1) + loss <=
      reserveTailLoss eta stage loss stage := by
  rw [reserveTailLoss_pred eta stage_pos loss, reserveTailLoss_at]
  have hpred : stage - 1 <= stage := Nat.sub_le stage 1
  linarith [eta_monotone hpred]

/-- The only upper-exponent cost of reserving the loss is visible at the
selected stage. -/
theorem reserveTailLoss_stage_le
    {eta : Nat -> Real} {stage : Nat} {loss epsilon : Real}
    (hroom : eta stage + loss <= epsilon) :
    reserveTailLoss eta stage loss stage <= epsilon := by
  simpa using hroom

/-- The literal profile returned by constant absorption. -/
def recoveredReservedProfile
    (eta : Nat -> Real) (stage : Nat) (loss : Real) : Nat -> Real :=
  lowerStoppingExponent (reserveTailLoss eta stage loss) stage loss

/-- At the selected stage the reserve and the paid loss cancel exactly. -/
@[simp]
theorem recoveredReservedProfile_at
    (eta : Nat -> Real) (stage : Nat) (loss : Real) :
    recoveredReservedProfile eta stage loss stage = eta stage := by
  simp [recoveredReservedProfile]

/-- The predecessor, used by the global and adjacent upper bounds, is also
the original target profile. -/
@[simp]
theorem recoveredReservedProfile_pred
    (eta : Nat -> Real) {stage : Nat} (stage_pos : 1 <= stage)
    (loss : Real) :
    recoveredReservedProfile eta stage loss (stage - 1) =
      eta (stage - 1) := by
  rw [recoveredReservedProfile,
    lowerStoppingExponent_pred (reserveTailLoss eta stage loss)
      stage_pos loss,
    reserveTailLoss_pred eta stage_pos loss]

/-- Reserving and then paying the loss leaves a monotone literal output
profile, without a caller-supplied adjacent-gap proof. -/
theorem recoveredReservedProfile_monotone
    {eta : Nat -> Real} {stage : Nat} (stage_pos : 1 <= stage)
    {loss : Real} (eta_monotone : Monotone eta)
    (loss_nonneg : 0 <= loss) :
    Monotone (recoveredReservedProfile eta stage loss) := by
  exact lowerStoppingExponent_monotone
    (reserveTailLoss eta stage loss) stage_pos loss_nonneg
      (reserveTailLoss_monotone eta_monotone loss_nonneg)
      (loss_le_reserveTailLoss_gap stage_pos eta_monotone)

variable {delta : NNReal} {N stage : Nat} {epsilon loss : Real}
  {eta : Nat -> Real} {K : ENNReal}

/-- End-to-end profile adapter.  A constant-bearing witness run with the
reserved profile and the honest small-delta budget produces a literal witness
whose stopping exponent is the original target value. -/
theorem exists_literalWitness_for_recoveredReservedProfile
    (W : KatzTaoConstantDividingWitness delta N epsilon
      (reserveTailLoss eta stage loss) K)
    (hstage : W.stage = stage)
    (delta_pos : 0 < delta) (tau_pos : 0 < W.tau)
    (B : SmallDeltaExponentLossBudget delta epsilon K loss) :
    Nonempty (KatzTaoDividingWitness delta N epsilon
      (recoveredReservedProfile eta stage loss)) := by
  let endpointBudget : EndpointScaleGapExponentLossBudget W loss :=
    B.toEndpointScaleGapExponentLossBudget delta_pos
  let bufferedBudget : BufferedExponentLossBudget W loss :=
    endpointBudget.toBufferedExponentLossBudget tau_pos
  let E :=
    FamilyStickyScaleChainConstantExponentLossEndpointV1.KatzTaoConstantDividingWitness.toExponentLossWitness
      W tau_pos loss bufferedBudget
  have hEstage : E.original.stage = stage := by
    change W.stage = stage
    exact hstage
  exact ⟨by
    simpa only [hEstage, recoveredReservedProfile] using
      FamilyStickyScaleChainConstantExponentLossEndpointV1.KatzTaoExponentLossDividingWitness.toLiteralDividingWitness E⟩

#print axioms reserveTailLoss_at
#print axioms reserveTailLoss_pred
#print axioms reserveTailLoss_monotone
#print axioms loss_le_reserveTailLoss_gap
#print axioms reserveTailLoss_stage_le
#print axioms recoveredReservedProfile_at
#print axioms recoveredReservedProfile_pred
#print axioms recoveredReservedProfile_monotone
#print axioms exists_literalWitness_for_recoveredReservedProfile

end
end FamilyStickyScaleChainReservedExponentProfileV1
