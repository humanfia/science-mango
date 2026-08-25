import FamilyStickyGrounding.FamilyStickyScaleChainReservedExponentProfileV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 100000

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainConstantBearingStoppingEndpointV1
open FamilyStickyScaleChainConstantExponentLossEndpointV1
open FamilyStickyScaleChainReservedExponentProfileV1

noncomputable section

/-!
# Producing the small-delta exponent-loss budget

The preceding constant-absorption endpoint requires

`K <= delta ^ (-(epsilon ^ 2 * loss))`.

For finite `K` and a positive exponent this is not an additional analytic
input.  This file supplies the explicit threshold

`(K.toNNReal + 1) ^ (-(1 / exponent))`.

Every positive `delta` below that threshold absorbs `K`.  For the reserved
profile, half of the strict room between `eta stage` and `epsilon` is chosen
as the loss.  Thus both the small-delta budget and the upper-exponent room are
produced from primitive strict inequalities, and the result feeds directly
into the literal-witness endpoint.

The zero-exponent case is kept separate: there the power is exactly one, so
the budget exists exactly when `K <= 1`.  Making `delta` smaller cannot absorb
a larger constant in that case.
-/

/-! ## A finite constant is absorbed below an explicit threshold -/

/-- Explicit positive threshold for absorbing a finite `ENNReal` constant by
the negative `exponent` power of a small scale. -/
def finiteConstantSmallDeltaThreshold (K : ENNReal) (exponent : Real) : NNReal :=
  (K.toNNReal + 1) ^ (-(1 / exponent))

/-- The explicit threshold is positive, including in the degenerate
zero-exponent convention. -/
theorem finiteConstantSmallDeltaThreshold_pos
    (K : ENNReal) (exponent : Real) :
    0 < finiteConstantSmallDeltaThreshold K exponent := by
  apply NNReal.rpow_pos
  positivity

/-- For a positive exponent the explicit threshold lies in the usual
small-scale interval `(0, 1]`. -/
theorem finiteConstantSmallDeltaThreshold_le_one
    (K : ENNReal) {exponent : Real} (hexponent : 0 < exponent) :
    finiteConstantSmallDeltaThreshold K exponent <= 1 := by
  apply NNReal.rpow_le_one_of_one_le_of_nonpos
  · exact le_add_of_nonneg_left (bot_le : (0 : NNReal) <= K.toNNReal)
  · have hinv : 0 < 1 / exponent := one_div_pos.mpr hexponent
    linarith

/-- Raising the threshold back to the negative exponent recovers the padded
finite constant exactly. -/
theorem finiteConstantSmallDeltaThreshold_rpow
    (K : ENNReal) {exponent : Real} (hexponent : 0 < exponent) :
    (finiteConstantSmallDeltaThreshold K exponent) ^ (-exponent) =
      K.toNNReal + 1 := by
  have hmul : (-(1 / exponent)) * (-exponent) = (1 : Real) := by
    field_simp [ne_of_gt hexponent]
  calc
    (finiteConstantSmallDeltaThreshold K exponent) ^ (-exponent) =
        ((K.toNNReal + 1) ^ (-(1 / exponent))) ^ (-exponent) := by
          rfl
    _ = (K.toNNReal + 1) ^ ((-(1 / exponent)) * (-exponent)) := by
      rw [NNReal.rpow_mul]
    _ = K.toNNReal + 1 := by rw [hmul, NNReal.rpow_one]

/-- The numerical absorption lemma.  Finiteness is used only to identify `K`
with the coercion of `K.toNNReal`; positivity of the exponent is precisely
what makes a small-scale threshold possible for arbitrary finite `K`. -/
theorem finiteConstant_le_delta_negativePower
    {delta : NNReal} {K : ENNReal} {exponent : Real}
    (K_ne_top : K ≠ ∞)
    (exponent_pos : 0 < exponent)
    (delta_pos : 0 < delta)
    (delta_le : delta <= finiteConstantSmallDeltaThreshold K exponent) :
    K <= (delta : ENNReal) ^ (-exponent) := by
  have hthreshold : K.toNNReal + 1 <= delta ^ (-exponent) := by
    calc
      K.toNNReal + 1 =
          (finiteConstantSmallDeltaThreshold K exponent) ^ (-exponent) :=
        (finiteConstantSmallDeltaThreshold_rpow K exponent_pos).symm
      _ <= delta ^ (-exponent) :=
        NNReal.rpow_le_rpow_of_nonpos delta_pos delta_le
          (neg_nonpos.mpr exponent_pos.le)
  have hfinite : K.toNNReal <= delta ^ (-exponent) :=
    (le_add_right (le_refl K.toNNReal)).trans hthreshold
  rw [<- ENNReal.coe_toNNReal K_ne_top,
    <- ENNReal.coe_rpow_of_ne_zero (ne_of_gt delta_pos) (-exponent)]
  exact ENNReal.coe_le_coe.mpr hfinite

/-! ## The actual `epsilon ^ 2 * loss` budget -/

/-- The explicit threshold specialized to the exponent used by
`SmallDeltaExponentLossBudget`. -/
def smallDeltaExponentLossThreshold
    (K : ENNReal) (epsilon loss : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold K (epsilon ^ 2 * loss)

theorem smallDeltaExponentLossThreshold_pos
    (K : ENNReal) (epsilon loss : Real) :
    0 < smallDeltaExponentLossThreshold K epsilon loss :=
  finiteConstantSmallDeltaThreshold_pos K (epsilon ^ 2 * loss)

/-- Positive `epsilon` and positive loss put the specialized threshold in
`(0, 1]`. -/
theorem smallDeltaExponentLossThreshold_le_one
    (K : ENNReal) {epsilon loss : Real}
    (epsilon_pos : 0 < epsilon) (loss_pos : 0 < loss) :
    smallDeltaExponentLossThreshold K epsilon loss <= 1 := by
  exact finiteConstantSmallDeltaThreshold_le_one K (by positivity)

/-- Below the explicit threshold, finite `K` automatically gives the exact
small-delta budget required by the constant-absorption endpoint. -/
theorem smallDeltaExponentLossBudget_of_le_threshold
    {delta : NNReal} {epsilon loss : Real} {K : ENNReal}
    (K_ne_top : K ≠ ∞)
    (epsilon_pos : 0 < epsilon) (loss_pos : 0 < loss)
    (delta_pos : 0 < delta)
    (delta_le : delta <= smallDeltaExponentLossThreshold K epsilon loss) :
    SmallDeltaExponentLossBudget delta epsilon K loss where
  epsilon_nonneg := epsilon_pos.le
  loss_nonneg := loss_pos.le
  constant_le_delta_power := by
    exact finiteConstant_le_delta_negativePower K_ne_top (by positivity)
      delta_pos delta_le

/-- Existential sufficiently-small form of the explicit producer. -/
theorem exists_threshold_for_smallDeltaExponentLossBudget
    {epsilon loss : Real} {K : ENNReal}
    (K_ne_top : K ≠ ∞)
    (epsilon_pos : 0 < epsilon) (loss_pos : 0 < loss) :
    exists delta0 : NNReal,
      0 < delta0 /\ delta0 <= 1 /\
      forall delta : NNReal, 0 < delta -> delta <= delta0 ->
        SmallDeltaExponentLossBudget delta epsilon K loss := by
  refine ⟨smallDeltaExponentLossThreshold K epsilon loss,
    smallDeltaExponentLossThreshold_pos K epsilon loss,
    smallDeltaExponentLossThreshold_le_one K epsilon_pos loss_pos, ?_⟩
  intro delta delta_pos delta_le
  exact smallDeltaExponentLossBudget_of_le_threshold K_ne_top epsilon_pos
    loss_pos delta_pos delta_le

/-! ## An automatic positive loss inside the reserved-profile room -/

/-- Spend exactly half of the available strict exponent room. -/
def halfReservedExponentRoom
    (eta : Nat -> Real) (stage : Nat) (epsilon : Real) : Real :=
  (epsilon - eta stage) / 2

/-- Strict room produces a genuinely positive loss. -/
theorem halfReservedExponentRoom_pos
    {eta : Nat -> Real} {stage : Nat} {epsilon : Real}
    (strict_room : eta stage < epsilon) :
    0 < halfReservedExponentRoom eta stage epsilon := by
  rw [halfReservedExponentRoom]
  linarith

/-- The half-room choice automatically satisfies the exact upper-exponent
inequality required to run the reserved stopping profile. -/
theorem eta_add_halfReservedExponentRoom_le
    {eta : Nat -> Real} {stage : Nat} {epsilon : Real}
    (strict_room : eta stage < epsilon) :
    eta stage + halfReservedExponentRoom eta stage epsilon <= epsilon := by
  rw [halfReservedExponentRoom]
  linarith

/-- Strict room is not an artifact of the half-room choice: it is equivalent
to the existence of any positive loss satisfying the target room inequality. -/
theorem exists_positive_loss_with_room_iff
    {eta : Nat -> Real} {stage : Nat} {epsilon : Real} :
    (exists loss : Real, 0 < loss /\ eta stage + loss <= epsilon) <->
      eta stage < epsilon := by
  constructor
  · rintro ⟨loss, loss_pos, room⟩
    linarith
  · intro strict_room
    exact ⟨halfReservedExponentRoom eta stage epsilon,
      halfReservedExponentRoom_pos strict_room,
      eta_add_halfReservedExponentRoom_le strict_room⟩

/-! ## Combined reserved-profile producer and literal endpoint -/

/-- Threshold obtained after fixing the canonical half-room loss. -/
def recoveredReservedProfileSmallDeltaThreshold
    (eta : Nat -> Real) (stage : Nat) (epsilon : Real) (K : ENNReal) : NNReal :=
  smallDeltaExponentLossThreshold K epsilon
    (halfReservedExponentRoom eta stage epsilon)

theorem recoveredReservedProfileSmallDeltaThreshold_pos
    (eta : Nat -> Real) (stage : Nat) (epsilon : Real) (K : ENNReal) :
    0 < recoveredReservedProfileSmallDeltaThreshold eta stage epsilon K :=
  smallDeltaExponentLossThreshold_pos K epsilon
    (halfReservedExponentRoom eta stage epsilon)

theorem recoveredReservedProfileSmallDeltaThreshold_le_one
    {eta : Nat -> Real} {stage : Nat} {epsilon : Real} (K : ENNReal)
    (epsilon_pos : 0 < epsilon) (strict_room : eta stage < epsilon) :
    recoveredReservedProfileSmallDeltaThreshold eta stage epsilon K <= 1 := by
  exact smallDeltaExponentLossThreshold_le_one K epsilon_pos
    (halfReservedExponentRoom_pos strict_room)

/-- The canonical loss simultaneously has room and carries the exact
small-delta budget. -/
theorem room_and_budget_of_le_recoveredThreshold
    {delta : NNReal} {eta : Nat -> Real} {stage : Nat}
    {epsilon : Real} {K : ENNReal}
    (K_ne_top : K ≠ ∞)
    (epsilon_pos : 0 < epsilon) (strict_room : eta stage < epsilon)
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      recoveredReservedProfileSmallDeltaThreshold eta stage epsilon K) :
    eta stage + halfReservedExponentRoom eta stage epsilon <= epsilon /\
      SmallDeltaExponentLossBudget delta epsilon K
        (halfReservedExponentRoom eta stage epsilon) := by
  exact ⟨eta_add_halfReservedExponentRoom_le strict_room,
    smallDeltaExponentLossBudget_of_le_threshold K_ne_top epsilon_pos
      (halfReservedExponentRoom_pos strict_room) delta_pos delta_le⟩

/-- Existential loss form: no loss or target room inequality is supplied by
the caller.  The producer chooses the loss and proves both facts. -/
theorem exists_loss_with_room_and_budget_of_le_recoveredThreshold
    {delta : NNReal} {eta : Nat -> Real} {stage : Nat}
    {epsilon : Real} {K : ENNReal}
    (K_ne_top : K ≠ ∞)
    (epsilon_pos : 0 < epsilon) (strict_room : eta stage < epsilon)
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      recoveredReservedProfileSmallDeltaThreshold eta stage epsilon K) :
    exists loss : Real, 0 < loss /\ eta stage + loss <= epsilon /\
      SmallDeltaExponentLossBudget delta epsilon K loss := by
  let loss := halfReservedExponentRoom eta stage epsilon
  have combined := room_and_budget_of_le_recoveredThreshold K_ne_top
    epsilon_pos strict_room delta_pos delta_le
  exact ⟨loss, halfReservedExponentRoom_pos strict_room,
    combined.1, combined.2⟩

variable {delta : NNReal} {N stage : Nat} {epsilon : Real}
  {eta : Nat -> Real} {K : ENNReal}

/-- End-to-end endpoint.  A reserved-profile constant-bearing witness, a
finite constant, strict exponent room, and the explicit smallness check yield
the literal recovered-profile witness with no separately supplied loss budget
or room inequality. -/
theorem exists_literalWitness_for_halfRoomRecoveredProfile
    (W : KatzTaoConstantDividingWitness delta N epsilon
      (reserveTailLoss eta stage
        (halfReservedExponentRoom eta stage epsilon)) K)
    (W_stage : W.stage = stage)
    (K_ne_top : K ≠ ∞)
    (epsilon_pos : 0 < epsilon) (strict_room : eta stage < epsilon)
    (delta_pos : 0 < delta) (tau_pos : 0 < W.tau)
    (delta_le : delta <=
      recoveredReservedProfileSmallDeltaThreshold eta stage epsilon K) :
    Nonempty (KatzTaoDividingWitness delta N epsilon
      (recoveredReservedProfile eta stage
        (halfReservedExponentRoom eta stage epsilon))) := by
  have budget : SmallDeltaExponentLossBudget delta epsilon K
      (halfReservedExponentRoom eta stage epsilon) :=
    (room_and_budget_of_le_recoveredThreshold K_ne_top epsilon_pos
      strict_room delta_pos delta_le).2
  exact exists_literalWitness_for_recoveredReservedProfile W W_stage
    delta_pos tau_pos budget

/-- The same end-to-end call also returns the room inequality used by the
reserved input profile, rather than leaving that fact disconnected from the
literal witness. -/
theorem room_and_exists_literalWitness_for_halfRoomRecoveredProfile
    (W : KatzTaoConstantDividingWitness delta N epsilon
      (reserveTailLoss eta stage
        (halfReservedExponentRoom eta stage epsilon)) K)
    (W_stage : W.stage = stage)
    (K_ne_top : K ≠ ∞)
    (epsilon_pos : 0 < epsilon) (strict_room : eta stage < epsilon)
    (delta_pos : 0 < delta) (tau_pos : 0 < W.tau)
    (delta_le : delta <=
      recoveredReservedProfileSmallDeltaThreshold eta stage epsilon K) :
    eta stage + halfReservedExponentRoom eta stage epsilon <= epsilon /\
      Nonempty (KatzTaoDividingWitness delta N epsilon
        (recoveredReservedProfile eta stage
          (halfReservedExponentRoom eta stage epsilon))) := by
  exact ⟨eta_add_halfReservedExponentRoom_le strict_room,
    exists_literalWitness_for_halfRoomRecoveredProfile W W_stage K_ne_top
      epsilon_pos strict_room delta_pos tau_pos delta_le⟩

/-! ## Sharp zero-exponent obstruction -/

/-- When the exponent is zero, the small-delta condition is exactly `K <= 1`.
This identifies the genuine obstruction rather than hiding it in a smallness
premise. -/
theorem smallDeltaExponentLossBudget_zeroExponent_iff
    {delta : NNReal} {epsilon loss : Real} {K : ENNReal}
    (epsilon_nonneg : 0 <= epsilon) (loss_nonneg : 0 <= loss)
    (exponent_zero : epsilon ^ 2 * loss = 0) :
    SmallDeltaExponentLossBudget delta epsilon K loss <-> K <= 1 := by
  constructor
  · intro budget
    calc
      K <= (delta : ENNReal) ^ (-(epsilon ^ 2 * loss)) :=
        budget.constant_le_delta_power
      _ = 1 := by simp [exponent_zero]
  · intro K_le_one
    exact
      { epsilon_nonneg := epsilon_nonneg
        loss_nonneg := loss_nonneg
        constant_le_delta_power := by simpa [exponent_zero] using K_le_one }

/-- Consequently a constant strictly larger than one can never be absorbed
at zero exponent, at any scale. -/
theorem no_smallDeltaExponentLossBudget_of_zeroExponent
    {delta : NNReal} {epsilon loss : Real} {K : ENNReal}
    (K_gt_one : 1 < K) (exponent_zero : epsilon ^ 2 * loss = 0) :
    Not (SmallDeltaExponentLossBudget delta epsilon K loss) := by
  intro budget
  have K_le_one : K <= 1 := by
    calc
      K <= (delta : ENNReal) ^ (-(epsilon ^ 2 * loss)) :=
        budget.constant_le_delta_power
      _ = 1 := by simp [exponent_zero]
  exact (not_le_of_gt K_gt_one) K_le_one

#print axioms finiteConstantSmallDeltaThreshold_pos
#print axioms finiteConstantSmallDeltaThreshold_le_one
#print axioms finiteConstantSmallDeltaThreshold_rpow
#print axioms finiteConstant_le_delta_negativePower
#print axioms smallDeltaExponentLossBudget_of_le_threshold
#print axioms exists_threshold_for_smallDeltaExponentLossBudget
#print axioms exists_positive_loss_with_room_iff
#print axioms room_and_budget_of_le_recoveredThreshold
#print axioms exists_loss_with_room_and_budget_of_le_recoveredThreshold
#print axioms exists_literalWitness_for_halfRoomRecoveredProfile
#print axioms room_and_exists_literalWitness_for_halfRoomRecoveredProfile
#print axioms smallDeltaExponentLossBudget_zeroExponent_iff
#print axioms no_smallDeltaExponentLossBudget_of_zeroExponent

end
end FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
