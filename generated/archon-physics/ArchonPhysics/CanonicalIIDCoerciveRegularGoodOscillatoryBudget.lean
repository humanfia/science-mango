import ArchonPhysics.CanonicalIIDCoerciveActualGardenHistoryDecomposition
import ArchonPhysics.FreeFPUTRegularArbitraryOrderOscillatoryHistory
import ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA

/-!
# Actual regular-good histories: oscillatory and coupling-power budget

This module connects the exact canonical four-sector history decomposition to
the proved arbitrary-order integration-by-parts estimate.  A single explicit
realization certificate says that every contribution labelled
`regularGoodGarden` is an actual ordered oscillatory integral, has a fixed
order, is fully nonresonant at gap `gamma`, and has the displayed microscopic
coupling power.  From that certificate we prove, rather than assume,

* the per-history bound
  `coefficient * |g|^power * (2 / gamma)^order`;
* the corresponding finite regular-sector budget, with an explicit history
  capacity;
* the quadratic and quartic square-cutoff garden envelopes; and
* decay of their coupling-weighted contribution at kinetic time
  `time = tau / g^2` for every fixed pair of orders.

For the square cutoff `gamma = |g|^2`, the sufficient powers are
`2 * order + 2` in the quadratic channel and `2 * order + 1` in the quartic
channel.  The realization certificate is deliberately the only
model-specific input: this file does not claim that the current microscopic
Hamiltonian expansion already supplies those extra powers.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveRegularGoodOscillatoryBudget

open scoped BigOperators

open Filter Topology
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualGardenHistoryDecomposition
open ArchonPhysics.FreeFPUTRegularArbitraryOrderOscillatoryHistory
open ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA

noncomputable section

variable {History I : Type*} [DecidableEq History] [DecidableEq I]
variable {left right : Finset I}
variable {leftDefect rightDefect : I -> Complex}

/-- Total number of history occurrences in the left and right finite slot
expansions.  This deliberately counts all histories, so it is a transparent
upper bound for the number of regular-good histories. -/
def clusterUnitSlotTotalHistoryCapacity
    (expansion : ClusterUnitSlotHistoryExpansion History I
      left right leftDefect rightDefect) : Nat :=
  (∑ slot ∈ left, (expansion.leftHistories slot).card) +
    ∑ slot ∈ right, (expansion.rightHistories slot).card

/-- The sole model-specific bridge needed below.  On every history actually
labelled regular-good, it identifies the contribution with an ordered
oscillatory integral and supplies the microscopic amplitude power.  The
remaining fields are checkable order, gap, positivity, and finite-capacity
certificates. -/
structure RegularGoodOscillatoryRealization
    (expansion : ClusterUnitSlotHistoryExpansion History I
      left right leftDefect rightDefect)
    (order couplingPower capacity : Nat)
    (coefficient g gamma time : Real) where
  coefficient_nonneg : 0 <= coefficient
  gap_pos : 0 < gamma
  capacity_bound : clusterUnitSlotTotalHistoryCapacity expansion <= capacity
  leftAmplitude : I -> History -> Complex
  rightAmplitude : I -> History -> Complex
  leftPhaseHistory : I -> History -> List Real
  rightPhaseHistory : I -> History -> List Real
  left_length : forall slot, slot ∈ left -> forall history,
    history ∈ expansion.leftHistories slot ->
      expansion.leftSector slot history = .regularGoodGarden ->
        (leftPhaseHistory slot history).length = order
  right_length : forall slot, slot ∈ right -> forall history,
    history ∈ expansion.rightHistories slot ->
      expansion.rightSector slot history = .regularGoodGarden ->
        (rightPhaseHistory slot history).length = order
  left_nonresonant : forall slot, slot ∈ left -> forall history,
    history ∈ expansion.leftHistories slot ->
      expansion.leftSector slot history = .regularGoodGarden ->
        FullyNonresonantOrderedHistory gamma
          (leftPhaseHistory slot history)
  right_nonresonant : forall slot, slot ∈ right -> forall history,
    history ∈ expansion.rightHistories slot ->
      expansion.rightSector slot history = .regularGoodGarden ->
        FullyNonresonantOrderedHistory gamma
          (rightPhaseHistory slot history)
  left_realizes : forall slot, slot ∈ left -> forall history,
    history ∈ expansion.leftHistories slot ->
      expansion.leftSector slot history = .regularGoodGarden ->
        expansion.leftContribution slot history =
          leftAmplitude slot history *
            linearOrderedOscillatoryIntegral
              (leftPhaseHistory slot history) time
  right_realizes : forall slot, slot ∈ right -> forall history,
    history ∈ expansion.rightHistories slot ->
      expansion.rightSector slot history = .regularGoodGarden ->
        expansion.rightContribution slot history =
          rightAmplitude slot history *
            linearOrderedOscillatoryIntegral
              (rightPhaseHistory slot history) time
  left_amplitude_bound : forall slot, slot ∈ left -> forall history,
    history ∈ expansion.leftHistories slot ->
      expansion.leftSector slot history = .regularGoodGarden ->
        ‖leftAmplitude slot history‖ <=
          coefficient * |g| ^ couplingPower
  right_amplitude_bound : forall slot, slot ∈ right -> forall history,
    history ∈ expansion.rightHistories slot ->
      expansion.rightSector slot history = .regularGoodGarden ->
        ‖rightAmplitude slot history‖ <=
          coefficient * |g| ^ couplingPower

/-- A finite sector budget is at most its total history count times any
uniform nonnegative per-history bound. -/
theorem finiteHistorySectorNormBudget_le_card_mul
    (histories : Finset History)
    (sector : History -> GardenHistorySector)
    (contribution : History -> Complex)
    (target : GardenHistorySector) {bound : Real}
    (hbound0 : 0 <= bound)
    (hbound : forall history, history ∈ histories ->
      sector history = target -> ‖contribution history‖ <= bound) :
    finiteHistorySectorNormBudget histories sector contribution target <=
      (histories.card : Real) * bound := by
  unfold finiteHistorySectorNormBudget
  calc
    (∑ history ∈ histories,
        if sector history = target then ‖contribution history‖ else 0) <=
        ∑ _history ∈ histories, bound := by
      apply Finset.sum_le_sum
      intro history hhistory
      split_ifs with hsector
      · exact hbound history hhistory hsector
      · exact hbound0
    _ = (histories.card : Real) * bound := by simp

/-- Every finite history-sector norm budget is nonnegative. -/
theorem finiteHistorySectorNormBudget_nonneg
    (histories : Finset History)
    (sector : History -> GardenHistorySector)
    (contribution : History -> Complex)
    (target : GardenHistorySector) :
    0 <= finiteHistorySectorNormBudget
      histories sector contribution target := by
  unfold finiteHistorySectorNormBudget
  positivity

/-- Consequently every left/right cluster sector budget is nonnegative. -/
theorem clusterUnitSlotHistorySectorNormBudget_nonneg
    (expansion : ClusterUnitSlotHistoryExpansion History I
      left right leftDefect rightDefect)
    (target : GardenHistorySector) :
    0 <= expansion.sectorNormBudget target := by
  unfold ClusterUnitSlotHistoryExpansion.sectorNormBudget
  exact add_nonneg
    (Finset.sum_nonneg (fun slot _hslot =>
      finiteHistorySectorNormBudget_nonneg
        (expansion.leftHistories slot) (expansion.leftSector slot)
          (expansion.leftContribution slot) target))
    (Finset.sum_nonneg (fun slot _hslot =>
      finiteHistorySectorNormBudget_nonneg
        (expansion.rightHistories slot) (expansion.rightSector slot)
          (expansion.rightContribution slot) target))

namespace RegularGoodOscillatoryRealization

variable {order couplingPower capacity : Nat}
variable {coefficient g gamma time : Real}
variable {expansion : ClusterUnitSlotHistoryExpansion History I
  left right leftDefect rightDefect}

/-- True arbitrary-order resolvent bound for one actual left regular-good
history.  It is uniform in the supplied time endpoint. -/
theorem norm_leftContribution_le_coupling_resolvent
    (realization : RegularGoodOscillatoryRealization expansion
      order couplingPower capacity coefficient g gamma time)
    {slot : I} (hslot : slot ∈ left) {history : History}
    (hhistory : history ∈ expansion.leftHistories slot)
    (hsector : expansion.leftSector slot history = .regularGoodGarden) :
    ‖expansion.leftContribution slot history‖ <=
      coefficient * |g| ^ couplingPower * (2 / gamma) ^ order := by
  rw [realization.left_realizes slot hslot history hhistory hsector,
    norm_mul]
  have hosc := norm_linearOrderedOscillatoryIntegral_le_resolvent
    realization.gap_pos
      (realization.left_nonresonant slot hslot history hhistory hsector) time
  calc
    ‖realization.leftAmplitude slot history‖ *
          ‖linearOrderedOscillatoryIntegral
            (realization.leftPhaseHistory slot history) time‖ <=
        (coefficient * |g| ^ couplingPower) *
          (2 / gamma) ^
            (realization.leftPhaseHistory slot history).length := by
      exact mul_le_mul
        (realization.left_amplitude_bound
          slot hslot history hhistory hsector)
        hosc (norm_nonneg _)
        (mul_nonneg realization.coefficient_nonneg
          (pow_nonneg (abs_nonneg g) couplingPower))
    _ = coefficient * |g| ^ couplingPower * (2 / gamma) ^ order := by
      rw [realization.left_length slot hslot history hhistory hsector]

/-- Right-slot version of the genuine arbitrary-order resolvent bound. -/
theorem norm_rightContribution_le_coupling_resolvent
    (realization : RegularGoodOscillatoryRealization expansion
      order couplingPower capacity coefficient g gamma time)
    {slot : I} (hslot : slot ∈ right) {history : History}
    (hhistory : history ∈ expansion.rightHistories slot)
    (hsector : expansion.rightSector slot history = .regularGoodGarden) :
    ‖expansion.rightContribution slot history‖ <=
      coefficient * |g| ^ couplingPower * (2 / gamma) ^ order := by
  rw [realization.right_realizes slot hslot history hhistory hsector,
    norm_mul]
  have hosc := norm_linearOrderedOscillatoryIntegral_le_resolvent
    realization.gap_pos
      (realization.right_nonresonant slot hslot history hhistory hsector) time
  calc
    ‖realization.rightAmplitude slot history‖ *
          ‖linearOrderedOscillatoryIntegral
            (realization.rightPhaseHistory slot history) time‖ <=
        (coefficient * |g| ^ couplingPower) *
          (2 / gamma) ^
            (realization.rightPhaseHistory slot history).length := by
      exact mul_le_mul
        (realization.right_amplitude_bound
          slot hslot history hhistory hsector)
        hosc (norm_nonneg _)
        (mul_nonneg realization.coefficient_nonneg
          (pow_nonneg (abs_nonneg g) couplingPower))
    _ = coefficient * |g| ^ couplingPower * (2 / gamma) ^ order := by
      rw [realization.right_length slot hslot history hhistory hsector]

/-- The complete actual regular-good sector is bounded by the explicit
coupling power, resolvent loss, and the certified finite history capacity. -/
theorem sectorNormBudget_le_coupling_resolvent
    (realization : RegularGoodOscillatoryRealization expansion
      order couplingPower capacity coefficient g gamma time) :
    expansion.sectorNormBudget .regularGoodGarden <=
      (capacity : Real) *
        (coefficient * |g| ^ couplingPower * (2 / gamma) ^ order) := by
  let bound : Real :=
    coefficient * |g| ^ couplingPower * (2 / gamma) ^ order
  have hbound0 : 0 <= bound := by
    dsimp [bound]
    exact mul_nonneg
      (mul_nonneg realization.coefficient_nonneg
        (pow_nonneg (abs_nonneg g) couplingPower))
      (pow_nonneg (le_of_lt (div_pos (by norm_num) realization.gap_pos)) order)
  have hraw : expansion.sectorNormBudget .regularGoodGarden <=
      (clusterUnitSlotTotalHistoryCapacity expansion : Real) * bound := by
    unfold ClusterUnitSlotHistoryExpansion.sectorNormBudget
    calc
      (∑ slot ∈ left,
          finiteHistorySectorNormBudget
            (expansion.leftHistories slot) (expansion.leftSector slot)
              (expansion.leftContribution slot) .regularGoodGarden) +
          ∑ slot ∈ right,
          finiteHistorySectorNormBudget
            (expansion.rightHistories slot) (expansion.rightSector slot)
              (expansion.rightContribution slot) .regularGoodGarden <=
        (∑ slot ∈ left,
            ((expansion.leftHistories slot).card : Real) * bound) +
          ∑ slot ∈ right,
            ((expansion.rightHistories slot).card : Real) * bound := by
        apply add_le_add <;> apply Finset.sum_le_sum
        · intro slot hslot
          exact finiteHistorySectorNormBudget_le_card_mul
            (expansion.leftHistories slot) (expansion.leftSector slot)
            (expansion.leftContribution slot) .regularGoodGarden hbound0
            (fun history hhistory hsector =>
              realization.norm_leftContribution_le_coupling_resolvent
                hslot hhistory hsector)
        · intro slot hslot
          exact finiteHistorySectorNormBudget_le_card_mul
            (expansion.rightHistories slot) (expansion.rightSector slot)
            (expansion.rightContribution slot) .regularGoodGarden hbound0
            (fun history hhistory hsector =>
              realization.norm_rightContribution_le_coupling_resolvent
                hslot hhistory hsector)
      _ = (clusterUnitSlotTotalHistoryCapacity expansion : Real) * bound := by
        unfold clusterUnitSlotTotalHistoryCapacity
        push_cast
        rw [add_mul, Finset.sum_mul, Finset.sum_mul]
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast realization.capacity_bound) hbound0)

/-- With the square cutoff, the quadratic microscopic power
`2 * order + 2` produces exactly the existing quadratic good-garden
envelope. -/
theorem sectorNormBudget_le_quadraticGardenGoodEnvelope
    (realization : RegularGoodOscillatoryRealization expansion
      order (2 * order + 2) capacity coefficient g
        (squareCouplingCutoff g) time) :
    expansion.sectorNormBudget .regularGoodGarden <=
      quadraticGardenGoodEnvelope order
        ((capacity : Real) * coefficient * (2 : Real) ^ order) g := by
  apply realization.sectorNormBudget_le_coupling_resolvent.trans_eq
  unfold quadraticGardenGoodEnvelope
  rw [div_pow]
  ring

/-- With the same square cutoff, the quartic microscopic power
`2 * order + 1` produces exactly the existing quartic good-garden envelope. -/
theorem sectorNormBudget_le_quarticGardenGoodEnvelope
    (realization : RegularGoodOscillatoryRealization expansion
      order (2 * order + 1) capacity coefficient g
        (squareCouplingCutoff g) time) :
    expansion.sectorNormBudget .regularGoodGarden <=
      quarticGardenGoodEnvelope order
        ((capacity : Real) * coefficient * (2 : Real) ^ order) g := by
  apply realization.sectorNormBudget_le_coupling_resolvent.trans_eq
  unfold quarticGardenGoodEnvelope
  rw [div_pow]
  ring

end RegularGoodOscillatoryRealization

/-! ## Fixed-order square-cutoff kinetic-time schedule -/

variable {QuadraticHistory QuarticHistory : Type*}
  [DecidableEq QuadraticHistory] [DecidableEq QuarticHistory]

/-- For any fixed quadratic and quartic history orders, actual regular-good
realizations with the displayed powers vanish after the physical outer
couplings and kinetic-time factor are applied.  No bad-denominator,
recollision, or truncation sector is included in this conclusion. -/
theorem regularGoodCouplingBudget_tendsto_zero_at_kineticTime_squareCutoff
    (quadraticLeft quadraticRight quarticLeft quarticRight :
      Nat -> I -> Complex)
    (quadraticExpansion : forall n,
      ClusterUnitSlotHistoryExpansion QuadraticHistory I left right
        (quadraticLeft n) (quadraticRight n))
    (quarticExpansion : forall n,
      ClusterUnitSlotHistoryExpansion QuarticHistory I left right
        (quarticLeft n) (quarticRight n))
    (quadraticOrder quarticOrder quadraticCapacity quarticCapacity : Nat)
    (quadraticCoefficient quarticCoefficient : Real)
    (g : Nat -> Real) (kappa beta tau : Real)
    (hquadraticRealization : forall n,
      RegularGoodOscillatoryRealization (quadraticExpansion n)
        quadraticOrder (2 * quadraticOrder + 2) quadraticCapacity
        quadraticCoefficient (g n) (squareCouplingCutoff (g n))
          (tau / (g n) ^ 2))
    (hquarticRealization : forall n,
      RegularGoodOscillatoryRealization (quarticExpansion n)
        quarticOrder (2 * quarticOrder + 1) quarticCapacity
        quarticCoefficient (g n) (squareCouplingCutoff (g n))
          (tau / (g n) ^ 2))
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : forall n, g n ≠ 0) :
    Tendsto (fun n =>
      (|kappa * g n| *
          (quadraticExpansion n).sectorNormBudget .regularGoodGarden +
        |beta * (g n) ^ 2| *
          (quarticExpansion n).sectorNormBudget .regularGoodGarden) *
        |tau / (g n) ^ 2|) atTop (nhds 0) := by
  let quadraticBudget : Nat -> Real := fun n =>
    (quadraticExpansion n).sectorNormBudget .regularGoodGarden
  let quarticBudget : Nat -> Real := fun n =>
    (quarticExpansion n).sectorNormBudget .regularGoodGarden
  have hlimit :=
    coupling_channel_budget_tendsto_zero_at_kineticTime_squareCutoff
      quadraticOrder quarticOrder g quadraticBudget quarticBudget
      (fun _n => 0) (fun _n => 0) kappa beta tau
      ((quadraticCapacity : Real) * quadraticCoefficient *
        (2 : Real) ^ quadraticOrder)
      ((quarticCapacity : Real) * quarticCoefficient *
        (2 : Real) ^ quarticOrder)
      0 0 0 0 hg hg0
      (fun n => clusterUnitSlotHistorySectorNormBudget_nonneg
        (quadraticExpansion n) .regularGoodGarden)
      (fun n => clusterUnitSlotHistorySectorNormBudget_nonneg
        (quarticExpansion n) .regularGoodGarden)
      (fun _n => le_rfl) (fun _n => le_rfl)
      (fun n => by
        simpa only [quadraticBudget, zero_mul, add_zero] using
          (hquadraticRealization n).sectorNormBudget_le_quadraticGardenGoodEnvelope)
      (fun n => by
        simpa only [quarticBudget, zero_mul, add_zero] using
          (hquarticRealization n).sectorNormBudget_le_quarticGardenGoodEnvelope)
      (fun _n => by simp [squareCouplingCutoff])
      (fun _n => by simp [squareCouplingCutoff])
  simpa only [quadraticBudget, quarticBudget] using hlimit

end

end ArchonPhysics.CanonicalIIDCoerciveRegularGoodOscillatoryBudget
