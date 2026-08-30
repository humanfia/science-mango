import ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotCouplingScaling

/-!
# Time-uniform deterministic frontier for canonical unit source slots

The continuous canonical expectation layer gives deterministic, all-time
bounds for every normalized quadratic and quartic source-slot defect.  This
module sums those bounds over both sides of a binary cluster split.  Thus the
actual unit-slot budgets have explicit finite envelopes uniformly on every
time interval, including the expanding kinetic interval.

These envelopes use absolute values before summation.  Consequently they do
not contain the oscillatory/garden cancellation needed for the sharper
quadratic `o(|g|)` and quartic `o(1)` estimates.  The latter cannot be inferred
from the bounds below or from a small-denominator probability estimate alone.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualUnitSlotCostFrontier

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotCouplingScaling
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualSourceSlotExpectation
open ArchonPhysics.CanonicalIIDCoercivePotentialChannelExpectation
open ArchonPhysics.CanonicalIIDCoerciveSourceSlotCouplingScalingExpectation
open ArchonPhysics.CanonicalIIDCoerciveSourceSlotExpectationClosure
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.RandomMassPositiveCollisionData

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Deterministic all-time cost for the complete normalized quadratic source
of one binary cluster split. -/
def canonicalClusterUnitQuadraticSourceSlotCost
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (left right : Finset I) : Real :=
  let A := canonicalSignedAmplitudeEnvelope N kappa beta g hbeta
  let B := canonicalWeightedCoordinateEnvelope N kappa beta g hbeta
  let S := canonicalSignedPotentialChannelSourceEnvelope N 1 0 1 B
  (∑ slot ∈ left,
    canonicalLeftSourceSlotDefectCost A S left right slot) +
  ∑ slot ∈ right,
    canonicalRightSourceSlotDefectCost A S left right slot

/-- Deterministic all-time cost for the complete normalized quartic source
of one binary cluster split. -/
def canonicalClusterUnitQuarticSourceSlotCost
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (left right : Finset I) : Real :=
  let A := canonicalSignedAmplitudeEnvelope N kappa beta g hbeta
  let B := canonicalWeightedCoordinateEnvelope N kappa beta g hbeta
  let S := canonicalSignedPotentialChannelSourceEnvelope N 0 1 1 B
  (∑ slot ∈ left,
    canonicalLeftSourceSlotDefectCost A S left right slot) +
  ∑ slot ∈ right,
    canonicalRightSourceSlotDefectCost A S left right slot

/-- The complete continuous canonical unit-quadratic source-slot norm sum is
bounded by an explicit cost independent of time. -/
theorem canonicalUnitQuadraticNormSum_le_cost
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (time : Real) :
    canonicalClusterUnitQuadraticSourceSlotNormSum (N := N)
        kappa beta g hbeta a entry left right time ≤
      canonicalClusterUnitQuadraticSourceSlotCost (N := N)
        kappa beta g hbeta left right := by
  unfold canonicalClusterUnitQuadraticSourceSlotNormSum
    canonicalClusterUnitQuadraticSourceSlotCost
  apply add_le_add
  · apply Finset.sum_le_sum
    intro slot _hslot
    unfold canonicalLeftUnitQuadraticSourceSlotFactorizationDefect
    exact norm_canonicalLeftPotentialSourceSlotFactorizationDefect_le_cost
      hN ha0 ha1 kappa beta g hbeta 1 0 1
        entry hpositive left right slot time
  · apply Finset.sum_le_sum
    intro slot _hslot
    unfold canonicalRightUnitQuadraticSourceSlotFactorizationDefect
    exact norm_canonicalRightPotentialSourceSlotFactorizationDefect_le_cost
      hN ha0 ha1 kappa beta g hbeta 1 0 1
        entry hpositive left right slot time

/-- The complete continuous canonical unit-quartic source-slot norm sum is
bounded by an explicit cost independent of time. -/
theorem canonicalUnitQuarticNormSum_le_cost
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (time : Real) :
    canonicalClusterUnitQuarticSourceSlotNormSum (N := N)
        kappa beta g hbeta a entry left right time ≤
      canonicalClusterUnitQuarticSourceSlotCost (N := N)
        kappa beta g hbeta left right := by
  unfold canonicalClusterUnitQuarticSourceSlotNormSum
    canonicalClusterUnitQuarticSourceSlotCost
  apply add_le_add
  · apply Finset.sum_le_sum
    intro slot _hslot
    unfold canonicalLeftUnitQuarticSourceSlotFactorizationDefect
    exact norm_canonicalLeftPotentialSourceSlotFactorizationDefect_le_cost
      hN ha0 ha1 kappa beta g hbeta 0 1 1
        entry hpositive left right slot time
  · apply Finset.sum_le_sum
    intro slot _hslot
    unfold canonicalRightUnitQuarticSourceSlotFactorizationDefect
    exact norm_canonicalRightPotentialSourceSlotFactorizationDefect_le_cost
      hN ha0 ha1 kappa beta g hbeta 0 1 1
        entry hpositive left right slot time

/-- The two explicit costs are genuine all-time budgets.  In particular the
same witnesses control every expanding kinetic interval. -/
theorem exists_timeUniform_canonicalUnitSlotBudgets
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) :
    ∃ quadraticBudget quarticBudget : Real,
      (∀ time,
        canonicalClusterUnitQuadraticSourceSlotNormSum (N := N)
            kappa beta g hbeta a entry left right time ≤ quadraticBudget) ∧
      (∀ time,
        canonicalClusterUnitQuarticSourceSlotNormSum (N := N)
            kappa beta g hbeta a entry left right time ≤ quarticBudget) := by
  refine ⟨canonicalClusterUnitQuadraticSourceSlotCost (N := N)
      kappa beta g hbeta left right,
    canonicalClusterUnitQuarticSourceSlotCost (N := N)
      kappa beta g hbeta left right, ?_, ?_⟩
  · intro time
    exact canonicalUnitQuadraticNormSum_le_cost
      hN ha0 ha1 kappa beta g hbeta entry hpositive left right time
  · intro time
    exact canonicalUnitQuarticNormSum_le_cost
      hN ha0 ha1 kappa beta g hbeta entry hpositive left right time

end

end ArchonPhysics.CanonicalIIDCoerciveActualUnitSlotCostFrontier
