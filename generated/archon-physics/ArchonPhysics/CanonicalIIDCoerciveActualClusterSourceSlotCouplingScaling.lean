import ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotClosure
import ArchonPhysics.CanonicalIIDCoerciveSourceSlotCouplingScalingExpectation

/-!
# Canonical iid full-cluster source with explicit coupling powers

The existing continuous-law cluster closure resolves the exact full source
into all left and right source slots.  The source-slot split resolves each
full slot into quadratic and quartic channels, while the expectation-level
coupling theorem factors those channels as

  (kappa * g) * unitQuadratic  and  (beta * g^2) * unitQuartic.

This module composes those three identities.  It also records the direct
finite-sum norm bound with the two coupling powers pulled outside explicit
sums of unit-slot norms.  Nothing here asserts decay, RPA, nonresonance,
Markov closure, or recollision suppression.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotCouplingScaling

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotClosure
open ArchonPhysics.CanonicalIIDCoerciveActualSourceSlotSplit
open ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSourceSlotCouplingScalingExpectation
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.RandomMassPositiveCollisionData

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Explicit finite sum of all left/right unit quadratic slot norms. -/
def canonicalClusterUnitQuadraticSourceSlotNormSum
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (time : Real) : Real :=
  (∑ slot ∈ left,
    ‖canonicalLeftUnitQuadraticSourceSlotFactorizationDefect (N := N)
      kappa beta g hbeta a entry left right slot time‖) +
  ∑ slot ∈ right,
    ‖canonicalRightUnitQuadraticSourceSlotFactorizationDefect (N := N)
      kappa beta g hbeta a entry left right slot time‖

/-- Explicit finite sum of all left/right unit quartic slot norms. -/
def canonicalClusterUnitQuarticSourceSlotNormSum
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (time : Real) : Real :=
  (∑ slot ∈ left,
    ‖canonicalLeftUnitQuarticSourceSlotFactorizationDefect (N := N)
      kappa beta g hbeta a entry left right slot time‖) +
  ∑ slot ∈ right,
    ‖canonicalRightUnitQuarticSourceSlotFactorizationDefect (N := N)
      kappa beta g hbeta a entry left right slot time‖

/-- Exact full-cluster source as the finite sum of all actual unit quadratic
and unit quartic left/right slot defects with their physical coupling
powers. -/
theorem canonicalCoerciveClusterFactorizationDefectSource_eq_coupling_unitSlotSums
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    {left right : Finset I} (hindex : Disjoint left right)
    (time : Real) :
    canonicalCoerciveClusterFactorizationDefectSource (N := N)
        kappa beta g hbeta a entry left right time =
      (∑ slot ∈ left,
        (((kappa * g : Real) : Complex) *
            canonicalLeftUnitQuadraticSourceSlotFactorizationDefect (N := N)
              kappa beta g hbeta a entry left right slot time +
          ((beta * g ^ 2 : Real) : Complex) *
            canonicalLeftUnitQuarticSourceSlotFactorizationDefect (N := N)
              kappa beta g hbeta a entry left right slot time)) +
      (∑ slot ∈ right,
        (((kappa * g : Real) : Complex) *
            canonicalRightUnitQuadraticSourceSlotFactorizationDefect (N := N)
              kappa beta g hbeta a entry left right slot time +
          ((beta * g ^ 2 : Real) : Complex) *
            canonicalRightUnitQuarticSourceSlotFactorizationDefect (N := N)
              kappa beta g hbeta a entry left right slot time)) := by
  rw [canonicalCoerciveClusterFactorizationDefectSource_eq_fullSlotSums
    hN ha0 ha1 kappa beta g hbeta entry hpositive hindex time]
  apply congrArg₂ (fun x y : Complex => x + y)
  · apply Finset.sum_congr rfl
    intro slot _hslot
    rw [canonicalLeftFullSourceSlotFactorizationDefect_eq_channels
      hN ha0 ha1 kappa beta g hbeta entry hpositive
        left right slot time,
      canonicalLeftQuadraticSourceSlotFactorizationDefect_eq_coupling_mul_unit,
      canonicalLeftQuarticSourceSlotFactorizationDefect_eq_coupling_mul_unit]
  · apply Finset.sum_congr rfl
    intro slot _hslot
    rw [canonicalRightFullSourceSlotFactorizationDefect_eq_channels
      hN ha0 ha1 kappa beta g hbeta entry hpositive
        left right slot time,
      canonicalRightQuadraticSourceSlotFactorizationDefect_eq_coupling_mul_unit,
      canonicalRightQuarticSourceSlotFactorizationDefect_eq_coupling_mul_unit]

/-- Direct finite-sum norm bound for the exact coupling-resolved cluster
source.  The unit-slot sums are not claimed to be small. -/
theorem norm_canonicalCoerciveClusterFactorizationDefectSource_le_coupling_unitSlotNormSums
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    {left right : Finset I} (hindex : Disjoint left right)
    (time : Real) :
    ‖canonicalCoerciveClusterFactorizationDefectSource (N := N)
        kappa beta g hbeta a entry left right time‖ ≤
      |kappa * g| *
          canonicalClusterUnitQuadraticSourceSlotNormSum (N := N)
            kappa beta g hbeta a entry left right time +
        |beta * g ^ 2| *
          canonicalClusterUnitQuarticSourceSlotNormSum (N := N)
            kappa beta g hbeta a entry left right time := by
  rw [canonicalCoerciveClusterFactorizationDefectSource_eq_coupling_unitSlotSums
    hN ha0 ha1 kappa beta g hbeta entry hpositive hindex time]
  calc
    ‖(∑ slot ∈ left,
          (((kappa * g : Real) : Complex) *
              canonicalLeftUnitQuadraticSourceSlotFactorizationDefect (N := N)
                kappa beta g hbeta a entry left right slot time +
            ((beta * g ^ 2 : Real) : Complex) *
              canonicalLeftUnitQuarticSourceSlotFactorizationDefect (N := N)
                kappa beta g hbeta a entry left right slot time)) +
        (∑ slot ∈ right,
          (((kappa * g : Real) : Complex) *
              canonicalRightUnitQuadraticSourceSlotFactorizationDefect (N := N)
                kappa beta g hbeta a entry left right slot time +
            ((beta * g ^ 2 : Real) : Complex) *
              canonicalRightUnitQuarticSourceSlotFactorizationDefect (N := N)
                kappa beta g hbeta a entry left right slot time))‖ ≤
      (∑ slot ∈ left,
        ‖((kappa * g : Real) : Complex) *
              canonicalLeftUnitQuadraticSourceSlotFactorizationDefect (N := N)
                kappa beta g hbeta a entry left right slot time +
            ((beta * g ^ 2 : Real) : Complex) *
              canonicalLeftUnitQuarticSourceSlotFactorizationDefect (N := N)
                kappa beta g hbeta a entry left right slot time‖) +
      ∑ slot ∈ right,
        ‖((kappa * g : Real) : Complex) *
              canonicalRightUnitQuadraticSourceSlotFactorizationDefect (N := N)
                kappa beta g hbeta a entry left right slot time +
            ((beta * g ^ 2 : Real) : Complex) *
              canonicalRightUnitQuarticSourceSlotFactorizationDefect (N := N)
                kappa beta g hbeta a entry left right slot time‖ := by
        exact (norm_add_le _ _).trans
          (add_le_add (norm_sum_le _ _) (norm_sum_le _ _))
    _ ≤
      (∑ slot ∈ left,
        (|kappa * g| *
            ‖canonicalLeftUnitQuadraticSourceSlotFactorizationDefect (N := N)
              kappa beta g hbeta a entry left right slot time‖ +
          |beta * g ^ 2| *
            ‖canonicalLeftUnitQuarticSourceSlotFactorizationDefect (N := N)
              kappa beta g hbeta a entry left right slot time‖)) +
      (∑ slot ∈ right,
        (|kappa * g| *
            ‖canonicalRightUnitQuadraticSourceSlotFactorizationDefect (N := N)
              kappa beta g hbeta a entry left right slot time‖ +
          |beta * g ^ 2| *
            ‖canonicalRightUnitQuarticSourceSlotFactorizationDefect (N := N)
              kappa beta g hbeta a entry left right slot time‖)) := by
        apply add_le_add <;> apply Finset.sum_le_sum
        · intro slot _hslot
          exact (norm_add_le _ _).trans_eq (by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul])
        · intro slot _hslot
          exact (norm_add_le _ _).trans_eq (by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul])
    _ = |kappa * g| *
          canonicalClusterUnitQuadraticSourceSlotNormSum (N := N)
            kappa beta g hbeta a entry left right time +
        |beta * g ^ 2| *
          canonicalClusterUnitQuarticSourceSlotNormSum (N := N)
            kappa beta g hbeta a entry left right time := by
      unfold canonicalClusterUnitQuadraticSourceSlotNormSum
        canonicalClusterUnitQuarticSourceSlotNormSum
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

end

end ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotCouplingScaling
