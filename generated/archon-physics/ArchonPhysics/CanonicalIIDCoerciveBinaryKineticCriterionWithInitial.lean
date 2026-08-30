import ArchonPhysics.CanonicalIIDCoerciveBinaryHigherOrderKineticCriterion
import ArchonPhysics.CanonicalIIDCoerciveClusterFactorizationPropagationWithInitial

/-!
# Continuous binary kinetic criterion with annealed initial covariance

This variant retains the exact time-zero factorization defect.  It is the
appropriate statement for an annealed random-mass law: Haar phases cancel
nonzero charge sectors exactly, while two charge-balanced blocks may share a
mass-dependent radial covariance.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveBinaryKineticCriterionWithInitial

open Filter Topology

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotCouplingScaling
open ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveClusterFactorizationPropagationWithInitial
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.RandomMassPositiveCollisionData

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Finite-time channel estimate retaining the exact initial defect. -/
theorem norm_canonicalCoerciveClusterFactorizationDefect_le_initial_add_binary_channels
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    {left right : Finset I} (hindex : Disjoint left right)
    (time quadraticBudget quarticBudget : Real)
    (hquadratic : ∀ s ∈ Set.uIcc 0 time,
      canonicalClusterUnitQuadraticSourceSlotNormSum (N := N)
        kappa beta g hbeta a entry left right s ≤ quadraticBudget)
    (hquartic : ∀ s ∈ Set.uIcc 0 time,
      canonicalClusterUnitQuarticSourceSlotNormSum (N := N)
        kappa beta g hbeta a entry left right s ≤ quarticBudget) :
    ‖canonicalCoerciveClusterFactorizationDefect (N := N)
      kappa beta g hbeta a entry left right time‖ ≤
        ‖canonicalCoerciveClusterFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right 0‖ +
        (|kappa * g| * quadraticBudget +
          |beta * g ^ 2| * quarticBudget) * |time| := by
  apply norm_canonicalCoerciveClusterFactorizationDefect_le_initial_add_source
    hN ha0 ha1 kappa beta g hbeta entry hpositive left right time
      (|kappa * g| * quadraticBudget +
        |beta * g ^ 2| * quarticBudget)
  intro s hs
  apply
    (norm_canonicalCoerciveClusterFactorizationDefectSource_le_coupling_unitSlotNormSums
      hN ha0 ha1 kappa beta g hbeta entry hpositive hindex s).trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left (hquadratic s hs) (abs_nonneg _))
    (mul_le_mul_of_nonneg_left (hquartic s hs) (abs_nonneg _))

/-- At kinetic time, decay of the exact initial annealed covariance and of
the coupling-weighted source budget jointly imply binary RPA convergence. -/
theorem canonicalBinaryDefect_tendsto_zero_at_kineticTime_of_initial_and_channels
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta tau : Real) (g : Nat → Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    {left right : Finset I} (hindex : Disjoint left right)
    (quadraticBudget quarticBudget : Nat → Real)
    (hquadratic : ∀ system, ∀ s ∈ Set.uIcc 0 (tau / (g system) ^ 2),
      canonicalClusterUnitQuadraticSourceSlotNormSum (N := N)
        kappa beta (g system) hbeta a entry left right s ≤
          quadraticBudget system)
    (hquartic : ∀ system, ∀ s ∈ Set.uIcc 0 (tau / (g system) ^ 2),
      canonicalClusterUnitQuarticSourceSlotNormSum (N := N)
        kappa beta (g system) hbeta a entry left right s ≤
          quarticBudget system)
    (hinitial : Tendsto (fun system =>
      ‖canonicalCoerciveClusterFactorizationDefect (N := N)
        kappa beta (g system) hbeta a entry left right 0‖)
      atTop (nhds 0))
    (hchannel : Tendsto (fun system =>
      (|kappa * g system| * quadraticBudget system +
        |beta * (g system) ^ 2| * quarticBudget system) *
          |tau / (g system) ^ 2|) atTop (nhds 0)) :
    Tendsto (fun system =>
      ‖canonicalCoerciveClusterFactorizationDefect (N := N)
        kappa beta (g system) hbeta a entry left right
          (tau / (g system) ^ 2)‖) atTop (nhds 0) := by
  apply squeeze_zero
  · intro system
    exact norm_nonneg _
  · intro system
    exact
      norm_canonicalCoerciveClusterFactorizationDefect_le_initial_add_binary_channels
        hN ha0 ha1 kappa beta (g system) hbeta entry hpositive hindex
          (tau / (g system) ^ 2)
          (quadraticBudget system) (quarticBudget system)
          (hquadratic system) (hquartic system)
  · simpa using hinitial.add hchannel

end

end ArchonPhysics.CanonicalIIDCoerciveBinaryKineticCriterionWithInitial
