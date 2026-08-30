import ArchonPhysics.CanonicalIIDCoerciveBinaryHigherOrderKineticCriterion

/-!
# Continuous canonical binary subkinetic criterion

An all-time `O(1)` bound for the normalized quadratic and quartic source
slots is already enough to propagate binary factorization on time sequences
for which both `|g| |t|` and `|g|^2 |t|` vanish.  This is a genuine
Hamiltonian consequence of the exact source identity; it does not use a
Markov or RPA renewal assumption.

The result deliberately stops short of kinetic time `t ~ g^-2`.  Reaching
that scale requires the additional oscillatory/garden gains isolated by the
kinetic criterion.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveBinarySubkineticCriterion

open Filter Topology

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotCouplingScaling
open ArchonPhysics.CanonicalIIDCoerciveBinaryHigherOrderKineticCriterion
open ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.RandomMassPositiveCollisionData

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Algebraic subkinetic cancellation of the physical coupling factors. -/
theorem coupling_channel_tendsto_zero_of_subkinetic
    (kappa beta quadraticBudget quarticBudget : Real)
    (g time : Nat -> Real)
    (hquadraticTime : Tendsto
      (fun system => |g system| * |time system|) atTop (nhds 0))
    (hquarticTime : Tendsto
      (fun system => |g system| ^ 2 * |time system|) atTop (nhds 0)) :
    Tendsto (fun system =>
      (|kappa * g system| * quadraticBudget +
        |beta * (g system) ^ 2| * quarticBudget) * |time system|)
      atTop (nhds 0) := by
  have hquadratic : Tendsto (fun system =>
      (|kappa| * quadraticBudget) *
        (|g system| * |time system|)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hquadraticTime)
  have hquartic : Tendsto (fun system =>
      (|beta| * quarticBudget) *
        (|g system| ^ 2 * |time system|)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hquarticTime)
  have hsum : Tendsto (fun system =>
      (|kappa| * quadraticBudget) *
          (|g system| * |time system|) +
        (|beta| * quarticBudget) *
          (|g system| ^ 2 * |time system|)) atTop (nhds 0) := by
    simpa using hquadratic.add hquartic
  convert hsum using 1
  funext system
  rw [abs_mul, abs_mul, abs_pow]
  ring

/-- Uniform `O(1)` unit-slot budgets propagate binary factorization along
every subkinetic time sequence.  Initial factorization remains explicit so
that either the annealed charge selector or the quenched Haar theorem can
supply it in downstream modules. -/
theorem canonicalBinaryDefect_tendsto_zero_at_subkineticTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (kappa beta : Real) (g time : Nat -> Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    {left right : Finset I} (hindex : Disjoint left right)
    (hzero : forall system,
      canonicalCoerciveClusterFactorizationDefect (N := N)
        kappa beta (g system) hbeta a entry left right 0 = 0)
    (quadraticBudget quarticBudget : Real)
    (hquadratic : forall system s,
      s ∈ Set.uIcc 0 (time system) ->
        canonicalClusterUnitQuadraticSourceSlotNormSum (N := N)
          kappa beta (g system) hbeta a entry left right s <=
            quadraticBudget)
    (hquartic : forall system s,
      s ∈ Set.uIcc 0 (time system) ->
        canonicalClusterUnitQuarticSourceSlotNormSum (N := N)
          kappa beta (g system) hbeta a entry left right s <=
            quarticBudget)
    (hquadraticTime : Tendsto
      (fun system => |g system| * |time system|) atTop (nhds 0))
    (hquarticTime : Tendsto
      (fun system => |g system| ^ 2 * |time system|) atTop (nhds 0)) :
    Tendsto (fun system =>
      ‖canonicalCoerciveClusterFactorizationDefect (N := N)
        kappa beta (g system) hbeta a entry left right (time system)‖)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro system
    exact norm_nonneg _
  · intro system
    exact norm_canonicalCoerciveClusterFactorizationDefect_le_binary_channels
      hN ha0 ha1 kappa beta (g system) hbeta entry hpositive hindex
        (hzero system) (time system) quadraticBudget quarticBudget
        (hquadratic system) (hquartic system)
  · exact coupling_channel_tendsto_zero_of_subkinetic
      kappa beta quadraticBudget quarticBudget g time
        hquadraticTime hquarticTime

end

end ArchonPhysics.CanonicalIIDCoerciveBinarySubkineticCriterion
