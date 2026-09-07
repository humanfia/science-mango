import ArchonPhysics.FrozenUnitShellKineticClockCorrection
import ArchonPhysics.RandomMassPhaseInitialData

/-!
# Frozen v0.3 root clock audit

This module isolates the normalization arithmetic used by the frozen v0.3
thermalization root.

* The frozen target profile has total harmonic energy `1`.
* The Hamiltonian parameter `g` is the unit-shell parameter and the root
  observes the microscopic path at physical time `tau / g^2`.
* Reinterpreting the same unit-shell parameter at fixed energy density divides
  it by the square root of the count used to define density.  The corresponding
  kinetic clock is therefore multiplied by that count.

For density per physical site the count is `N`; for density per nontranslation
mode it is `N - 1`.  The frozen root itself uses physical-site density when it
speaks about density normalization, so its correction factor is `N`.

Only definitional unfolding and real-field algebra are used.  No dynamical or
thermalization claim is made.
-/

namespace ArchonPhysics.FrozenV03RootClockAudit

open ArchonPhysics
open ArchonPhysics.CanonicalFrozenClosedHittingRescaling
open ArchonPhysics.CanonicalRandomMassPhaseThermalizationObservable
open ArchonPhysics.DensityNormalizedFrozenRescaling
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPositiveCollisionData

noncomputable section

/-- The frozen target profile used by the root has total harmonic energy one. -/
theorem frozenTargetTotalHarmonicEnergy_eq_one
    {N : Nat} [NeZero N] (hN : 3 ≤ N) (a : Real) :
    (∑ k : OrderedModeIndex N, orderedTargetEnergy N a k) = 1 := by
  exact sum_orderedTargetEnergy_eq_one hN a

/-- In the frozen microscopic Hamiltonian, `g` multiplies the cubic term and
`g^2` multiplies the stabilizing quartic term. -/
theorem frozenRootPotential_couplingParameter
    (kappa beta g x : Real) :
    CoerciveCubicPotential.potential kappa beta g x =
      x ^ 2 / 2 + (kappa * g / 3) * x ^ 3 +
        (beta * g ^ 2 / 4) * x ^ 4 := by
  rfl

/-- The root's scaled microscopic observable is evaluated at physical time
`tau / g^2`, with the same `g` passed to the unit-shell Hamiltonian. -/
theorem rootScaledDistance_observationTime
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu : Real) (n : Nat) (g : Real)
    (omega : RandomEnsemble.SampleSpace) (tau : Real) :
    scaledDistance kappa beta hbeta mu n g omega tau =
      canonicalFrozenLateWindowL1Distance
        (N := n + 3) kappa beta g hbeta (1 / 4) mu
          (tau / g ^ 2) omega := by
  rfl

/-- Minimal clock-conversion identity.  If density is normalized by a positive
real count `M`, the fixed-density coupling is `g / sqrt M`, and its clock is
exactly `M` times the unit-shell clock. -/
theorem fixedDensityClock_eq_count_mul_unitShellClock
    (M g tau : Real) (hM : 0 < M) (hg : g ≠ 0) :
    tau / (g / Real.sqrt M) ^ 2 = M * (tau / g ^ 2) := by
  rw [div_pow, Real.sq_sqrt hM.le]
  field_simp [hM.ne', hg]

/-- With density defined per physical site, the frozen schedule has physical
site count `N = n + 3`, so the correction factor is `N`. -/
theorem frozenSchedule_siteDensityClock_eq_N_mul
    (n : Nat) (g tau : Real) (hg : g ≠ 0) :
    tau / (g / Real.sqrt (frozenSiteCountReal n)) ^ 2 =
      frozenSiteCountReal n * (tau / g ^ 2) := by
  exact fixedDensityClock_eq_count_mul_unitShellClock
    (frozenSiteCountReal n) g tau (frozenSiteCountReal_pos n) hg

/-- With density instead defined per nontranslation mode, the same algebra uses
the count `N - 1`; this is a different convention from per-site density. -/
theorem frozenSchedule_positiveModeDensityClock_eq_N_sub_one_mul
    (n : Nat) (g tau : Real) (hg : g ≠ 0) :
    tau /
        (g / Real.sqrt (((frozenSiteCount n - 1 : Nat) : Real))) ^ 2 =
      ((frozenSiteCount n - 1 : Nat) : Real) * (tau / g ^ 2) := by
  have hcount :
      0 < ((frozenSiteCount n - 1 : Nat) : Real) := by
    norm_num [frozenSiteCount]
    positivity
  exact fixedDensityClock_eq_count_mul_unitShellClock
    ((frozenSiteCount n - 1 : Nat) : Real) g tau hcount hg

end

end ArchonPhysics.FrozenV03RootClockAudit

open ArchonPhysics.FrozenV03RootClockAudit

#print axioms frozenTargetTotalHarmonicEnergy_eq_one
#print axioms frozenRootPotential_couplingParameter
#print axioms rootScaledDistance_observationTime
#print axioms fixedDensityClock_eq_count_mul_unitShellClock
#print axioms frozenSchedule_siteDensityClock_eq_N_mul
#print axioms frozenSchedule_positiveModeDensityClock_eq_N_sub_one_mul
