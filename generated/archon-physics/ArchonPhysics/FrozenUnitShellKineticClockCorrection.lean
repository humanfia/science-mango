import ArchonPhysics.DensityNormalizedFrozenRescalingV4

/-!
# Kinetic clock induced by the frozen unit-energy normalization

The frozen v0.3 state has total harmonic energy one, rather than fixed
positive energy density.  This file records the exact conversion between its
internal Hamiltonian parameter `g` and the public fixed-density coupling.
At `N` physical sites the latter is `g / sqrt N`; consequently its kinetic
clock is `N / g^2`, not `1 / g^2`.

Only algebra and the already verified density-normalization identity are used.
No dynamical persistence or thermalization statement is made.
-/

namespace ArchonPhysics.FrozenUnitShellKineticClockCorrection

open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassPhaseThermalizationObservable
open ArchonPhysics.DensityNormalizedFrozenRescaling

noncomputable section

local instance frozenSiteCount_neZero (n : Nat) :
    NeZero (frozenSiteCount n) :=
  ⟨by simp [frozenSiteCount]⟩

/-- Public fixed-density coupling represented by an internal unit-shell
Hamiltonian parameter `g`. -/
def unitShellDensityCoupling (n : Nat) (g : Real) : Real :=
  g / Real.sqrt (frozenSiteCountReal n)

/-- Converting the public coupling back to the internal parameter recovers
`g` exactly. -/
theorem volumeLiftedCoupling_unitShellDensityCoupling
    (n : Nat) (g : Real) :
    volumeLiftedCoupling n (unitShellDensityCoupling n g) = g := by
  unfold volumeLiftedCoupling unitShellDensityCoupling
  rw [mul_div_cancel₀ g
    (Real.sqrt_ne_zero'.2 (frozenSiteCountReal_pos n))]

/-- The square of the public coupling contains the inverse volume factor. -/
theorem unitShellDensityCoupling_sq (n : Nat) (g : Real) :
    unitShellDensityCoupling n g ^ 2 =
      g ^ 2 / frozenSiteCountReal n := by
  unfold unitShellDensityCoupling
  rw [div_pow, Real.sq_sqrt (frozenSiteCountReal_pos n).le]

/-- Exact kinetic-time conversion for a nonzero internal coupling. -/
theorem div_unitShellDensityCoupling_sq
    (n : Nat) (g tau : Real) (hg : g ≠ 0) :
    tau / unitShellDensityCoupling n g ^ 2 =
      frozenSiteCountReal n * tau / g ^ 2 := by
  rw [unitShellDensityCoupling_sq]
  field_simp [hg, (frozenSiteCountReal_pos n).ne']

/-- The density-normalized kinetic path represented on the unit shell uses
physical time `N * tau / g^2`.  This is the exact observable identity behind
the extra volume factor in the thermodynamic clock. -/
theorem densityNormalizedScaledDistance_unitShellDensityCoupling
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu : Real) (n : Nat) (g : Real) (hg : g ≠ 0)
    (omega : RandomEnsemble.SampleSpace) (tau : Real) :
    densityNormalizedScaledDistance kappa beta hbeta mu n
        (unitShellDensityCoupling n g) omega tau =
      canonicalFrozenLateWindowL1Distance
        (N := frozenSiteCount n) kappa beta g hbeta (1 / 4) mu
          (frozenSiteCountReal n * tau / g ^ 2) omega := by
  unfold densityNormalizedScaledDistance densityNormalizedDistance
  rw [volumeLiftedCoupling_unitShellDensityCoupling,
    div_unitShellDensityCoupling_sq n g tau hg]

end

end ArchonPhysics.FrozenUnitShellKineticClockCorrection

open ArchonPhysics.FrozenUnitShellKineticClockCorrection

#print axioms volumeLiftedCoupling_unitShellDensityCoupling
#print axioms unitShellDensityCoupling_sq
#print axioms div_unitShellDensityCoupling_sq
#print axioms densityNormalizedScaledDistance_unitShellDensityCoupling
