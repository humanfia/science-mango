import ArchonPhysics.BondPotentialHamiltonians
import ArchonPhysics.CanonicalFrozenClosedHittingRescaling

/-!
# Harmonic-density-normalized wrapper for the frozen unit-energy ensemble

The frozen canonical initial profile has total **harmonic** energy one.  For a
chain with `N` sites, the state with harmonic energy density one is therefore
obtained by multiplying the frozen state by `sqrt N`.  Under that amplitude
change, a public cubic density coupling `gamma` becomes the internal
unit-shell Hamiltonian parameter `sqrt N * gamma`; the quartic coefficient
changes by the corresponding square.

This module keeps those two parameters separate:

* `gamma` is the public harmonic-energy-density coupling and sets physical
  kinetic time `tau / gamma^2`;
* `volumeLiftedCoupling n gamma` is passed to the existing frozen Hamiltonian
  at the physical site count `n + 3`.

If energy density is instead defined using the full nonlinear Hamiltonian,
an additional unit-shell energy factor `h_N` must be retained through
`G^2 * h_N = N * gamma^2`; this file does not identify `h_N` with one.

Only exact rescaling and hitting-time identities are proved here.  No
microscopic-to-kinetic or thermalization claim is made.
-/

namespace ArchonPhysics.DensityNormalizedFrozenRescaling

open ArchonPhysics
open ArchonPhysics.BondPotentialHamiltonians
open ArchonPhysics.CanonicalFrozenClosedHittingAdapter
open ArchonPhysics.CanonicalFrozenClosedHittingRescaling
open ArchonPhysics.CanonicalRandomMassPhaseThermalizationObservable
open ArchonPhysics.HamiltonianScaling
open ArchonPhysics.ThermalizationTransfer
open Filter MeasureTheory

noncomputable section

/-- The physical site count used by the frozen closed-hitting API. -/
def frozenSiteCount (n : Nat) : Nat := n + 3

/-- The frozen site count is never zero. -/
local instance frozenSiteCount_neZero (n : Nat) :
    NeZero (frozenSiteCount n) :=
  ⟨by simp [frozenSiteCount]⟩

/-- The same site count as a real amplitude/energy scale. -/
def frozenSiteCountReal (n : Nat) : Real := (frozenSiteCount n : Real)

theorem frozenSiteCountReal_pos (n : Nat) :
    0 < frozenSiteCountReal n := by
  unfold frozenSiteCountReal frozenSiteCount
  positivity

/-- Convert the public harmonic-density coupling to the parameter of the
existing total-harmonic-energy-one Hamiltonian. -/
def volumeLiftedCoupling (n : Nat) (gamma : Real) : Real :=
  Real.sqrt (frozenSiteCountReal n) * gamma

theorem volumeLiftedCoupling_sq (n : Nat) (gamma : Real) :
    volumeLiftedCoupling n gamma ^ 2 =
      frozenSiteCountReal n * gamma ^ 2 := by
  unfold volumeLiftedCoupling
  rw [mul_pow, Real.sq_sqrt (frozenSiteCountReal_pos n).le]

theorem volumeLiftedCoupling_ne_zero (n : Nat) {gamma : Real}
    (hgamma : gamma ≠ 0) :
    volumeLiftedCoupling n gamma ≠ 0 := by
  exact mul_ne_zero
    (Real.sqrt_ne_zero'.2 (frozenSiteCountReal_pos n)) hgamma

/-- For the cubic harmonic-density coupling
`gamma = lambda * sqrt epsilon`, the internal parameter is exactly
`lambda * sqrt (N * epsilon)`. -/
theorem volumeLiftedCoupling_cubicDensityCoupling
    (n : Nat) (lambda epsilon : Real) :
    volumeLiftedCoupling n (lambda * Real.sqrt epsilon) =
      lambda * Real.sqrt (frozenSiteCountReal n * epsilon) := by
  unfold volumeLiftedCoupling
  rw [Real.sqrt_mul (frozenSiteCountReal_pos n).le]
  ring

/-- Exact Hamiltonian normalization at the frozen site count.

The left side has extensive harmonic energy after multiplying a unit-shell
state by `sqrt N` and uses the public density coupling `gamma`.  The right
side is `N` times the existing unit-shell Hamiltonian with internal parameter
`sqrt N * gamma`.
-/
theorem alphaBetaHamiltonian_densityNormalization
    (n : Nat)
    (m : Lattice.PositiveMassConfig (frozenSiteCount n))
    (kappa beta gamma : Real)
    (p q : Lattice.Configuration (frozenSiteCount n)) :
    alphaBetaHamiltonian m (kappa * gamma) (beta * gamma ^ 2)
        (rescaleConfiguration (frozenSiteCountReal n) p)
        (rescaleConfiguration (frozenSiteCountReal n) q) =
      frozenSiteCountReal n *
        CoerciveLatticeEnergy.hamiltonian m kappa beta
          (volumeLiftedCoupling n gamma) p q := by
  rw [alphaBetaHamiltonian_rescale m
    (kappa * gamma) (beta * gamma ^ 2)
    (frozenSiteCountReal_pos n).le p q]
  have hcubic :
      (kappa * gamma) * Real.sqrt (frozenSiteCountReal n) =
        kappa * volumeLiftedCoupling n gamma := by
    unfold volumeLiftedCoupling
    ring
  have hquartic :
      (beta * gamma ^ 2) * frozenSiteCountReal n =
        beta * volumeLiftedCoupling n gamma ^ 2 := by
    rw [volumeLiftedCoupling_sq]
    ring
  rw [hcubic, hquartic,
    alphaBetaHamiltonian_eq_coerciveLatticeEnergy]

/-- The unscaled frozen distance, with the volume-lifted parameter passed to
the actual Hamiltonian flow. -/
def densityNormalizedDistance
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu : Real) (n : Nat) (gamma : Real)
    (omega : RandomEnsemble.SampleSpace) (time : Real) : Real :=
  canonicalFrozenLateWindowL1Distance
    (N := frozenSiteCount n) kappa beta (volumeLiftedCoupling n gamma)
      hbeta (1 / 4) mu time omega

/-- The physical distance path on kinetic time.  The denominator is the
public density coupling `gamma^2`, not the squared internal lifted parameter.
-/
def densityNormalizedScaledDistance
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu : Real) (n : Nat) (gamma : Real)
    (omega : RandomEnsemble.SampleSpace) (tau : Real) : Real :=
  densityNormalizedDistance kappa beta hbeta mu n gamma omega
    (tau / gamma ^ 2)

/-- True closed-threshold equilibration time for the density-normalized
public coupling. -/
def densityNormalizedTeq
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (n : Nat) (gamma : Real)
    (omega : RandomEnsemble.SampleSpace) : ENNReal :=
  closedEquilibrationTime kappa beta hbeta mu delta n
    (volumeLiftedCoupling n gamma) omega

/-- Everywhere-measurable outer-rational representative of the same public
family. -/
def measurableDensityNormalizedTeq
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (n : Nat) (gamma : Real)
    (omega : RandomEnsemble.SampleSpace) : ENNReal :=
  measurableClosedEquilibrationTime kappa beta hbeta mu delta n
    (volumeLiftedCoupling n gamma) omega

theorem measurable_measurableDensityNormalizedTeq
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (n : Nat) (gamma : Real) :
    Measurable
      (measurableDensityNormalizedTeq
        kappa beta hbeta mu delta n gamma) := by
  exact measurable_measurableClosedEquilibrationTime
    kappa beta hbeta mu delta n (volumeLiftedCoupling n gamma)

/-- The true public `Teq` is the first closed hit of the volume-lifted
microscopic distance. -/
theorem densityNormalizedTeq_eq_distanceThresholdHittingTime
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (n : Nat) (gamma : Real)
    (omega : RandomEnsemble.SampleSpace) :
    densityNormalizedTeq kappa beta hbeta mu delta n gamma omega =
      distanceThresholdHittingTime
        (densityNormalizedDistance
          kappa beta hbeta mu n gamma omega) delta := by
  unfold densityNormalizedTeq densityNormalizedDistance
    closedEquilibrationTime canonicalFrozenQuarterClosedHittingTime
  rfl

/-- Exact public kinetic rescaling.  The Hamiltonian sees
`sqrt (n + 3) * gamma`, while physical time is observed at
`tau / gamma^2`. -/
theorem scaled_densityNormalizedTeq_eq_hittingTime
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (n : Nat) (gamma : Real) (hgamma : gamma ≠ 0)
    (omega : RandomEnsemble.SampleSpace) :
    scaledEquilibrationTime
        (densityNormalizedTeq kappa beta hbeta mu delta)
        n gamma omega =
      distanceThresholdHittingTime
        (densityNormalizedScaledDistance
          kappa beta hbeta mu n gamma omega) delta := by
  unfold scaledEquilibrationTime
  rw [densityNormalizedTeq_eq_distanceThresholdHittingTime]
  change
    ENNReal.ofReal (gamma ^ 2) *
        distanceThresholdHittingTime
          (densityNormalizedDistance
            kappa beta hbeta mu n gamma omega) delta =
      distanceThresholdHittingTime
        (fun tau => densityNormalizedDistance
          kappa beta hbeta mu n gamma omega (tau / gamma ^ 2)) delta
  exact distanceThresholdHittingTime_kineticScale
    (densityNormalizedDistance kappa beta hbeta mu n gamma omega)
    delta gamma hgamma

/-- The measurable representative agrees almost surely with the true public
closed hitting time below the same frozen initial separation. -/
theorem measurableDensityNormalizedTeq_eq_true_ae
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (hmu0 : 0 ≤ mu) (hmu1 : mu < 1)
    (hdelta : delta < 1 / 8) (n : Nat) (gamma : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      measurableDensityNormalizedTeq
          kappa beta hbeta mu delta n gamma omega =
        densityNormalizedTeq
          kappa beta hbeta mu delta n gamma omega := by
  exact measurableClosedEquilibrationTime_eq_closed_ae
    kappa beta hbeta mu delta hmu0 hmu1 hdelta n
      (volumeLiftedCoupling n gamma)

/-- Almost-sure exact scaled-hitting semantics for the everywhere-measurable
public representative. -/
theorem scaled_measurableDensityNormalizedTeq_eq_hittingTime_ae
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (hmu0 : 0 ≤ mu) (hmu1 : mu < 1)
    (hdelta : delta < 1 / 8) (n : Nat)
    (gamma : Real) (hgamma : gamma ≠ 0) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      scaledEquilibrationTime
          (measurableDensityNormalizedTeq
            kappa beta hbeta mu delta)
          n gamma omega =
        distanceThresholdHittingTime
          (densityNormalizedScaledDistance
            kappa beta hbeta mu n gamma omega) delta := by
  filter_upwards
    [measurableDensityNormalizedTeq_eq_true_ae
      kappa beta hbeta mu delta hmu0 hmu1 hdelta n gamma]
      with omega heq
  unfold scaledEquilibrationTime
  rw [heq, densityNormalizedTeq_eq_distanceThresholdHittingTime]
  change
    ENNReal.ofReal (gamma ^ 2) *
        distanceThresholdHittingTime
          (densityNormalizedDistance
            kappa beta hbeta mu n gamma omega) delta =
      distanceThresholdHittingTime
        (fun tau => densityNormalizedDistance
          kappa beta hbeta mu n gamma omega (tau / gamma ^ 2)) delta
  exact distanceThresholdHittingTime_kineticScale
    (densityNormalizedDistance kappa beta hbeta mu n gamma omega)
    delta gamma hgamma

end

end ArchonPhysics.DensityNormalizedFrozenRescaling
