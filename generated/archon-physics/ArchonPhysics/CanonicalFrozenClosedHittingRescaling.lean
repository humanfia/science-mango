import ArchonPhysics.CanonicalFrozenClosedHittingAdapter
import ArchonPhysics.ClosedHittingTimeRescaling

/-!
# Canonical frozen closed hitting under kinetic rescaling

This module specializes exact `ENNReal` hitting-time rescaling to the frozen
quarter-profile random-mass lattice at the nondegenerate volumes `N = n + 3`.
It keeps two versions separate:

* the true positive-time closed hit, which has the physical semantics;
* the outer-rational representative, which is measurable everywhere and
  agrees almost surely with the true hit below the frozen `1 / 8` initial
  separation.

Consequently the measurable representative, after multiplication by `g²`,
agrees almost surely with the true hitting time of the distance path observed
at kinetic time `tau / g²`.
-/

namespace ArchonPhysics.CanonicalFrozenClosedHittingRescaling

open Filter MeasureTheory
open ArchonPhysics
open ArchonPhysics.CanonicalFrozenClosedHittingAdapter
open ArchonPhysics.CanonicalRandomMassPhaseThermalizationObservable
open ArchonPhysics.ThermalizationTransfer

noncomputable section

/-- The true closed-threshold equilibration-time family at physical volume
`n + 3`. -/
def closedEquilibrationTime
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (n : Nat) (g : Real)
    (omega : RandomEnsemble.SampleSpace) : ENNReal :=
  canonicalFrozenQuarterClosedHittingTime
    (N := n + 3) kappa beta g hbeta mu delta omega

/-- The everywhere-measurable outer-rational version of the same family. -/
def measurableClosedEquilibrationTime
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (n : Nat) (g : Real)
    (omega : RandomEnsemble.SampleSpace) : ENNReal :=
  canonicalFrozenQuarterOuterRationalClosedHittingTime
    (N := n + 3) kappa beta g hbeta mu delta omega

/-- The physical microscopic late-window distance observed in kinetic time.
-/
def scaledDistance
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu : Real) (n : Nat) (g : Real)
    (omega : RandomEnsemble.SampleSpace) (tau : Real) : Real :=
  canonicalFrozenLateWindowL1Distance
    (N := n + 3) kappa beta g hbeta (1 / 4) mu
      (tau / g ^ 2) omega

/-- The outer-rational representative is measurable for every finite model,
with no simple-spectrum premise exposed. -/
theorem measurable_measurableClosedEquilibrationTime
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (n : Nat) (g : Real) :
    Measurable
      (measurableClosedEquilibrationTime
        kappa beta hbeta mu delta n g) := by
  exact measurable_canonicalFrozenQuarterOuterRationalClosedHittingTime
    (N := n + 3) kappa beta g hbeta mu delta

/-- Below the frozen initial separation, the measurable family is almost
surely the true positive-time closed hit. -/
theorem measurableClosedEquilibrationTime_eq_closed_ae
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (hmu0 : 0 ≤ mu) (hmu1 : mu < 1)
    (hdelta : delta < 1 / 8) (n : Nat) (g : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      measurableClosedEquilibrationTime
          kappa beta hbeta mu delta n g omega =
        closedEquilibrationTime
          kappa beta hbeta mu delta n g omega := by
  simpa [measurableClosedEquilibrationTime, closedEquilibrationTime] using
    (canonicalFrozenQuarterOuterRationalClosedHittingTime_eq_closed_ae
      (N := n + 3) (by omega) kappa beta g hbeta mu delta
      hmu0 hmu1 hdelta)

/-- Pointwise exact scaling for the true closed hit.  The conclusion remains
valid when the unscaled hit is `⊤`. -/
theorem scaled_closedEquilibrationTime_eq_hittingTime
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (n : Nat) (g : Real) (hg : g ≠ 0)
    (omega : RandomEnsemble.SampleSpace) :
    scaledEquilibrationTime
        (closedEquilibrationTime kappa beta hbeta mu delta)
        n g omega =
      distanceThresholdHittingTime
        (scaledDistance kappa beta hbeta mu n g omega) delta := by
  apply scaledEquilibrationTime_eq_hittingTime_of_eq
    (distance := fun T => canonicalFrozenLateWindowL1Distance
      (N := n + 3) kappa beta g hbeta (1 / 4) mu T omega)
    (delta := delta) (hg := hg)
  rfl

/-- The everywhere-measurable representative has the same exact scaled
physical hitting semantics almost surely. -/
theorem scaled_measurableClosedEquilibrationTime_eq_hittingTime_ae
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (hmu0 : 0 ≤ mu) (hmu1 : mu < 1)
    (hdelta : delta < 1 / 8) (n : Nat) (g : Real) (hg : g ≠ 0) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      scaledEquilibrationTime
          (measurableClosedEquilibrationTime
            kappa beta hbeta mu delta)
          n g omega =
        distanceThresholdHittingTime
          (scaledDistance kappa beta hbeta mu n g omega) delta := by
  filter_upwards
    [measurableClosedEquilibrationTime_eq_closed_ae
      kappa beta hbeta mu delta hmu0 hmu1 hdelta n g] with omega heq
  unfold scaledEquilibrationTime
  rw [heq]
  exact distanceThresholdHittingTime_kineticScale
    (fun T => canonicalFrozenLateWindowL1Distance
      (N := n + 3) kappa beta g hbeta (1 / 4) mu T omega)
    delta g hg

end

end ArchonPhysics.CanonicalFrozenClosedHittingRescaling
