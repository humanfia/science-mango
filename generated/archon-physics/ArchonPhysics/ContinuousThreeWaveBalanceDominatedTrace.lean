import ArchonPhysics.ContinuousThreeWaveBalanceAEBounded

/-!
# Continuous three-wave rigidity from a dominated planar trace

The rigidity argument only needs the child-frequency pair measure to have
full relative support on the additive triangle.  An explicit positive
Radon--Nikodym density is sufficient for this, but is stronger than needed.

This module records the weaker interface naturally produced by a lower
spectral-averaging estimate: Lebesgue measure on the additive triangle is
absolutely continuous with respect to the on-shell child-pair trace.  Thus no
density function has to be selected or identified.
-/

namespace ArchonPhysics.ContinuousThreeWaveBalanceDominatedTrace

open Set MeasureTheory
open ArchonPhysics.AdditiveTriangleMeasureSupport
open ArchonPhysics.ContinuousThreeWaveBalanceAEBounded
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- Reverse absolute continuity of the planar on-shell trace is enough for
continuous frequency-profile rigidity.  This is strictly weaker data than an
explicit a.e.-positive density identity. -/
theorem continuousFrequencyProfile_ae_proportional_of_dominated_volumeTrace
    (collision : ResonantThreeWaveMeasure Mode) {W : Real} (hW : 0 < W)
    (hfrequencyCollision :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        forall leg : Fin 3,
          collision.frequency (triad leg) ∈ Icc (0 : Real) W)
    (hfrequencyReference :
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        collision.frequency mode ∈ Icc (0 : Real) W)
    {profile : Real -> Real}
    (hprofile : ContinuousOn profile (Icc (0 : Real) W))
    (hbalance :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        profile (collision.frequency (triad 0)) =
          profile (collision.frequency (triad 1)) +
            profile (collision.frequency (triad 2)))
    (htrace : volume.restrict (additiveFrequencyTriangle W) ≪
      (childFrequencyPairMeasure collision).restrict
        (additiveFrequencyTriangle W)) :
    exists beta : Real,
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        profile (collision.frequency mode) =
          beta * collision.frequency mode := by
  apply continuousFrequencyProfile_ae_proportional_of_collision_ae_bounds
    collision hW hfrequencyCollision hfrequencyReference hprofile hbalance
  exact fullSupport_of_volume_absolutelyContinuous hW htrace

end

end ArchonPhysics.ContinuousThreeWaveBalanceDominatedTrace
