import ArchonPhysics.AdditiveTriangleMeasureSupport

/-!
# Positive on-shell traces imply continuous three-wave balance rigidity

This module exposes the model-facing form of the support bridge.  A child-pair
trace with a Lebesgue-a.e. nonzero density on the additive triangle dominates
Lebesgue null sets, hence has full relative support.  The existing continuous
restricted-Cauchy theorem then classifies every continuous frequency-only
balanced profile.

For the canonical random lattice, the remaining model-specific input is now
an equality identifying the restricted child-pair measure with such a positive
on-shell density.  Merely knowing positive total collision mass is not enough
to inhabit this input.
-/

namespace ArchonPhysics.ContinuousThreeWaveBalanceVolumeTrace

open Set MeasureTheory
open ArchonPhysics.AdditiveTriangleMeasureSupport
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym

noncomputable section

/-- An a.e.-positive density on restricted planar Lebesgue measure gives the
reverse absolute-continuity direction needed for relative full support. -/
theorem fullSupport_of_restrict_eq_withDensity
    {W : Real} (hW : 0 < W) {pairMeasure : Measure (Real × Real)}
    {density : Real × Real -> ENNReal}
    (hdensity : AEMeasurable density
      (volume.restrict (additiveFrequencyTriangle W)))
    (hdensity_ne_zero :
      ∀ᵐ pair ∂volume.restrict (additiveFrequencyTriangle W),
        density pair ≠ 0)
    (hpair : pairMeasure.restrict (additiveFrequencyTriangle W) =
      (volume.restrict (additiveFrequencyTriangle W)).withDensity density) :
    additiveFrequencyTriangle W ⊆
      (pairMeasure.restrict (additiveFrequencyTriangle W)).support := by
  apply fullSupport_of_volume_absolutelyContinuous hW
  rw [hpair]
  exact withDensity_absolutelyContinuous' hdensity hdensity_ne_zero

variable {Mode : Type*} [MeasurableSpace Mode]

/-- A continuous frequency-only balanced profile is linear whenever the
collision child-pair trace has an a.e.-positive planar density on the entire
additive triangle. -/
theorem continuousFrequencyProfile_linear_of_positive_volumeTrace
    (collision : ResonantThreeWaveMeasure Mode) {W : Real} (hW : 0 < W)
    (hfrequency : forall mode,
      collision.frequency mode ∈ Icc (0 : Real) W)
    {profile : Real -> Real}
    (hprofile : ContinuousOn profile (Icc (0 : Real) W))
    (hbalance :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        profile (collision.frequency (triad 0)) =
          profile (collision.frequency (triad 1)) +
            profile (collision.frequency (triad 2)))
    {density : Real × Real -> ENNReal}
    (hdensity : AEMeasurable density
      (volume.restrict (additiveFrequencyTriangle W)))
    (hdensity_ne_zero :
      ∀ᵐ pair ∂volume.restrict (additiveFrequencyTriangle W),
        density pair ≠ 0)
    (hpair :
      (childFrequencyPairMeasure collision).restrict
          (additiveFrequencyTriangle W) =
        (volume.restrict (additiveFrequencyTriangle W)).withDensity density) :
    exists beta : Real,
      (forall omega, omega ∈ Icc (0 : Real) W ->
        profile omega = beta * omega) ∧
      (forall mode, profile (collision.frequency mode) =
        beta * collision.frequency mode) := by
  apply continuousFrequencyProfile_linear_of_collision_ae_balance
    collision hW hfrequency hprofile hbalance
  exact fullSupport_of_restrict_eq_withDensity hW hdensity
    hdensity_ne_zero hpair

/-- The same positive-trace input supplies the reference-measure a.e.
proportionality conclusion used by the entropy equality case, for continuous
frequency-only weights. -/
theorem continuousFrequencyProfile_ae_proportional_of_positive_volumeTrace
    (collision : ResonantThreeWaveMeasure Mode) {W : Real} (hW : 0 < W)
    (hfrequency : forall mode,
      collision.frequency mode ∈ Icc (0 : Real) W)
    {profile : Real -> Real}
    (hprofile : ContinuousOn profile (Icc (0 : Real) W))
    (hbalance :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        profile (collision.frequency (triad 0)) =
          profile (collision.frequency (triad 1)) +
            profile (collision.frequency (triad 2)))
    {density : Real × Real -> ENNReal}
    (hdensity : AEMeasurable density
      (volume.restrict (additiveFrequencyTriangle W)))
    (hdensity_ne_zero :
      ∀ᵐ pair ∂volume.restrict (additiveFrequencyTriangle W),
        density pair ≠ 0)
    (hpair :
      (childFrequencyPairMeasure collision).restrict
          (additiveFrequencyTriangle W) =
        (volume.restrict (additiveFrequencyTriangle W)).withDensity density) :
    exists beta : Real,
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        profile (collision.frequency mode) =
          beta * collision.frequency mode := by
  apply continuousFrequencyProfile_ae_proportional_of_collision_ae_balance
    collision hW hfrequency hprofile hbalance
  exact fullSupport_of_restrict_eq_withDensity hW hdensity
    hdensity_ne_zero hpair

end

end ArchonPhysics.ContinuousThreeWaveBalanceVolumeTrace
