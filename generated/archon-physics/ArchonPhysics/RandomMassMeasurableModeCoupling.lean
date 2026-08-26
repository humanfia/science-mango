import ArchonPhysics.MeasurableOrderedModeCoupling
import ArchonPhysics.RandomMassOrderedProjectorBridge

/-!
# Measurable ordered interaction weights for iid random masses

This module combines the globally measurable projector formula for a squared
mode coupling with the almost-sure simplicity theorem for iid positive masses.
The resulting random variable is defined and measurable on the whole sample
space.  Almost surely it equals the physical normalized vertex square formed
from Mathlib's normal-mode eigenbasis.

No empirical-measure convergence, resonance-density limit, or nonzero lower
bound for an individual coupling is asserted.
-/

namespace ArchonPhysics.RandomMassMeasurableModeCoupling

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassOrderedProjectorBridge
open MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Ordered physical vertex square as a globally defined random variable. -/
def orderedNormalizedInteractionWeightSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N n : Nat} [NeZero N]
    (modes : Fin n → Fin (Fintype.card (Lattice.Site N)))
    (omega : Omega) : Real :=
  harmonicOrderedNormalizedInteractionWeight
    (ensemble.restrictPositiveMass (N := N) omega) modes

/-- The ordered vertex square is globally measurable, including on the null
set where the finite spectrum may be degenerate. -/
theorem measurable_orderedNormalizedInteractionWeightSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N n : Nat} [NeZero N]
    (modes : Fin n → Fin (Fintype.card (Lattice.Site N))) :
    Measurable (orderedNormalizedInteractionWeightSample ensemble modes) := by
  exact measurable_harmonicOrderedNormalizedInteractionWeight
    (ensemble.restrictPositiveMass (N := N))
    (measurable_restrictPositiveMass_coordinate ensemble) modes

/-- Almost surely the measurable projector construction agrees with the
existing physical normalized interaction weight in the corresponding ordered
normal-mode indices. -/
theorem orderedNormalizedInteractionWeightSample_eq_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N n : Nat} [NeZero N] (hN : 2 ≤ N)
    (modes : Fin n → Fin (Fintype.card (Lattice.Site N))) :
    ∀ᵐ omega ∂ensemble.probability,
      orderedNormalizedInteractionWeightSample ensemble modes omega =
        NormalizedModeCoupling.normalizedInteractionWeight
          (ensemble.restrictPositiveMass (N := N) omega)
          (fun r ↦ orderedIndexEquiv (modes r)) := by
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN] with omega hsimple
  apply harmonicOrderedNormalizedInteractionWeight_eq
  simpa [MeasurableOrderedSpectrum.harmonicHermitianSample,
    harmonicHermitian] using hsimple

/-- Canonical iid Uniform `[4/5,6/5]` specialization of global measurability. -/
theorem measurable_canonicalOrderedNormalizedInteractionWeightSample
    {N n : Nat} [NeZero N]
    (modes : Fin n → Fin (Fintype.card (Lattice.Site N))) :
    Measurable
      (orderedNormalizedInteractionWeightSample
        canonicalIIDMassPhaseEnsemble modes) :=
  measurable_orderedNormalizedInteractionWeightSample
    canonicalIIDMassPhaseEnsemble modes

/-- Canonical iid Uniform `[4/5,6/5]` specialization of the almost-sure
identification with the physical vertex square. -/
theorem canonicalOrderedNormalizedInteractionWeightSample_eq_ae
    {N n : Nat} [NeZero N] (hN : 2 ≤ N)
    (modes : Fin n → Fin (Fintype.card (Lattice.Site N))) :
    ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
      orderedNormalizedInteractionWeightSample
          canonicalIIDMassPhaseEnsemble modes omega =
        NormalizedModeCoupling.normalizedInteractionWeight
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)
          (fun r ↦ orderedIndexEquiv (modes r)) :=
  orderedNormalizedInteractionWeightSample_eq_ae
    canonicalIIDMassPhaseEnsemble hN modes

end

end ArchonPhysics.RandomMassMeasurableModeCoupling
