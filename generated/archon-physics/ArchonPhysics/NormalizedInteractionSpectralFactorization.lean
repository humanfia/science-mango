import ArchonPhysics.OrderedInteractionSpectralFactorization

/-!
# Physical normalized interaction spectral factorization

This module attaches the existing positive-frequency normalization to each
leg of the exact projector-kernel factorization.  It remains a finite identity
and asserts no spectral-kernel limit.
-/

namespace ArchonPhysics.OrderedInteractionSpectralFactorization.Harmonic

open ArchonPhysics
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum

noncomputable section

/-- Attach the physical positive-frequency normalization to each spectral
leg.  The inverse is totalized to zero at zero frequency. -/
def harmonicNormalizedLegWeight {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (weight : Fin n → Fin (Fintype.card (Lattice.Site N)) → Real)
    (r : Fin n) (k : Fin (Fintype.card (Lattice.Site N))) : Real :=
  weight r k * (2 * orderedModeFrequency (harmonicHermitian m) k)⁻¹

/-- Physical normalized interaction moment with arbitrary additional one-leg
test weights. -/
def harmonicWeightedNormalizedInteractionMoment {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (weight : Fin n → Fin (Fintype.card (Lattice.Site N)) → Real) : Real :=
  weightedInteractionMoment (massWeightedDifferenceMatrix m)
    (harmonicHermitian m) (harmonicNormalizedLegWeight m weight)

/-- The leg-normalized definition is exactly the finite sum of the existing
physical normalized ordered interaction weights. -/
theorem harmonicWeightedNormalizedInteractionMoment_eq_sum
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (weight : Fin n → Fin (Fintype.card (Lattice.Site N)) → Real) :
    harmonicWeightedNormalizedInteractionMoment m weight =
      ∑ modes, harmonicOrderedNormalizedInteractionWeight m modes *
        ∏ r, weight r (modes r) := by
  unfold harmonicWeightedNormalizedInteractionMoment weightedInteractionMoment
    harmonicNormalizedLegWeight harmonicOrderedNormalizedInteractionWeight
    harmonicOrderedInteractionWeightSq
  apply Finset.sum_congr rfl
  intro modes _hmodes
  rw [Finset.prod_mul_distrib]
  ring

/-- Exact projector-kernel factorization for the physically normalized
interaction sum. -/
theorem harmonicWeightedNormalizedInteractionMoment_factorization
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (weight : Fin n → Fin (Fintype.card (Lattice.Site N)) → Real) :
    (∑ modes, harmonicOrderedNormalizedInteractionWeight m modes *
        ∏ r, weight r (modes r)) =
      ∑ j, ∑ l, ∏ r,
        weightedProjectedBondKernel (massWeightedDifferenceMatrix m)
          (harmonicHermitian m) (harmonicNormalizedLegWeight m weight r) j l := by
  rw [← harmonicWeightedNormalizedInteractionMoment_eq_sum]
  exact weightedInteractionMoment_eq_projectedKernelProduct _ _ _

end


end ArchonPhysics.OrderedInteractionSpectralFactorization.Harmonic
