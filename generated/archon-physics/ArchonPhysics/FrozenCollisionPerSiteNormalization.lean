import ArchonPhysics.FrozenCollisionMassExtensiveLowerBound

/-!
# Per-site normalization of the frozen collision measure

The extensive collision-mass estimate selects the natural finite-volume
normalization by the number of sites.  This module bundles that normalization
and proves a realization- and volume-independent positive lower bound for its
total mass.
-/

namespace ArchonPhysics.FrozenCollisionPerSiteNormalization

open ArchonPhysics
open ArchonPhysics.CollisionFourierWeakLimitBridge
open ArchonPhysics.FrozenCollisionMassExtensiveLowerBound
open ArchonPhysics.FrozenUniformCollisionFiniteMeasureBound
open ArchonPhysics.FrozenUniformCollisionMassBound
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open MeasureTheory

noncomputable section

/-- Coupling-weighted mismatch measure normalized by the number of sites. -/
def perSitePositiveWeightedMismatchFiniteMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) : FiniteMeasure Real :=
  ((N : NNReal)⁻¹) • positiveWeightedMismatchFiniteMeasure m sign

/-- Exact real mass of the per-site normalized measure. -/
theorem perSitePositiveWeightedMismatchFiniteMeasure_mass_real
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) :
    ((perSitePositiveWeightedMismatchFiniteMeasure m sign).mass : Real) =
      (N : Real)⁻¹ * positiveOrderedTotalInteractionWeight m := by
  unfold perSitePositiveWeightedMismatchFiniteMeasure
  have hsmul :
      ((((N : NNReal)⁻¹) •
        positiveWeightedMismatchFiniteMeasure m sign).mass) =
        (N : NNReal)⁻¹ *
          (positiveWeightedMismatchFiniteMeasure m sign).mass := by
    unfold FiniteMeasure.mass
    rw [FiniteMeasure.smul_apply]
    rfl
  rw [hsmul, positiveWeightedMismatchFiniteMeasure_mass_eq_toNNReal]
  simp only [NNReal.coe_mul, NNReal.coe_inv]
  rw [Real.coe_toNNReal _ (positiveOrderedTotalInteractionWeight_nonneg m)]
  norm_cast

/-- The per-site normalized collision measure has a uniform strictly
positive mass lower bound for every simple frozen realization. -/
theorem iidCollisionWeightDensityLower_le_perSite_mass
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) (hN : 3 ≤ N)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (ensemble.restrictPositiveMass (N := N) omega)))
    (sign : Fin 3 → InteractionSign) :
    iidCollisionWeightDensityLower ≤
      ((perSitePositiveWeightedMismatchFiniteMeasure
        (ensemble.restrictPositiveMass (N := N) omega) sign).mass : Real) := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  rw [perSitePositiveWeightedMismatchFiniteMeasure_mass_real]
  have hNpos : 0 < (N : Real) := by positivity
  have hextensive :=
    iid_collisionWeight_extensive_lower ensemble omega hN hsimple
  calc
    iidCollisionWeightDensityLower =
        (N : Real)⁻¹ *
          (iidCollisionWeightDensityLower * (N : Real)) := by
      field_simp
    _ ≤ (N : Real)⁻¹ * positiveOrderedTotalInteractionWeight m :=
      mul_le_mul_of_nonneg_left hextensive (inv_nonneg.mpr hNpos.le)

end

end ArchonPhysics.FrozenCollisionPerSiteNormalization
