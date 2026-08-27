import ArchonPhysics.CollisionFourierWeakLimitBridge
import ArchonPhysics.FrozenUniformCollisionMassBound

/-!
# Uniform finite-measure mass bound for frozen collision data

This module scales the genuine positive weighted mismatch finite measure by
the reciprocal number of ordered mode triples.  Its `NNReal` mass is exactly
the same tuple normalization of the existing positive total interaction
weight.  The frozen iid spectral and vertex estimates therefore give a
realization-independent mass ceiling.

The simple-spectrum hypothesis used by the frozen vertex estimate remains
explicit.  No convergence or limiting collision measure is asserted.
-/

namespace ArchonPhysics.FrozenUniformCollisionFiniteMeasureBound

open ArchonPhysics
open ArchonPhysics.CollisionFourierWeakLimitBridge
open ArchonPhysics.FrozenUniformCollisionMassBound
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open MeasureTheory

noncomputable section

/-- The positive ordered total interaction weight is nonnegative. -/
theorem positiveOrderedTotalInteractionWeight_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    0 ≤ positiveOrderedTotalInteractionWeight m := by
  classical
  unfold positiveOrderedTotalInteractionWeight
  apply Finset.sum_nonneg
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · rw [if_pos hpositive]
    exact harmonicOrderedNormalizedInteractionWeight_nonneg m modes
  · rw [if_neg hpositive]

/-- The mass of the genuine finite mismatch measure is precisely the
nonnegative-real lift of the positive ordered total interaction weight. -/
theorem positiveWeightedMismatchFiniteMeasure_mass_eq_toNNReal
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) :
    (positiveWeightedMismatchFiniteMeasure m sign).mass =
      Real.toNNReal (positiveOrderedTotalInteractionWeight m) := by
  classical
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (positiveOrderedTotalInteractionWeight_nonneg m)]
  change (positiveWeightedMismatchMeasure m sign Set.univ).toReal = _
  unfold positiveWeightedMismatchMeasure positiveOrderedTotalInteractionWeight
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  have hfinite : ∀ modes ∈ (Finset.univ : Finset (OrderedModeTriple N)),
      (((if IsPositiveOrderedTriple m modes then
          ENNReal.ofReal
              (harmonicOrderedNormalizedInteractionWeight m modes) •
            Measure.dirac (orderedThreeWaveMismatch m sign modes)
        else 0) : Measure Real) Set.univ) ≠ (⊤ : ENNReal) := by
    intro modes _hmodes
    by_cases hpositive : IsPositiveOrderedTriple m modes
    · simp [hpositive]
    · simp [hpositive]
  rw [ENNReal.toReal_sum hfinite]
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · simp [hpositive, ENNReal.toReal_ofReal,
      harmonicOrderedNormalizedInteractionWeight_nonneg m modes]
  · simp [hpositive]

/-- The collision finite measure normalized by the number of all ordered
mode triples. -/
def tupleNormalizedPositiveWeightedMismatchFiniteMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) : FiniteMeasure Real :=
  (Fintype.card (OrderedModeTriple N) : NNReal)⁻¹ •
    positiveWeightedMismatchFiniteMeasure m sign

/-- Its mass, viewed in `Real`, is exactly the already defined averaged
positive ordered total interaction weight. -/
theorem tupleNormalizedPositiveWeightedMismatchFiniteMeasure_mass_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) :
    ((tupleNormalizedPositiveWeightedMismatchFiniteMeasure m sign).mass : Real) =
      averagedPositiveOrderedTotalInteractionWeight m := by
  unfold tupleNormalizedPositiveWeightedMismatchFiniteMeasure
    averagedPositiveOrderedTotalInteractionWeight
  have hsmul :
      (((Fintype.card (OrderedModeTriple N) : NNReal)⁻¹ •
        positiveWeightedMismatchFiniteMeasure m sign).mass) =
        (Fintype.card (OrderedModeTriple N) : NNReal)⁻¹ *
          (positiveWeightedMismatchFiniteMeasure m sign).mass := by
    unfold FiniteMeasure.mass
    rw [FiniteMeasure.smul_apply]
    rfl
  rw [hsmul, positiveWeightedMismatchFiniteMeasure_mass_eq_toNNReal]
  simp only [NNReal.coe_mul, NNReal.coe_inv]
  rw [Real.coe_toNNReal _ (positiveOrderedTotalInteractionWeight_nonneg m)]
  rfl

/-- The explicit frozen realization-independent collision mass ceiling. -/
def frozenCollisionMassCeiling : NNReal :=
  Real.toNNReal (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8)

/-- Frozen iid tuple-normalized collision finite measures have uniformly
bounded `NNReal` mass whenever the ordered harmonic spectrum is simple. -/
theorem iid_tupleNormalizedPositiveWeightedMismatchFiniteMeasure_mass_le
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (sign : Fin 3 → InteractionSign)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (ensemble.restrictPositiveMass (N := N) omega))) :
    (tupleNormalizedPositiveWeightedMismatchFiniteMeasure
        (ensemble.restrictPositiveMass (N := N) omega) sign).mass ≤
      frozenCollisionMassCeiling := by
  rw [← NNReal.coe_le_coe]
  unfold frozenCollisionMassCeiling
  rw [Real.coe_toNNReal _ (by positivity :
    0 ≤ Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8)]
  rw [tupleNormalizedPositiveWeightedMismatchFiniteMeasure_mass_eq]
  exact iid_averagedPositiveOrderedTotalInteractionWeight_le
    ensemble omega hsimple

/-- The same frozen ceiling after coercing both masses to `ENNReal`. -/
theorem iid_tupleNormalizedPositiveWeightedMismatchFiniteMeasure_ennrealMass_le
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (sign : Fin 3 → InteractionSign)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (ensemble.restrictPositiveMass (N := N) omega))) :
    ((tupleNormalizedPositiveWeightedMismatchFiniteMeasure
        (ensemble.restrictPositiveMass (N := N) omega) sign).mass : ENNReal) ≤
      (frozenCollisionMassCeiling : ENNReal) :=
  ENNReal.coe_le_coe.mpr
    (iid_tupleNormalizedPositiveWeightedMismatchFiniteMeasure_mass_le
      ensemble omega sign hsimple)

/-- Sequence interface: every fixed-size sequence of frozen iid realizations
satisfying the explicit simple-spectrum condition has the same mass bound. -/
theorem iid_tupleNormalizedPositiveWeightedMismatchFiniteMeasure_mass_uniform
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Nat → Omega)
    (sign : Fin 3 → InteractionSign)
    (hsimple : ∀ n, SimpleOrderedSpectrum
      (harmonicHermitian (ensemble.restrictPositiveMass (N := N) (omega n)))) :
    ∀ n,
      (tupleNormalizedPositiveWeightedMismatchFiniteMeasure
        (ensemble.restrictPositiveMass (N := N) (omega n)) sign).mass ≤
        frozenCollisionMassCeiling := by
  intro n
  exact iid_tupleNormalizedPositiveWeightedMismatchFiniteMeasure_mass_le
    ensemble (omega n) sign (hsimple n)


/-- Dependent-size sequence interface: the same mass ceiling holds when the
finite site count varies with the sequence index. -/
theorem iid_varyingSize_tupleNormalizedPositiveWeightedMismatchFiniteMeasure_mass_uniform
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (N : Nat → Nat) [hN : ∀ n, NeZero (N n)] (omega : Nat → Omega)
    (sign : Fin 3 → InteractionSign)
    (hsimple : ∀ n, SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N n) (omega n)))) :
    ∀ n,
      (tupleNormalizedPositiveWeightedMismatchFiniteMeasure
        (ensemble.restrictPositiveMass (N := N n) (omega n)) sign).mass ≤
        frozenCollisionMassCeiling := by
  intro n
  exact iid_tupleNormalizedPositiveWeightedMismatchFiniteMeasure_mass_le
    ensemble (omega n) sign (hsimple n)
end

end ArchonPhysics.FrozenUniformCollisionFiniteMeasureBound
