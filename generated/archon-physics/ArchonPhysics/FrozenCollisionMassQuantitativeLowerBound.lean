import ArchonPhysics.FrozenInteractionTensorQuantitativeLowerBound
import ArchonPhysics.FrozenUniformCollisionCompactSupport

/-!
# Quantitative lower bounds for frozen collision mass

The full ordered positive-mode collision weight is first reindexed as the
sum of the physical normalized interaction weights.  Tensors with a zero
frequency leg vanish, so the positive-mode filter loses no tensor square.
An upper frequency ceiling then gives a common lower bound on every inverse
frequency normalization factor.

Combining this observation with the quantitative modal-completeness bound
gives a lower bound for the *unnormalized* collision mass that is uniform in
`N`.  By contrast, the single-entry bound in the imported tensor module has
an `N^3` denominator, and tuple-averaging this measure would likewise destroy
the uniform lower bound.  No resonance-density or kinetic statement is made.
-/

namespace ArchonPhysics.FrozenCollisionMassQuantitativeLowerBound

open ArchonPhysics
open ArchonPhysics.CollisionFourierWeakLimitBridge
open ArchonPhysics.FrozenCollisionMassPositivity
open ArchonPhysics.FrozenInteractionTensorQuantitativeLowerBound
open ArchonPhysics.FrozenUniformCollisionFiniteMeasureBound
open ArchonPhysics.FrozenUniformCollisionMassBound
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open MeasureTheory

noncomputable section

/-- Coordinatewise transport from ordered triples to physical mode triples. -/
def orderedPhysicalTripleEquiv {N : Nat} [NeZero N] :
    OrderedModeTriple N ≃ (Fin 3 → Lattice.Site N) :=
  Equiv.piCongrRight fun _r ↦ orderedIndexEquiv

/-- Under simple spectrum, the positive ordered total is exactly the sum of
all physical normalized interaction weights.  Tuples outside the positive
filter have a zero-frequency leg and hence zero interaction tensor. -/
theorem positiveOrderedTotalInteractionWeight_eq_physical_sum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m)) :
    positiveOrderedTotalInteractionWeight m =
      ∑ modes : Fin 3 → Lattice.Site N,
        normalizedInteractionWeight m modes := by
  classical
  unfold positiveOrderedTotalInteractionWeight
  rw [← (orderedPhysicalTripleEquiv (N := N)).sum_comp
    (fun modes ↦ normalizedInteractionWeight m modes)]
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · rw [if_pos hpositive,
      harmonicOrderedNormalizedInteractionWeight_eq m hsimple]
    rfl
  · rw [if_neg hpositive]
    have hnotPhysical : ¬ PositiveModeTuple m
        (fun r ↦ orderedIndexEquiv (modes r)) := by
      exact fun hphysical ↦ hpositive
        ((isPositiveOrderedTriple_iff_physical m modes).2 hphysical)
    simp only [PositiveModeTuple, not_forall] at hnotPhysical
    obtain ⟨r, hr⟩ := hnotPhysical
    have hzero : modeFrequency m (orderedIndexEquiv (modes r)) = 0 :=
      le_antisymm (not_lt.mp hr) (modeFrequency_nonneg m _)
    change 0 = normalizedInteractionWeight m
      (fun s ↦ orderedIndexEquiv (modes s))
    unfold normalizedInteractionWeight
    rw [interactionTensor_eq_zero_of_modeFrequency_eq_zero
      m (fun s ↦ orderedIndexEquiv (modes s)) r hzero]
    simp

/-- A common frequency ceiling turns a physical tensor square into a lower
bound for its normalized interaction weight. -/
theorem constant_mul_interactionTensor_sq_le_normalizedInteractionWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (frequencyCeiling : Real) (hceiling : 0 < frequencyCeiling)
    (hfrequency : ∀ k, modeFrequency m k ≤ frequencyCeiling)
    (modes : Fin 3 → Lattice.Site N) :
    ((2 * frequencyCeiling)⁻¹) ^ 3 *
        (interactionTensor m 3 modes) ^ 2 ≤
      normalizedInteractionWeight m modes := by
  by_cases hpositive : PositiveModeTuple m modes
  · have hleg (r : Fin 3) :
        (2 * frequencyCeiling)⁻¹ ≤
          (2 * modeFrequency m (modes r))⁻¹ := by
      apply (inv_le_inv₀ (mul_pos zero_lt_two hceiling)
        (mul_pos zero_lt_two (hpositive r))).2
      exact mul_le_mul_of_nonneg_left (hfrequency (modes r)) zero_le_two
    have hproduct :
        ((2 * frequencyCeiling)⁻¹) ^ 3 ≤
          ∏ r, (2 * modeFrequency m (modes r))⁻¹ := by
      have hprod := Finset.prod_le_prod
        (s := Finset.univ)
        (f := fun _r : Fin 3 ↦ (2 * frequencyCeiling)⁻¹)
        (g := fun r ↦ (2 * modeFrequency m (modes r))⁻¹)
        (fun _r _hr ↦ inv_nonneg.mpr
          (mul_nonneg zero_le_two hceiling.le))
        (fun r _hr ↦ hleg r)
      simpa [Fin.prod_univ_three, pow_succ] using hprod
    unfold normalizedInteractionWeight
    calc
      _ = (interactionTensor m 3 modes) ^ 2 *
          ((2 * frequencyCeiling)⁻¹) ^ 3 := by ring
      _ ≤ (interactionTensor m 3 modes) ^ 2 *
          ∏ r, (2 * modeFrequency m (modes r))⁻¹ :=
        mul_le_mul_of_nonneg_left hproduct (sq_nonneg _)
  · simp only [PositiveModeTuple, not_forall] at hpositive
    obtain ⟨r, hr⟩ := hpositive
    have hzero : modeFrequency m (modes r) = 0 :=
      le_antisymm (not_lt.mp hr) (modeFrequency_nonneg m _)
    have htensor : interactionTensor m 3 modes = 0 :=
      interactionTensor_eq_zero_of_modeFrequency_eq_zero m modes r hzero
    simp [normalizedInteractionWeight, htensor]

/-- Summed form of the inverse-frequency lower bound. -/
theorem constant_mul_tensorSquareSum_le_positiveOrderedTotalInteractionWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (frequencyCeiling : Real) (hceiling : 0 < frequencyCeiling)
    (hfrequency : ∀ k, modeFrequency m k ≤ frequencyCeiling) :
    ((2 * frequencyCeiling)⁻¹) ^ 3 *
        (∑ modes : Fin 3 → Lattice.Site N,
          (interactionTensor m 3 modes) ^ 2) ≤
      positiveOrderedTotalInteractionWeight m := by
  rw [positiveOrderedTotalInteractionWeight_eq_physical_sum m hsimple,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun modes _hmodes ↦
    constant_mul_interactionTensor_sq_le_normalizedInteractionWeight
      m frequencyCeiling hceiling hfrequency modes

/-- General `N`-uniform lower bound for the unnormalized positive collision
weight under coordinatewise mass and frequency upper bounds. -/
theorem collisionWeightLowerBound_le_positiveOrderedTotalInteractionWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hN : 3 ≤ N) (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (mUpper frequencyCeiling : Real)
    (hmUpper : ∀ i, m.mass i ≤ mUpper)
    (hceiling : 0 < frequencyCeiling)
    (hfrequency : ∀ k, modeFrequency m k ≤ frequencyCeiling) :
    ((2 * frequencyCeiling)⁻¹) ^ 3 *
        (36 / (5 * mUpper) ^ 3) ≤
      positiveOrderedTotalInteractionWeight m := by
  have hmUpperPos : 0 < mUpper :=
    (m.mass_pos 0).trans_le (hmUpper 0)
  have hmassCubePos : 0 < (5 * mUpper) ^ 3 := by positivity
  have htensorLower :
      36 / (5 * mUpper) ^ 3 ≤
        ∑ modes : Fin 3 → Lattice.Site N,
          (interactionTensor m 3 modes) ^ 2 := by
    apply (div_le_iff₀ hmassCubePos).2
    simpa using (thirtySix_le_tensorSquareSum_mul_massUpperCube
      m hN mUpper hmUpper)
  have hconstantNonneg : 0 ≤ ((2 * frequencyCeiling)⁻¹) ^ 3 := by
    positivity
  exact (mul_le_mul_of_nonneg_left htensorLower hconstantNonneg).trans
    (constant_mul_tensorSquareSum_le_positiveOrderedTotalInteractionWeight
      m hsimple frequencyCeiling hceiling hfrequency)

/-- Universal frozen-IID lower constant for the unnormalized collision
weight.  It is independent of `N` and of the frozen sample. -/
def iidCollisionWeightLower : Real :=
  ((2 * Real.sqrt 5)⁻¹) ^ 3 * (1 / 6)

theorem iidCollisionWeightLower_pos : 0 < iidCollisionWeightLower := by
  unfold iidCollisionWeightLower
  positivity

/-- Every frozen IID realization with `N ≥ 3` and simple ordered spectrum
has total positive collision weight at least the universal constant. -/
theorem iidCollisionWeightLower_le_positiveOrderedTotalInteractionWeight
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) (hN : 3 ≤ N)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (ensemble.restrictPositiveMass (N := N) omega))) :
    iidCollisionWeightLower ≤
      positiveOrderedTotalInteractionWeight
        (ensemble.restrictPositiveMass (N := N) omega) := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  have hmUpper : ∀ i, m.mass i ≤ RandomEnsemble.massUpper := by
    intro i
    simpa [m] using (ensemble.mass_mem_support i.val omega).2
  have hfrequency : ∀ k, modeFrequency m k ≤ Real.sqrt 5 := by
    intro k
    have hk := iid_orderedModeFrequency_harmonic_le_sqrt_five
      ensemble omega (orderedIndexEquiv.symm k)
    rw [orderedModeFrequency_harmonicHermitian_eq] at hk
    simpa [m] using hk
  have hbound := collisionWeightLowerBound_le_positiveOrderedTotalInteractionWeight
    m hN hsimple RandomEnsemble.massUpper (Real.sqrt 5)
      hmUpper (by positivity) hfrequency
  have hrational : 36 / (5 * RandomEnsemble.massUpper) ^ 3 = (1 / 6 : Real) := by
    norm_num [RandomEnsemble.massUpper]
  rw [hrational] at hbound
  simpa [iidCollisionWeightLower, RandomEnsemble.massUpper] using hbound

/-- The same universal lower bound for the `NNReal` mass of the genuine
bundled finite collision measure. -/
theorem iidCollisionWeightLower_toNNReal_le_finiteMeasure_mass
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) (hN : 3 ≤ N)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (ensemble.restrictPositiveMass (N := N) omega)))
    (sign : Fin 3 → InteractionSign) :
    Real.toNNReal iidCollisionWeightLower ≤
      (positiveWeightedMismatchFiniteMeasure
        (ensemble.restrictPositiveMass (N := N) omega) sign).mass := by
  rw [positiveWeightedMismatchFiniteMeasure_mass_eq_toNNReal]
  exact Real.toNNReal_mono
    (iidCollisionWeightLower_le_positiveOrderedTotalInteractionWeight
      ensemble omega hN hsimple)

end

end ArchonPhysics.FrozenCollisionMassQuantitativeLowerBound
