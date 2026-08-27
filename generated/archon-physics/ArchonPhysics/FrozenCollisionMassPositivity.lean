import ArchonPhysics.FrozenUniformCollisionCompactSupport
import ArchonPhysics.PhysicalHarmonicEnergyIdentity

/-!
# Positivity criteria for frozen collision-measure mass

This module isolates the exact nondegeneracy needed to remove the external
`mass ≠ 0` input from normalized collision characteristic functions and Levy
bridges.  A single strictly positive positive-mode three-wave weight makes
the full collision mass strictly positive.  Under simple spectrum, it is
enough that one physical three-wave interaction tensor be nonzero.

For three sites the latter condition is proved without an extra hypothesis.
The explicit physical configuration with values `0, 1, 2` has cubic forward-
difference sum `-6`.  Exact modal expansion therefore forces some cubic
interaction tensor to be nonzero.  A zero-frequency leg has identically zero
bond coefficients, so that tensor necessarily uses only positive modes.

For arbitrary `N ≥ 3`, this file does not assert that the cubic tensor is
nonzero: beyond the proved three-site case, nondegeneracy remains an explicit
hypothesis.  No resonance, kinetic limit, or relaxation conclusion is made.
-/

open scoped Topology

namespace ArchonPhysics.FrozenCollisionMassPositivity

open ArchonPhysics
open ArchonPhysics.AcousticVertexScaling
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.CollisionFourierWeakLimitBridge
open ArchonPhysics.FrozenUniformCollisionFiniteMeasureBound
open ArchonPhysics.FrozenUniformCollisionMassBound
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.ReducedModeTransform
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open Filter
open MeasureTheory

noncomputable section

/-- One strictly positive normalized interaction weight in the positive-mode
sector.  This is the minimal finite-volume input for positive collision mass. -/
def HasPositiveCollisionTriple {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) : Prop :=
  ∃ modes : OrderedModeTriple N,
    IsPositiveOrderedTriple m modes ∧
      0 < harmonicOrderedNormalizedInteractionWeight m modes

/-- A basis-dependent but sign-insensitive nondegeneracy criterion: one
ordered physical three-wave interaction tensor is nonzero. -/
def HasNonzeroThreeWaveInteractionTensor {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) : Prop :=
  ∃ modes : OrderedModeTriple N,
    interactionTensor m 3 (fun r ↦ orderedIndexEquiv (modes r)) ≠ 0

/-- A zero-frequency normal mode has zero coefficient on every physical bond. -/
theorem bondModeCoefficient_eq_zero_of_modeFrequency_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k j : Lattice.Site N) (hfrequency : modeFrequency m k = 0) :
    bondModeCoefficient m j k = 0 := by
  have hsum : ∑ i, (bondModeCoefficient m i k) ^ 2 = 0 := by
    rw [sum_sq_bondModeCoefficient, ← modeFrequency_sq, hfrequency]
    norm_num
  have hj := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _hi ↦ sq_nonneg (bondModeCoefficient m i k))).mp
      hsum j (Finset.mem_univ j)
  exact sq_eq_zero_iff.mp hj

/-- Any interaction tensor containing a zero-frequency leg vanishes. -/
theorem interactionTensor_eq_zero_of_modeFrequency_eq_zero
    {N n : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : Fin n → Lattice.Site N) (r : Fin n)
    (hfrequency : modeFrequency m (modes r) = 0) :
    interactionTensor m n modes = 0 := by
  unfold interactionTensor
  apply Finset.sum_eq_zero
  intro j _hj
  apply Finset.prod_eq_zero (Finset.mem_univ r)
  exact bondModeCoefficient_eq_zero_of_modeFrequency_eq_zero
    m (modes r) j hfrequency

/-- Every leg of a nonzero ordered three-wave tensor has positive frequency. -/
theorem isPositiveOrderedTriple_of_interactionTensor_ne_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N)
    (htensor : interactionTensor m 3
      (fun r ↦ orderedIndexEquiv (modes r)) ≠ 0) :
    IsPositiveOrderedTriple m modes := by
  intro r
  rw [mem_orderedPositiveModeIndices_iff,
    orderedModeFrequency_harmonicHermitian_eq]
  by_contra hnot
  have hzero : modeFrequency m (orderedIndexEquiv (modes r)) = 0 :=
    le_antisymm (not_lt.mp hnot) (modeFrequency_nonneg m _)
  exact htensor (interactionTensor_eq_zero_of_modeFrequency_eq_zero
    m (fun s ↦ orderedIndexEquiv (modes s)) r hzero)

/-- Under simple spectrum, one nonzero physical tensor gives a strictly
positive basis-free normalized ordered weight. -/
theorem harmonicOrderedNormalizedInteractionWeight_pos_of_tensor_ne_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (modes : OrderedModeTriple N)
    (htensor : interactionTensor m 3
      (fun r ↦ orderedIndexEquiv (modes r)) ≠ 0) :
    0 < harmonicOrderedNormalizedInteractionWeight m modes := by
  have hpositive := isPositiveOrderedTriple_of_interactionTensor_ne_zero
    m modes htensor
  have hphysical : PositiveModeTuple m
      (fun r ↦ orderedIndexEquiv (modes r)) :=
    (isPositiveOrderedTriple_iff_physical m modes).mp hpositive
  rw [harmonicOrderedNormalizedInteractionWeight_eq m hsimple modes]
  unfold normalizedInteractionWeight
  apply mul_pos
  · exact sq_pos_of_ne_zero htensor
  · apply Finset.prod_pos
    intro r _hr
    exact inv_pos.mpr (mul_pos zero_lt_two (hphysical r))

/-- Simple spectrum converts the nonzero-tensor criterion into the minimal
positive-triple criterion. -/
theorem hasPositiveCollisionTriple_of_nonzeroTensor
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hTensor : HasNonzeroThreeWaveInteractionTensor m) :
    HasPositiveCollisionTriple m := by
  obtain ⟨modes, htensor⟩ := hTensor
  exact ⟨modes,
    isPositiveOrderedTriple_of_interactionTensor_ne_zero m modes htensor,
    harmonicOrderedNormalizedInteractionWeight_pos_of_tensor_ne_zero
      m hsimple modes htensor⟩

/-- One positive triple makes the full filtered total interaction weight
strictly positive. -/
theorem positiveOrderedTotalInteractionWeight_pos
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (htriple : HasPositiveCollisionTriple m) :
    0 < positiveOrderedTotalInteractionWeight m := by
  classical
  obtain ⟨modes, hpositive, hweight⟩ := htriple
  unfold positiveOrderedTotalInteractionWeight
  apply Finset.sum_pos'
  · intro tuple _htuple
    by_cases hp : IsPositiveOrderedTriple m tuple
    · rw [if_pos hp]
      exact harmonicOrderedNormalizedInteractionWeight_nonneg m tuple
    · rw [if_neg hp]
  · exact ⟨modes, Finset.mem_univ modes, by simpa [hpositive] using hweight⟩

/-- One positive triple makes the bundled finite collision measure have
strictly positive `NNReal` mass, independently of the sign channel. -/
theorem positiveWeightedMismatchFiniteMeasure_mass_pos
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign)
    (htriple : HasPositiveCollisionTriple m) :
    0 < (positiveWeightedMismatchFiniteMeasure m sign).mass := by
  rw [positiveWeightedMismatchFiniteMeasure_mass_eq_toNNReal]
  exact Real.toNNReal_pos.mpr
    (positiveOrderedTotalInteractionWeight_pos m htriple)

/-- Nonzero-mass form used directly by probability normalization. -/
theorem positiveWeightedMismatchFiniteMeasure_mass_ne_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign)
    (htriple : HasPositiveCollisionTriple m) :
    (positiveWeightedMismatchFiniteMeasure m sign).mass ≠ 0 :=
  ne_of_gt (positiveWeightedMismatchFiniteMeasure_mass_pos m sign htriple)

/-- Under simple spectrum, the explicit nonzero-tensor condition already
implies strictly positive total interaction weight. -/
theorem positiveOrderedTotalInteractionWeight_pos_of_nonzeroTensor
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hTensor : HasNonzeroThreeWaveInteractionTensor m) :
    0 < positiveOrderedTotalInteractionWeight m :=
  positiveOrderedTotalInteractionWeight_pos m
    (hasPositiveCollisionTriple_of_nonzeroTensor m hsimple hTensor)

/-- Characteristic-function factorization with the mass-nonzero premise
discharged by the positive-triple condition. -/
theorem charFun_normalizedPositiveWeightedMismatchMeasure_factorization_of_positiveTriple
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (t : Real)
    (htriple : HasPositiveCollisionTriple m) :
    charFun (normalizedPositiveWeightedMismatchMeasure m sign : Measure Real) t =
      ((positiveWeightedMismatchFiniteMeasure m sign).mass⁻¹ : Real) *
        (∑ j, ∑ l, ∏ r,
          complexWeightedProjectedBondKernel (massWeightedDifferenceMatrix m)
            (harmonicHermitian m)
            (orderedNormalizedPhaseLeg m sign t r) j l) :=
  charFun_normalizedPositiveWeightedMismatchMeasure_factorization
    m sign t
      (positiveWeightedMismatchFiniteMeasure_mass_ne_zero m sign htriple)

/-! ## An unconditional three-site nonzero cubic tensor -/

/-- Explicit three-site physical configuration used to witness a nonzero
cubic bond polynomial. -/
def threeSiteCubicWitness : Lattice.Configuration 3 := fun i =>
  if i = 0 then 0 else if i = 1 then 1 else 2

/-- Hilbert-space packaging of the explicit three-site witness. -/
def threeSiteCubicWitnessHilbert : HilbertConfiguration 3 :=
  WithLp.toLp 2 threeSiteCubicWitness

/-- The explicit witness has forward differences `1, 1, -2`, whose cubes
sum to `-6`. -/
theorem threeSiteCubicWitness_sum_forwardDifference_cube :
    (∑ i : Lattice.Site 3,
      (Lattice.forwardDifference threeSiteCubicWitness i) ^ 3) = -6 := by
  have hwrap : (ZMod.finEquiv 3 (2 : Fin 3) + 1) = 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have hz20 : ZMod.finEquiv 3 (2 : Fin 3) ≠ 0 := by decide
  have hz21 : ZMod.finEquiv 3 (2 : Fin 3) ≠ 1 := by decide
  have hz20prime : (2 : ZMod 3) ≠ 0 := by decide
  have hz21prime : (2 : ZMod 3) ≠ 1 := by decide
  rw [← (ZMod.finEquiv 3).toEquiv.sum_comp]
  rw [Fin.sum_univ_three]
  norm_num [threeSiteCubicWitness, Lattice.forwardDifference, hwrap,
    h20, h21, hz20, hz21, hz20prime, hz21prime]

/-- Exact modal expansion of the nonzero cubic polynomial forces at least one
three-site physical interaction tensor to be nonzero. -/
theorem exists_threeSite_interactionTensor_ne_zero
    (m : Lattice.PositiveMassConfig 3) :
    ∃ modes : Fin 3 → Lattice.Site 3,
      interactionTensor m 3 modes ≠ 0 := by
  let amplitude : WeightedConfiguration 3 :=
    modalCoordinates m (sqrtMassTransform m threeSiteCubicWitnessHilbert)
  have hexpansion := sum_forwardDifference_pow_eq_interactionTensor
    (n := 3) m amplitude
  have hreconstruction :
      physicalReconstruction m amplitude = threeSiteCubicWitness := by
    change physicalReconstruction m
      (modalCoordinates m
        (sqrtMassTransform m threeSiteCubicWitnessHilbert)) =
          threeSiteCubicWitness
    exact (physicalReconstruction_modalCoordinates_sqrtMassTransform
      m threeSiteCubicWitnessHilbert).trans (by rfl)
  rw [hreconstruction,
    threeSiteCubicWitness_sum_forwardDifference_cube] at hexpansion
  by_contra hnone
  push Not at hnone
  have hzero :
      (∑ modes : Fin 3 → Lattice.Site 3,
        interactionTensor m 3 modes * ∏ r, amplitude (modes r)) = 0 := by
    apply Finset.sum_eq_zero
    intro modes _hmodes
    rw [hnone modes, zero_mul]
  rw [hzero] at hexpansion
  norm_num at hexpansion

/-- Every positive three-site mass realization has some nonzero ordered
physical three-wave tensor. -/
theorem threeSite_hasNonzeroThreeWaveInteractionTensor
    (m : Lattice.PositiveMassConfig 3) :
    HasNonzeroThreeWaveInteractionTensor m := by
  obtain ⟨physicalModes, htensor⟩ :=
    exists_threeSite_interactionTensor_ne_zero m
  refine ⟨fun r ↦ orderedIndexEquiv.symm (physicalModes r), ?_⟩
  simpa using htensor

/-- Under simple spectrum, three sites therefore always supply a positive
collision triple. -/
theorem threeSite_hasPositiveCollisionTriple
    (m : Lattice.PositiveMassConfig 3)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m)) :
    HasPositiveCollisionTriple m :=
  hasPositiveCollisionTriple_of_nonzeroTensor m hsimple
    (threeSite_hasNonzeroThreeWaveInteractionTensor m)

/-- Three-site total collision weight is strictly positive at every simple-
spectrum positive-mass realization. -/
theorem threeSite_positiveOrderedTotalInteractionWeight_pos
    (m : Lattice.PositiveMassConfig 3)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m)) :
    0 < positiveOrderedTotalInteractionWeight m :=
  positiveOrderedTotalInteractionWeight_pos m
    (threeSite_hasPositiveCollisionTriple m hsimple)

/-- Three-site bundled collision mass is strictly positive. -/
theorem threeSite_positiveWeightedMismatchFiniteMeasure_mass_pos
    (m : Lattice.PositiveMassConfig 3)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (sign : Fin 3 → InteractionSign) :
    0 < (positiveWeightedMismatchFiniteMeasure m sign).mass :=
  positiveWeightedMismatchFiniteMeasure_mass_pos m sign
    (threeSite_hasPositiveCollisionTriple m hsimple)

/-- Three-site bundled collision mass is nonzero, with no additional tensor
nondegeneracy hypothesis. -/
theorem threeSite_positiveWeightedMismatchFiniteMeasure_mass_ne_zero
    (m : Lattice.PositiveMassConfig 3)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (sign : Fin 3 → InteractionSign) :
    (positiveWeightedMismatchFiniteMeasure m sign).mass ≠ 0 :=
  ne_of_gt (threeSite_positiveWeightedMismatchFiniteMeasure_mass_pos
    m hsimple sign)

/-- Three-site normalized characteristic-function factorization with no
external mass-nonzero premise. -/
theorem threeSite_charFun_normalizedPositiveWeightedMismatchMeasure_factorization
    (m : Lattice.PositiveMassConfig 3)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (sign : Fin 3 → InteractionSign) (t : Real) :
    charFun (normalizedPositiveWeightedMismatchMeasure m sign : Measure Real) t =
      ((positiveWeightedMismatchFiniteMeasure m sign).mass⁻¹ : Real) *
        (∑ j, ∑ l, ∏ r,
          complexWeightedProjectedBondKernel (massWeightedDifferenceMatrix m)
            (harmonicHermitian m)
            (orderedNormalizedPhaseLeg m sign t r) j l) :=
  charFun_normalizedPositiveWeightedMismatchMeasure_factorization
    m sign t
      (threeSite_positiveWeightedMismatchFiniteMeasure_mass_ne_zero
        m hsimple sign)

/-! ## Levy bridges with positivity replacing an external mass premise -/

/-- Dependent-size Levy bridge whose nonzero masses are discharged by a
positive collision triple at every index. -/
theorem tendsto_varyingSize_normalizedCollision_of_kernelProduct_of_positiveTriple
    (N : Nat → Nat) [hN : ∀ n, NeZero (N n)]
    (m : ∀ n, Lattice.PositiveMassConfig (N n))
    (sign : Fin 3 → InteractionSign)
    (htriple : ∀ n, HasPositiveCollisionTriple (m n))
    (target : ProbabilityMeasure Real)
    (hkernel : ∀ t : Real,
      Tendsto
        (fun n ↦
          ((positiveWeightedMismatchFiniteMeasure (m n) sign).mass⁻¹ : Real) *
            (∑ j, ∑ l, ∏ r,
              complexWeightedProjectedBondKernel
                (massWeightedDifferenceMatrix (m n))
                (harmonicHermitian (m n))
                (orderedNormalizedPhaseLeg (m n) sign t r) j l))
        atTop (𝓝 (charFun (target : Measure Real) t))) :
    Tendsto (fun n ↦ normalizedPositiveWeightedMismatchMeasure (m n) sign)
      atTop (𝓝 target) :=
  tendsto_varyingSize_normalizedPositiveWeightedMismatchMeasure_of_kernelProduct
    N m sign
      (fun n ↦ positiveWeightedMismatchFiniteMeasure_mass_ne_zero
        (m n) sign (htriple n)) target hkernel

/-- Dependent-size mass-plus-shape bridge with the same positive-triple
replacement for all external mass-nonzero hypotheses. -/
theorem tendsto_varyingSize_collisionFiniteMeasure_of_mass_and_kernelProduct_of_positiveTriple
    (N : Nat → Nat) [hN : ∀ n, NeZero (N n)]
    (m : ∀ n, Lattice.PositiveMassConfig (N n))
    (sign : Fin 3 → InteractionSign)
    (htriple : ∀ n, HasPositiveCollisionTriple (m n))
    (target : FiniteMeasure Real)
    (hmassLimit : Tendsto
      (fun n ↦ (positiveWeightedMismatchFiniteMeasure (m n) sign).mass)
      atTop (𝓝 target.mass))
    (hkernel : ∀ t : Real,
      Tendsto
        (fun n ↦
          ((positiveWeightedMismatchFiniteMeasure (m n) sign).mass⁻¹ : Real) *
            (∑ j, ∑ l, ∏ r,
              complexWeightedProjectedBondKernel
                (massWeightedDifferenceMatrix (m n))
                (harmonicHermitian (m n))
                (orderedNormalizedPhaseLeg (m n) sign t r) j l))
        atTop (𝓝 (charFun (target.normalize : Measure Real) t))) :
    Tendsto (fun n ↦ positiveWeightedMismatchFiniteMeasure (m n) sign)
      atTop (𝓝 target) :=
  tendsto_varyingSize_positiveWeightedMismatchFiniteMeasure_of_mass_and_kernelProduct
    N m sign
      (fun n ↦ positiveWeightedMismatchFiniteMeasure_mass_ne_zero
        (m n) sign (htriple n)) target hmassLimit hkernel

/-- Fixed three-site Levy bridge: simple spectrum alone now discharges every
collision-mass nonzero premise. -/
theorem tendsto_threeSite_normalizedCollision_of_kernelProduct
    (m : Nat → Lattice.PositiveMassConfig 3)
    (sign : Fin 3 → InteractionSign)
    (hsimple : ∀ n, SimpleOrderedSpectrum (harmonicHermitian (m n)))
    (target : ProbabilityMeasure Real)
    (hkernel : ∀ t : Real,
      Tendsto
        (fun n ↦
          ((positiveWeightedMismatchFiniteMeasure (m n) sign).mass⁻¹ : Real) *
            (∑ j, ∑ l, ∏ r,
              complexWeightedProjectedBondKernel
                (massWeightedDifferenceMatrix (m n))
                (harmonicHermitian (m n))
                (orderedNormalizedPhaseLeg (m n) sign t r) j l))
        atTop (𝓝 (charFun (target : Measure Real) t))) :
    Tendsto (fun n ↦ normalizedPositiveWeightedMismatchMeasure (m n) sign)
      atTop (𝓝 target) :=
  tendsto_normalizedPositiveWeightedMismatchMeasure_of_kernelProduct
    m sign
      (fun n ↦ threeSite_positiveWeightedMismatchFiniteMeasure_mass_ne_zero
        (m n) (hsimple n) sign) target hkernel

end

end ArchonPhysics.FrozenCollisionMassPositivity
