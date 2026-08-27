import ArchonPhysics.FrozenCollisionMassPositivity

/-!
# Frozen collision-mass positivity at every size `N ≥ 3`

This module removes the finite-volume cubic-tensor nondegeneracy hypothesis
left explicit in `FrozenCollisionMassPositivity`.  For `N ≥ 4`, the periodic
configuration supported at sites `1` and `2`, with values `1` and `2`, has
forward differences `1, 1, -2` and zero elsewhere.  Its cubic bond sum is
therefore `-6`.  Exact modal reconstruction forces at least one physical
three-wave interaction tensor to be nonzero.  The already proved three-site
witness handles the remaining endpoint `N = 3`.

Simple ordered spectrum is used only when converting a nonzero physical
tensor into a positive basis-free ordered interaction weight.  No resonance,
kinetic limit, relaxation, or thermodynamic-limit assertion is made.  The
Levy bridges below retain their kernel convergence assumptions explicitly.
-/

open scoped Topology

namespace ArchonPhysics.FrozenCollisionMassPositivity

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.CollisionFourierWeakLimitBridge
open ArchonPhysics.FrozenUniformCollisionMassBound
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ReducedModeTransform
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open Filter
open MeasureTheory

noncomputable section

private theorem zmod_natCast_ne_of_ne_of_lt
    {N a b : Nat} (hab : a ≠ b) (ha : a < N) (hb : b < N) :
    (a : ZMod N) ≠ (b : ZMod N) := by
  intro h
  have hmod := (ZMod.natCast_eq_natCast_iff a b N).mp h
  exact hab (hmod.eq_of_lt_of_lt ha hb)

/-- A local periodic configuration whose only nonzero values are `q 1 = 1`
and `q 2 = 2`. -/
def cubicWitnessConfiguration (N : Nat) : Lattice.Configuration N := fun i =>
  if i = 1 then 1 else if i = 2 then 2 else 0

/-- For `N ≥ 4`, the local witness has bond differences `1, 1, -2` at
sites `0, 1, 2`, respectively, and zero at every other site. -/
theorem cubicWitnessConfiguration_forwardDifference
    {N : Nat} (hN : 4 ≤ N) (i : Lattice.Site N) :
    Lattice.forwardDifference (cubicWitnessConfiguration N) i =
      if i = 0 then 1 else if i = 1 then 1 else if i = 2 then -2 else 0 := by
  have h01 : (0 : ZMod N) ≠ 1 := by
    simpa using (zmod_natCast_ne_of_ne_of_lt (N := N) (a := 0) (b := 1)
      (by omega) (by omega) (by omega))
  have h02 : (0 : ZMod N) ≠ 2 := by
    simpa using (zmod_natCast_ne_of_ne_of_lt (N := N) (a := 0) (b := 2)
      (by omega) (by omega) (by omega))
  have h12 : (1 : ZMod N) ≠ 2 := by
    simpa using (zmod_natCast_ne_of_ne_of_lt (N := N) (a := 1) (b := 2)
      (by omega) (by omega) (by omega))
  have h30 : (3 : ZMod N) ≠ 0 := by
    simpa using (zmod_natCast_ne_of_ne_of_lt (N := N) (a := 3) (b := 0)
      (by omega) (by omega) (by omega))
  have h31 : (3 : ZMod N) ≠ 1 := by
    simpa using (zmod_natCast_ne_of_ne_of_lt (N := N) (a := 3) (b := 1)
      (by omega) (by omega) (by omega))
  have h32 : (3 : ZMod N) ≠ 2 := by
    simpa using (zmod_natCast_ne_of_ne_of_lt (N := N) (a := 3) (b := 2)
      (by omega) (by omega) (by omega))
  have h20 : (2 : ZMod N) ≠ 0 := Ne.symm h02
  have h21 : (2 : ZMod N) ≠ 1 := Ne.symm h12
  by_cases hi0 : i = 0
  · subst i
    norm_num [Lattice.forwardDifference, cubicWitnessConfiguration,
      h01, h02, h12, h20, h21]
  by_cases hi1 : i = 1
  · subst i
    norm_num [Lattice.forwardDifference, cubicWitnessConfiguration,
      h01, h02, h12, h20, h21]
  by_cases hi2 : i = 2
  · subst i
    norm_num [Lattice.forwardDifference, cubicWitnessConfiguration,
      h01, h02, h12, h20, h21, h30, h31, h32]
  · have hplusOne1 : i + 1 ≠ 1 := by
      intro h
      apply hi0
      apply add_right_cancel (b := (1 : ZMod N))
      calc
        i + 1 = 1 := h
        _ = 0 + 1 := by norm_num
    have hplusOne2 : i + 1 ≠ 2 := by
      intro h
      apply hi1
      apply add_right_cancel (b := (1 : ZMod N))
      calc
        i + 1 = 2 := h
        _ = 1 + 1 := by norm_num
    simp [Lattice.forwardDifference, cubicWitnessConfiguration,
      hi0, hi1, hi2, hplusOne1, hplusOne2]

private theorem cubicProfile_sum_cube
    {N : Nat} [NeZero N] (hN : 4 ≤ N) :
    (∑ i : ZMod N,
      (if i = 0 then (1 : Real)
        else if i = 1 then 1 else if i = 2 then -2 else 0) ^ 3) = -6 := by
  have h01 : (0 : ZMod N) ≠ 1 := by
    simpa using (zmod_natCast_ne_of_ne_of_lt (N := N) (a := 0) (b := 1)
      (by omega) (by omega) (by omega))
  have h02 : (0 : ZMod N) ≠ 2 := by
    simpa using (zmod_natCast_ne_of_ne_of_lt (N := N) (a := 0) (b := 2)
      (by omega) (by omega) (by omega))
  have h12 : (1 : ZMod N) ≠ 2 := by
    simpa using (zmod_natCast_ne_of_ne_of_lt (N := N) (a := 1) (b := 2)
      (by omega) (by omega) (by omega))
  classical
  calc
    _ = ∑ i : ZMod N,
        ((if i = 0 then (1 : Real) else 0) +
          (if i = 1 then 1 else 0) + (if i = 2 then -8 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hi0 : i = 0
      · subst i
        simp [h01, h02]
      by_cases hi1 : i = 1
      · subst i
        simp [h12, Ne.symm h01]
      by_cases hi2 : i = 2
      · subst i
        norm_num [Ne.symm h02, Ne.symm h12]
      · simp [hi0, hi1, hi2]
    _ = -6 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      norm_num [Finset.sum_ite_eq']

/-- The local witness has nonzero cubic bond polynomial at every `N ≥ 4`. -/
theorem cubicWitnessConfiguration_sum_forwardDifference_cube
    {N : Nat} [NeZero N] (hN : 4 ≤ N) :
    (∑ i : Lattice.Site N,
      (Lattice.forwardDifference (cubicWitnessConfiguration N) i) ^ 3) = -6 := by
  calc
    _ = ∑ i : ZMod N,
        (if i = 0 then (1 : Real)
          else if i = 1 then 1 else if i = 2 then -2 else 0) ^ 3 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [cubicWitnessConfiguration_forwardDifference hN i]
    _ = -6 := cubicProfile_sum_cube hN

/-- Any physical configuration with nonzero cubic bond sum forces some
ordered physical three-wave tensor to be nonzero by exact modal completeness. -/
theorem hasNonzeroThreeWaveInteractionTensor_of_cubicWitness
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (q : Lattice.Configuration N)
    (hcubic : (∑ i : Lattice.Site N,
      (Lattice.forwardDifference q i) ^ 3) ≠ 0) :
    HasNonzeroThreeWaveInteractionTensor m := by
  let qHilbert : HilbertConfiguration N := WithLp.toLp 2 q
  let amplitude : WeightedConfiguration N :=
    modalCoordinates m (sqrtMassTransform m qHilbert)
  have hexpansion := sum_forwardDifference_pow_eq_interactionTensor
    (n := 3) m amplitude
  have hreconstruction : physicalReconstruction m amplitude = q := by
    change physicalReconstruction m
      (modalCoordinates m (sqrtMassTransform m qHilbert)) = q
    exact (physicalReconstruction_modalCoordinates_sqrtMassTransform
      m qHilbert).trans (by rfl)
  rw [hreconstruction] at hexpansion
  by_contra hnone
  simp only [HasNonzeroThreeWaveInteractionTensor, not_exists] at hnone
  have hzero :
      (∑ modes : Fin 3 → Lattice.Site N,
        interactionTensor m 3 modes * ∏ r, amplitude (modes r)) = 0 := by
    apply Finset.sum_eq_zero
    intro modes _hmodes
    have htensor := hnone
      (fun r ↦ orderedIndexEquiv.symm (modes r))
    have htensorPhysical : interactionTensor m 3 modes = 0 := by
      simpa using htensor
    rw [htensorPhysical, zero_mul]
  rw [hzero] at hexpansion
  exact hcubic hexpansion

/-- At every size `N ≥ 4`, every positive mass realization has a nonzero
physical three-wave interaction tensor. -/
theorem hasNonzeroThreeWaveInteractionTensor_of_four_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hN : 4 ≤ N) : HasNonzeroThreeWaveInteractionTensor m := by
  apply hasNonzeroThreeWaveInteractionTensor_of_cubicWitness m
    (cubicWitnessConfiguration N)
  rw [cubicWitnessConfiguration_sum_forwardDifference_cube hN]
  norm_num

/-- Every positive periodic mass realization of size `N ≥ 3` has a
nonzero physical three-wave interaction tensor.  No spectral assumption is
needed for this physical-tensor statement. -/
theorem hasNonzeroThreeWaveInteractionTensor_of_three_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hN : 3 ≤ N) : HasNonzeroThreeWaveInteractionTensor m := by
  rcases eq_or_lt_of_le hN with hEq | hLt
  · subst N
    exact threeSite_hasNonzeroThreeWaveInteractionTensor m
  · exact hasNonzeroThreeWaveInteractionTensor_of_four_le m (by omega)

/-- Simple spectrum converts the unconditional `N ≥ 3` physical tensor
witness into a strictly positive ordered collision triple. -/
theorem hasPositiveCollisionTriple_of_three_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hN : 3 ≤ N) : HasPositiveCollisionTriple m :=
  hasPositiveCollisionTriple_of_nonzeroTensor m hsimple
    (hasNonzeroThreeWaveInteractionTensor_of_three_le m hN)

/-- The total positive-mode ordered interaction weight is strictly positive
at every simple-spectrum realization of size at least three. -/
theorem positiveOrderedTotalInteractionWeight_pos_of_three_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hN : 3 ≤ N) : 0 < positiveOrderedTotalInteractionWeight m :=
  positiveOrderedTotalInteractionWeight_pos m
    (hasPositiveCollisionTriple_of_three_le m hsimple hN)

/-- Every sign channel has strictly positive bundled collision mass at a
simple-spectrum realization of size at least three. -/
theorem positiveWeightedMismatchFiniteMeasure_mass_pos_of_three_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (sign : Fin 3 → InteractionSign) (hN : 3 ≤ N) :
    0 < (positiveWeightedMismatchFiniteMeasure m sign).mass :=
  positiveWeightedMismatchFiniteMeasure_mass_pos m sign
    (hasPositiveCollisionTriple_of_three_le m hsimple hN)

/-- Nonzero-mass form used by probability normalization. -/
theorem positiveWeightedMismatchFiniteMeasure_mass_ne_zero_of_three_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (sign : Fin 3 → InteractionSign) (hN : 3 ≤ N) :
    (positiveWeightedMismatchFiniteMeasure m sign).mass ≠ 0 :=
  ne_of_gt (positiveWeightedMismatchFiniteMeasure_mass_pos_of_three_le
    m hsimple sign hN)

/-- Exact normalized characteristic-function factorization with its mass
premise discharged by `N ≥ 3` and simple spectrum. -/
theorem charFun_normalizedPositiveWeightedMismatchMeasure_factorization_of_three_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (sign : Fin 3 → InteractionSign) (t : Real) (hN : 3 ≤ N) :
    charFun (normalizedPositiveWeightedMismatchMeasure m sign : Measure Real) t =
      ((positiveWeightedMismatchFiniteMeasure m sign).mass⁻¹ : Real) *
        (∑ j, ∑ l, ∏ r,
          complexWeightedProjectedBondKernel (massWeightedDifferenceMatrix m)
            (harmonicHermitian m)
            (orderedNormalizedPhaseLeg m sign t r) j l) :=
  charFun_normalizedPositiveWeightedMismatchMeasure_factorization
    m sign t
      (positiveWeightedMismatchFiniteMeasure_mass_ne_zero_of_three_le
        m hsimple sign hN)

/-- Varying-size Levy bridge when every size is at least three.  No separate
tensor or collision-mass hypothesis remains. -/
theorem tendsto_varyingSize_normalizedCollision_of_kernelProduct_of_three_le
    (N : Nat → Nat) [hN : ∀ n, NeZero (N n)]
    (m : ∀ n, Lattice.PositiveMassConfig (N n))
    (sign : Fin 3 → InteractionSign)
    (hsize : ∀ n, 3 ≤ N n)
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
  tendsto_varyingSize_normalizedCollision_of_kernelProduct_of_positiveTriple
    N m sign
      (fun n ↦ hasPositiveCollisionTriple_of_three_le
        (m n) (hsimple n) (hsize n)) target hkernel

/-- Tail version of the varying-size Levy bridge.  Finitely many sizes below
three are harmless: only eventual `N n ≥ 3` is required. -/
theorem tendsto_varyingSize_normalizedCollision_of_kernelProduct_of_eventually_three_le
    (N : Nat → Nat) [hN : ∀ n, NeZero (N n)]
    (m : ∀ n, Lattice.PositiveMassConfig (N n))
    (sign : Fin 3 → InteractionSign)
    (hsize : ∀ᶠ n in atTop, 3 ≤ N n)
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
      atTop (𝓝 target) := by
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro t
  refine Tendsto.congr' ?_ (hkernel t)
  filter_upwards [hsize] with n hn
  exact (charFun_normalizedPositiveWeightedMismatchMeasure_factorization_of_three_le
    (m n) (hsimple n) sign t hn).symm

/-- Unnormalized mass-plus-shape tail bridge.  The mass limit and normalized
kernel-product limit remain explicit; eventual `N n ≥ 3` supplies only the
normalization nondegeneracy. -/
theorem tendsto_varyingSize_collisionFiniteMeasure_of_mass_and_kernelProduct_of_eventually_three_le
    (N : Nat → Nat) [hN : ∀ n, NeZero (N n)]
    (m : ∀ n, Lattice.PositiveMassConfig (N n))
    (sign : Fin 3 → InteractionSign)
    (hsize : ∀ᶠ n in atTop, 3 ≤ N n)
    (hsimple : ∀ n, SimpleOrderedSpectrum (harmonicHermitian (m n)))
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
      atTop (𝓝 target) := by
  apply FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
  · simpa [normalizedPositiveWeightedMismatchMeasure] using
      tendsto_varyingSize_normalizedCollision_of_kernelProduct_of_eventually_three_le
        N m sign hsize hsimple target.normalize hkernel
  · exact hmassLimit

end

end ArchonPhysics.FrozenCollisionMassPositivity
