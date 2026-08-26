import ArchonPhysics.RandomMassReducedPhaseInitialData
import ArchonPhysics.PhysicalHarmonicEnergyIdentity

/-!
# A sample-independent nonlinear energy bound for the random initial state

The frozen random-mass initial profile has total physical harmonic energy one.
This module turns that normalization into an explicit upper bound for the
stabilized cubic-leading Hamiltonian at time zero.

The estimate is intentionally coarse.  Harmonic energy one gives
`sum_i (Delta q_i)^2 <= 2`, hence every bond satisfies `|Delta q_i| <= 2`.
Consequently

* `sum_i |Delta q_i|^3 <= 4`, and
* `sum_i (Delta q_i)^4 <= 4`.

For `beta > 2*kappa^2/9`, this yields the system-size- and sample-independent
bound

`H0(kappa,beta,g) = 1 + 4 * |kappa*g/3| + beta*g^2`.

No flow, kinetic limit, or thermalization statement is used.
-/

namespace ArchonPhysics.RandomMassInitialEnergyBound

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.PhysicalHarmonicEnergyIdentity
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassReducedPhaseInitialData
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.OrderedSingleModeProjector
open scoped BigOperators

noncomputable section

/-- Explicit common energy ceiling for every normalized random initial state. -/
def initialEnergyUpperBound (kappa beta g : Real) : Real :=
  1 + 4 * |kappa * g / 3| + beta * g ^ 2

/-- Harmonic energy one controls the total squared bond difference. -/
theorem sum_sq_forwardDifference_le_two_of_harmonicEnergy_eq_one
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (p q : Lattice.Configuration N)
    (henergy : physicalHarmonicHamiltonian m p q = 1) :
    (∑ i : Lattice.Site N, Lattice.forwardDifference q i ^ 2) ≤ 2 := by
  have hkinetic : 0 ≤ Lattice.kineticEnergy m p :=
    Lattice.kineticEnergy_nonneg m p
  have hbond : harmonicBondEnergy q ≤ 1 := by
    unfold physicalHarmonicHamiltonian at henergy
    linarith
  unfold harmonicBondEnergy at hbond
  rw [← Finset.sum_div] at hbond
  linarith

/-- Every individual bond difference has square at most two. -/
theorem forwardDifference_sq_le_two_of_harmonicEnergy_eq_one
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (p q : Lattice.Configuration N)
    (henergy : physicalHarmonicHamiltonian m p q = 1)
    (i : Lattice.Site N) :
    Lattice.forwardDifference q i ^ 2 ≤ 2 := by
  calc
    Lattice.forwardDifference q i ^ 2 ≤
        ∑ j : Lattice.Site N, Lattice.forwardDifference q j ^ 2 :=
      Finset.single_le_sum
        (fun j _hj ↦ sq_nonneg (Lattice.forwardDifference q j))
        (Finset.mem_univ i)
    _ ≤ 2 :=
      sum_sq_forwardDifference_le_two_of_harmonicEnergy_eq_one
        m p q henergy

/-- The normalized harmonic shell gives the convenient coarse pointwise
bound `|Delta q_i| <= 2`. -/
theorem abs_forwardDifference_le_two_of_harmonicEnergy_eq_one
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (p q : Lattice.Configuration N)
    (henergy : physicalHarmonicHamiltonian m p q = 1)
    (i : Lattice.Site N) :
    |Lattice.forwardDifference q i| ≤ 2 := by
  have hsq := forwardDifference_sq_le_two_of_harmonicEnergy_eq_one
    m p q henergy i
  have habsSq : |Lattice.forwardDifference q i| ^ 2 ≤ 2 := by
    simpa only [sq_abs] using hsq
  nlinarith [abs_nonneg (Lattice.forwardDifference q i)]

/-- The sum of absolute cubic bond powers is at most four. -/
theorem sum_abs_cube_forwardDifference_le_four_of_harmonicEnergy_eq_one
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (p q : Lattice.Configuration N)
    (henergy : physicalHarmonicHamiltonian m p q = 1) :
    (∑ i : Lattice.Site N, |Lattice.forwardDifference q i ^ 3|) ≤ 4 := by
  have hterm (i : Lattice.Site N) :
      |Lattice.forwardDifference q i ^ 3| ≤
        2 * Lattice.forwardDifference q i ^ 2 := by
    let x := Lattice.forwardDifference q i
    have habs : |x| ≤ 2 :=
      abs_forwardDifference_le_two_of_harmonicEnergy_eq_one
        m p q henergy i
    calc
      |Lattice.forwardDifference q i ^ 3| = |x| ^ 3 := by
        rw [abs_pow]
      _ = |x| * |x| ^ 2 := by ring
      _ = |x| * x ^ 2 := by rw [sq_abs]
      _ ≤ 2 * x ^ 2 :=
        mul_le_mul_of_nonneg_right habs (sq_nonneg x)
      _ = 2 * Lattice.forwardDifference q i ^ 2 := by rfl
  calc
    (∑ i : Lattice.Site N, |Lattice.forwardDifference q i ^ 3|) ≤
        ∑ i : Lattice.Site N, 2 * Lattice.forwardDifference q i ^ 2 :=
      Finset.sum_le_sum fun i _hi ↦ hterm i
    _ = 2 * (∑ i : Lattice.Site N,
        Lattice.forwardDifference q i ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * 2 := by
      gcongr
      exact sum_sq_forwardDifference_le_two_of_harmonicEnergy_eq_one
        m p q henergy
    _ = 4 := by norm_num

/-- The sum of quartic bond powers is at most four. -/
theorem sum_fourth_forwardDifference_le_four_of_harmonicEnergy_eq_one
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (p q : Lattice.Configuration N)
    (henergy : physicalHarmonicHamiltonian m p q = 1) :
    (∑ i : Lattice.Site N, Lattice.forwardDifference q i ^ 4) ≤ 4 := by
  have hterm (i : Lattice.Site N) :
      Lattice.forwardDifference q i ^ 4 ≤
        2 * Lattice.forwardDifference q i ^ 2 := by
    let x := Lattice.forwardDifference q i
    have hsq : x ^ 2 ≤ 2 :=
      forwardDifference_sq_le_two_of_harmonicEnergy_eq_one
        m p q henergy i
    calc
      Lattice.forwardDifference q i ^ 4 = x ^ 2 * x ^ 2 := by
        simp only [x]
        ring
      _ ≤ 2 * x ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg x)
      _ = 2 * Lattice.forwardDifference q i ^ 2 := by rfl
  calc
    (∑ i : Lattice.Site N, Lattice.forwardDifference q i ^ 4) ≤
        ∑ i : Lattice.Site N, 2 * Lattice.forwardDifference q i ^ 2 :=
      Finset.sum_le_sum fun i _hi ↦ hterm i
    _ = 2 * (∑ i : Lattice.Site N,
        Lattice.forwardDifference q i ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * 2 := by
      gcongr
      exact sum_sq_forwardDifference_le_two_of_harmonicEnergy_eq_one
        m p q henergy
    _ = 4 := by norm_num

/-- Deterministic core estimate: any state of physical harmonic energy one
lies below the explicit stabilized-Hamiltonian ceiling. -/
theorem hamiltonian_le_initialEnergyUpperBound_of_harmonicEnergy_eq_one
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {kappa beta : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (g : Real) (p q : Lattice.Configuration N)
    (henergy : physicalHarmonicHamiltonian m p q = 1) :
    CoerciveLatticeEnergy.hamiltonian m kappa beta g p q ≤
      initialEnergyUpperBound kappa beta g := by
  let d : Lattice.Site N → Real := fun i ↦ Lattice.forwardDifference q i
  have hdecomp :
      CoerciveLatticeEnergy.hamiltonian m kappa beta g p q =
        physicalHarmonicHamiltonian m p q +
          (kappa * g / 3) * (∑ i : Lattice.Site N, d i ^ 3) +
          (beta * g ^ 2 / 4) * (∑ i : Lattice.Site N, d i ^ 4) := by
    unfold CoerciveLatticeEnergy.hamiltonian
      CoerciveLatticeEnergy.potentialEnergy
      CoerciveCubicPotential.potential
      physicalHarmonicHamiltonian harmonicBondEnergy d
    simp_rw [Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have hcubeAbs : |∑ i : Lattice.Site N, d i ^ 3| ≤ 4 := by
    calc
      |∑ i : Lattice.Site N, d i ^ 3| ≤
          ∑ i : Lattice.Site N, |d i ^ 3| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ 4 := by
        simpa [d] using
          sum_abs_cube_forwardDifference_le_four_of_harmonicEnergy_eq_one
            m p q henergy
  have hcubic :
      (kappa * g / 3) * (∑ i : Lattice.Site N, d i ^ 3) ≤
        4 * |kappa * g / 3| := by
    calc
      (kappa * g / 3) * (∑ i : Lattice.Site N, d i ^ 3) ≤
          |(kappa * g / 3) * (∑ i : Lattice.Site N, d i ^ 3)| :=
        le_abs_self _
      _ = |kappa * g / 3| * |∑ i : Lattice.Site N, d i ^ 3| :=
        abs_mul _ _
      _ ≤ |kappa * g / 3| * 4 :=
        mul_le_mul_of_nonneg_left hcubeAbs (abs_nonneg _)
      _ = 4 * |kappa * g / 3| := by ring
  have hquarticSum : (∑ i : Lattice.Site N, d i ^ 4) ≤ 4 := by
    simpa [d] using
      sum_fourth_forwardDifference_le_four_of_harmonicEnergy_eq_one
        m p q henergy
  have hbetaPos : 0 < beta := CoerciveCubicPotential.beta_pos hbeta
  have hquartic :
      (beta * g ^ 2 / 4) * (∑ i : Lattice.Site N, d i ^ 4) ≤
        beta * g ^ 2 := by
    calc
      (beta * g ^ 2 / 4) * (∑ i : Lattice.Site N, d i ^ 4) ≤
          (beta * g ^ 2 / 4) * 4 := by
        exact mul_le_mul_of_nonneg_left hquarticSum (by positivity)
      _ = beta * g ^ 2 := by ring
  rw [hdecomp, henergy]
  unfold initialEnergyUpperBound
  linarith

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The frozen random reduced initial point has the common explicit energy
ceiling on every simple realization. -/
theorem reducedHamiltonian_reducedInitialStateOfSimple_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    {kappa beta : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (g : Real) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega))) :
    reducedHamiltonian
        (ensemble.restrictPositiveMass (N := N) omega)
        kappa beta g
        (reducedInitialStateOfSimple ensemble a omega hsimple) ≤
      initialEnergyUpperBound kappa beta g := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  have hmodal :
      (∑ k : OrderedModeIndex N,
        harmonicOrderedPhysicalModeEnergy
          (ensemble.restrictPositiveMass (N := N))
          (initialPhysicalPosition ensemble a)
          (initialPhysicalMomentum ensemble a) omega k) = 1 := by
    calc
      (∑ k : OrderedModeIndex N,
        harmonicOrderedPhysicalModeEnergy
          (ensemble.restrictPositiveMass (N := N))
          (initialPhysicalPosition ensemble a)
          (initialPhysicalMomentum ensemble a) omega k) =
          ∑ k : OrderedModeIndex N, orderedTargetEnergy N a k := by
        apply Finset.sum_congr rfl
        intro k _hk
        exact harmonicOrderedPhysicalModeEnergy_initial_eq_target
          ensemble hN ha0 ha1 omega hsimple k
      _ = 1 := sum_orderedTargetEnergy_eq_one hN a
  have hharmonic :
      physicalHarmonicHamiltonian m
        (initialPhysicalMomentum ensemble a omega)
        (initialPhysicalPosition ensemble a omega) = 1 := by
    rw [← hmodal]
    exact (sum_harmonicOrderedPhysicalModeEnergy_eq_physical_of_simple
      (ensemble.restrictPositiveMass (N := N))
      (initialPhysicalPosition ensemble a)
      (initialPhysicalMomentum ensemble a) omega
      (by simpa [harmonicHermitianSample, harmonicHermitian, m] using hsimple)).symm
  unfold reducedHamiltonian reducedInitialStateOfSimple
  exact hamiltonian_le_initialEnergyUpperBound_of_harmonicEnergy_eq_one
    m hbeta g
    (initialPhysicalMomentum ensemble a omega)
    (initialPhysicalPosition ensemble a omega) hharmonic

/-- Formula-level lock for the common ceiling. -/
theorem initialEnergyUpperBound_spec (kappa beta g : Real) :
    initialEnergyUpperBound kappa beta g =
      1 + 4 * |kappa * g / 3| + beta * g ^ 2 := rfl

end

end ArchonPhysics.RandomMassInitialEnergyBound
