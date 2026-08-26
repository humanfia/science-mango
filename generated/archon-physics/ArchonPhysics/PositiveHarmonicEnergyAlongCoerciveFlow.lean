import ArchonPhysics.RandomMassPositiveLateWindowObservable
import ArchonPhysics.RandomMassInitialEnergyBound
import ArchonPhysics.TranslationZeroModeEnergy
import ArchonPhysics.CanonicalReducedParametricGlobalFlow

/-!
# Strict positivity of harmonic energy along the genuine coercive flow

For the stabilized cubic-leading chain, strict bond coercivity makes the
nonlinear Hamiltonian of every unit-harmonic-energy initial state strictly
positive.  Energy conservation along a genuine reduced Hamilton trajectory
then prevents the physical harmonic energy from vanishing at any later time:
vanishing harmonic energy would force both canonical momentum and every bond
difference to vanish, hence would force the full nonlinear Hamiltonian to be
zero.

The second half integrates the strictly positive reduced positive-mode energy
over a genuine late window.  A final adapter transfers the statement to an
ambient sampled flow only under an explicit all-time matching hypothesis; no
claim is made on cutoff trajectories away from that matched orbit.
-/

namespace ArchonPhysics.PositiveHarmonicEnergyAlongCoerciveFlow

open ArchonPhysics
open ArchonPhysics.CanonicalReducedParametricGlobalFlow
open ArchonPhysics.CoerciveCubicPotential
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.GlobalRandomMassModalObservable
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedHarmonicEnergy
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.PhysicalHarmonicEnergyIdentity
open ArchonPhysics.RandomMassPositiveLateWindowObservable
open ArchonPhysics.TranslationZeroModeEnergy
open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The physical harmonic Hamiltonian restricted to the reduced phase space. -/
def reducedPhysicalHarmonicEnergy
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (z : ReducedPhaseSpace m) : Real :=
  physicalHarmonicHamiltonian m
    (asConfiguration (z.2 : HilbertConfiguration N))
    (asConfiguration (z.1 : HilbertConfiguration N))

theorem reducedMassWeightedHarmonicEnergy_eq_reducedPhysical
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (z : ReducedPhaseSpace m) :
    reducedMassWeightedHarmonicEnergy m z.1 z.2 =
      reducedPhysicalHarmonicEnergy m z := by
  unfold reducedMassWeightedHarmonicEnergy reducedPhysicalHarmonicEnergy
  exact massWeightedEnergy_eq_physicalHarmonicHamiltonian
    m (z.1 : HilbertConfiguration N) (z.2 : HilbertConfiguration N)

/-- Physical harmonic energy is nonnegative at every reduced state. -/
theorem reducedPhysicalHarmonicEnergy_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (z : ReducedPhaseSpace m) :
    0 ≤ reducedPhysicalHarmonicEnergy m z := by
  unfold reducedPhysicalHarmonicEnergy physicalHarmonicHamiltonian
    harmonicBondEnergy
  exact add_nonneg
    (Lattice.kineticEnergy_nonneg m
      (asConfiguration (z.2 : HilbertConfiguration N)))
    (Finset.sum_nonneg fun i _hi ↦
      div_nonneg (sq_nonneg _) (by norm_num))

/-- Twice the strict coercivity constant is at most one. -/
theorem two_mul_coercivityConstant_le_one
    {kappa beta : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    2 * coercivityConstant kappa beta ≤ 1 := by
  have hbetaPos : 0 < beta := beta_pos hbeta
  have hfrac : 0 ≤ kappa ^ 2 / (9 * beta) := by positivity
  unfold coercivityConstant
  linarith

/-- Quantitative comparison of the stabilized and harmonic Hamiltonians. -/
theorem two_coercivity_mul_physicalHarmonicEnergy_le_hamiltonian
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {kappa beta : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (g : Real) (p q : Lattice.Configuration N) :
    2 * coercivityConstant kappa beta *
        physicalHarmonicHamiltonian m p q ≤
      CoerciveLatticeEnergy.hamiltonian m kappa beta g p q := by
  let K := Lattice.kineticEnergy m p
  let S := ∑ i : Lattice.Site N, Lattice.forwardDifference q i ^ 2
  have hK : 0 ≤ K := Lattice.kineticEnergy_nonneg m p
  have htwo : 2 * coercivityConstant kappa beta ≤ 1 :=
    two_mul_coercivityConstant_le_one hbeta
  have hkinetic : 2 * coercivityConstant kappa beta * K ≤ K := by
    nlinarith
  have hpotential : coercivityConstant kappa beta * S ≤
      CoerciveLatticeEnergy.potentialEnergy kappa beta g q := by
    simpa [S] using
      CoerciveLatticeEnergy.potentialEnergy_lower_bound hbeta g q
  have hbond : harmonicBondEnergy q = S / 2 := by
    unfold harmonicBondEnergy S
    rw [← Finset.sum_div]
  unfold CoerciveLatticeEnergy.hamiltonian physicalHarmonicHamiltonian
  rw [hbond]
  calc
    2 * coercivityConstant kappa beta *
        (Lattice.kineticEnergy m p + S / 2) =
        2 * coercivityConstant kappa beta * K +
          coercivityConstant kappa beta * S := by
      simp only [K]
      ring
    _ ≤ K + CoerciveLatticeEnergy.potentialEnergy kappa beta g q :=
      add_le_add hkinetic hpotential
    _ = Lattice.kineticEnergy m p +
        CoerciveLatticeEnergy.potentialEnergy kappa beta g q := by rfl

/-- Unit physical harmonic energy forces strictly positive nonlinear energy. -/
theorem reducedHamiltonian_pos_of_reducedPhysicalHarmonicEnergy_eq_one
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {kappa beta : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (g : Real) (z : ReducedPhaseSpace m)
    (hunit : reducedPhysicalHarmonicEnergy m z = 1) :
    0 < reducedHamiltonian m kappa beta g z := by
  have hlower :=
    two_coercivity_mul_physicalHarmonicEnergy_le_hamiltonian
      m hbeta g
      (asConfiguration (z.2 : HilbertConfiguration N))
      (asConfiguration (z.1 : HilbertConfiguration N))
  have hc : 0 < coercivityConstant kappa beta :=
    coercivityConstant_pos hbeta
  unfold reducedHamiltonian
  rw [show physicalHarmonicHamiltonian m
      (asConfiguration (z.2 : HilbertConfiguration N))
      (asConfiguration (z.1 : HilbertConfiguration N)) = 1 from hunit]
    at hlower
  nlinarith

/-- If physical harmonic energy vanishes, then the stabilized Hamiltonian
vanishes as well, for arbitrary nonlinear coefficients. -/
theorem reducedHamiltonian_eq_zero_of_reducedPhysicalHarmonicEnergy_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa beta g : Real) (z : ReducedPhaseSpace m)
    (hzero : reducedPhysicalHarmonicEnergy m z = 0) :
    reducedHamiltonian m kappa beta g z = 0 := by
  let p : Lattice.Configuration N :=
    asConfiguration (z.2 : HilbertConfiguration N)
  let q : Lattice.Configuration N :=
    asConfiguration (z.1 : HilbertConfiguration N)
  have hKnonneg : 0 ≤ Lattice.kineticEnergy m p :=
    Lattice.kineticEnergy_nonneg m p
  have hBnonneg : 0 ≤ harmonicBondEnergy q := by
    unfold harmonicBondEnergy
    exact Finset.sum_nonneg fun i _hi ↦
      div_nonneg (sq_nonneg _) (by norm_num)
  have hsum : Lattice.kineticEnergy m p + harmonicBondEnergy q = 0 := by
    simpa [reducedPhysicalHarmonicEnergy, physicalHarmonicHamiltonian, p, q]
      using hzero
  have hKzero : Lattice.kineticEnergy m p = 0 := by linarith
  have hBzero : harmonicBondEnergy q = 0 := by linarith
  have hSqSum : (∑ i : Lattice.Site N,
      Lattice.forwardDifference q i ^ 2) = 0 := by
    unfold harmonicBondEnergy at hBzero
    rw [← Finset.sum_div] at hBzero
    linarith
  have hdifference (i : Lattice.Site N) :
      Lattice.forwardDifference q i = 0 := by
    have hsingle : Lattice.forwardDifference q i ^ 2 ≤
        ∑ j : Lattice.Site N, Lattice.forwardDifference q j ^ 2 :=
      Finset.single_le_sum
        (fun j _hj ↦ sq_nonneg (Lattice.forwardDifference q j))
        (Finset.mem_univ i)
    rw [hSqSum] at hsingle
    nlinarith [sq_nonneg (Lattice.forwardDifference q i)]
  unfold reducedHamiltonian CoerciveLatticeEnergy.hamiltonian
    CoerciveLatticeEnergy.potentialEnergy CoerciveCubicPotential.potential
  change Lattice.kineticEnergy m p +
      (∑ i : Lattice.Site N,
        (Lattice.forwardDifference q i ^ 2 / 2 +
          (kappa * g / 3) * Lattice.forwardDifference q i ^ 3 +
          (beta * g ^ 2 / 4) * Lattice.forwardDifference q i ^ 4)) = 0
  rw [hKzero]
  simp [hdifference]

/-- Along a genuine two-sided reduced Hamilton trajectory issued from unit
physical harmonic energy, the physical harmonic energy is strictly positive
at every real time. -/
theorem reducedPhysicalHarmonicEnergy_pos_along_trajectory
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {kappa beta : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (g : Real) (z0 : ReducedPhaseSpace m)
    (z : Real → ReducedPhaseSpace m)
    (hz0 : z 0 = z0)
    (hz : ∀ t, HasDerivAt z
      (reducedVectorField m kappa beta g (z t)) t)
    (hunit : reducedPhysicalHarmonicEnergy m z0 = 1)
    (t : Real) :
    0 < reducedPhysicalHarmonicEnergy m (z t) := by
  have hinitialPos : 0 < reducedHamiltonian m kappa beta g z0 :=
    reducedHamiltonian_pos_of_reducedPhysicalHarmonicEnergy_eq_one
      m hbeta g z0 hunit
  have hconserved : reducedHamiltonian m kappa beta g (z t) =
      reducedHamiltonian m kappa beta g z0 :=
    reducedHamiltonian_eq_initial_of_global_trajectory
      m kappa beta g z0 hz0 hz t
  have hcurrentPos : 0 < reducedHamiltonian m kappa beta g (z t) := by
    rw [hconserved]
    exact hinitialPos
  have hnonneg := reducedPhysicalHarmonicEnergy_nonneg m (z t)
  apply lt_of_le_of_ne hnonneg
  intro hEq
  have hzero : reducedPhysicalHarmonicEnergy m (z t) = 0 := hEq.symm
  have hHamiltonZero :=
    reducedHamiltonian_eq_zero_of_reducedPhysicalHarmonicEnergy_eq_zero
      m kappa beta g (z t) hzero
  linarith

/-- Positive ordered physical energy profile of a genuine reduced path. -/
def reducedPositiveOrderedEnergyProfile
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (z : Real → ReducedPhaseSpace m) (t : Real)
    (k : OrderedModeIndex N) : Real :=
  if k ∈ positiveModeIndices (harmonicHermitian m) then
    reducedPhysicalOrderedModeEnergy m (z t) k
  else 0

/-- Genuine reduced-path counterpart of the sampled late-window total. -/
def reducedPositiveLateWindowTotalWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (z : Real → ReducedPhaseSpace m) (mu T : Real) : Real :=
  totalWeight (lateWindowAverage
    (reducedPositiveOrderedEnergyProfile m z) mu T)

theorem sum_reducedPositiveOrderedEnergyProfile_eq_physical
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (z : Real → ReducedPhaseSpace m) (t : Real) :
    (∑ k : OrderedModeIndex N,
      reducedPositiveOrderedEnergyProfile m z t k) =
      reducedPhysicalHarmonicEnergy m (z t) := by
  let zeroMode := lastOrderedIndex (ι := Lattice.Site N)
  have hzero : orderedEigenvalue (harmonicHermitian m) zeroMode = 0 :=
    harmonic_lastOrderedEigenvalue_eq_zero m
  rw [← reducedMassWeightedHarmonicEnergy_eq_reducedPhysical m (z t)]
  rw [← sum_positive_physicalHarmonicModeEnergy_eq_reducedEnergy
    m hsimple zeroMode hzero (z t).1 (z t).2]
  unfold reducedPositiveOrderedEnergyProfile reducedPhysicalOrderedModeEnergy
  rw [show harmonicHermitianSample (fun _ : Unit ↦ m) () =
    harmonicHermitian m by rfl]
  exact Fintype.sum_ite_mem _ _

theorem continuous_reducedPositiveOrderedEnergyProfile
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (z : Real → ReducedPhaseSpace m) (hz : Continuous z)
    (k : OrderedModeIndex N) :
    Continuous fun t ↦ reducedPositiveOrderedEnergyProfile m z t k := by
  by_cases hk : k ∈ positiveModeIndices (harmonicHermitian m)
  · simp only [reducedPositiveOrderedEnergyProfile, hk, if_true]
    unfold reducedPhysicalOrderedModeEnergy orderedHarmonicModeEnergy
      OrderedSingleModeProjector.orderedModeEnergy
      OrderedSingleModeProjector.orderedModeProjectedState
      SpectralBandEnergyObservable.coordinateEnergy
    fun_prop
  · simpa [reducedPositiveOrderedEnergyProfile, hk] using
      (continuous_const : Continuous (fun _ : Real ↦ (0 : Real)))

/-- The genuine reduced positive-mode late-window total is strictly positive
on every nondegenerate late window. -/
theorem reducedPositiveLateWindowTotalWeight_pos
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {kappa beta : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (g : Real) (z0 : ReducedPhaseSpace m)
    (z : Real → ReducedPhaseSpace m)
    (hz0 : z 0 = z0)
    (hz : ∀ t, HasDerivAt z
      (reducedVectorField m kappa beta g (z t)) t)
    (hunit : reducedPhysicalHarmonicEnergy m z0 = 1)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (mu T : Real) (_hmu : 0 ≤ mu) (hmuOne : mu < 1) (hT : 0 < T) :
    0 < reducedPositiveLateWindowTotalWeight m z mu T := by
  have hzcont : Continuous z :=
    continuous_iff_continuousAt.mpr fun t ↦ (hz t).continuousAt
  have hmodeInt (k : OrderedModeIndex N) :
      IntervalIntegrable
        (fun t ↦ reducedPositiveOrderedEnergyProfile m z t k)
        volume (mu * T) T :=
    (continuous_reducedPositiveOrderedEnergyProfile m z hzcont k).intervalIntegrable (mu * T) T
  have hsumContinuous : Continuous
      (fun t ↦ ∑ k : OrderedModeIndex N,
        reducedPositiveOrderedEnergyProfile m z t k) := by
    exact continuous_finsetSum Finset.univ fun k _hk ↦
      continuous_reducedPositiveOrderedEnergyProfile m z hzcont k
  have hsumInt : IntervalIntegrable
      (fun t ↦ ∑ k : OrderedModeIndex N,
        reducedPositiveOrderedEnergyProfile m z t k)
      volume (mu * T) T :=
    hsumContinuous.intervalIntegrable (mu * T) T
  have hinterval : mu * T < T := by
    nlinarith
  have hintegral : 0 < ∫ t in mu * T..T,
      (∑ k : OrderedModeIndex N,
        reducedPositiveOrderedEnergyProfile m z t k) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos hsumInt
    · intro t
      rw [sum_reducedPositiveOrderedEnergyProfile_eq_physical
        m hsimple z t]
      exact reducedPhysicalHarmonicEnergy_pos_along_trajectory
        m hbeta g z0 z hz0 hz hunit t
    · exact hinterval
  unfold reducedPositiveLateWindowTotalWeight totalWeight lateWindowAverage
  rw [← Finset.mul_sum]
  rw [← intervalIntegral.integral_finsetSum
    (fun k _hk ↦ hmodeInt k)]
  have hfactor : 0 < ((1 - mu) * T)⁻¹ := by positivity
  exact mul_pos hfactor hintegral

variable {S : Type*}

/-- Explicit matching adapter: an ambient sampled flow has the same strictly
positive late-window total as the genuine reduced trajectory only when it is
known to equal the reduced embedding for every time. -/
theorem sampledPositiveLateWindowTotalWeight_eq_reduced_of_match
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa beta g : Real)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (s : S) (z : Real → ReducedPhaseSpace m)
    (hmatch : ∀ t, flow (initial s, t) =
      embedReducedPoint m kappa beta g (z t))
    (mu T : Real) :
    sampledPositiveLateWindowTotalWeight
        (fun _ : S ↦ m) initial flow mu T s =
      reducedPositiveLateWindowTotalWeight m z mu T := by
  unfold sampledPositiveLateWindowTotalWeight
    sampledPositiveLateWindowAverage reducedPositiveLateWindowTotalWeight
    totalWeight lateWindowAverage
  apply Finset.sum_congr rfl
  intro k _hk
  change ((1 - mu) * T)⁻¹ *
      (∫ t in mu * T..T,
        sampledPositivePhysicalOrderedEnergyProfileAlongFlow
          (fun _ : S ↦ m) initial flow (s, t) k) =
    ((1 - mu) * T)⁻¹ *
      (∫ t in mu * T..T, reducedPositiveOrderedEnergyProfile m z t k)
  congr 1
  apply intervalIntegral.integral_congr
  intro t _ht
  unfold sampledPositivePhysicalOrderedEnergyProfileAlongFlow
    reducedPositiveOrderedEnergyProfile
  change (if k ∈ positiveModeIndices
      (harmonicHermitianSample (fun _ : S ↦ m) s) then
        sampledPhysicalOrderedModeEnergyAlongFlow
          (fun _ : S ↦ m) initial flow (s, t) k
      else 0) =
    if k ∈ positiveModeIndices (harmonicHermitian m) then
      reducedPhysicalOrderedModeEnergy m (z t) k
    else 0
  rw [show harmonicHermitianSample (fun _ : S ↦ m) s =
    harmonicHermitian m by rfl]
  split_ifs with hk
  · exact sampledPhysicalOrderedModeEnergyAlongFlow_eq_reduced_of_match
      m kappa beta g (z t) initial flow (s, t) (hmatch t) k
  · rfl

/-- Under explicit all-time matching, the ambient sampled positive-mode
late-window denominator is strictly positive. -/
theorem sampledPositiveLateWindowTotalWeight_pos_of_match
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {kappa beta : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (g : Real) (z0 : ReducedPhaseSpace m)
    (z : Real → ReducedPhaseSpace m)
    (hz0 : z 0 = z0)
    (hz : ∀ t, HasDerivAt z
      (reducedVectorField m kappa beta g (z t)) t)
    (hunit : reducedPhysicalHarmonicEnergy m z0 = 1)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (s : S)
    (hmatch : ∀ t, flow (initial s, t) =
      embedReducedPoint m kappa beta g (z t))
    (mu T : Real) (hmu : 0 ≤ mu) (hmuOne : mu < 1) (hT : 0 < T) :
    0 < sampledPositiveLateWindowTotalWeight
      (fun _ : S ↦ m) initial flow mu T s := by
  rw [sampledPositiveLateWindowTotalWeight_eq_reduced_of_match
    m kappa beta g initial flow s z hmatch mu T]
  exact reducedPositiveLateWindowTotalWeight_pos
    m hbeta g z0 z hz0 hz hunit hsimple mu T hmu hmuOne hT

end

end ArchonPhysics.PositiveHarmonicEnergyAlongCoerciveFlow
