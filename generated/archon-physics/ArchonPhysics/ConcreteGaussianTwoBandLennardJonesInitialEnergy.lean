import ArchonPhysics.ConcreteGaussianTwoBandPhysicalInitialData
import ArchonPhysics.LennardJonesQuantitativeTaylorTube

/-!
# Exact Lennard--Jones energy of the concrete Gaussian two-band initial state

The existing physical initial-data construction has unit harmonic spring
constant and, on a simple mass realization, total harmonic energy exactly
`N * epsilon`.  To compare this number with the exact Lennard--Jones
Hamiltonian we therefore normalize the well depth to

`D = r0^2 / 72`,

for which the Lennard--Jones harmonic stiffness is exactly one.

On a bond tube `|x_i| <= rho * r0` and a (possibly sharper) displacement
bound `|x_i| <= amplitude`, the exact potential differs from its unit
quadratic part by

* an explicit cubic contribution of order `amplitude^3`,
* an explicit quartic contribution of order `amplitude^4`, and
* the already grounded exact Lennard--Jones/FPUT remainder of order `rho^5`.

We sum this pointwise estimate and specialize it to the constructed physical
initial state.  Thus the input parameter `epsilon` differs from the exact LJ
energy density by the displayed per-bond error.  The tube is an explicit
hypothesis; this file does not claim that every random initial sample lies in
it, nor does it assert any dynamical propagation or thermalization result.
-/

namespace ArchonPhysics.ConcreteGaussianTwoBandLennardJonesInitialEnergy

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ConcreteGaussianTwoBandInitialEnsemble
open ArchonPhysics.ConcreteGaussianTwoBandPhysicalInitialData
open ArchonPhysics.LennardJonesPotential
open ArchonPhysics.LennardJonesQuantitativeTaylorTube
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhysicalHarmonicEnergyIdentity
open scoped BigOperators

noncomputable section

/-- A per-bond envelope for exact LJ minus a unit-stiffness harmonic bond.
The three summands respectively bound the cubic, quartic, and exact
fifth-order Taylor-remainder contributions. -/
def harmonicComparisonPerBondBound
    (depth r0 rho amplitude : Real) : Real :=
  |alphaCoefficient depth r0| * amplitude ^ 3 / 3 +
    |betaCoefficient depth r0| * amplitude ^ 4 / 4 +
    depth * fourthOrderTubeConstant rho * rho ^ 5

theorem harmonicComparisonPerBondBound_nonneg
    {depth r0 rho amplitude : Real}
    (hdepth : 0 <= depth) (hrho0 : 0 <= rho)
    (hrho1 : rho < 1) (hamplitude : 0 <= amplitude) :
    0 <= harmonicComparisonPerBondBound depth r0 rho amplitude := by
  unfold harmonicComparisonPerBondBound
  apply add_nonneg
  · exact add_nonneg
      (div_nonneg
        (mul_nonneg (abs_nonneg _) (pow_nonneg hamplitude 3)) (by norm_num))
      (div_nonneg
        (mul_nonneg (abs_nonneg _) (pow_nonneg hamplitude 4)) (by norm_num))
  · exact mul_nonneg
      (mul_nonneg hdepth (fourthOrderTubeConstant_nonneg hrho0 hrho1))
      (pow_nonneg hrho0 5)

/-- Once the LJ curvature is normalized to one, subtracting the harmonic
quadratic term leaves exactly its local cubic and quartic FPUT terms. -/
theorem localAlphaBetaPotential_sub_unitHarmonic
    {depth r0 x : Real}
    (hstiffness : harmonicStiffness depth r0 = 1) :
    localAlphaBetaPotential depth r0 x - x ^ 2 / 2 =
      alphaCoefficient depth r0 * x ^ 3 / 3 +
        betaCoefficient depth r0 * x ^ 4 / 4 := by
  unfold localAlphaBetaPotential
  rw [hstiffness]
  ring

/-- One-click pointwise comparison of an exact LJ bond with the unit
quadratic bond.  The exact LJ/FPUT remainder is fifth order; because the LJ
potential is asymmetric, the full LJ/harmonic difference honestly starts at
third order. -/
theorem abs_bondPotential_sub_unitHarmonic_le
    {depth r0 rho amplitude x : Real}
    (hdepth : 0 <= depth) (hr0 : 0 < r0)
    (hrho0 : 0 <= rho) (hrho1 : rho < 1)
    (_hamplitude0 : 0 <= amplitude)
    (hstiffness : harmonicStiffness depth r0 = 1)
    (htube : |x| <= rho * r0) (hamplitude : |x| <= amplitude) :
    |bondPotential depth r0 x - x ^ 2 / 2| <=
      harmonicComparisonPerBondBound depth r0 rho amplitude := by
  have hrem := abs_bondPotential_sub_localAlphaBetaPotential_le
    hdepth hr0 hrho0 hrho1 htube
  have hratio : |x| / r0 <= rho := (div_le_iff₀ hr0).2 htube
  have hratio0 : 0 <= |x| / r0 := div_nonneg (abs_nonneg x) hr0.le
  have hpow5 : (|x| / r0) ^ 5 <= rho ^ 5 :=
    pow_le_pow_left₀ hratio0 hratio 5
  have hremainder :
      |bondPotential depth r0 x - localAlphaBetaPotential depth r0 x| <=
        depth * fourthOrderTubeConstant rho * rho ^ 5 :=
    hrem.trans (mul_le_mul_of_nonneg_left hpow5
      (mul_nonneg hdepth (fourthOrderTubeConstant_nonneg hrho0 hrho1)))
  have hpow3 : |x| ^ 3 <= amplitude ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg x) hamplitude 3
  have hcubic :
      |alphaCoefficient depth r0 * x ^ 3 / 3| <=
        |alphaCoefficient depth r0| * amplitude ^ 3 / 3 := by
    calc
      |alphaCoefficient depth r0 * x ^ 3 / 3| =
          |alphaCoefficient depth r0| * |x| ^ 3 / 3 := by
        rw [abs_div, abs_mul, abs_pow]
        norm_num
      _ <= |alphaCoefficient depth r0| * amplitude ^ 3 / 3 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow3 (abs_nonneg _)) (by norm_num)
  have hpow4 : |x| ^ 4 <= amplitude ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg x) hamplitude 4
  have hquartic :
      |betaCoefficient depth r0 * x ^ 4 / 4| <=
        |betaCoefficient depth r0| * amplitude ^ 4 / 4 := by
    calc
      |betaCoefficient depth r0 * x ^ 4 / 4| =
          |betaCoefficient depth r0| * |x| ^ 4 / 4 := by
        rw [abs_div, abs_mul, abs_pow]
        norm_num
      _ <= |betaCoefficient depth r0| * amplitude ^ 4 / 4 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow4 (abs_nonneg _)) (by norm_num)
  have hsplit :
      bondPotential depth r0 x - x ^ 2 / 2 =
        (bondPotential depth r0 x - localAlphaBetaPotential depth r0 x) +
          (alphaCoefficient depth r0 * x ^ 3 / 3 +
            betaCoefficient depth r0 * x ^ 4 / 4) := by
    rw [<- localAlphaBetaPotential_sub_unitHarmonic hstiffness]
    ring
  rw [hsplit]
  calc
    |(bondPotential depth r0 x - localAlphaBetaPotential depth r0 x) +
        (alphaCoefficient depth r0 * x ^ 3 / 3 +
          betaCoefficient depth r0 * x ^ 4 / 4)| <=
      |bondPotential depth r0 x - localAlphaBetaPotential depth r0 x| +
        |alphaCoefficient depth r0 * x ^ 3 / 3 +
          betaCoefficient depth r0 * x ^ 4 / 4| := abs_add_le _ _
    _ <= |bondPotential depth r0 x - localAlphaBetaPotential depth r0 x| +
        (|alphaCoefficient depth r0 * x ^ 3 / 3| +
          |betaCoefficient depth r0 * x ^ 4 / 4|) :=
      add_le_add le_rfl (abs_add_le _ _)
    _ <= depth * fourthOrderTubeConstant rho * rho ^ 5 +
        (|alphaCoefficient depth r0| * amplitude ^ 3 / 3 +
          |betaCoefficient depth r0| * amplitude ^ 4 / 4) :=
      add_le_add hremainder (add_le_add hcubic hquartic)
    _ = harmonicComparisonPerBondBound depth r0 rho amplitude := by
      unfold harmonicComparisonPerBondBound
      ring

/-- Finite periodic Hamiltonian comparison.  Kinetic energies cancel exactly,
so summing the pointwise potential estimate gives an extensive error bound. -/
theorem abs_periodicRandomMassHamiltonian_sub_physicalHarmonic_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (p q : Lattice.Configuration N)
    {depth r0 rho amplitude : Real}
    (hdepth : 0 <= depth) (hr0 : 0 < r0)
    (hrho0 : 0 <= rho) (hrho1 : rho < 1)
    (hamplitude0 : 0 <= amplitude)
    (hstiffness : harmonicStiffness depth r0 = 1)
    (htube : forall i, |Lattice.forwardDifference q i| <= rho * r0)
    (hamplitude : forall i,
      |Lattice.forwardDifference q i| <= amplitude) :
    |periodicRandomMassHamiltonian m depth r0 p q -
        physicalHarmonicHamiltonian m p q| <=
      (N : Real) * harmonicComparisonPerBondBound depth r0 rho amplitude := by
  have hidentity :
      periodicRandomMassHamiltonian m depth r0 p q -
          physicalHarmonicHamiltonian m p q =
        ∑ i : Lattice.Site N,
          (bondPotential depth r0 (Lattice.forwardDifference q i) -
            Lattice.forwardDifference q i ^ 2 / 2) := by
    unfold periodicRandomMassHamiltonian physicalHarmonicHamiltonian
    unfold periodicPotentialEnergy harmonicBondEnergy
    rw [Finset.sum_sub_distrib]
    ring
  rw [hidentity]
  calc
    |∑ i : Lattice.Site N,
        (bondPotential depth r0 (Lattice.forwardDifference q i) -
          Lattice.forwardDifference q i ^ 2 / 2)| <=
      ∑ i : Lattice.Site N,
        |bondPotential depth r0 (Lattice.forwardDifference q i) -
          Lattice.forwardDifference q i ^ 2 / 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _i : Lattice.Site N,
        harmonicComparisonPerBondBound depth r0 rho amplitude :=
      Finset.sum_le_sum fun i _ =>
        abs_bondPotential_sub_unitHarmonic_le hdepth hr0 hrho0 hrho1
          hamplitude0 hstiffness (htube i) (hamplitude i)
    _ = (N : Real) *
        harmonicComparisonPerBondBound depth r0 rho amplitude := by
      simp [Lattice.Site, nsmul_eq_mul]

/-! ## Unit-stiffness LJ normalization and the concrete random initial state -/

/-- LJ well depth whose equilibrium harmonic stiffness is one. -/
def unitStiffnessDepth (r0 : Real) : Real :=
  r0 ^ 2 / 72

theorem unitStiffnessDepth_nonneg (r0 : Real) :
    0 <= unitStiffnessDepth r0 := by
  unfold unitStiffnessDepth
  positivity

theorem harmonicStiffness_unitStiffnessDepth
    {r0 : Real} (hr0 : 0 < r0) :
    harmonicStiffness (unitStiffnessDepth r0) r0 = 1 := by
  unfold harmonicStiffness unitStiffnessDepth
  field_simp [ne_of_gt hr0]

/-- The exact LJ Hamiltonian of the already constructed Gaussian two-band
physical initial state. -/
def exactLJInitialHamiltonian {N : Nat} [NeZero N]
    (r0 energyDensity : Real) (sample : SampleSpace) : Real :=
  periodicRandomMassHamiltonian (massSample (N := N) sample)
    (unitStiffnessDepth r0) r0
    (asConfiguration (initialPhysicalMomentum (N := N) energyDensity sample))
    (asConfiguration (initialPhysicalPosition (N := N) energyDensity sample))

/-- Exact LJ initial energy per site. -/
def exactLJInitialEnergyDensity {N : Nat} [NeZero N]
    (r0 energyDensity : Real) (sample : SampleSpace) : Real :=
  exactLJInitialHamiltonian (N := N) r0 energyDensity sample / (N : Real)

/-- On a simple realization, the exact initial LJ total energy differs from
the prescribed harmonic total `N * epsilon` by at most the summed per-bond
third-plus-fourth-plus-fifth-order envelope. -/
theorem abs_exactLJInitialHamiltonian_sub_prescribedTotal_le
    {N : Nat} [NeZero N] (hN : 3 <= N)
    {energyDensity : Real} (henergyDensity : 0 <= energyDensity)
    (sample : SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (massSample (N := N) sample)))
    {r0 rho amplitude : Real}
    (hr0 : 0 < r0) (hrho0 : 0 <= rho) (hrho1 : rho < 1)
    (hamplitude0 : 0 <= amplitude)
    (htube : forall i : Lattice.Site N,
      |Lattice.forwardDifference
        (asConfiguration (initialPhysicalPosition (N := N) energyDensity sample)) i| <=
          rho * r0)
    (hamplitude : forall i : Lattice.Site N,
      |Lattice.forwardDifference
        (asConfiguration (initialPhysicalPosition (N := N) energyDensity sample)) i| <=
          amplitude) :
    |exactLJInitialHamiltonian (N := N) r0 energyDensity sample -
        (N : Real) * energyDensity| <=
      (N : Real) * harmonicComparisonPerBondBound
        (unitStiffnessDepth r0) r0 rho amplitude := by
  have hcomparison :=
    abs_periodicRandomMassHamiltonian_sub_physicalHarmonic_le
      (massSample (N := N) sample)
      (asConfiguration (initialPhysicalMomentum (N := N) energyDensity sample))
      (asConfiguration (initialPhysicalPosition (N := N) energyDensity sample))
      (unitStiffnessDepth_nonneg r0) hr0 hrho0 hrho1 hamplitude0
      (harmonicStiffness_unitStiffnessDepth hr0) htube hamplitude
  have hharmonic := physicalHarmonicHamiltonian_initial_eq_total
    hN henergyDensity sample hsimple
  rw [hharmonic] at hcomparison
  exact hcomparison

/-- Consequently the prescribed parameter `epsilon` and the exact LJ initial
energy density differ by no more than the same per-bond envelope. -/
theorem abs_exactLJInitialEnergyDensity_sub_parameter_le
    {N : Nat} [NeZero N] (hN : 3 <= N)
    {energyDensity : Real} (henergyDensity : 0 <= energyDensity)
    (sample : SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (massSample (N := N) sample)))
    {r0 rho amplitude : Real}
    (hr0 : 0 < r0) (hrho0 : 0 <= rho) (hrho1 : rho < 1)
    (hamplitude0 : 0 <= amplitude)
    (htube : forall i : Lattice.Site N,
      |Lattice.forwardDifference
        (asConfiguration (initialPhysicalPosition (N := N) energyDensity sample)) i| <=
          rho * r0)
    (hamplitude : forall i : Lattice.Site N,
      |Lattice.forwardDifference
        (asConfiguration (initialPhysicalPosition (N := N) energyDensity sample)) i| <=
          amplitude) :
    |exactLJInitialEnergyDensity (N := N) r0 energyDensity sample -
        energyDensity| <=
      harmonicComparisonPerBondBound
        (unitStiffnessDepth r0) r0 rho amplitude := by
  have htotal := abs_exactLJInitialHamiltonian_sub_prescribedTotal_le
    hN henergyDensity sample hsimple hr0 hrho0 hrho1 hamplitude0
    htube hamplitude
  have hNpos : 0 < (N : Real) := by positivity
  have heq :
      exactLJInitialEnergyDensity (N := N) r0 energyDensity sample -
          energyDensity =
        (exactLJInitialHamiltonian (N := N) r0 energyDensity sample -
          (N : Real) * energyDensity) / (N : Real) := by
    unfold exactLJInitialEnergyDensity
    field_simp
  rw [heq, abs_div, abs_of_pos hNpos]
  calc
    |exactLJInitialHamiltonian (N := N) r0 energyDensity sample -
        (N : Real) * energyDensity| / (N : Real) <=
      ((N : Real) * harmonicComparisonPerBondBound
        (unitStiffnessDepth r0) r0 rho amplitude) / (N : Real) :=
      (div_le_div_iff_of_pos_right hNpos).2 htotal
    _ = harmonicComparisonPerBondBound
        (unitStiffnessDepth r0) r0 rho amplitude := by
      field_simp

/-- At `r0 = 1` and the explicit tube radius/amplitude `1/40`, the complete
per-bond cubic-plus-quartic-plus-fifth-order envelope is below `1/16000`. -/
theorem harmonicComparisonPerBondBound_one_div_forty_lt :
    harmonicComparisonPerBondBound (unitStiffnessDepth 1) 1
      (1 / 40) (1 / 40) < (1 / 16000 : Real) := by
  have hrem :=
    fourthOrderTubeConstant_mul_one_div_forty_pow_five_lt
  norm_num [harmonicComparisonPerBondBound, unitStiffnessDepth,
    alphaCoefficient, betaCoefficient] at hrem ⊢
  nlinarith

end

end ArchonPhysics.ConcreteGaussianTwoBandLennardJonesInitialEnergy
