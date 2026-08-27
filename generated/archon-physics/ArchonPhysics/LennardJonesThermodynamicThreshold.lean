import ArchonPhysics.LennardJonesTaylorRemainder
import ArchonPhysics.LennardJonesAlphaBetaBridge

/-!
# Thermodynamic small-strain thresholds for Lennard--Jones chains

This module separates three statements which are often conflated in a
low-energy discussion of a Lennard--Jones chain.

* A *total-energy* barrier controls every bond, uniformly at a fixed finite
  volume.
* At fixed energy density that deterministic argument has threshold of order
  `1 / N`, and hence has no positive thermodynamic limit.
* A fixed energy density controls only the density of bonds outside the local
  Taylor tube.  A uniform-in-bond Taylor comparison in the thermodynamic limit
  therefore needs an additional sup-norm, Gibbs-tail, or high-probability
  hypothesis.

The results below are static energy estimates.  They do not transfer a Toda or
FPUT thermalization time law to the exact Lennard--Jones flow; such a transfer
requires a separate long-time dynamical stability theorem.
-/

namespace ArchonPhysics.LennardJonesThermodynamicThreshold

open LennardJonesPotential
open Filter
open scoped Topology

noncomputable section

/-- The symmetric relative-strain tube `|x| < ρ r₀`. -/
def InRelativeTube (r₀ ρ x : Real) : Prop :=
  |x| < ρ * r₀

/-- All periodic bonds lie in the same relative-strain tube. -/
def UniformRelativeTube {N : Nat} (r₀ ρ : Real)
    (q : Lattice.Configuration N) : Prop :=
  ∀ i : Lattice.Site N, InRelativeTube r₀ ρ (Lattice.forwardDifference q i)

/-- The sharp one-bond energy on the tensile boundary `x = ρ r₀`.

For `0 ≤ ρ < 1`, the compressive boundary has still larger energy, so this is
the barrier for leaving the symmetric admissible tube. -/
def relativeTubeBarrier (depth ρ : Real) : Real :=
  depth * (1 - (1 / (1 + ρ)) ^ 6) ^ 2

/-- A convenient, slightly weaker algebraic barrier.  It is useful when only a
simple closed expression is needed. -/
def elementaryRelativeTubeBarrier (depth ρ : Real) : Real :=
  depth * (ρ / (1 + ρ)) ^ 2

/-- The sharp barrier is nonnegative for nonnegative well depth. -/
theorem relativeTubeBarrier_nonneg {depth ρ : Real} (hdepth : 0 ≤ depth) :
    0 ≤ relativeTubeBarrier depth ρ := by
  unfold relativeTubeBarrier
  positivity

/-- The elementary barrier is positive for positive physical parameters. -/
theorem elementaryRelativeTubeBarrier_pos {depth ρ : Real}
    (hdepth : 0 < depth) (hρ : 0 < ρ) :
    0 < elementaryRelativeTubeBarrier depth ρ := by
  unfold elementaryRelativeTubeBarrier
  have hden : 0 < 1 + ρ := by linarith
  exact mul_pos hdepth (sq_pos_of_pos (div_pos hρ hden))

/-- The tensile boundary realizes the sharp barrier exactly. -/
theorem bondPotential_relativeTubeBoundary {depth r₀ ρ : Real}
    (hr₀ : r₀ ≠ 0) (hρ : 1 + ρ ≠ 0) :
    bondPotential depth r₀ (ρ * r₀) = relativeTubeBarrier depth ρ := by
  rw [bondPotential, shiftedPotential_factor]
  unfold relativeTubeBarrier
  have hsum : r₀ + ρ * r₀ = (1 + ρ) * r₀ := by ring
  rw [hsum]
  field_simp [hr₀, hρ]
  ring

/-- Dimensionless cubic coupling obtained by measuring the displacement at
the harmonic energy scale `e / k`. -/
def dimensionlessEffectiveCubicCoupling (depth r₀ e : Real) : Real :=
  LennardJonesAlphaBetaBridge.normalizedAlpha depth r₀ *
    Real.sqrt (e / harmonicStiffness depth r₀)

/-- The equilibrium length cancels from the squared LJ cubic coupling. -/
theorem dimensionlessEffectiveCubicCoupling_sq
    {depth r₀ e : Real} (hdepth : 0 < depth)
    (hr₀ : 0 < r₀) (he : 0 ≤ e) :
    dimensionlessEffectiveCubicCoupling depth r₀ e ^ 2 =
      49 * e / (32 * depth) := by
  unfold dimensionlessEffectiveCubicCoupling
  rw [LennardJonesAlphaBetaBridge.normalizedAlpha_eq hdepth hr₀]
  unfold harmonicStiffness
  have hk : 0 < 72 * depth / r₀ ^ 2 :=
    div_pos (mul_pos (by norm_num) hdepth) (sq_pos_of_pos hr₀)
  have hratio : 0 ≤ e / (72 * depth / r₀ ^ 2) := div_nonneg he hk.le
  rw [mul_pow, Real.sq_sqrt hratio]
  field_simp [ne_of_gt hdepth, ne_of_gt hr₀]
  ring

/-- Conversion of any admissible kinetic weak-coupling cutoff into an
`N`-independent LJ energy-density ratio cutoff.  This is only an algebraic
conversion: the existence of a kinetic theorem valid up to `gStar`, and its
long-time transfer to exact LJ dynamics, remain separate hypotheses. -/
theorem energyRatio_le_of_effectiveCubicCoupling_sq_le
    {depth r₀ e gStar : Real} (hdepth : 0 < depth)
    (hr₀ : 0 < r₀) (he : 0 ≤ e)
    (hg : dimensionlessEffectiveCubicCoupling depth r₀ e ^ 2 ≤ gStar ^ 2) :
    e / depth ≤ (32 / 49 : Real) * gStar ^ 2 := by
  rw [dimensionlessEffectiveCubicCoupling_sq hdepth hr₀ he] at hg
  have hden : 0 < 32 * depth := mul_pos (by norm_num) hdepth
  have hraw : 49 * e ≤ gStar ^ 2 * (32 * depth) := by
    exact (div_le_iff₀ hden).mp hg
  apply (div_le_iff₀ hdepth).2
  nlinarith

/-- Exact closed form of the illustrative `ρ = 1/40` one-bond barrier. -/
theorem relativeTubeBarrier_one_fortieth (depth : Real) :
    relativeTubeBarrier depth ((1 : Real) / 40) =
      depth * (1 - ((40 : Real) / 41) ^ 6) ^ 2 := by
  norm_num [relativeTubeBarrier]


/-- Quartic coefficient of the Toda exponential whose quadratic and cubic
Taylor coefficients match a normalized FPUT alpha coefficient. -/
def matchedTodaBeta (alpha : Real) : Real :=
  2 * alpha ^ 2 / 3

/-- The normalized LJ quartic coefficient differs explicitly from its
quadratic/cubic-matched Toda reference.  Thus Toda is a coefficient-level
integrable reference, not the exact LJ dynamics. -/
theorem normalizedBeta_sub_matchedTodaBeta
    {depth r₀ : Real} (hdepth : 0 < depth) (hr₀ : 0 < r₀) :
    LennardJonesAlphaBetaBridge.normalizedBeta depth r₀ -
        matchedTodaBeta
          (LennardJonesAlphaBetaBridge.normalizedAlpha depth r₀) =
      -35 / (3 * r₀ ^ 2) := by
  rw [LennardJonesAlphaBetaBridge.normalizedAlpha_eq hdepth hr₀,
    LennardJonesAlphaBetaBridge.normalizedBeta_eq hdepth hr₀]
  unfold matchedTodaBeta
  field_simp [ne_of_gt hr₀]
  ring

/-- Polynomial parametrization of the balanced thermodynamic-average regime:
energy ratio `s = t^7` and tube radius `ρ = t^2` correspond to exponent
`a = 2/7`. -/
def balancedEnergyRatio (t : Real) : Real := t ^ 7

def balancedTubeRadius (t : Real) : Real := t ^ 2

/-- At the balanced choice, the energy-counting bad-bond scale is `t^3`. -/
theorem balanced_badBondScale {t : Real} (ht : t ≠ 0) :
    balancedEnergyRatio t / balancedTubeRadius t ^ 2 = t ^ 3 := by
  unfold balancedEnergyRatio balancedTubeRadius
  field_simp [ht]

/-- At the same choice, a fifth-order good-bond Taylor remainder divided by
the energy density also has scale `t^3`. -/
theorem balanced_goodRemainderScale {t : Real} (ht : t ≠ 0) :
    balancedTubeRadius t ^ 5 / balancedEnergyRatio t = t ^ 3 := by
  unfold balancedEnergyRatio balancedTubeRadius
  field_simp [ht]

/-- Both balanced error scales vanish as the low-density parameter tends to
zero. -/
theorem balanced_errorScale_tendsto_zero :
    Tendsto (fun t : Real => t ^ 3) (nhds 0) (nhds 0) := by
  have h : ContinuousAt (fun t : Real => t ^ 3) 0 := by fun_prop
  simpa only [ContinuousAt, zero_pow (by norm_num : (3 : Nat) ≠ 0)] using h


/-- Leaving the admissible symmetric tube costs at least the tensile-boundary
energy.  This is the exact one-bond barrier used by the finite-volume
Hamiltonian estimate below. -/
theorem relativeTubeBarrier_le_bondPotential_of_not_inTube
    {depth r₀ ρ x : Real}
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀)
    (hρ0 : 0 ≤ ρ)
    (hbond : BondAdmissible r₀ x)
    (hout : ¬ InRelativeTube r₀ ρ x) :
    relativeTubeBarrier depth ρ ≤ bondPotential depth r₀ x := by
  have hρden : 0 < 1 + ρ := by linarith
  have hr : 0 < r₀ + x := hbond
  have ha0 : 0 ≤ 1 / (1 + ρ) := div_nonneg zero_le_one hρden.le
  have ha1 : 1 / (1 + ρ) ≤ 1 := by
    exact (div_le_one hρden).2 (by linarith)
  have ha6 : (1 / (1 + ρ)) ^ 6 ≤ 1 := by
    simpa using pow_le_pow_left₀ ha0 ha1 6
  have hb0 : 0 ≤ 1 - (1 / (1 + ρ)) ^ 6 := by linarith
  rw [bondPotential, shiftedPotential_factor]
  unfold relativeTubeBarrier
  apply mul_le_mul_of_nonneg_left _ hdepth
  by_cases hx : 0 ≤ x
  · have hxout : ρ * r₀ ≤ x := by
      rw [InRelativeTube, not_lt] at hout
      simpa [abs_of_nonneg hx] using hout
    have hdenOrder : (1 + ρ) * r₀ ≤ r₀ + x := by nlinarith
    have hdenPos : 0 < (1 + ρ) * r₀ := mul_pos hρden hr₀
    have hzle : r₀ / (r₀ + x) ≤ 1 / (1 + ρ) := by
      calc
        r₀ / (r₀ + x) ≤ r₀ / ((1 + ρ) * r₀) :=
          div_le_div_of_nonneg_left hr₀.le hdenPos hdenOrder
        _ = 1 / (1 + ρ) := by field_simp [ne_of_gt hr₀, ne_of_gt hρden]
    have hz0 : 0 ≤ r₀ / (r₀ + x) := div_nonneg hr₀.le hr.le
    have hz6 : (r₀ / (r₀ + x)) ^ 6 ≤ (1 / (1 + ρ)) ^ 6 :=
      pow_le_pow_left₀ hz0 hzle 6
    have hlin :
        1 - (1 / (1 + ρ)) ^ 6 ≤ 1 - (r₀ / (r₀ + x)) ^ 6 := by
      linarith
    have hsquare := (sq_le_sq₀ hb0 (by linarith)).2 hlin
    nlinarith
  · have hxneg : x ≤ 0 := le_of_not_ge hx
    have hxout : ρ * r₀ ≤ -x := by
      rw [InRelativeTube, not_lt] at hout
      simpa [abs_of_nonpos hxneg] using hout
    have hsMul : (1 + ρ) * (r₀ + x) ≤ r₀ := by
      have hρsq : 0 ≤ ρ ^ 2 := sq_nonneg ρ
      nlinarith
    have hsz : 1 + ρ ≤ r₀ / (r₀ + x) :=
      (le_div_iff₀ hr).2 hsMul
    have hs0 : 0 ≤ 1 + ρ := hρden.le
    have hz6 : (1 + ρ) ^ 6 ≤ (r₀ / (r₀ + x)) ^ 6 :=
      pow_le_pow_left₀ hs0 hsz 6
    have hrecip : (1 + ρ) ^ 3 * (1 / (1 + ρ)) ^ 3 = 1 := by
      field_simp [ne_of_gt hρden]
    have hamgm : 2 ≤ (1 + ρ) ^ 6 + (1 / (1 + ρ)) ^ 6 := by
      nlinarith [sq_nonneg ((1 + ρ) ^ 3 - (1 / (1 + ρ)) ^ 3)]
    have hlin :
        1 - (1 / (1 + ρ)) ^ 6 ≤ (r₀ / (r₀ + x)) ^ 6 - 1 := by
      linarith
    have hzMinus0 : 0 ≤ (r₀ / (r₀ + x)) ^ 6 - 1 := by
      have honez : 1 ≤ r₀ / (r₀ + x) := by linarith
      have hzpow : (1 : Real) ^ 6 ≤ (r₀ / (r₀ + x)) ^ 6 :=
        pow_le_pow_left₀ zero_le_one honez 6
      norm_num at hzpow ⊢
      linarith
    have hsquare := (sq_le_sq₀ hb0 hzMinus0).2 hlin
    nlinarith

/-- Pointwise potential-energy domination by the full periodic potential
energy. -/
theorem bondPotential_le_periodicPotentialEnergy
    {N : Nat} [NeZero N] {depth r₀ : Real} (hdepth : 0 ≤ depth)
    (q : Lattice.Configuration N) (i : Lattice.Site N) :
    bondPotential depth r₀ (Lattice.forwardDifference q i) ≤
      periodicPotentialEnergy depth r₀ q := by
  unfold periodicPotentialEnergy
  exact Finset.single_le_sum
    (fun j _ => by
      simpa [bondPotential] using
        (shiftedPotential_nonneg (r₀ := r₀)
          (r := r₀ + Lattice.forwardDifference q j) hdepth))
    (Finset.mem_univ i)

/-- Potential energy is bounded by the full Hamiltonian because kinetic energy
is nonnegative. -/
theorem periodicPotentialEnergy_le_hamiltonian
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {depth r₀ : Real} (p q : Lattice.Configuration N) :
    periodicPotentialEnergy depth r₀ q ≤
      periodicRandomMassHamiltonian m depth r₀ p q := by
  unfold periodicRandomMassHamiltonian
  exact le_add_of_nonneg_left (Lattice.kineticEnergy_nonneg m p)

/-- Abstract total-energy barrier principle.  Supplying a pointwise LJ barrier
immediately controls every bond of every finite periodic chain. -/
theorem uniformRelativeTube_of_hamiltonian_lt
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {depth r₀ ρ barrier : Real}
    (hdepth : 0 ≤ depth)
    (hpoint : ∀ x : Real,
      BondAdmissible r₀ x → ¬ InRelativeTube r₀ ρ x →
        barrier ≤ bondPotential depth r₀ x)
    (p q : Lattice.Configuration N)
    (hadmissible : AdmissibleConfiguration r₀ q)
    (henergy : periodicRandomMassHamiltonian m depth r₀ p q < barrier) :
    UniformRelativeTube r₀ ρ q := by
  intro i
  by_contra hout
  have hbarrier := hpoint (Lattice.forwardDifference q i)
    (hadmissible i) hout
  have hbondPotential := bondPotential_le_periodicPotentialEnergy
    (r₀ := r₀) hdepth q i
  have hpotentialHamiltonian := periodicPotentialEnergy_le_hamiltonian
    (depth := depth) (r₀ := r₀) m p q
  linarith

/-- Concrete finite-volume LJ consequence of the sharp tube barrier. -/
theorem uniformRelativeTube_of_hamiltonian_lt_relativeTubeBarrier
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {depth r₀ ρ : Real}
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀) (hρ : 0 ≤ ρ)
    (p q : Lattice.Configuration N)
    (hadmissible : AdmissibleConfiguration r₀ q)
    (henergy : periodicRandomMassHamiltonian m depth r₀ p q <
      relativeTubeBarrier depth ρ) :
    UniformRelativeTube r₀ ρ q := by
  exact uniformRelativeTube_of_hamiltonian_lt m hdepth
    (fun x hx hxtube =>
      relativeTubeBarrier_le_bondPotential_of_not_inTube
        hdepth hr₀ hρ hx hxtube)
    p q hadmissible henergy

/-- Hamiltonian energy per periodic site. -/
def periodicEnergyDensity {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (p q : Lattice.Configuration N) : Real :=
  periodicRandomMassHamiltonian m depth r₀ p q / N


/-- The deterministic all-bond condition expressed per site.  Its threshold is
`barrier / N`, not a positive constant independent of `N`. -/
def deterministicAllBondDensityThreshold (barrier : Real) (N : Nat) : Real :=
  barrier / N

/-- The finite-volume density formulation is exactly the total-energy barrier
condition, and therefore still has a `1 / N` threshold. -/
theorem uniformRelativeTube_of_energyDensity_lt_threshold
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {depth r₀ ρ : Real}
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀) (hρ : 0 ≤ ρ)
    (p q : Lattice.Configuration N)
    (hadmissible : AdmissibleConfiguration r₀ q)
    (henergy : periodicEnergyDensity m depth r₀ p q <
      deterministicAllBondDensityThreshold
        (relativeTubeBarrier depth ρ) N) :
    UniformRelativeTube r₀ ρ q := by
  have hN : 0 < (N : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have htotal : periodicRandomMassHamiltonian m depth r₀ p q <
      relativeTubeBarrier depth ρ := by
    unfold periodicEnergyDensity deterministicAllBondDensityThreshold at henergy
    exact (div_lt_div_iff_of_pos_right hN).mp henergy
  exact uniformRelativeTube_of_hamiltonian_lt_relativeTubeBarrier
    m hdepth hr₀ hρ p q hadmissible htotal


/-- Multiplying the per-site threshold by the volume recovers the one-defect
total-energy barrier. -/
theorem deterministicAllBondDensityThreshold_mul_volume
    {barrier : Real} {N : Nat} (hN : N ≠ 0) :
    deterministicAllBondDensityThreshold barrier N * N = barrier := by
  unfold deterministicAllBondDensityThreshold
  field_simp

/-- Along any volume sequence tending to infinity, the deterministic
all-bond energy-density threshold vanishes. -/
theorem deterministicAllBondDensityThreshold_tendsto_zero
    (barrier : Real) :
    Tendsto (deterministicAllBondDensityThreshold barrier)
      Filter.atTop (nhds 0) := by
  unfold deterministicAllBondDensityThreshold
  simpa only [div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := Real)))

/-- Hence every fixed positive energy density eventually lies above the
deterministic threshold furnished by a one-bond barrier. -/
theorem eventually_threshold_lt_fixed_density
    {barrier e : Real} (he : 0 < e) :
    ∀ᶠ N : Nat in Filter.atTop,
      deterministicAllBondDensityThreshold barrier N < e := by
  exact (deterministicAllBondDensityThreshold_tendsto_zero barrier).eventually
    (Iio_mem_nhds he)

/-- Sites whose relative bond strain lies outside the closed Taylor tube. -/
def badBondSet {N : Nat} [NeZero N] (r₀ ρ : Real)
    (q : Lattice.Configuration N) : Finset (Lattice.Site N) :=
  Finset.univ.filter fun i =>
    ρ * r₀ ≤ |Lattice.forwardDifference q i|

/-- Fraction of periodic bonds outside the closed Taylor tube. -/
def badBondFraction {N : Nat} [NeZero N] (r₀ ρ : Real)
    (q : Lattice.Configuration N) : Real :=
  (badBondSet r₀ ρ q).card / N


/-- A generic counting lemma behind the deterministic bad-bond-density bound.
Each bad bond costs at least `barrier`, so their number times the barrier is at
most the total potential energy. -/
theorem barrier_mul_badBondSet_card_le
    {N : Nat} [NeZero N] {depth r₀ ρ barrier : Real}
    (hdepth : 0 ≤ depth)
    (q : Lattice.Configuration N)
    (hpoint : ∀ i : Lattice.Site N,
      ρ * r₀ ≤ |Lattice.forwardDifference q i| →
        barrier ≤ bondPotential depth r₀ (Lattice.forwardDifference q i)) :
    barrier * (badBondSet r₀ ρ q).card ≤
      periodicPotentialEnergy depth r₀ q := by
  rw [mul_comm]
  change (badBondSet r₀ ρ q).card * barrier ≤ _
  calc
    ((badBondSet r₀ ρ q).card : Real) * barrier =
        ∑ _i ∈ badBondSet r₀ ρ q, barrier := by simp
    _ ≤ ∑ i ∈ badBondSet r₀ ρ q,
        bondPotential depth r₀ (Lattice.forwardDifference q i) := by
      exact Finset.sum_le_sum fun i hi =>
        hpoint i ((Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i : Lattice.Site N,
        bondPotential depth r₀ (Lattice.forwardDifference q i) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun i _ _ => by
          simpa [bondPotential] using
            (shiftedPotential_nonneg (r₀ := r₀)
              (r := r₀ + Lattice.forwardDifference q i) hdepth))
    _ = periodicPotentialEnergy depth r₀ q := rfl

/-- The sharp LJ barrier controls the density, rather than the absence, of bad
bonds at fixed positive energy density. -/
theorem badBondFraction_le_energyDensity_div_barrier
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {depth r₀ ρ : Real}
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀) (hρ : 0 ≤ ρ)
    (hbarrier : 0 < relativeTubeBarrier depth ρ)
    (p q : Lattice.Configuration N)
    (hadmissible : AdmissibleConfiguration r₀ q) :
    badBondFraction r₀ ρ q ≤
      periodicEnergyDensity m depth r₀ p q /
        relativeTubeBarrier depth ρ := by
  have hcount : relativeTubeBarrier depth ρ *
      (badBondSet r₀ ρ q).card ≤ periodicPotentialEnergy depth r₀ q := by
    apply barrier_mul_badBondSet_card_le hdepth q
    intro i hi
    exact relativeTubeBarrier_le_bondPotential_of_not_inTube
      hdepth hr₀ hρ (hadmissible i) (not_lt_of_ge hi)
  have htotal : relativeTubeBarrier depth ρ *
      (badBondSet r₀ ρ q).card ≤
        periodicRandomMassHamiltonian m depth r₀ p q :=
    hcount.trans (periodicPotentialEnergy_le_hamiltonian m p q)
  have hN : 0 < (N : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hden : 0 < relativeTubeBarrier depth ρ * (N : Real) :=
    mul_pos hbarrier hN
  unfold badBondFraction periodicEnergyDensity
  calc
    ((badBondSet r₀ ρ q).card : Real) / (N : Real) =
        (relativeTubeBarrier depth ρ *
          (badBondSet r₀ ρ q).card) /
          (relativeTubeBarrier depth ρ * (N : Real)) := by
      field_simp [ne_of_gt hbarrier, ne_of_gt hN]
    _ ≤ periodicRandomMassHamiltonian m depth r₀ p q /
          (relativeTubeBarrier depth ρ * (N : Real)) :=
      (div_le_div_iff_of_pos_right hden).2 htotal
    _ = periodicRandomMassHamiltonian m depth r₀ p q / (N : Real) /
          relativeTubeBarrier depth ρ := by
      field_simp [ne_of_gt hbarrier, ne_of_gt hN]


end

end ArchonPhysics.LennardJonesThermodynamicThreshold
