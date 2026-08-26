import ArchonPhysics.CoerciveHamiltonianContinuation

/-!
# Uniform coercivity in a mass-weighted translation gauge

This file removes the dependence on a particular mass realization from the
finite-chain Poincare constant.  It works in the fixed ambient physical phase
space `Configuration N × Configuration N`, rather than in the mass-dependent
subtype `ReducedPhaseSpace m`.

The main observation is elementary but useful: subtract the ordinary mean of
a configuration.  The centered configuration has zero ordinary mean and the
same bond differences.  If the original configuration has zero mass-weighted
mean, positivity of the masses bounds the removed constant by the sup norm of
the centered configuration.  Thus twice any zero-mean Poincare constant works
simultaneously for every positive mass profile.

The resulting energy-sublevel radius uses only an upper mass bound.  A lower
bound is not needed here because strict positivity is already part of
`PositiveMassConfig`; it becomes relevant when one asks for parameter-uniform
regularity of the vector field.
-/

namespace ArchonPhysics.UniformMassGaugeCoercivity

open CoerciveHamiltonianContinuation
open TranslationReducedCoercivity

noncomputable section

/-- The ordinary arithmetic mean of a physical configuration. -/
def configurationMean {N : Nat} [NeZero N]
    (q : Lattice.Configuration N) : Real :=
  (∑ i, q i) / (N : Real)

/-- Remove the ordinary (not mass-weighted) translation coordinate. -/
def centeredConfiguration {N : Nat} [NeZero N]
    (q : Lattice.Configuration N) : Lattice.Configuration N :=
  fun i => q i - configurationMean q

/-- The centered configuration belongs to the ordinary zero-mean subspace. -/
theorem centeredConfiguration_zeroMean {N : Nat} [NeZero N]
    (q : Lattice.Configuration N) :
    centeredConfiguration q ∈ zeroMeanSubspace N := by
  rw [mem_zeroMeanSubspace_iff]
  unfold centeredConfiguration configurationMean
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ : Finset (Lattice.Site N)).card = N := by
    simp [ZMod.card]
  rw [hcard]
  have hN : (N : Real) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp
  ring

/-- Centering does not change any periodic bond difference. -/
theorem forwardDifference_centeredConfiguration {N : Nat} [NeZero N]
    (q : Lattice.Configuration N) :
    Lattice.forwardDifference (centeredConfiguration q) =
      Lattice.forwardDifference q := by
  ext i
  simp [Lattice.forwardDifference, centeredConfiguration]

/-- Total mass of a positive mass realization. -/
def totalMass {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) : Real :=
  ∑ i, m.mass i

theorem totalMass_pos {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) : 0 < totalMass m := by
  unfold totalMass
  exact Finset.sum_pos (fun i _ => m.mass_pos i) Finset.univ_nonempty

/-- The sup norm of a constant configuration is the absolute value of the
constant. -/
theorem norm_const_configuration {N : Nat} [NeZero N] (c : Real) :
    ‖(fun _ : Lattice.Site N => c)‖ = |c| := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonempty]
    intro i
    simp [Real.norm_eq_abs]
  · let i : Lattice.Site N := Classical.arbitrary (Lattice.Site N)
    simpa only [Real.norm_eq_abs, i] using
      norm_le_pi_norm (fun _ : Lattice.Site N => c) i

/-- In the mass-weighted gauge, the removed ordinary mean is controlled by
the centered configuration, uniformly over all positive mass profiles. -/
theorem abs_configurationMean_le_norm_centered_of_massGauge
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (q : Lattice.Configuration N)
    (hgauge : ∑ i, m.mass i * q i = 0) :
    |configurationMean q| ≤ ‖centeredConfiguration q‖ := by
  let c := configurationMean q
  let r := centeredConfiguration q
  have hq : ∀ i, q i = r i + c := by
    intro i
    simp [r, c, centeredConfiguration]
  have hsum : (∑ i, m.mass i * r i) + c * totalMass m = 0 := by
    rw [← hgauge]
    unfold totalMass
    simp_rw [hq]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    ring_nf
  have hc : c = -(∑ i, m.mass i * r i) / totalMass m := by
    have hM := ne_of_gt (totalMass_pos m)
    apply (eq_div_iff hM).2
    linarith
  change |c| ≤ ‖r‖
  rw [hc, abs_div]
  rw [div_le_iff₀ (abs_pos.mpr (ne_of_gt (totalMass_pos m)))]
  calc
    |-(∑ i, m.mass i * r i)| = |∑ i, m.mass i * r i| := abs_neg _
    _ ≤ ∑ i, |m.mass i * r i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, m.mass i * ‖r‖ := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [abs_mul, abs_of_pos (m.mass_pos i)]
      exact mul_le_mul_of_nonneg_left
        (by simpa [Real.norm_eq_abs] using norm_le_pi_norm r i)
        (m.mass_pos i).le
    _ = |totalMass m| * ‖r‖ := by
      rw [abs_of_pos (totalMass_pos m)]
      unfold totalMass
      rw [← Finset.sum_mul]
    _ = ‖r‖ * |totalMass m| := mul_comm _ _

/-- Uniform comparison between a mass-gauged configuration and its ordinary
centered representative. -/
theorem norm_le_two_mul_norm_centered_of_massGauge
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (q : Lattice.Configuration N)
    (hgauge : ∑ i, m.mass i * q i = 0) :
    ‖q‖ ≤ 2 * ‖centeredConfiguration q‖ := by
  let c := configurationMean q
  let r := centeredConfiguration q
  have hqr : q = r + fun _ => c := by
    ext i
    simp [r, c, centeredConfiguration]
  change ‖q‖ ≤ 2 * ‖r‖
  have hcBound : |c| ≤ ‖r‖ := by
    simpa [c, r] using
      abs_configurationMean_le_norm_centered_of_massGauge m q hgauge
  rw [hqr]
  calc
    ‖r + fun _ => c‖ ≤ ‖r‖ + ‖fun _ : Lattice.Site N => c‖ :=
      norm_add_le _ _
    _ = ‖r‖ + |c| := by rw [norm_const_configuration]
    _ ≤ ‖r‖ + ‖r‖ := add_le_add_right hcBound _
    _ = 2 * ‖r‖ := by ring

/-- A single Poincare constant, depending only on the finite lattice, works
for every strictly positive mass realization. -/
theorem exists_uniform_massWeighted_poincareConstant
    {N : Nat} [NeZero N] :
    ∃ C : Real, 0 < C ∧
      ∀ (m : Lattice.PositiveMassConfig N) (q : Lattice.Configuration N),
        (∑ i, m.mass i * q i = 0) →
          ‖q‖ ≤ C * ‖Lattice.forwardDifference q‖ := by
  obtain ⟨C, hC, hP⟩ := exists_zeroMean_poincareConstant (N := N)
  refine ⟨2 * C, mul_pos (by norm_num) hC, fun m q hgauge => ?_⟩
  calc
    ‖q‖ ≤ 2 * ‖centeredConfiguration q‖ :=
      norm_le_two_mul_norm_centered_of_massGauge m q hgauge
    _ ≤ 2 * (C * ‖Lattice.forwardDifference (centeredConfiguration q)‖) := by
      gcongr
      exact hP (centeredConfiguration q) (centeredConfiguration_zeroMean q)
    _ = (2 * C) * ‖Lattice.forwardDifference q‖ := by
      rw [forwardDifference_centeredConfiguration]
      ring

/-- Fixed ambient physical phase space: position first, momentum second. -/
abbrev PhysicalPhaseSpace (N : Nat) :=
  Lattice.Configuration N × Lattice.Configuration N

/-- The mass-gauged energy sublevel in the fixed physical phase space. -/
def physicalEnergySublevel {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g H : Real) :
    Set (PhysicalPhaseSpace N) :=
  {z | (∑ i, m.mass i * z.1 i = 0) ∧
    CoerciveLatticeEnergy.hamiltonian m kappa beta g z.2 z.1 ≤ H}

private theorem norm_le_sq_add_one
    {E : Type*} [SeminormedAddGroup E] (x : E) :
    ‖x‖ ≤ ‖x‖ ^ 2 + 1 := by
  nlinarith [sq_nonneg (‖x‖ - (1 / 2 : Real))]

private theorem configuration_norm_le_of_sum_sq_le
    {N : Nat} [NeZero N] (x : Lattice.Configuration N) {B : Real}
    (hB : (∑ i, x i ^ 2) ≤ B) :
    ‖x‖ ≤ B + 1 := by
  rw [pi_norm_le_iff_of_nonempty]
  intro i
  have hi : x i ^ 2 ≤ ∑ j, x j ^ 2 := by
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j))
      (Finset.mem_univ i)
  calc
    ‖x i‖ ≤ ‖x i‖ ^ 2 + 1 := norm_le_sq_add_one (x i)
    _ = x i ^ 2 + 1 := by rw [Real.norm_eq_abs, sq_abs]
    _ ≤ B + 1 := by simpa only [add_comm] using add_le_add_right (hi.trans hB) 1

private theorem configuration_norm_le_of_forall_sq_le
    {N : Nat} [NeZero N] (x : Lattice.Configuration N) {B : Real}
    (hB : ∀ i, x i ^ 2 ≤ B) :
    ‖x‖ ≤ B + 1 := by
  rw [pi_norm_le_iff_of_nonempty]
  intro i
  calc
    ‖x i‖ ≤ ‖x i‖ ^ 2 + 1 := norm_le_sq_add_one (x i)
    _ = x i ^ 2 + 1 := by rw [Real.norm_eq_abs, sq_abs]
    _ ≤ B + 1 := by simpa only [add_comm] using add_le_add_right (hB i) 1

/-- Uniform radius for all mass-gauged energy sublevels whose masses have the
same pointwise upper bound.  The constant `C` is independent of the mass
profile.  No lower bound beyond `PositiveMassConfig.mass_pos` is needed. -/
theorem physicalEnergySublevel_norm_le
    {N : Nat} [NeZero N]
    {C mUpper kappa beta g H : Real}
    (hC : 0 ≤ C)
    (hPoincare : ∀ (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) →
        ‖q‖ ≤ C * ‖Lattice.forwardDifference q‖)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (m : Lattice.PositiveMassConfig N)
    (hmUpper : ∀ i, m.mass i ≤ mUpper)
    {z : PhysicalPhaseSpace N}
    (hz : z ∈ physicalEnergySublevel m kappa beta g H) :
    ‖z‖ ≤ max
      (C * (H / CoerciveCubicPotential.coercivityConstant kappa beta + 1))
      (2 * mUpper * H + 1) := by
  rcases hz with ⟨hgauge, henergy⟩
  have hH : 0 ≤ H :=
    (CoerciveLatticeEnergy.hamiltonian_nonneg m hbeta g z.2 z.1).trans henergy
  have hc : 0 < CoerciveCubicPotential.coercivityConstant kappa beta :=
    CoerciveCubicPotential.coercivityConstant_pos hbeta
  have hdifferenceSq :
      (∑ i, Lattice.forwardDifference z.1 i ^ 2) ≤
        H / CoerciveCubicPotential.coercivityConstant kappa beta := by
    exact (CoerciveLatticeEnergy.sum_sq_forwardDifference_le_energy_div
      m hbeta g z.2 z.1).trans (div_le_div_of_nonneg_right henergy hc.le)
  have hdifferenceNorm :
      ‖Lattice.forwardDifference z.1‖ ≤
        H / CoerciveCubicPotential.coercivityConstant kappa beta + 1 :=
    configuration_norm_le_of_sum_sq_le _ hdifferenceSq
  have hq :
      ‖z.1‖ ≤ C *
        (H / CoerciveCubicPotential.coercivityConstant kappa beta + 1) :=
    (hPoincare m z.1 hgauge).trans
      (mul_le_mul_of_nonneg_left hdifferenceNorm hC)
  have hpCoordinate (i : Lattice.Site N) :
      z.2 i ^ 2 ≤ 2 * mUpper * H := by
    calc
      z.2 i ^ 2 ≤ 2 * m.mass i *
          CoerciveLatticeEnergy.hamiltonian m kappa beta g z.2 z.1 :=
        CoerciveLatticeEnergy.momentum_sq_le_mass_mul_energy
          m hbeta g z.2 z.1 i
      _ ≤ 2 * m.mass i * H := by
        exact mul_le_mul_of_nonneg_left henergy
          (mul_nonneg (by norm_num) (m.mass_pos i).le)
      _ ≤ 2 * mUpper * H := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hmUpper i) (by norm_num)) hH
  have hp : ‖z.2‖ ≤ 2 * mUpper * H + 1 :=
    configuration_norm_le_of_forall_sq_le _ hpCoordinate
  rw [Prod.norm_def]
  exact max_le_max hq hp

/-- Each fixed-mass physical energy sublevel is closed. -/
theorem physicalEnergySublevel_isClosed
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa beta g H : Real) :
    IsClosed (physicalEnergySublevel m kappa beta g H) := by
  unfold physicalEnergySublevel CoerciveLatticeEnergy.hamiltonian
    Lattice.kineticEnergy CoerciveLatticeEnergy.potentialEnergy
    CoerciveCubicPotential.potential Lattice.forwardDifference
  have hgauge : Continuous (fun z : PhysicalPhaseSpace N =>
      ∑ i, m.mass i * z.1 i) := by fun_prop
  have henergy : Continuous (fun z : PhysicalPhaseSpace N =>
      ∑ i, z.2 i ^ 2 / (2 * m.mass i) +
        ∑ i, ((z.1 (i + 1) - z.1 i) ^ 2 / 2 +
          (kappa * g / 3) * (z.1 (i + 1) - z.1 i) ^ 3 +
          (beta * g ^ 2 / 4) * (z.1 (i + 1) - z.1 i) ^ 4)) := by
    fun_prop
  exact (isClosed_eq hgauge continuous_const).inter
    (isClosed_le henergy continuous_const)

/-- For a fixed positive mass realization, a mass-gauged coercive energy
sublevel is compact in the fixed physical phase space. -/
theorem physicalEnergySublevel_isCompact
    {N : Nat} [NeZero N]
    {C kappa beta g H : Real}
    (hC : 0 ≤ C)
    (hPoincare : ∀ (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) →
        ‖q‖ ≤ C * ‖Lattice.forwardDifference q‖)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (m : Lattice.PositiveMassConfig N) :
    IsCompact (physicalEnergySublevel m kappa beta g H) := by
  have hclosed := physicalEnergySublevel_isClosed m kappa beta g H
  obtain ⟨mUpper, hmUpper⟩ :=
    Finite.exists_le (fun i : Lattice.Site N => m.mass i)
  apply Metric.isCompact_of_isClosed_isBounded hclosed
  rw [isBounded_iff_forall_norm_le]
  refine ⟨max
    (C * (H / CoerciveCubicPotential.coercivityConstant kappa beta + 1))
    (2 * mUpper * H + 1), ?_⟩
  intro z hz
  exact physicalEnergySublevel_norm_le hC hPoincare hbeta m hmUpper hz

end

end ArchonPhysics.UniformMassGaugeCoercivity
