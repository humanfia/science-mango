import ArchonPhysics.LennardJonesThermodynamicThreshold

/-!
# Consumer: thermodynamic Lennard--Jones low-energy threshold

This consumer locks the distinction between a finite-volume all-bond energy
barrier and a positive thermodynamic energy-density threshold.  The former is
proved; the latter does not follow from deterministic energy density alone.

Toda enters only through its matched quartic Taylor coefficient, and the FPUT
alpha-beta model through the exact fourth-order LJ jet.  No statement here
transfers a thermalization time law from either reference dynamics to the exact
Lennard--Jones flow.
-/

namespace ArchonPhysicsConsumers.Thermalization.LennardJonesThermodynamicThreshold

open ArchonPhysics
open ArchonPhysics.LennardJonesPotential
open ArchonPhysics.LennardJonesThermodynamicThreshold
open Filter
open scoped Topology

noncomputable section

/-- Kernel lock for the dimensionless cubic coupling and the matched-Toda
quartic gap. -/
theorem lj_fput_toda_coefficient_lock
    {depth r₀ e : Real} (hdepth : 0 < depth)
    (hr₀ : 0 < r₀) (he : 0 ≤ e) :
    dimensionlessEffectiveCubicCoupling depth r₀ e ^ 2 =
        49 * e / (32 * depth) ∧
      LennardJonesAlphaBetaBridge.normalizedBeta depth r₀ -
          matchedTodaBeta
            (LennardJonesAlphaBetaBridge.normalizedAlpha depth r₀) =
        -35 / (3 * r₀ ^ 2) := by
  exact ⟨dimensionlessEffectiveCubicCoupling_sq hdepth hr₀ he,
    normalizedBeta_sub_matchedTodaBeta hdepth hr₀⟩

/-- The tensile boundary realizes the sharp barrier, and every admissible bond
outside the symmetric tube costs at least that amount. -/
theorem lj_sharp_relative_tube_barrier
    {depth r₀ ρ x : Real}
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀) (hρ : 0 ≤ ρ)
    (hbond : BondAdmissible r₀ x)
    (hout : ¬ InRelativeTube r₀ ρ x) :
    bondPotential depth r₀ (ρ * r₀) = relativeTubeBarrier depth ρ ∧
      relativeTubeBarrier depth ρ ≤ bondPotential depth r₀ x := by
  exact ⟨bondPotential_relativeTubeBoundary (ne_of_gt hr₀) (by linarith),
    relativeTubeBarrier_le_bondPotential_of_not_inTube
      hdepth hr₀ hρ hbond hout⟩

/-- Concrete `N`-site density criterion.  Its right-hand side is explicitly
the one-bond barrier divided by `N`. -/
theorem lj_all_bonds_small_of_density_below_barrier_over_N
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {depth r₀ ρ : Real}
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀) (hρ : 0 ≤ ρ)
    (p q : Lattice.Configuration N)
    (hadmissible : AdmissibleConfiguration r₀ q)
    (henergy : periodicEnergyDensity m depth r₀ p q <
      deterministicAllBondDensityThreshold
        (relativeTubeBarrier depth ρ) N) :
    UniformRelativeTube r₀ ρ q :=
  uniformRelativeTube_of_energyDensity_lt_threshold
    m hdepth hr₀ hρ p q hadmissible henergy

/-- The deterministic all-bond density threshold vanishes in the
thermodynamic limit, and every fixed positive density eventually exceeds it. -/
theorem lj_deterministic_density_threshold_no_go
    {depth ρ e : Real} (he : 0 < e) :
    Tendsto
        (deterministicAllBondDensityThreshold
          (relativeTubeBarrier depth ρ)) atTop (nhds 0) ∧
      ∀ᶠ N : Nat in atTop,
        deterministicAllBondDensityThreshold
          (relativeTubeBarrier depth ρ) N < e := by
  exact ⟨deterministicAllBondDensityThreshold_tendsto_zero _,
    eventually_threshold_lt_fixed_density he⟩

/-- What fixed density does control: the fraction of bonds outside the tube. -/
theorem lj_bad_bond_fraction_bound
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {depth r₀ ρ : Real}
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀) (hρ : 0 ≤ ρ)
    (hbarrier : 0 < relativeTubeBarrier depth ρ)
    (p q : Lattice.Configuration N)
    (hadmissible : AdmissibleConfiguration r₀ q) :
    badBondFraction r₀ ρ q ≤
      periodicEnergyDensity m depth r₀ p q /
        relativeTubeBarrier depth ρ :=
  badBondFraction_le_energyDensity_div_barrier
    m hdepth hr₀ hρ hbarrier p q hadmissible

/-- Exact balanced thermodynamic-average bookkeeping: with `s=t^7` and
`ρ=t^2`, both the bad-bond counting scale and the normalized fifth-order
good-bond remainder scale equal `t^3`, which tends to zero. -/
theorem lj_balanced_average_scales
    {t : Real} (ht : t ≠ 0) :
    balancedEnergyRatio t / balancedTubeRadius t ^ 2 = t ^ 3 ∧
      balancedTubeRadius t ^ 5 / balancedEnergyRatio t = t ^ 3 ∧
      Tendsto (fun u : Real => u ^ 3) (nhds 0) (nhds 0) := by
  exact ⟨balanced_badBondScale ht, balanced_goodRemainderScale ht,
    balanced_errorScale_tendsto_zero⟩

/-- If an upstream kinetic theorem supplies a squared-coupling cutoff
`gStar^2`, the corresponding LJ ratio is `e/depth ≤ (32/49) gStar^2`.
This theorem performs only that exact unit conversion. -/
theorem lj_kinetic_cutoff_energy_ratio
    {depth r₀ e gStar : Real} (hdepth : 0 < depth)
    (hr₀ : 0 < r₀) (he : 0 ≤ e)
    (hg : dimensionlessEffectiveCubicCoupling depth r₀ e ^ 2 ≤ gStar ^ 2) :
    e / depth ≤ (32 / 49 : Real) * gStar ^ 2 :=
  energyRatio_le_of_effectiveCubicCoupling_sq_le hdepth hr₀ he hg

/-- Exact value of the illustrative one-bond `ρ=1/40` safety barrier. -/
theorem lj_one_fortieth_barrier (depth : Real) :
    relativeTubeBarrier depth ((1 : Real) / 40) =
      depth * (1 - ((40 : Real) / 41) ^ 6) ^ 2 :=
  relativeTubeBarrier_one_fortieth depth

/-- Exact fifth-order remainder factorization used on good bonds. -/
theorem lj_exact_fifth_order_remainder
    {depth r₀ x : Real} (hr₀ : r₀ ≠ 0) (hbond : r₀ + x ≠ 0) :
    bondPotential depth r₀ x - localAlphaBetaPotential depth r₀ x =
      x ^ 5 *
        ArchonPhysics.LennardJonesTaylorRemainder.fourthOrderRemainderFactor depth r₀ x :=
  ArchonPhysics.LennardJonesTaylorRemainder.bondPotential_sub_localAlphaBetaPotential_factor hr₀ hbond


#print axioms lj_fput_toda_coefficient_lock
#print axioms lj_sharp_relative_tube_barrier
#print axioms lj_all_bonds_small_of_density_below_barrier_over_N
#print axioms lj_deterministic_density_threshold_no_go
#print axioms lj_bad_bond_fraction_bound
#print axioms lj_balanced_average_scales
#print axioms lj_kinetic_cutoff_energy_ratio
#print axioms lj_one_fortieth_barrier
#print axioms lj_exact_fifth_order_remainder

end

end ArchonPhysicsConsumers.Thermalization.LennardJonesThermodynamicThreshold
