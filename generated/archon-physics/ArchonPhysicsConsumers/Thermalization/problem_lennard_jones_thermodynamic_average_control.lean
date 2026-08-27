import ArchonPhysics.LennardJonesThermodynamicAverageControl

/-!
# Consumer: volume-uniform LJ thermodynamic-average control

This consumer locks the static, `N`-uniform low-density estimates for actual
periodic forward differences.  It deliberately makes no claim about transfer
to the long-time Lennard--Jones flow.
-/

namespace ArchonPhysicsConsumers.Thermalization.LennardJonesThermodynamicAverageControl

open ArchonPhysics
open ArchonPhysics.LennardJonesPotential
open ArchonPhysics.LennardJonesThermodynamicThreshold
open ArchonPhysics.LennardJonesQuantitativeTaylorTube
open ArchonPhysics.LennardJonesThermodynamicAverageControl
open Filter
open scoped Topology

noncomputable section

/-- Kernel lock for the sharp-to-elementary one-bond barrier comparison. -/
theorem lj_sharp_barrier_dominates_elementary
    {depth rho : Real} (hdepth : 0 <= depth) (hrho : 0 <= rho) :
    elementaryRelativeTubeBarrier depth rho <=
      relativeTubeBarrier depth rho :=
  elementaryRelativeTubeBarrier_le_relativeTubeBarrier hdepth hrho

/-- The actual periodic bad-bond density is bounded by the energy ratio and
the elementary tube factor, with no volume-dependent constant. -/
theorem lj_actual_bad_bond_fraction_elementary_bound
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {depth r0 rho : Real}
    (hdepth : 0 < depth) (hr0 : 0 < r0) (hrho : 0 < rho)
    (p q : Lattice.Configuration N)
    (hadmissible : AdmissibleConfiguration r0 q) :
    badBondFraction r0 rho q <=
      (periodicEnergyDensity m depth r0 p q / depth) *
        (1 + rho) ^ 2 / rho ^ 2 :=
  badBondFraction_le_energyRatio_mul_elementaryFactor
    m hdepth hr0 hrho p q hadmissible

/-- Complete static balanced estimate for an actual `N`-site periodic LJ
state.  Both right-hand sides are independent of `N`. -/
theorem lj_actual_balanced_N_uniform_average_control
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {depth r0 t : Real}
    (hdepth : 0 < depth) (hr0 : 0 < r0)
    (ht0 : 0 < t) (ht1 : t < 1)
    (p q : Lattice.Configuration N)
    (hadmissible : AdmissibleConfiguration r0 q)
    (henergyRatio : periodicEnergyDensity m depth r0 p q / depth <= t ^ 7) :
    badBondFraction r0 (t ^ 2) q <= balancedBadBondUpperBound t /\
      perSiteGoodBondAbsoluteFourthOrderRemainder depth r0 (t ^ 2)
            (fun i => Lattice.forwardDifference q i) /
          (depth * t ^ 7) <=
        balancedGoodBondRelativeRemainderUpperBound t := by
  exact ⟨
    (balanced_badBondFraction_le m hdepth hr0 ht0 ht1 p q
      hadmissible henergyRatio),
    (balanced_forwardDifference_goodBondRelativeRemainder_le
      q hdepth hr0 ht0 ht1)⟩

/-- The sharp good-bond Taylor estimate itself, before normalization by
`depth*t^7`. -/
theorem lj_actual_good_bond_remainder_volume_uniform
    {N : Nat} [NeZero N]
    {depth r0 rho : Real} (q : Lattice.Configuration N)
    (hdepth : 0 <= depth) (hr0 : 0 < r0)
    (hrho0 : 0 <= rho) (hrho1 : rho < 1) :
    perSiteGoodBondAbsoluteFourthOrderRemainder depth r0 rho
        (fun i => Lattice.forwardDifference q i) <=
      depth * fourthOrderTubeConstant rho * rho ^ 5 :=
  forwardDifference_goodBondRemainder_le_tubePower
    q hdepth hr0 hrho0 hrho1

/-- The two explicit volume-uniform balanced errors tend to zero, while the
tube constant itself tends to the exact coefficient `3864`. -/
theorem lj_balanced_average_limit_lock :
    Tendsto (fun t : Real => fourthOrderTubeConstant (t ^ 2))
        (nhds 0) (nhds 3864) /\
      Tendsto balancedBadBondUpperBound (nhds 0) (nhds 0) /\
      Tendsto balancedGoodBondRelativeRemainderUpperBound
        (nhds 0) (nhds 0) := by
  exact ⟨fourthOrderTubeConstant_sq_tendsto_3864,
    balanced_upperBounds_tendsto_zero⟩

/-- Tolerance-dependent threshold interface: sufficiently small positive
`t` makes both static errors less than `eta`; the corresponding energy ratio
cutoff is `s = t^7`. -/
theorem lj_eventually_balanced_average_errors_below_tolerance
    {eta : Real} (heta : 0 < eta) :
    ∀ᶠ t : Real in nhdsWithin 0 (Set.Ioo 0 1),
      balancedBadBondUpperBound t < eta /\
        balancedGoodBondRelativeRemainderUpperBound t < eta :=
  eventually_balanced_upperBounds_lt heta

/-- Explicit parameter-threshold form: `t0^7` is the certified energy-ratio
cutoff associated with the requested error tolerance. -/
theorem lj_exists_tolerance_dependent_energy_ratio_threshold
    {eta : Real} (heta : 0 < eta) :
    ∃ t0 : Real, 0 < t0 ∧ t0 < 1 ∧
      ∀ t : Real, 0 < t → t < t0 →
        balancedBadBondUpperBound t < eta ∧
          balancedGoodBondRelativeRemainderUpperBound t < eta :=
  exists_balanced_parameter_threshold heta

#print axioms lj_sharp_barrier_dominates_elementary
#print axioms lj_actual_bad_bond_fraction_elementary_bound
#print axioms lj_actual_balanced_N_uniform_average_control
#print axioms lj_actual_good_bond_remainder_volume_uniform
#print axioms lj_balanced_average_limit_lock
#print axioms lj_eventually_balanced_average_errors_below_tolerance
#print axioms lj_exists_tolerance_dependent_energy_ratio_threshold

end

end ArchonPhysicsConsumers.Thermalization.LennardJonesThermodynamicAverageControl
