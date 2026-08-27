import ArchonPhysics.LennardJonesForceTaylorTube

/-!
# Finite-volume averaging of the Lennard--Jones force Taylor remainder

This module lifts the pointwise force-remainder estimate from
`LennardJonesForceTaylorTube` to a finite periodic lattice. It controls the
absolute force remainder per site by the empirical fourth relative-strain
moment, and then by a bound independent of the number of sites.

These are static, instantaneous estimates for one strain configuration. They
do not control time accumulation along a trajectory and do not establish a
kinetic-time approximation.
-/

namespace ArchonPhysics.LennardJonesForceTaylorLattice

open ArchonPhysics.LennardJonesForceTaylorTube
open ArchonPhysics.BondPotentialHamiltonianPhyslib

noncomputable section

/-- Absolute Lennard--Jones force Taylor remainder, averaged over lattice sites. -/
def perSiteAbsoluteForceRemainder {N : Nat} [NeZero N]
    (depth r₀ : Real) (strain : Lattice.Site N → Real) : Real :=
  (∑ i : Lattice.Site N,
      |lennardJonesDerivative depth r₀ (strain i) -
        localAlphaBetaForce depth r₀ (strain i)|) / (N : Real)

/-- Empirical fourth moment of the relative bond strain. -/
def empiricalRelativeFourthStrainMoment {N : Nat} [NeZero N]
    (r₀ : Real) (strain : Lattice.Site N → Real) : Real :=
  (∑ i : Lattice.Site N, (|strain i| / r₀) ^ 4) / (N : Real)

/-- Under one uniform relative tube, the per-site force remainder is controlled
by the empirical fourth relative-strain moment. This is an instantaneous
finite-volume estimate, not a time-integrated error bound. -/
theorem perSiteAbsoluteForceRemainder_le_fourthMoment
    {N : Nat} [NeZero N]
    {depth r₀ rho : Real} (strain : Lattice.Site N → Real)
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (htube : ∀ i, |strain i| ≤ rho * r₀) :
    perSiteAbsoluteForceRemainder depth r₀ strain ≤
      depth / r₀ * forceRemainderTubeConstant rho *
        empiricalRelativeFourthStrainMoment r₀ strain := by
  have hN : 0 < (N : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hsum :
      (∑ i : Lattice.Site N,
        |lennardJonesDerivative depth r₀ (strain i) -
          localAlphaBetaForce depth r₀ (strain i)|) ≤
      ∑ i : Lattice.Site N,
        depth / r₀ * forceRemainderTubeConstant rho *
          (|strain i| / r₀) ^ 4 := by
    exact Finset.sum_le_sum fun i _ ↦
      abs_lennardJonesDerivative_sub_localAlphaBetaForce_le
        hdepth hr₀ hrho0 hrho1 (htube i)
  unfold perSiteAbsoluteForceRemainder empiricalRelativeFourthStrainMoment
  calc
    (∑ i : Lattice.Site N,
        |lennardJonesDerivative depth r₀ (strain i) -
          localAlphaBetaForce depth r₀ (strain i)|) / (N : Real) ≤
        (∑ i : Lattice.Site N,
          depth / r₀ * forceRemainderTubeConstant rho *
            (|strain i| / r₀) ^ 4) / (N : Real) :=
      (div_le_div_iff_of_pos_right hN).2 hsum
    _ = depth / r₀ * forceRemainderTubeConstant rho *
        ((∑ i : Lattice.Site N, (|strain i| / r₀) ^ 4) /
          (N : Real)) := by
      rw [← Finset.mul_sum]
      ring

/-- The uniform tube implies an `N`-independent `rho ^ 4` force-remainder
bound. The conclusion is still static and instantaneous; it says nothing
about persistence of the tube or accumulation over kinetic time. -/
theorem perSiteAbsoluteForceRemainder_le_tubePower
    {N : Nat} [NeZero N]
    {depth r₀ rho : Real} (strain : Lattice.Site N → Real)
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (htube : ∀ i, |strain i| ≤ rho * r₀) :
    perSiteAbsoluteForceRemainder depth r₀ strain ≤
      depth / r₀ * forceRemainderTubeConstant rho * rho ^ 4 := by
  have hmoment := perSiteAbsoluteForceRemainder_le_fourthMoment
    strain hdepth hr₀ hrho0 hrho1 htube
  have hN : 0 < (N : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hratio : ∀ i, |strain i| / r₀ ≤ rho := fun i ↦
    (div_le_iff₀ hr₀).2 (htube i)
  have hsum :
      (∑ i : Lattice.Site N, (|strain i| / r₀) ^ 4) ≤
        ∑ _i : Lattice.Site N, rho ^ 4 := by
    exact Finset.sum_le_sum fun i _ ↦
      pow_le_pow_left₀ (div_nonneg (abs_nonneg _) hr₀.le) (hratio i) 4
  have haverage : empiricalRelativeFourthStrainMoment r₀ strain ≤ rho ^ 4 := by
    unfold empiricalRelativeFourthStrainMoment
    calc
      (∑ i : Lattice.Site N, (|strain i| / r₀) ^ 4) / (N : Real) ≤
          (∑ _i : Lattice.Site N, rho ^ 4) / (N : Real) :=
        (div_le_div_iff_of_pos_right hN).2 hsum
      _ = rho ^ 4 := by
        simp [Lattice.Site, ne_of_gt hN]
  exact hmoment.trans <|
    mul_le_mul_of_nonneg_left haverage
      (mul_nonneg (div_nonneg hdepth hr₀.le)
        (forceRemainderTubeConstant_pos hrho0 hrho1).le)

end

end ArchonPhysics.LennardJonesForceTaylorLattice
