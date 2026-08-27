import ArchonPhysics.LennardJonesQuantitativeTaylorTube
import ArchonPhysics.LennardJonesThermodynamicThreshold

/-!
# Consumer: sharp quantitative LJ Taylor tube

This consumer records the radius-dependent pointwise and thermodynamic
per-site remainder endpoints.  It deliberately makes no long-time flow
comparison or thermalization-transfer claim.
-/

namespace ArchonPhysicsConsumers.Thermalization.LennardJonesQuantitativeTaylorTube

open ArchonPhysics.LennardJonesPotential
open ArchonPhysics.LennardJonesThermodynamicThreshold
open ArchonPhysics.LennardJonesQuantitativeTaylorTube

noncomputable section

/-- At relative strain `1/40`, the sharp radius-dependent constant is below
`6553`; the bound retains the actual fifth power of the strain. -/
theorem one_div_forty_pointwise_remainder
    {depth r0 x : Real}
    (hdepth : 0 <= depth) (hr0 : 0 < r0)
    (hx : |x| <= (1 / 40 : Real) * r0) :
    |bondPotential depth r0 x - localAlphaBetaPotential depth r0 x| <=
      depth * 6553 * (|x| / r0) ^ 5 := by
  calc
    |bondPotential depth r0 x - localAlphaBetaPotential depth r0 x| <=
        depth * fourthOrderTubeConstant (1 / 40 : Real) *
          (|x| / r0) ^ 5 :=
      abs_bondPotential_sub_localAlphaBetaPotential_le
        hdepth hr0 (by norm_num) (by norm_num) hx
    _ <= depth * 6553 * (|x| / r0) ^ 5 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          fourthOrderTubeConstant_one_div_forty_lt.le hdepth)
        (pow_nonneg (div_nonneg (abs_nonneg _) hr0.le) 5)

/-- Uniformly in the finite lattice size, putting every bond in the `1/40`
tube bounds the per-site summed Taylor error by `6.4e-5 * depth`. -/
theorem one_div_forty_perSite_remainder
    {N : Nat} [NeZero N]
    {depth r0 : Real} (strain : ArchonPhysics.Lattice.Site N -> Real)
    (hdepth : 0 <= depth) (hr0 : 0 < r0)
    (htube : forall i, |strain i| <= (1 / 40 : Real) * r0) :
    perSiteAbsoluteFourthOrderRemainder depth r0 strain <=
      depth * (64 / 1000000 : Real) := by
  calc
    perSiteAbsoluteFourthOrderRemainder depth r0 strain <=
        depth * fourthOrderTubeConstant (1 / 40 : Real) *
          (1 / 40 : Real) ^ 5 :=
      perSiteAbsoluteFourthOrderRemainder_le_tubePower
        strain hdepth hr0 (by norm_num) (by norm_num) htube
    _ <= depth * (64 / 1000000 : Real) := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left
          fourthOrderTubeConstant_mul_one_div_forty_pow_five_lt.le hdepth

/-- Restricted-good-bond endpoint: no all-bond tube assumption is made, and
the exact good-bond fraction remains visible. -/
theorem restricted_goodBond_perSite_remainder
    {N : Nat} [NeZero N]
    {depth r0 rho : Real} (strain : ArchonPhysics.Lattice.Site N -> Real)
    (hdepth : 0 <= depth) (hr0 : 0 < r0)
    (hrho0 : 0 <= rho) (hrho1 : rho < 1) :
    perSiteGoodBondAbsoluteFourthOrderRemainder depth r0 rho strain <=
      depth * fourthOrderTubeConstant rho * rho ^ 5 *
        ((relativeTaylorGoodBondSet r0 rho strain).card : Real) / (N : Real) :=
  perSiteGoodBondAbsoluteFourthOrderRemainder_le_cardFraction
    strain hdepth hr0 hrho0 hrho1

/-- Consumer-level link to the existing balanced `s = t^7`, `rho = t^2`
thermodynamic-average parametrization. -/
theorem balanced_perSite_remainder_div_energyRatio
    {N : Nat} [NeZero N]
    {depth r0 t : Real} (strain : ArchonPhysics.Lattice.Site N -> Real)
    (hdepth : 0 < depth) (hr0 : 0 < r0)
    (ht0 : 0 < t) (ht1 : t < 1)
    (htube : forall i, |strain i| <= balancedTubeRadius t * r0) :
    perSiteAbsoluteFourthOrderRemainder depth r0 strain /
        (depth * balancedEnergyRatio t) <=
      fourthOrderTubeConstant (balancedTubeRadius t) * t ^ 3 := by
  simpa [balancedEnergyRatio, balancedTubeRadius] using
    perSiteAbsoluteFourthOrderRemainder_div_balancedEnergyRatio_le
      strain hdepth hr0 ht0 ht1 htube

#check abs_dimensionlessFourthOrderNumerator_le_radiusPolynomial
#check abs_bondPotential_sub_localAlphaBetaPotential_le
#check perSiteAbsoluteFourthOrderRemainder_le_fifthMoment
#check perSiteAbsoluteFourthOrderRemainder_le_tubePower
#check perSiteGoodBondAbsoluteFourthOrderRemainder_le_cardFraction
#check perSiteAbsoluteFourthOrderRemainder_div_balancedEnergyRatio_le
#check fourthOrderTubeConstant_one_div_forty_lt
#check fourthOrderTubeConstant_mul_one_div_forty_pow_five_lt

#print axioms one_div_forty_pointwise_remainder
#print axioms one_div_forty_perSite_remainder
#print axioms restricted_goodBond_perSite_remainder
#print axioms balanced_perSite_remainder_div_energyRatio

end

end ArchonPhysicsConsumers.Thermalization.LennardJonesQuantitativeTaylorTube
