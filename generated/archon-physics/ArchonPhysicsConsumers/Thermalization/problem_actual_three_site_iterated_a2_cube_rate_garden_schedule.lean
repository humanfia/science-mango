import ArchonPhysics.ActualThreeSiteIteratedA2CubeRateGardenSchedule

/-!
# Consumer for the cube-rate three-site garden schedule

This consumer exposes the actual iid three-mass exceptional-event estimate,
its real-valued bad budget, and the sextic-cutoff power schedule used by the
kinetic-time RPA criterion.
-/

open scoped ENNReal

namespace ArchonPhysicsConsumers.Thermalization

namespace ActualThreeSiteIteratedA2CubeRateGardenScheduleConsumer

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2CubeRateGardenSchedule
open ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeSmallBall
open ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity

noncomputable section

theorem actualSmallBallAtSexticCutoff
    {g : Real} (hg : g ≠ 0) :
    iidMassTripleLaw
        (threeSiteOuterNearMismatchEvent (sexticCouplingCutoff g)) ≤
      840 * ENNReal.ofReal (squareCouplingCutoff g) :=
  iidMassTripleLaw_threeSiteOuterNearMismatchEvent_sextic_le hg

theorem actualRealBadBudgetAtSexticCutoff
    {g : Real} (hg : g ≠ 0) :
    threeSiteOuterSexticCutoffBadBudget g ≤
      840 * squareCouplingCutoff g :=
  threeSiteOuterSexticCutoffBadBudget_le hg

theorem quadraticGoodAfterKineticDivision
    (order : Nat) (coefficient : Real) {g : Real} (hg : g ≠ 0) :
    cubeRateQuadraticGardenGoodEnvelope order coefficient g / |g| =
      coefficient * |g| :=
  cubeRateQuadraticGardenGoodEnvelope_div_abs order coefficient hg

theorem quarticGoodAfterSexticDenominators
    (order : Nat) (coefficient : Real) {g : Real} (hg : g ≠ 0) :
    cubeRateQuarticGardenGoodEnvelope order coefficient g =
      coefficient * |g| :=
  cubeRateQuarticGardenGoodEnvelope_eq order coefficient hg

#check coupling_channel_budget_tendsto_zero_at_kineticTime_cubeRate

#print axioms actualSmallBallAtSexticCutoff
#print axioms actualRealBadBudgetAtSexticCutoff
#print axioms quadraticGoodAfterKineticDivision
#print axioms quarticGoodAfterSexticDenominators
#print axioms coupling_channel_budget_tendsto_zero_at_kineticTime_cubeRate

end

end ActualThreeSiteIteratedA2CubeRateGardenScheduleConsumer

end ArchonPhysicsConsumers.Thermalization
