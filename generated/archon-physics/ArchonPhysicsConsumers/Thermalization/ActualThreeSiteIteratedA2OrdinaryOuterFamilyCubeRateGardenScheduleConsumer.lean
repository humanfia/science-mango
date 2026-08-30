import ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyCubeRateGardenSchedule

/-!
# Consumer for the actual ordinary-outer-family cube-rate schedule

This consumer exposes the actual four-history exceptional probability at the
sextic cutoff and the kinetic-time estimate obtained by using that probability
as both displayed bad terms.  The regular-good envelope bounds remain explicit
hypotheses.
-/

namespace ArchonPhysicsConsumers.Thermalization
namespace ActualThreeSiteIteratedA2OrdinaryOuterFamilyCubeRateGardenScheduleConsumer

open Filter Topology
open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2CubeRateGardenSchedule
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyCubeRateGardenSchedule
open ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA
open scoped ENNReal

noncomputable section

theorem actualFamilySexticProbability_le (g : Real) :
    ordinaryOuterFamilySexticCutoffBadBudgetENNReal g ≤
      840 * ENNReal.ofReal (squareCouplingCutoff g) :=
  ordinaryOuterFamilySexticCutoffBadBudgetENNReal_le g

theorem actualFamilySexticRealBudget_nonneg (g : Real) :
    0 ≤ ordinaryOuterFamilySexticCutoffBadBudget g :=
  ordinaryOuterFamilySexticCutoffBadBudget_nonneg g

theorem actualFamilySexticRealBudget_le (g : Real) :
    ordinaryOuterFamilySexticCutoffBadBudget g ≤
      840 * squareCouplingCutoff g :=
  ordinaryOuterFamilySexticCutoffBadBudget_le g

theorem actualQuadraticBadBudget_le (g : Real) :
    ordinaryOuterFamilyQuadraticBadBudget g ≤
      840 * squareCouplingCutoff g :=
  ordinaryOuterFamilyQuadraticBadBudget_le g

theorem actualQuarticBadBudget_le (g : Real) :
    ordinaryOuterFamilyQuarticBadBudget g ≤
      840 * squareCouplingCutoff g :=
  ordinaryOuterFamilyQuarticBadBudget_le g

/-- Consumer-facing kinetic-time result with both bad terms fixed to the
actual four-history ordinary outer probability. -/
theorem actualFamilyBudget_tendsto_zero_at_kineticTime
    (quadraticOrder quarticOrder : Nat)
    (g quadraticBudget quarticBudget : Nat → Real)
    (kappa beta tau : Real)
    (quadraticGoodCoefficient quarticGoodCoefficient : Real)
    (quadraticGlobal quarticGlobal : Real)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ n, g n ≠ 0)
    (hquadraticBudget0 : ∀ n, 0 ≤ quadraticBudget n)
    (hquarticBudget0 : ∀ n, 0 ≤ quarticBudget n)
    (hquadraticBudget : ∀ n,
      quadraticBudget n ≤
        cubeRateQuadraticGardenGoodEnvelope quadraticOrder
            quadraticGoodCoefficient (g n) +
          quadraticGlobal * ordinaryOuterFamilyQuadraticBadBudget (g n))
    (hquarticBudget : ∀ n,
      quarticBudget n ≤
        cubeRateQuarticGardenGoodEnvelope quarticOrder
            quarticGoodCoefficient (g n) +
          quarticGlobal * ordinaryOuterFamilyQuarticBadBudget (g n)) :
    Tendsto (fun n =>
      (|kappa * g n| * quadraticBudget n +
        |beta * (g n) ^ 2| * quarticBudget n) *
          |tau / (g n) ^ 2|) atTop (nhds 0) :=
  coupling_channel_budget_tendsto_zero_at_kineticTime_actualOrdinaryOuterFamily
    quadraticOrder quarticOrder g quadraticBudget quarticBudget
    kappa beta tau quadraticGoodCoefficient quarticGoodCoefficient
    quadraticGlobal quarticGlobal hg hg0
    hquadraticBudget0 hquarticBudget0 hquadraticBudget hquarticBudget

#print axioms actualFamilySexticProbability_le
#print axioms actualFamilySexticRealBudget_nonneg
#print axioms actualFamilySexticRealBudget_le
#print axioms actualQuadraticBadBudget_le
#print axioms actualQuarticBadBudget_le
#print axioms actualFamilyBudget_tendsto_zero_at_kineticTime

end


end ActualThreeSiteIteratedA2OrdinaryOuterFamilyCubeRateGardenScheduleConsumer
end ArchonPhysicsConsumers.Thermalization
