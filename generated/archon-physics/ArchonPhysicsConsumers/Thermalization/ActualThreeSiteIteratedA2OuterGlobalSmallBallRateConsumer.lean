import ArchonPhysics.ActualThreeSiteIteratedA2OuterGlobalSmallBallRate

/-!
# Consumer for the global three-site outer small-ball rate

This consumer exposes the fixed-sign middle-mass derivative, global
injectivity, explicit exceptional-mass budget, and the resulting atlas-free
small-ball estimate used by the thermalization pipeline.
-/

open scoped ENNReal

namespace ArchonPhysicsConsumers.Thermalization

namespace ActualThreeSiteIteratedA2OuterGlobalSmallBallRateConsumer

open ArchonPhysics
open ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
open ArchonPhysics.ActualThreeSiteIteratedA2OuterCompactAtlas
open ArchonPhysics.ActualThreeSiteIteratedA2OuterGlobalSmallBallRate
open ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeBridges
open ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeSmallBall
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterProjectorWeightJacobian
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Set

noncomputable section

theorem middleMassDerivative_strictlyPositive
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (hne : triple.1.1⁻¹ ≠ triple.2⁻¹) :
    0 < threeSiteOuterTripleMismatchDerivative triple (massTripleBasis 1) :=
  threeSiteOuterTripleMismatchDerivative_second_pos htriple hne

theorem augmentedChart_globalInjective
    {delta : Real} (hdelta : 0 < delta) :
    InjOn threeSiteOuterAugmentedChart
      (threeSiteOuterGlobalGoodSet delta) :=
  injOn_threeSiteOuterAugmentedChart_globalGood hdelta

theorem globalExceptionalMass_le_tenDelta
    {delta : Real} (hdelta : 0 ≤ delta) :
    iidMassTripleLaw (threeSiteOuterGlobalGoodSet delta)ᶜ ≤
      10 * ENNReal.ofReal delta :=
  iidMassTripleLaw_globalGood_compl_le hdelta

theorem globalSmallBall_explicitDet
    {delta epsilon : Real} (hdelta : 0 < delta) (hepsilon : 0 ≤ epsilon) :
    iidMassTripleLaw (threeSiteOuterNearMismatchEvent epsilon) ≤
      (27 * (ENNReal.ofReal (delta ^ 2 / 4000))⁻¹) *
          (8 * ENNReal.ofReal epsilon) +
        10 * ENNReal.ofReal delta :=
  iidMassTripleLaw_threeSiteOuterNearMismatchEvent_le_explicitDet
    hdelta hepsilon

theorem globalSmallBall_explicit
    {delta epsilon : Real} (hdelta : 0 < delta) (hepsilon : 0 ≤ epsilon) :
    iidMassTripleLaw (threeSiteOuterNearMismatchEvent epsilon) ≤
      10 * ENNReal.ofReal delta +
        864000 * ENNReal.ofReal epsilon * (ENNReal.ofReal delta)⁻¹ ^ 2 :=
  iidMassTripleLaw_threeSiteOuterNearMismatchEvent_le_explicit
    hdelta hepsilon

theorem globalSmallBall_cube_le
    {rho : Real} (hrho : 0 < rho) :
    iidMassTripleLaw (threeSiteOuterNearMismatchEvent (rho ^ 3)) ≤
      840 * ENNReal.ofReal rho :=
  iidMassTripleLaw_threeSiteOuterNearMismatchEvent_cube_le hrho

#print axioms middleMassDerivative_strictlyPositive
#print axioms augmentedChart_globalInjective
#print axioms globalExceptionalMass_le_tenDelta
#print axioms globalSmallBall_explicitDet
#print axioms globalSmallBall_explicit
#print axioms globalSmallBall_cube_le

end

end ActualThreeSiteIteratedA2OuterGlobalSmallBallRateConsumer

end ArchonPhysicsConsumers.Thermalization
