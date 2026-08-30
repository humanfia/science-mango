import ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyHolderSmallBall

/-!
# Consumer for the three-site ordinary outer-family Hölder small ball

This consumer exposes the zero-width boundary, the all-width cube-root
estimate, the four individual actual history events, and their exact finite
union without a loss in the constant.
-/

open scoped ENNReal

namespace ArchonPhysicsConsumers.Thermalization

namespace ActualThreeSiteIteratedA2OrdinaryOuterFamilyHolderSmallBallConsumer

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyHolderSmallBall
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily
open ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeSmallBall
open ArchonPhysics.ThreeParameterSpectralAveragingDensity

noncomputable section

theorem concreteNearMismatch_zero :
    iidMassTripleLaw (threeSiteOuterNearMismatchEvent 0) = 0 :=
  iidMassTripleLaw_threeSiteOuterNearMismatchEvent_zero

theorem concreteNearMismatch_allWidthHolder
    {epsilon : Real} (hepsilon : 0 ≤ epsilon) :
    iidMassTripleLaw (threeSiteOuterNearMismatchEvent epsilon) ≤
      840 * ENNReal.ofReal (epsilon ^ ((3 : Real)⁻¹)) :=
  iidMassTripleLaw_threeSiteOuterNearMismatchEvent_le_holder hepsilon

theorem displayedOrdinaryOuterHistory_card :
    Fintype.card ThreeSiteOrdinaryOuterHistoryIndex = 4 :=
  card_threeSiteOrdinaryOuterHistoryIndex

theorem oneHistoryNearMismatchEvent_exact
    (index : ThreeSiteOrdinaryOuterHistoryIndex) (epsilon : Real) :
    threeSiteOrdinaryOuterHistoryNearMismatchEvent index epsilon =
      threeSiteOuterNearMismatchEvent epsilon :=
  threeSiteOrdinaryOuterHistoryNearMismatchEvent_eq index epsilon

theorem oneHistoryNearMismatch_allWidthHolder
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    {epsilon : Real} (hepsilon : 0 ≤ epsilon) :
    iidMassTripleLaw
        (threeSiteOrdinaryOuterHistoryNearMismatchEvent index epsilon) ≤
      840 * ENNReal.ofReal (epsilon ^ ((3 : Real)⁻¹)) :=
  iidMassTripleLaw_threeSiteOrdinaryOuterHistoryNearMismatchEvent_le
    index hepsilon

theorem fourHistoryNearMismatchUnion_exact (epsilon : Real) :
    threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent epsilon =
      threeSiteOuterNearMismatchEvent epsilon :=
  threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent_eq epsilon

theorem fourHistoryNearMismatchUnion_allWidthHolder
    {epsilon : Real} (hepsilon : 0 ≤ epsilon) :
    iidMassTripleLaw
        (threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent epsilon) ≤
      840 * ENNReal.ofReal (epsilon ^ ((3 : Real)⁻¹)) :=
  iidMassTripleLaw_threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent_le
    hepsilon

#print axioms concreteNearMismatch_zero
#print axioms concreteNearMismatch_allWidthHolder
#print axioms displayedOrdinaryOuterHistory_card
#print axioms oneHistoryNearMismatchEvent_exact
#print axioms oneHistoryNearMismatch_allWidthHolder
#print axioms fourHistoryNearMismatchUnion_exact
#print axioms fourHistoryNearMismatchUnion_allWidthHolder

end


end ActualThreeSiteIteratedA2OrdinaryOuterFamilyHolderSmallBallConsumer

end ArchonPhysicsConsumers.Thermalization
