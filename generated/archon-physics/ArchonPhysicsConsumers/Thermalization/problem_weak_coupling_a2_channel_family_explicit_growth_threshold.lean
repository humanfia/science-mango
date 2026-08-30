import ArchonPhysics.WeakCouplingA2ChannelFamilyExplicitGrowthThreshold

/-!
Consumer for the explicit subcritical power-growth threshold for growing A2
channel families.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.WeakCouplingA2ChannelFamilyExplicitGrowthThreshold
open ArchonPhysics.WeakCouplingA2ChannelFamilyKineticAccumulation
open Filter
open scoped BigOperators Topology

example (exponent : Real) (hexponent : exponent < 2) :
    Tendsto
      (fun coupling : Real =>
        weakCouplingLogarithmicFactor coupling *
          coupling ^ (-exponent))
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_logarithmicFactor_mul_rpow_neg_of_lt_two exponent hexponent

example (cardExponent costExponent : Real)
    (hexponents : cardExponent + costExponent < 2) :
    Tendsto
      (fun coupling : Real =>
        weakCouplingLogarithmicFactor coupling *
          coupling ^ (-(cardExponent + costExponent)))
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_logarithmicFactor_mul_rpow_neg_add_of_add_lt_two
    cardExponent costExponent hexponents

example {Index : Type*}
    (active : Real -> Finset Index)
    (family : Index -> Real -> Real) (cost : Index -> Real)
    (uniformCost : Real -> Real)
    (cardExponent costExponent cardConstant costConstant : Real)
    (hexponents : cardExponent + costExponent < 2)
    (hcardConstant : 0 <= cardConstant)
    (hfamilyNonneg : forall index coupling,
      0 <= family index coupling)
    (hfamilyBound : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      ∀ index ∈ active coupling,
        family index coupling <=
          weakCouplingLogarithmicFactor coupling * cost index)
    (huniformCost : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      ∀ index ∈ active coupling,
        cost index <= uniformCost coupling)
    (hcard : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      ((active coupling).card : Real) <=
        cardConstant * coupling ^ (-cardExponent))
    (hcostNonneg : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      0 <= uniformCost coupling)
    (hcost : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      uniformCost coupling <=
        costConstant * coupling ^ (-costExponent)) :
    Tendsto
      (fun coupling =>
        ∑ index ∈ active coupling, family index coupling)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_growingFinset_sum_of_rpow_card_uniformCost active family cost
    uniformCost cardExponent costExponent cardConstant costConstant
      hexponents hcardConstant hfamilyNonneg hfamilyBound
      huniformCost hcard hcostNonneg hcost

#print axioms tendsto_logarithmicFactor_mul_rpow_neg_of_lt_two
#print axioms
  tendsto_logarithmicFactor_mul_card_mul_uniformCost_of_rpow_envelopes
#print axioms tendsto_growingFinset_sum_of_rpow_card_uniformCost

end ArchonPhysicsConsumers.Thermalization
