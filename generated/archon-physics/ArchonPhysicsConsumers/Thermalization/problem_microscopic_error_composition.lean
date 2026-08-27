import ArchonPhysics.MicroscopicErrorComposition

/-!
# Consumer: composition of leading and higher microscopic errors

This consumer records the exact F3 interface obtained after separately
supplying measurable good-event estimates for the leading microscopic term
and the higher-order remainder.
-/

namespace ArchonPhysicsConsumers.Thermalization.MicroscopicErrorComposition

open Filter MeasureTheory Set Topology
open ArchonPhysics
open ArchonPhysics.ThermalizationTransfer
open ArchonPhysics.MicroscopicErrorComposition

noncomputable section

/-- The two explicit good-event packages compose to the exact neighbourhood
law requested by the project-level kinetic-window certificate. -/
theorem problem_twoTerm_goodEvent_budgets_close_localUniformError_zero_law
    {Omega : Type*} [MeasurableSpace Omega]
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (leadingError higherRemainderError : Nat → Omega → ENNReal)
    (certificate : TwoTermGoodEventBudgetCertificate
      probability leadingError higherRemainderError) :
    ∀ U : Set ENNReal, MeasurableSet U → U ∈ nhds 0 →
      Tendsto
        (fun n ↦ probability
          ((twoTermError leadingError higherRemainderError n) ⁻¹' U))
        atTop (nhds 1) := by
  exact localUniformError_zero_law_of_twoTermCertificate
    probability leadingError higherRemainderError certificate

/-- Bundled convergence-in-probability statement consumed by the generic F3
transfer layer. -/
theorem problem_twoTerm_goodEvent_budgets_convergeInProbability
    {Omega : Type*} [MeasurableSpace Omega]
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (leadingError higherRemainderError : Nat → Omega → ENNReal)
    (certificate : TwoTermGoodEventBudgetCertificate
      probability leadingError higherRemainderError) :
    ConvergesInProbabilityTo probability
      (twoTermError leadingError higherRemainderError) 0 := by
  exact convergesInProbabilityTo_zero_of_twoTermCertificate
    probability leadingError higherRemainderError certificate

#print axioms problem_twoTerm_goodEvent_budgets_close_localUniformError_zero_law
#print axioms problem_twoTerm_goodEvent_budgets_convergeInProbability
#print axioms localUniformError_zero_law_of_twoTermCertificate
#print axioms convergesInProbabilityTo_zero_of_twoTermCertificate

end

end ArchonPhysicsConsumers.Thermalization.MicroscopicErrorComposition
