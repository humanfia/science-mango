import ArchonPhysics.MicroscopicErrorProbabilityUpgrade

/-!
# Consumer: microscopic error probability upgrade

These acceptance theorems expose the two model-independent ways to fill the
`ConditionalThermalizationCertificate.localUniformError_zero_law` field.
They do not provide the model-specific moment estimates, deterministic tube
bound, or probability of leaving the good event.
-/

namespace ArchonPhysicsConsumers.Thermalization.MicroscopicErrorProbabilityUpgrade

open ArchonPhysics.MicroscopicErrorProbabilityUpgrade
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A vanishing deterministic error on a high-probability good event supplies
the exact measurable-neighbourhood law expected by the F3 certificate. -/
theorem problem_goodEvent_budget_closes_localUniformError_zero_law
    (P : Measure Omega) [IsProbabilityMeasure P]
    (error : Nat → Omega → ENNReal)
    (herror : ∀ n, Measurable (error n))
    (goodEvent : Nat → Set Omega)
    (deterministicBudget badProbabilityBudget : Nat → ENNReal)
    (hcontrol : ∀ n omega, omega ∈ goodEvent n →
      error n omega ≤ deterministicBudget n)
    (hdeterministicBudget :
      Tendsto deterministicBudget atTop (nhds 0))
    (hbadProbability : ∀ n, P (goodEvent n)ᶜ ≤ badProbabilityBudget n)
    (hbadProbabilityBudget :
      Tendsto badProbabilityBudget atTop (nhds 0)) :
    ∀ U : Set ENNReal, MeasurableSet U → U ∈ 𝓝 0 →
      Tendsto (fun n => P (error n ⁻¹' U)) atTop (nhds 1) :=
  localUniformError_zero_law_of_goodEvent_budget
    P error herror goodEvent deterministicBudget badProbabilityBudget
    hcontrol hdeterministicBudget hbadProbability hbadProbabilityBudget

/-- Vanishing expectation of a nonnegative extended error supplies the same
certificate field by Markov's inequality. -/
theorem problem_firstMoment_closes_localUniformError_zero_law
    (P : Measure Omega) [IsProbabilityMeasure P]
    (error : Nat → Omega → ENNReal)
    (herror : ∀ n, Measurable (error n))
    (hfirstMoment : Tendsto
      (fun n => ∫⁻ omega, error n omega ∂P) atTop (nhds 0)) :
    ∀ U : Set ENNReal, MeasurableSet U → U ∈ 𝓝 0 →
      Tendsto (fun n => P (error n ⁻¹' U)) atTop (nhds 1) :=
  localUniformError_zero_law_of_lintegral_tendsto_zero
    P error herror hfirstMoment

/-- Vanishing second moment of a nonnegative extended error also supplies the
exact certificate field. -/
theorem problem_secondMoment_closes_localUniformError_zero_law
    (P : Measure Omega) [IsProbabilityMeasure P]
    (error : Nat → Omega → ENNReal)
    (herror : ∀ n, Measurable (error n))
    (hsecondMoment : Tendsto
      (fun n => ∫⁻ omega, (error n omega) ^ 2 ∂P)
      atTop (nhds 0)) :
    ∀ U : Set ENNReal, MeasurableSet U → U ∈ 𝓝 0 →
      Tendsto (fun n => P (error n ⁻¹' U)) atTop (nhds 1) :=
  localUniformError_zero_law_of_secondMoment_tendsto_zero
    P error herror hsecondMoment

#print axioms problem_goodEvent_budget_closes_localUniformError_zero_law
#print axioms problem_firstMoment_closes_localUniformError_zero_law
#print axioms problem_secondMoment_closes_localUniformError_zero_law

end


end ArchonPhysicsConsumers.Thermalization.MicroscopicErrorProbabilityUpgrade
