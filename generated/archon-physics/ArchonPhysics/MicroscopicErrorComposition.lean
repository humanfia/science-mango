import ArchonPhysics.MicroscopicErrorProbabilityUpgrade

/-!
# Composition of two microscopic error budgets

This module is a model-independent F3 adapter for the common decomposition

`total error = leading microscopic error + higher-order remainder`.

Each summand is controlled deterministically on its own measurable good event.
The combined good event is their intersection, its complement is bounded by a
union bound, and the two deterministic and probabilistic budgets are added.
If all four input budgets vanish, the resulting total error satisfies the
exact zero-neighbourhood law used by the project and hence converges to zero in
probability.

The certificate below contains only explicit inputs: measurability, on-event
estimates, probability inequalities, and four limits.  It does not assert a
random-phase propagation theorem, a Lennard--Jones tube estimate, or a
microscopic-to-kinetic approximation.
-/

namespace ArchonPhysics.MicroscopicErrorComposition

open ArchonPhysics
open ArchonPhysics.MicroscopicErrorProbabilityUpgrade
open ArchonPhysics.ProbabilisticHittingTransfer
open ArchonPhysics.ThermalizationTransfer
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The transparent two-term error used by the composition lemma. -/
def twoTermError
    (leadingError higherRemainderError : Nat → Omega → ENNReal) :
    Nat → Omega → ENNReal :=
  fun n omega ↦ leadingError n omega + higherRemainderError n omega

/-- Both component estimates hold on the intersection of their good events. -/
def intersectedGoodEvent
    (leadingGoodEvent higherRemainderGoodEvent : Nat → Set Omega) :
    Nat → Set Omega :=
  fun n ↦ leadingGoodEvent n ∩ higherRemainderGoodEvent n

/-- The deterministic budget for the sum is the sum of the two budgets. -/
def summedDeterministicBudget
    (leadingBudget higherRemainderBudget : Nat → ENNReal) : Nat → ENNReal :=
  fun n ↦ leadingBudget n + higherRemainderBudget n

/-- The union-bound budget is the sum of the two bad-event budgets. -/
def summedBadProbabilityBudget
    (leadingBadBudget higherRemainderBadBudget : Nat → ENNReal) :
    Nat → ENNReal :=
  fun n ↦ leadingBadBudget n + higherRemainderBadBudget n

/-- All primitive hypotheses needed to compose a leading error and a
higher-order remainder.  No convergence conclusion is stored as a field. -/
structure TwoTermGoodEventBudgetCertificate
    (probability : Measure Omega)
    (leadingError higherRemainderError : Nat → Omega → ENNReal) where
  leadingGoodEvent : Nat → Set Omega
  higherRemainderGoodEvent : Nat → Set Omega
  leadingDeterministicBudget : Nat → ENNReal
  higherRemainderDeterministicBudget : Nat → ENNReal
  leadingBadProbabilityBudget : Nat → ENNReal
  higherRemainderBadProbabilityBudget : Nat → ENNReal
  leadingError_measurable : ∀ n, Measurable (leadingError n)
  higherRemainderError_measurable :
    ∀ n, Measurable (higherRemainderError n)
  leadingGoodEvent_measurable : ∀ n, MeasurableSet (leadingGoodEvent n)
  higherRemainderGoodEvent_measurable :
    ∀ n, MeasurableSet (higherRemainderGoodEvent n)
  leadingError_le_on_good : ∀ n omega, omega ∈ leadingGoodEvent n →
    leadingError n omega ≤ leadingDeterministicBudget n
  higherRemainderError_le_on_good :
    ∀ n omega, omega ∈ higherRemainderGoodEvent n →
      higherRemainderError n omega ≤ higherRemainderDeterministicBudget n
  leadingDeterministicBudget_zero :
    Tendsto leadingDeterministicBudget atTop (nhds 0)
  higherRemainderDeterministicBudget_zero :
    Tendsto higherRemainderDeterministicBudget atTop (nhds 0)
  leadingBadProbability_le : ∀ n,
    probability (leadingGoodEvent n)ᶜ ≤ leadingBadProbabilityBudget n
  higherRemainderBadProbability_le : ∀ n,
    probability (higherRemainderGoodEvent n)ᶜ ≤
      higherRemainderBadProbabilityBudget n
  leadingBadProbabilityBudget_zero :
    Tendsto leadingBadProbabilityBudget atTop (nhds 0)
  higherRemainderBadProbabilityBudget_zero :
    Tendsto higherRemainderBadProbabilityBudget atTop (nhds 0)

theorem measurable_twoTermError
    (leadingError higherRemainderError : Nat → Omega → ENNReal)
    (hleading : ∀ n, Measurable (leadingError n))
    (hhigher : ∀ n, Measurable (higherRemainderError n)) :
    ∀ n, Measurable (twoTermError leadingError higherRemainderError n) := by
  intro n
  exact (hleading n).add (hhigher n)

theorem measurableSet_intersectedGoodEvent
    (leadingGoodEvent higherRemainderGoodEvent : Nat → Set Omega)
    (hleading : ∀ n, MeasurableSet (leadingGoodEvent n))
    (hhigher : ∀ n, MeasurableSet (higherRemainderGoodEvent n)) :
    ∀ n, MeasurableSet
      (intersectedGoodEvent leadingGoodEvent higherRemainderGoodEvent n) := by
  intro n
  exact (hleading n).inter (hhigher n)

omit [MeasurableSpace Omega] in
/-- On the intersected good event, the total error is bounded by the sum of
the two deterministic budgets. -/
theorem twoTermError_le_on_intersectedGoodEvent
    (leadingError higherRemainderError : Nat → Omega → ENNReal)
    (leadingGoodEvent higherRemainderGoodEvent : Nat → Set Omega)
    (leadingBudget higherRemainderBudget : Nat → ENNReal)
    (hleading : ∀ n omega, omega ∈ leadingGoodEvent n →
      leadingError n omega ≤ leadingBudget n)
    (hhigher : ∀ n omega, omega ∈ higherRemainderGoodEvent n →
      higherRemainderError n omega ≤ higherRemainderBudget n) :
    ∀ n omega,
      omega ∈ intersectedGoodEvent
        leadingGoodEvent higherRemainderGoodEvent n →
      twoTermError leadingError higherRemainderError n omega ≤
        summedDeterministicBudget leadingBudget higherRemainderBudget n := by
  intro n omega homega
  exact add_le_add (hleading n omega homega.1) (hhigher n omega homega.2)

/-- The complement of the intersected good event is bounded by the sum of the
two supplied bad-event budgets.  This is the only union bound in the adapter. -/
theorem measure_intersectedGoodEvent_compl_le_summedBudget
    (probability : Measure Omega)
    (leadingGoodEvent higherRemainderGoodEvent : Nat → Set Omega)
    (leadingBadBudget higherRemainderBadBudget : Nat → ENNReal)
    (hleading : ∀ n,
      probability (leadingGoodEvent n)ᶜ ≤ leadingBadBudget n)
    (hhigher : ∀ n,
      probability (higherRemainderGoodEvent n)ᶜ ≤ higherRemainderBadBudget n) :
    ∀ n,
      probability
          (intersectedGoodEvent
            leadingGoodEvent higherRemainderGoodEvent n)ᶜ ≤
        summedBadProbabilityBudget
          leadingBadBudget higherRemainderBadBudget n := by
  intro n
  calc
    probability
        (intersectedGoodEvent
          leadingGoodEvent higherRemainderGoodEvent n)ᶜ =
        probability ((leadingGoodEvent n)ᶜ ∪
          (higherRemainderGoodEvent n)ᶜ) := by
      rw [intersectedGoodEvent, Set.compl_inter]
    _ ≤ probability (leadingGoodEvent n)ᶜ +
          probability (higherRemainderGoodEvent n)ᶜ :=
      MeasureTheory.measure_union_le _ _
    _ ≤ summedBadProbabilityBudget
          leadingBadBudget higherRemainderBadBudget n := by
      exact add_le_add (hleading n) (hhigher n)

omit [MeasurableSpace Omega] in
theorem summedDeterministicBudget_tendsto_zero
    (leadingBudget higherRemainderBudget : Nat → ENNReal)
    (hleading : Tendsto leadingBudget atTop (nhds 0))
    (hhigher : Tendsto higherRemainderBudget atTop (nhds 0)) :
    Tendsto
      (summedDeterministicBudget leadingBudget higherRemainderBudget)
      atTop (nhds 0) := by
  change Tendsto (fun n ↦ leadingBudget n + higherRemainderBudget n) atTop (nhds 0)
  simpa using hleading.add hhigher

omit [MeasurableSpace Omega] in
theorem summedBadProbabilityBudget_tendsto_zero
    (leadingBadBudget higherRemainderBadBudget : Nat → ENNReal)
    (hleading : Tendsto leadingBadBudget atTop (nhds 0))
    (hhigher : Tendsto higherRemainderBadBudget atTop (nhds 0)) :
    Tendsto
      (summedBadProbabilityBudget leadingBadBudget higherRemainderBadBudget)
      atTop (nhds 0) := by
  change Tendsto (fun n ↦ leadingBadBudget n + higherRemainderBadBudget n) atTop (nhds 0)
  simpa using hleading.add hhigher

/-- The explicit two-term certificate closes the exact project
`localUniformError_zero_law` for the sum of the two errors. -/
theorem localUniformError_zero_law_of_twoTermCertificate
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (leadingError higherRemainderError : Nat → Omega → ENNReal)
    (certificate : TwoTermGoodEventBudgetCertificate
      probability leadingError higherRemainderError) :
    ∀ U : Set ENNReal, MeasurableSet U → U ∈ nhds 0 →
      Tendsto
        (fun n ↦ probability
          ((twoTermError leadingError higherRemainderError n) ⁻¹' U))
        atTop (nhds 1) := by
  apply localUniformError_zero_law_of_goodEvent_budget
    probability (twoTermError leadingError higherRemainderError)
      (measurable_twoTermError leadingError higherRemainderError
        certificate.leadingError_measurable
        certificate.higherRemainderError_measurable)
      (intersectedGoodEvent certificate.leadingGoodEvent
        certificate.higherRemainderGoodEvent)
      (summedDeterministicBudget certificate.leadingDeterministicBudget
        certificate.higherRemainderDeterministicBudget)
      (summedBadProbabilityBudget certificate.leadingBadProbabilityBudget
        certificate.higherRemainderBadProbabilityBudget)
  · exact twoTermError_le_on_intersectedGoodEvent
      leadingError higherRemainderError
      certificate.leadingGoodEvent certificate.higherRemainderGoodEvent
      certificate.leadingDeterministicBudget
      certificate.higherRemainderDeterministicBudget
      certificate.leadingError_le_on_good
      certificate.higherRemainderError_le_on_good
  · exact summedDeterministicBudget_tendsto_zero
      certificate.leadingDeterministicBudget
      certificate.higherRemainderDeterministicBudget
      certificate.leadingDeterministicBudget_zero
      certificate.higherRemainderDeterministicBudget_zero
  · exact measure_intersectedGoodEvent_compl_le_summedBudget
      probability certificate.leadingGoodEvent
      certificate.higherRemainderGoodEvent
      certificate.leadingBadProbabilityBudget
      certificate.higherRemainderBadProbabilityBudget
      certificate.leadingBadProbability_le
      certificate.higherRemainderBadProbability_le
  · exact summedBadProbabilityBudget_tendsto_zero
      certificate.leadingBadProbabilityBudget
      certificate.higherRemainderBadProbabilityBudget
      certificate.leadingBadProbabilityBudget_zero
      certificate.higherRemainderBadProbabilityBudget_zero

/-- Bundled project interface for the composed microscopic error. -/
theorem convergesInProbabilityTo_zero_of_twoTermCertificate
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (leadingError higherRemainderError : Nat → Omega → ENNReal)
    (certificate : TwoTermGoodEventBudgetCertificate
      probability leadingError higherRemainderError) :
    ConvergesInProbabilityTo probability
      (twoTermError leadingError higherRemainderError) 0 := by
  exact ⟨
    measurable_twoTermError leadingError higherRemainderError
      certificate.leadingError_measurable
      certificate.higherRemainderError_measurable,
    localUniformError_zero_law_of_twoTermCertificate
      probability leadingError higherRemainderError certificate⟩

end

end ArchonPhysics.MicroscopicErrorComposition
