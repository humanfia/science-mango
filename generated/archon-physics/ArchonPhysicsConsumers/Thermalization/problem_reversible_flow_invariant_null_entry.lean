import ArchonPhysics.ReversibleFlowInvariantNullEntry

/-!
# Consumer: invariant null sets under a reversible flow

This consumer records the exact conditional obstruction relevant to proposed
periodic-orbit or attractor exceptional sets.  It assumes invariance and
nullity; it does not assert those properties for a microscopic LJ chain.
-/

namespace ArchonPhysicsConsumers.Thermalization.ReversibleFlowInvariantNullEntry

open MeasureTheory Set
open ArchonPhysics.ReversibleFlowInvariantNullEntry

noncomputable section

variable {X : Type*} [AddAction ℝ X] [MeasurableSpace X]
variable {μ : Measure X} {A : Set X}

/-- A measurable invariant null exceptional set is exactly its own ever-entry
set, and almost every initial condition never enters it. -/
theorem problem_invariant_null_set_nonentry
    (hA : InvariantNullSet μ A) :
    everEnters A = A ∧
      MeasurableSet (everEnters A) ∧
      μ (everEnters A) = 0 ∧
      (∀ᵐ x ∂μ, ¬∃ t : ℝ, t +ᵥ x ∈ A) := by
  obtain ⟨hmeasurable, hnull, hae⟩ := hA.everEnters_certificate
  exact ⟨everEnters_eq_of_flowInvariant hA.invariant,
    hmeasurable, hnull, hae⟩

/-- A fixed measure-preserving time map cannot pull a null exceptional set
back to a positive-measure set. -/
theorem problem_fixed_time_null_preimage
    (t : ℝ) (hpreserving : MeasurePreserving (fun x : X ↦ t +ᵥ x) μ μ)
    (hAnull : μ A = 0) :
    μ ((fun x : X ↦ t +ᵥ x) ⁻¹' A) = 0 :=
  measure_fixedTime_preimage_eq_zero t A hpreserving hAnull

omit [AddAction ℝ X] in
/-- Conditional recurrence obstruction: with a finite invariant measure,
almost every initially above-threshold state fails the same threshold
infinitely often and therefore cannot settle below it forever. -/
theorem problem_fixed_size_permanent_settling_obstruction
    [TopologicalSpace X] [SecondCountableTopology X]
    [OpensMeasurableSpace X] [IsFiniteMeasure μ]
    (step : X → X) (hstep : MeasurePreserving step μ μ)
    (error : X → ℝ) (herror : Continuous error) (delta : ℝ) :
    ∀ᵐ x ∂μ, delta < error x →
      ¬∃ cutoff : ℕ, ∀ n ≥ cutoff, error (step^[n] x) ≤ delta :=
  ae_no_permanent_error_bound_of_measurePreserving
    step hstep error herror delta

/-- Conditional periodic-orbit certificate.  The assumptions explicitly
include measurability and nullity of the full periodic-point set. -/
theorem problem_periodic_orbit_nonentry
    (hperiodicMeasurable : MeasurableSet (periodicPoints : Set X))
    (hperiodicNull : μ (periodicPoints : Set X) = 0) :
    everEnters (periodicPoints : Set X) = periodicPoints ∧
      MeasurableSet (everEnters (periodicPoints : Set X)) ∧
      μ (everEnters (periodicPoints : Set X)) = 0 ∧
      (∀ᵐ x ∂μ,
        ¬∃ t : ℝ, t +ᵥ x ∈ (periodicPoints : Set X)) := by
  exact problem_invariant_null_set_nonentry
    (periodicPoints_invariantNullSet hperiodicMeasurable hperiodicNull)

#print axioms problem_invariant_null_set_nonentry
#print axioms problem_fixed_time_null_preimage
#print axioms problem_fixed_size_permanent_settling_obstruction
#print axioms problem_periodic_orbit_nonentry

end


end ArchonPhysicsConsumers.Thermalization.ReversibleFlowInvariantNullEntry
