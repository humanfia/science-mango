import Mathlib

/-!
# Reversible flows cannot enter an invariant null set from outside

An additive action of `ℝ` is used as the algebraic part of a two-sided flow.
If a set is forward invariant for every real time, negative time makes
membership equivalent along each orbit.  Consequently, the set of initial
points whose orbit ever enters an invariant set is exactly that set.

For a null invariant set this gives a zero-measure (and hence almost-sure)
non-entry statement.  The periodic-point corollary is deliberately
conditional on the whole periodic-point set being measurable and null.  This
module does **not** prove that periodic points of a Lennard--Jones lattice are
null.  It also does not exclude asymptotic approach without entry, invariant
sets of positive measure, or attractors under hypotheses weaker than the ones
stated here.
-/

namespace ArchonPhysics.ReversibleFlowInvariantNullEntry

open MeasureTheory Set Filter Topology

noncomputable section

variable {X : Type*} [AddAction ℝ X]

/-- Invariance under every real-time map of a reversible additive action.

Only the forward `MapsTo` formulation is stored.  Since time ranges over the
additive group `ℝ`, applying the same assumption at `-t` recovers the reverse
implication. -/
def FlowInvariant (A : Set X) : Prop :=
  ∀ t : ℝ, MapsTo (fun x : X ↦ t +ᵥ x) A A

/-- Initial points whose two-sided orbit enters `A` at some real time. -/
def everEnters (A : Set X) : Set X :=
  {x | ∃ t : ℝ, t +ᵥ x ∈ A}

/-- Membership in an invariant set is constant along every orbit. -/
theorem flowInvariant_vadd_mem_iff {A : Set X} (hA : FlowInvariant A)
    (t : ℝ) (x : X) :
    t +ᵥ x ∈ A ↔ x ∈ A := by
  constructor
  · intro htx
    have hback := hA (-t) htx
    simpa [← add_vadd] using hback
  · intro hx
    exact hA t hx

/-- Every fixed-time preimage of an invariant set is the set itself. -/
theorem preimage_vadd_eq_of_flowInvariant {A : Set X}
    (hA : FlowInvariant A) (t : ℝ) :
    (fun x : X ↦ t +ᵥ x) ⁻¹' A = A := by
  ext x
  exact flowInvariant_vadd_mem_iff hA t x

/-- Reversibility upgrades "ever enters" to exact equality with the invariant
set.  In particular, an orbit starting outside `A` never enters `A`. -/
theorem everEnters_eq_of_flowInvariant {A : Set X}
    (hA : FlowInvariant A) :
    everEnters A = A := by
  ext x
  constructor
  · rintro ⟨t, htx⟩
    exact (flowInvariant_vadd_mem_iff hA t x).mp htx
  · intro hx
    exact ⟨0, by simpa using hx⟩

section Measure

variable [MeasurableSpace X] {μ : Measure X}

/-- A measurable invariant set of measure zero, packaged with precisely the
hypotheses used by the non-entry certificate. -/
structure InvariantNullSet (μ : Measure X) (A : Set X) : Prop where
  invariant : FlowInvariant A
  measurableSet : MeasurableSet A
  measure_zero : μ A = 0

/-- The ever-entry set of a measurable invariant set is measurable. -/
theorem measurableSet_everEnters_of_flowInvariant {A : Set X}
    (hA : FlowInvariant A) (hAmeasurable : MeasurableSet A) :
    MeasurableSet (everEnters A) := by
  rw [everEnters_eq_of_flowInvariant hA]
  exact hAmeasurable

/-- Ever entering an invariant null set has measure zero.  No uncountable
union of time slices is used: the ever-entry set is first identified exactly
with `A`. -/
theorem measure_everEnters_eq_zero_of_flowInvariant {A : Set X}
    (hA : FlowInvariant A) (hAnull : μ A = 0) :
    μ (everEnters A) = 0 := by
  rw [everEnters_eq_of_flowInvariant hA]
  exact hAnull

/-- Almost every initial point never enters an invariant null set. -/
theorem ae_neverEnters_of_flowInvariant {A : Set X}
    (hA : FlowInvariant A) (hAnull : μ A = 0) :
    ∀ᵐ x ∂μ, ¬∃ t : ℝ, t +ᵥ x ∈ A := by
  simpa only [everEnters, Set.mem_ofPred_eq] using
    (measure_eq_zero_iff_ae_notMem.mp
      (measure_everEnters_eq_zero_of_flowInvariant hA hAnull))

/-- Bundled invariant-null sets have measurable, null ever-entry sets. -/
theorem InvariantNullSet.everEnters_certificate {A : Set X}
    (hA : InvariantNullSet μ A) :
    MeasurableSet (everEnters A) ∧
      μ (everEnters A) = 0 ∧
      (∀ᵐ x ∂μ, ¬∃ t : ℝ, t +ᵥ x ∈ A) := by
  exact ⟨measurableSet_everEnters_of_flowInvariant hA.invariant hA.measurableSet,
    measure_everEnters_eq_zero_of_flowInvariant hA.invariant hA.measure_zero,
    ae_neverEnters_of_flowInvariant hA.invariant hA.measure_zero⟩

/-- A measure-preserving time map pulls every null set back to a null set.

Unlike the invariant-set result, this fixed-time statement does not require
`A` itself to be invariant. -/
theorem measure_fixedTime_preimage_eq_zero
    (t : ℝ) (A : Set X)
    (hpreserving : MeasurePreserving (fun x : X ↦ t +ᵥ x) μ μ)
    (hAnull : μ A = 0) :
    μ ((fun x : X ↦ t +ᵥ x) ⁻¹' A) = 0 := by
  exact hpreserving.quasiMeasurePreserving.preimage_null hAnull

end Measure

section Recurrence

variable [MeasurableSpace X] [TopologicalSpace X]
variable [SecondCountableTopology X] [OpensMeasurableSpace X]
variable {μ : Measure X} [IsFiniteMeasure μ]

omit [AddAction ℝ X] in
/-- Conditional Poincaré obstruction to permanent fixed-size settling.

For a finite invariant measure and a measure-preserving discrete time step,
almost every point whose continuous error is initially above `delta` returns
above `delta` infinitely often.  Applying this theorem to an LJ chain requires
separate proofs that the selected time step preserves the relevant finite
Liouville measure and that all topological/measurability hypotheses hold. -/
theorem ae_frequently_error_gt_of_measurePreserving
    (step : X → X) (hstep : MeasurePreserving step μ μ)
    (error : X → ℝ) (herror : Continuous error) (delta : ℝ) :
    ∀ᵐ x ∂μ, delta < error x →
      ∃ᶠ n in Filter.atTop, delta < error (step^[n] x) := by
  filter_upwards
    [hstep.conservative.ae_frequently_mem_of_mem_nhds] with x hx
  intro hxFailure
  have hopen : IsOpen {y : X | delta < error y} :=
    isOpen_lt continuous_const herror
  have hneighborhood : {y : X | delta < error y} ∈ 𝓝 x :=
    hopen.mem_nhds hxFailure
  exact hx {y : X | delta < error y} hneighborhood

omit [AddAction ℝ X] in
/-- Under the same recurrence hypotheses, almost every initially failing
point cannot have any discrete cutoff after which the error stays at or below
the threshold forever. -/
theorem ae_no_permanent_error_bound_of_measurePreserving
    (step : X → X) (hstep : MeasurePreserving step μ μ)
    (error : X → ℝ) (herror : Continuous error) (delta : ℝ) :
    ∀ᵐ x ∂μ, delta < error x →
      ¬∃ cutoff : ℕ, ∀ n ≥ cutoff, error (step^[n] x) ≤ delta := by
  filter_upwards
    [ae_frequently_error_gt_of_measurePreserving
      step hstep error herror delta] with x hx
  intro hxFailure hsettles
  rcases hsettles with ⟨cutoff, hcutoff⟩
  rcases ((hx hxFailure).and_eventually
    (Filter.eventually_ge_atTop cutoff)).exists with ⟨n, hnFailure, hnCutoff⟩
  exact (not_lt_of_ge (hcutoff n hnCutoff)) hnFailure

end Recurrence

section Periodic

/-- Points lying on a nontrivial periodic orbit of the real-time action. -/
def periodicPoints : Set X :=
  {x | ∃ period : ℝ, period ≠ 0 ∧ period +ᵥ x = x}

/-- The set of all nontrivial periodic points is flow invariant. -/
theorem periodicPoints_flowInvariant : FlowInvariant (periodicPoints : Set X) := by
  intro t x hx
  rcases hx with ⟨period, hperiod, hfixed⟩
  refine ⟨period, hperiod, ?_⟩
  calc
    period +ᵥ (t +ᵥ x) = (period + t) +ᵥ x := (add_vadd period t x).symm
    _ = (t + period) +ᵥ x := by rw [add_comm]
    _ = t +ᵥ (period +ᵥ x) := add_vadd t period x
    _ = t +ᵥ x := by rw [hfixed]

/-- An orbit ever enters the periodic-point set exactly when its initial point
is already periodic. -/
theorem everEnters_periodicPoints_eq :
    everEnters (periodicPoints : Set X) = periodicPoints :=
  everEnters_eq_of_flowInvariant periodicPoints_flowInvariant

variable [MeasurableSpace X] {μ : Measure X}

/-- Conditional periodic-orbit exclusion: if the *entire* periodic-point set
has measure zero, then initial conditions that ever lie on a periodic orbit
have measure zero.  The nullity premise is not established here for any
specific Hamiltonian. -/
theorem measure_everEnters_periodicPoints_eq_zero
    (hperiodicNull : μ (periodicPoints : Set X) = 0) :
    μ (everEnters (periodicPoints : Set X)) = 0 :=
  measure_everEnters_eq_zero_of_flowInvariant
    periodicPoints_flowInvariant hperiodicNull

/-- Almost-sure form of the conditional periodic-orbit exclusion. -/
theorem ae_neverEnters_periodicPoints
    (hperiodicNull : μ (periodicPoints : Set X) = 0) :
    ∀ᵐ x ∂μ, ¬∃ t : ℝ, t +ᵥ x ∈ periodicPoints :=
  ae_neverEnters_of_flowInvariant periodicPoints_flowInvariant hperiodicNull

/-- Measurable-null periodic points form a bundled invariant null set. -/
theorem periodicPoints_invariantNullSet
    (hperiodicMeasurable : MeasurableSet (periodicPoints : Set X))
    (hperiodicNull : μ (periodicPoints : Set X) = 0) :
    InvariantNullSet μ periodicPoints :=
  ⟨periodicPoints_flowInvariant, hperiodicMeasurable, hperiodicNull⟩

end Periodic

end

end ArchonPhysics.ReversibleFlowInvariantNullEntry
