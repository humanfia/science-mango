import ArchonPhysics.ConditionalThermalizationCertificate
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Microscopic error estimates upgraded to probability laws

This module is a model-independent F3 adapter.  It converts either

* a vanishing first or second moment of a nonnegative `ENNReal` error, or
* deterministic control on a good event together with a vanishing bad-event
  probability budget,

into the exact zero-neighbourhood law used by
`ConditionalThermalizationCertificate.localUniformError_zero_law`.

No microscopic estimate, random-phase propagation statement, kinetic limit,
or Lennard--Jones tube probability is proved here.  Those remain the
model-specific inputs to these probability-theoretic implications.
-/

namespace ArchonPhysics.MicroscopicErrorProbabilityUpgrade

open ArchonPhysics
open ArchonPhysics.ProbabilisticHittingTransfer
open ArchonPhysics.ThermalizationTransfer
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The event on which an extended nonnegative error exceeds a threshold. -/
def errorAboveEvent (error : Nat → Omega → ENNReal)
    (threshold : ENNReal) (n : Nat) : Set Omega :=
  {omega | threshold ≤ error n omega}

theorem measurableSet_errorAboveEvent
    (error : Nat → Omega → ENNReal)
    (herror : ∀ n, Measurable (error n))
    (threshold : ENNReal) (n : Nat) :
    MeasurableSet (errorAboveEvent error threshold n) := by
  exact measurableSet_Ici.preimage (herror n)

omit [MeasurableSpace Omega] in
theorem errorAboveEvent_compl_eq_errorBelowEvent
    (error : Nat → Omega → ENNReal)
    (threshold : ENNReal) (n : Nat) :
    (errorAboveEvent error threshold n)ᶜ =
      error n ⁻¹' Iio threshold := by
  ext omega
  simp [errorAboveEvent]

/-! ## Deterministic control on a high-probability good event -/

omit [MeasurableSpace Omega] in
/-- If the deterministic budget is below the requested threshold, exceeding
that threshold can happen only outside the good event. -/
theorem errorAboveEvent_subset_compl_goodEvent_of_budget_lt
    (error : Omega → ENNReal) (goodEvent : Set Omega)
    (budget threshold : ENNReal)
    (hcontrol : ∀ omega ∈ goodEvent, error omega ≤ budget)
    (hbudget : budget < threshold) :
    {omega | threshold ≤ error omega} ⊆ goodEventᶜ := by
  intro omega hlarge hgood
  exact (not_lt_of_ge hlarge) ((hcontrol omega hgood).trans_lt hbudget)

/-- The corresponding finite-index probability bound.  Measurability of the
good event is not needed for monotonicity of outer measure. -/
theorem measure_errorAboveEvent_le_compl_goodEvent_of_budget_lt
    (P : Measure Omega) (error : Omega → ENNReal)
    (goodEvent : Set Omega) (budget threshold : ENNReal)
    (hcontrol : ∀ omega ∈ goodEvent, error omega ≤ budget)
    (hbudget : budget < threshold) :
    P {omega | threshold ≤ error omega} ≤ P goodEventᶜ :=
  measure_mono
    (errorAboveEvent_subset_compl_goodEvent_of_budget_lt
      error goodEvent budget threshold hcontrol hbudget)

/-- A deterministic error budget vanishing on good events, plus any vanishing
upper budget for their complements, forces every fixed positive error tail to
have vanishing probability. -/
theorem errorAboveEvent_measure_tendsto_zero_of_goodEvent_budget
    (P : Measure Omega)
    (error : Nat → Omega → ENNReal)
    (goodEvent : Nat → Set Omega)
    (deterministicBudget badProbabilityBudget : Nat → ENNReal)
    (hcontrol : ∀ n omega, omega ∈ goodEvent n →
      error n omega ≤ deterministicBudget n)
    (hdeterministicBudget :
      Tendsto deterministicBudget atTop (nhds 0))
    (hbadProbability : ∀ n, P (goodEvent n)ᶜ ≤ badProbabilityBudget n)
    (hbadProbabilityBudget :
      Tendsto badProbabilityBudget atTop (nhds 0))
    (threshold : ENNReal) (hthreshold : 0 < threshold) :
    Tendsto
      (fun n => P (errorAboveEvent error threshold n))
      atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro epsilon hepsilon
  filter_upwards
      [hdeterministicBudget.eventually (Iio_mem_nhds hthreshold),
        (ENNReal.tendsto_nhds_zero.mp hbadProbabilityBudget)
          epsilon hepsilon] with n hn hbad
  exact ((measure_errorAboveEvent_le_compl_goodEvent_of_budget_lt
    P (error n) (goodEvent n) (deterministicBudget n) threshold
    (hcontrol n) hn).trans (hbadProbability n)).trans hbad

/-- Exact-complement version of the good-event tail adapter. -/
theorem errorAboveEvent_measure_tendsto_zero_of_goodEvent
    (P : Measure Omega)
    (error : Nat → Omega → ENNReal)
    (goodEvent : Nat → Set Omega)
    (deterministicBudget : Nat → ENNReal)
    (hcontrol : ∀ n omega, omega ∈ goodEvent n →
      error n omega ≤ deterministicBudget n)
    (hdeterministicBudget :
      Tendsto deterministicBudget atTop (nhds 0))
    (hbadProbability :
      Tendsto (fun n => P (goodEvent n)ᶜ) atTop (nhds 0))
    (threshold : ENNReal) (hthreshold : 0 < threshold) :
    Tendsto
      (fun n => P (errorAboveEvent error threshold n))
      atTop (nhds 0) := by
  exact errorAboveEvent_measure_tendsto_zero_of_goodEvent_budget
    P error goodEvent deterministicBudget (fun n => P (goodEvent n)ᶜ)
    hcontrol hdeterministicBudget (fun _n => le_rfl) hbadProbability
    threshold hthreshold

/-! ## Fixed tails imply the certificate's zero-neighbourhood law -/

/-- Vanishing probability of every positive finite upper tail is equivalent
to the direction needed for the project's measurable-neighbourhood definition
of convergence in probability to zero. -/
theorem localUniformError_zero_law_of_tail_tendsto_zero
    (P : Measure Omega) [IsProbabilityMeasure P]
    (error : Nat → Omega → ENNReal)
    (herror : ∀ n, Measurable (error n))
    (htail : ∀ threshold : ENNReal, 0 < threshold → threshold ≠ ⊤ →
      Tendsto
        (fun n => P (errorAboveEvent error threshold n))
        atTop (nhds 0)) :
    ∀ U : Set ENNReal, MeasurableSet U → U ∈ 𝓝 0 →
      Tendsto (fun n => P (error n ⁻¹' U)) atTop (nhds 1) := by
  intro U _hUmeasurable hU
  obtain ⟨radius, hradius, hradiusSubset⟩ :=
    ENNReal.nhds_zero_basis.mem_iff.mp hU
  let finiteRadius : ENNReal := min radius 1
  have hfiniteRadius : 0 < finiteRadius := lt_min hradius zero_lt_one
  have hfiniteRadius_ne_top : finiteRadius ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (min_le_right radius 1)
  have hbelowSubset : Iio finiteRadius ⊆ U :=
    (Iio_subset_Iio (min_le_left radius 1)).trans hradiusSubset
  have htailZero := htail finiteRadius hfiniteRadius hfiniteRadius_ne_top
  have hbelowOne :
      Tendsto (fun n => P (error n ⁻¹' Iio finiteRadius))
        atTop (nhds 1) := by
    have hsub := ENNReal.Tendsto.sub
      (tendsto_const_nhds :
        Tendsto (fun _n : Nat => (1 : ENNReal)) atTop (nhds 1))
      htailZero (Or.inl ENNReal.one_ne_top)
    have hmeasureIdentity :
        (fun n => P (error n ⁻¹' Iio finiteRadius)) =
          (fun n => 1 - P (errorAboveEvent error finiteRadius n)) := by
      funext n
      rw [← errorAboveEvent_compl_eq_errorBelowEvent]
      rw [measure_compl
        (measurableSet_errorAboveEvent error herror finiteRadius n)
        (measure_ne_top P _), measure_univ]
    rw [hmeasureIdentity]
    simpa using hsub
  exact tendsto_measure_superset_atTop_one P
    (fun n => error n ⁻¹' Iio finiteRadius)
    (fun n => error n ⁻¹' U)
    hbelowOne (fun _n => preimage_mono hbelowSubset)

/-- Tail convergence plus measurability gives the bundled project interface. -/
theorem convergesInProbabilityTo_zero_of_tail_tendsto_zero
    (P : Measure Omega) [IsProbabilityMeasure P]
    (error : Nat → Omega → ENNReal)
    (herror : ∀ n, Measurable (error n))
    (htail : ∀ threshold : ENNReal, 0 < threshold → threshold ≠ ⊤ →
      Tendsto
        (fun n => P (errorAboveEvent error threshold n))
        atTop (nhds 0)) :
    ConvergesInProbabilityTo P error 0 := by
  exact ⟨herror,
    localUniformError_zero_law_of_tail_tendsto_zero
      P error herror htail⟩

/-- Good-event deterministic control and a vanishing complement budget close
the exact `localUniformError_zero_law` field. -/
theorem localUniformError_zero_law_of_goodEvent_budget
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
      Tendsto (fun n => P (error n ⁻¹' U)) atTop (nhds 1) := by
  apply localUniformError_zero_law_of_tail_tendsto_zero P error herror
  intro threshold hthreshold _hthresholdTop
  exact errorAboveEvent_measure_tendsto_zero_of_goodEvent_budget
    P error goodEvent deterministicBudget badProbabilityBudget
    hcontrol hdeterministicBudget hbadProbability hbadProbabilityBudget
    threshold hthreshold

/-- Bundled version of the preceding good-event adapter. -/
theorem convergesInProbabilityTo_zero_of_goodEvent_budget
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
    ConvergesInProbabilityTo P error 0 := by
  exact ⟨herror,
    localUniformError_zero_law_of_goodEvent_budget
      P error herror goodEvent deterministicBudget badProbabilityBudget
      hcontrol hdeterministicBudget hbadProbability hbadProbabilityBudget⟩

/-! ## Markov upgrades from moments -/

/-- A vanishing first moment gives vanishing probability above each fixed
positive finite threshold. -/
theorem errorAboveEvent_measure_tendsto_zero_of_lintegral
    (P : Measure Omega)
    (error : Nat → Omega → ENNReal)
    (herror : ∀ n, Measurable (error n))
    (hfirstMoment : Tendsto
      (fun n => ∫⁻ omega, error n omega ∂P) atTop (nhds 0))
    (threshold : ENNReal) (hthreshold : 0 < threshold)
    (hthresholdTop : threshold ≠ ⊤) :
    Tendsto
      (fun n => P (errorAboveEvent error threshold n))
      atTop (nhds 0) := by
  have hscaled : Tendsto
      (fun n => (∫⁻ omega, error n omega ∂P) / threshold)
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.div_const hfirstMoment (Or.inr hthreshold.ne')
  rw [ENNReal.tendsto_nhds_zero]
  intro epsilon hepsilon
  filter_upwards
      [(ENNReal.tendsto_nhds_zero.mp hscaled) epsilon hepsilon] with n hn
  exact (meas_ge_le_lintegral_div (herror n).aemeasurable
    hthreshold.ne' hthresholdTop).trans hn

/-- A vanishing first moment closes the exact local-error zero law. -/
theorem localUniformError_zero_law_of_lintegral_tendsto_zero
    (P : Measure Omega) [IsProbabilityMeasure P]
    (error : Nat → Omega → ENNReal)
    (herror : ∀ n, Measurable (error n))
    (hfirstMoment : Tendsto
      (fun n => ∫⁻ omega, error n omega ∂P) atTop (nhds 0)) :
    ∀ U : Set ENNReal, MeasurableSet U → U ∈ 𝓝 0 →
      Tendsto (fun n => P (error n ⁻¹' U)) atTop (nhds 1) := by
  apply localUniformError_zero_law_of_tail_tendsto_zero P error herror
  intro threshold hthreshold hthresholdTop
  exact errorAboveEvent_measure_tendsto_zero_of_lintegral
    P error herror hfirstMoment threshold hthreshold hthresholdTop

/-- Bundled first-moment Markov upgrade. -/
theorem convergesInProbabilityTo_zero_of_lintegral_tendsto_zero
    (P : Measure Omega) [IsProbabilityMeasure P]
    (error : Nat → Omega → ENNReal)
    (herror : ∀ n, Measurable (error n))
    (hfirstMoment : Tendsto
      (fun n => ∫⁻ omega, error n omega ∂P) atTop (nhds 0)) :
    ConvergesInProbabilityTo P error 0 := by
  exact ⟨herror,
    localUniformError_zero_law_of_lintegral_tendsto_zero
      P error herror hfirstMoment⟩

/-- A vanishing second moment gives the same fixed-tail conclusion. -/
theorem errorAboveEvent_measure_tendsto_zero_of_secondMoment
    (P : Measure Omega)
    (error : Nat → Omega → ENNReal)
    (herror : ∀ n, Measurable (error n))
    (hsecondMoment : Tendsto
      (fun n => ∫⁻ omega, (error n omega) ^ 2 ∂P)
      atTop (nhds 0))
    (threshold : ENNReal) (hthreshold : 0 < threshold)
    (hthresholdTop : threshold ≠ ⊤) :
    Tendsto
      (fun n => P (errorAboveEvent error threshold n))
      atTop (nhds 0) := by
  have hsquaredMeasurable : ∀ n, Measurable (fun omega =>
      (error n omega) ^ 2) := fun n => (herror n).pow_const 2
  have hsquaredTail := errorAboveEvent_measure_tendsto_zero_of_lintegral
    P (fun n omega => (error n omega) ^ 2) hsquaredMeasurable
    hsecondMoment (threshold ^ 2)
    (ENNReal.pow_pos hthreshold 2) (ENNReal.pow_ne_top hthresholdTop)
  simpa only [errorAboveEvent,
    ENNReal.pow_le_pow_left_iff (by norm_num : 2 ≠ 0)] using hsquaredTail

/-- A vanishing second moment closes the exact local-error zero law. -/
theorem localUniformError_zero_law_of_secondMoment_tendsto_zero
    (P : Measure Omega) [IsProbabilityMeasure P]
    (error : Nat → Omega → ENNReal)
    (herror : ∀ n, Measurable (error n))
    (hsecondMoment : Tendsto
      (fun n => ∫⁻ omega, (error n omega) ^ 2 ∂P)
      atTop (nhds 0)) :
    ∀ U : Set ENNReal, MeasurableSet U → U ∈ 𝓝 0 →
      Tendsto (fun n => P (error n ⁻¹' U)) atTop (nhds 1) := by
  apply localUniformError_zero_law_of_tail_tendsto_zero P error herror
  intro threshold hthreshold hthresholdTop
  exact errorAboveEvent_measure_tendsto_zero_of_secondMoment
    P error herror hsecondMoment threshold hthreshold hthresholdTop

/-- Bundled second-moment Markov upgrade. -/
theorem convergesInProbabilityTo_zero_of_secondMoment_tendsto_zero
    (P : Measure Omega) [IsProbabilityMeasure P]
    (error : Nat → Omega → ENNReal)
    (herror : ∀ n, Measurable (error n))
    (hsecondMoment : Tendsto
      (fun n => ∫⁻ omega, (error n omega) ^ 2 ∂P)
      atTop (nhds 0)) :
    ConvergesInProbabilityTo P error 0 := by
  exact ⟨herror,
    localUniformError_zero_law_of_secondMoment_tendsto_zero
      P error herror hsecondMoment⟩

end

end ArchonPhysics.MicroscopicErrorProbabilityUpgrade
