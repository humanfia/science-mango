import ArchonPhysics.PersistentEquipartition
import ArchonPhysics.TwoScaleProbabilityDiagonalization

/-!
# Arbitrarily long microscopic--kinetic persistence

This module separates two notions which are easy to conflate in a finite
Hamiltonian system:

* control on every time in one prescribed finite closed interval; and
* a single size selection which lets that finite interval grow along a
  thermodynamic sequence.

For a microscopic path `micro N omega` and a deterministic kinetic path
`kinetic`, the first theorem transfers fixed-window convergence in probability
to a deterministic equilibrium whenever the kinetic path stays within half of
the requested tolerance after the starting time.  The proof only uses the
triangle inequality and monotonicity of `Measure.real`.

The second part diagonalizes the fixed-horizon statements.  At integer horizon
`h`, `vanishingErrorCutoff` selects a size after which the bad probability is
smaller than `1 / (h + 1)`.  Consequently every sequence of horizons tending
to infinity and sizes eventually above the selected cutoff has vanishing bad
probability on the expanding windows.

No measurability of the uncountable existential event is assumed: Lean's
measure is defined on every set, and the argument needs only finite-measure
monotonicity.  In particular, this is an expanding-finite-window statement,
not a claim of permanent convergence of any fixed finite-volume orbit.
-/

namespace ArchonPhysics.ArbitrarilyLongMicroscopicKineticPersistence

open ArchonPhysics.QualitativeJointLimitDiagonalization
open ArchonPhysics.TwoScaleProbabilityDiagonalization
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega E : Type*} [PseudoMetricSpace E]

/-- The event that a microscopic path differs from its deterministic kinetic
reference by at least `threshold` at some time in the closed interval
`[start, horizon]`. -/
def microscopicKineticWindowBadEvent
    (micro : Nat -> Omega -> Real -> E) (kinetic : Real -> E)
    (start horizon threshold : Real) (N : Nat) : Set Omega :=
  {omega | exists time : Real, time ∈ Icc start horizon /\
    threshold <= dist (micro N omega time) (kinetic time)}

/-- The event that a microscopic path differs from the fixed equilibrium by
at least `threshold` at some time in the closed interval `[start, horizon]`. -/
def microscopicEquilibriumWindowBadEvent
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (start horizon threshold : Real) (N : Nat) : Set Omega :=
  {omega | exists time : Real, time ∈ Icc start horizon /\
    threshold <= dist (micro N omega time) equilibrium}

/-- If the kinetic path is within `threshold / 2` of equilibrium throughout
the post-`start` tail, every microscopic equilibrium failure at threshold
`threshold` on a finite window is a microscopic--kinetic failure at the half
threshold on the same window. -/
theorem microscopicEquilibriumWindowBadEvent_subset_halfKineticBadEvent
    (micro : Nat -> Omega -> Real -> E) (kinetic : Real -> E)
    (equilibrium : E) (start horizon threshold : Real) (N : Nat)
    (hkinetic : forall time : Real, start <= time ->
      dist (kinetic time) equilibrium < threshold / 2) :
    microscopicEquilibriumWindowBadEvent micro equilibrium
        start horizon threshold N ⊆
      microscopicKineticWindowBadEvent micro kinetic
        start horizon (threshold / 2) N := by
  rintro omega ⟨time, htime, hbad⟩
  refine ⟨time, htime, ?_⟩
  have htriangle :=
    dist_triangle (micro N omega time) (kinetic time) equilibrium
  have hkineticTime := hkinetic time htime.1
  linarith

/-! ## Numerical first hits versus persistent equilibration -/

/-- The strict finite-time equilibrium event used to compare a numerical
first hit with a genuinely persistent settling time.  Evaluation at `⊤` is
disabled by `strictFiniteDistanceEvent`. -/
def microscopicStrictFiniteEquilibriumEvent
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (threshold : Real) (N : Nat) (omega : Omega) : ENNReal -> Prop :=
  ArchonPhysics.PersistentEquipartition.strictFiniteDistanceEvent
    (fun time => dist (micro N omega time) equilibrium) threshold

/-- The numerical first-entry convention for one finite microscopic sample. -/
def microscopicFirstEquipartitionTime
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (threshold : Real) (N : Nat) (omega : Omega) : ENNReal :=
  ArchonPhysics.HittingTime.firstHittingTime
    (microscopicStrictFiniteEquilibriumEvent micro equilibrium threshold N omega)

/-- The sustained convention for one finite microscopic sample: the infimum
of positive finite starts after which the strict threshold holds at every
finite future time. -/
def microscopicPersistentEquipartitionTime
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (threshold : Real) (N : Nat) (omega : Omega) : ENNReal :=
  ArchonPhysics.PersistentEquipartition.strictDistanceSettlingTime
    (fun time => dist (micro N omega time) equilibrium) threshold

/-- A numerical first hit is always no later than the persistent settling
time; equality is not automatic. -/
theorem microscopicFirstEquipartitionTime_le_persistentEquipartitionTime
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (threshold : Real) (N : Nat) (omega : Omega) :
    microscopicFirstEquipartitionTime micro equilibrium threshold N omega <=
      microscopicPersistentEquipartitionTime micro equilibrium threshold N omega := by
  exact ArchonPhysics.PersistentEquipartition.firstHittingTime_le_settlingTime
    (microscopicStrictFiniteEquilibriumEvent micro equilibrium threshold N omega)

/-- The numerical first-hit time agrees with the persistent time under the
extra direction needed in applications: the first hit is positive, finite,
and already supports the whole finite-time tail. -/
theorem microscopicFirstEquipartitionTime_eq_persistent_of_firstHit_persists
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (threshold : Real) (N : Nat) (omega : Omega)
    (hpositive : 0 <
      microscopicFirstEquipartitionTime micro equilibrium threshold N omega)
    (hfinite :
      microscopicFirstEquipartitionTime micro equilibrium threshold N omega < ⊤)
    (hpersists : ArchonPhysics.PersistentEquipartition.TailPersistsFor
      (microscopicStrictFiniteEquilibriumEvent micro equilibrium threshold N omega)
      (microscopicFirstEquipartitionTime micro equilibrium threshold N omega)) :
    microscopicFirstEquipartitionTime micro equilibrium threshold N omega =
      microscopicPersistentEquipartitionTime micro equilibrium threshold N omega := by
  apply le_antisymm
  · exact microscopicFirstEquipartitionTime_le_persistentEquipartitionTime
      micro equilibrium threshold N omega
  · exact ArchonPhysics.PersistentEquipartition.settlingTime_le_of_mem
      (microscopicStrictFiniteEquilibriumEvent micro equilibrium threshold N omega)
      ⟨hpositive, hfinite, hpersists⟩

variable [MeasurableSpace Omega]


/-! ## A strict probabilistic finite-window thermalization time -/

/-- Positive finite starts whose entire following duration has equilibrium
failure probability at most failureTolerance.  Unlike a one-time numerical
threshold hit, membership controls every time in a complete interval. -/
def microscopicWindowThermalizationCandidates
    (mu : Measure Omega)
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance : Real) (N : Nat) : Set ENNReal :=
  {start | 0 < start ∧ start < ⊤ ∧
    mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
      start.toReal (start.toReal + duration) threshold N) ≤ failureTolerance}

/-- The strict probabilistic finite-window thermalization time.  It is the
first positive finite start, in the infimum sense, after which the probability
of violating the equipartition tolerance anywhere in the next duration is at
most failureTolerance.  Its value is top if there is no such start. -/
def microscopicWindowThermalizationTime
    (mu : Measure Omega)
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance : Real) (N : Nat) : ENNReal :=
  sInf (microscopicWindowThermalizationCandidates mu micro equilibrium
    threshold duration failureTolerance N)

/-- Any certified start bounds the strict window thermalization time. -/
theorem microscopicWindowThermalizationTime_le_of_badProbability_le
    (mu : Measure Omega)
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance : Real) (N : Nat)
    {start : ENNReal} (hstart : 0 < start) (hfinite : start < ⊤)
    (hprobability :
      mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
        start.toReal (start.toReal + duration) threshold N) ≤
          failureTolerance) :
    microscopicWindowThermalizationTime mu micro equilibrium
      threshold duration failureTolerance N ≤ start := by
  apply sInf_le
  exact ⟨hstart, hfinite, hprobability⟩

omit [MeasurableSpace Omega] in
/-- Increasing the allowed distance can only remove bad samples. -/
theorem microscopicEquilibriumWindowBadEvent_mono_threshold
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (start horizon thresholdSmall thresholdLarge : Real) (N : Nat)
    (hthreshold : thresholdSmall ≤ thresholdLarge) :
    microscopicEquilibriumWindowBadEvent micro equilibrium
        start horizon thresholdLarge N ⊆
      microscopicEquilibriumWindowBadEvent micro equilibrium
        start horizon thresholdSmall N := by
  rintro omega ⟨time, htime, hbad⟩
  exact ⟨time, htime, hthreshold.trans hbad⟩

omit [MeasurableSpace Omega] in
/-- Extending the right endpoint can only add bad samples. -/
theorem microscopicEquilibriumWindowBadEvent_mono_horizon
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (start horizonSmall horizonLarge threshold : Real) (N : Nat)
    (hhorizon : horizonSmall ≤ horizonLarge) :
    microscopicEquilibriumWindowBadEvent micro equilibrium
        start horizonSmall threshold N ⊆
      microscopicEquilibriumWindowBadEvent micro equilibrium
        start horizonLarge threshold N := by
  rintro omega ⟨time, htime, hbad⟩
  exact ⟨time, ⟨htime.1, htime.2.trans hhorizon⟩, hbad⟩

/-- A looser equipartition threshold cannot increase the strict window
thermalization time. -/
theorem microscopicWindowThermalizationTime_antitone_threshold
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (thresholdSmall thresholdLarge duration failureTolerance : Real)
    (N : Nat) (hthreshold : thresholdSmall ≤ thresholdLarge) :
    microscopicWindowThermalizationTime mu micro equilibrium
        thresholdLarge duration failureTolerance N ≤
      microscopicWindowThermalizationTime mu micro equilibrium
        thresholdSmall duration failureTolerance N := by
  unfold microscopicWindowThermalizationTime
  apply le_sInf
  intro start hstart
  apply sInf_le
  refine ⟨hstart.1, hstart.2.1, ?_⟩
  exact (measureReal_mono (h₂ := by finiteness)
    (microscopicEquilibriumWindowBadEvent_mono_threshold
      micro equilibrium start.toReal (start.toReal + duration)
        thresholdSmall thresholdLarge N hthreshold)).trans hstart.2.2

/-- Requiring a longer persistent window cannot decrease the strict window
thermalization time. -/
theorem microscopicWindowThermalizationTime_monotone_duration
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (threshold durationSmall durationLarge failureTolerance : Real)
    (N : Nat) (hduration : durationSmall ≤ durationLarge) :
    microscopicWindowThermalizationTime mu micro equilibrium
        threshold durationSmall failureTolerance N ≤
      microscopicWindowThermalizationTime mu micro equilibrium
        threshold durationLarge failureTolerance N := by
  unfold microscopicWindowThermalizationTime
  apply le_sInf
  intro start hstart
  apply sInf_le
  refine ⟨hstart.1, hstart.2.1, ?_⟩
  have hhorizon :
      start.toReal + durationSmall ≤ start.toReal + durationLarge :=
    by linarith
  exact (measureReal_mono (h₂ := by finiteness)
    (microscopicEquilibriumWindowBadEvent_mono_horizon
      micro equilibrium start.toReal
        (start.toReal + durationSmall) (start.toReal + durationLarge)
        threshold N hhorizon)).trans hstart.2.2

/-- Allowing a larger failure probability cannot increase the strict window
thermalization time. -/
theorem microscopicWindowThermalizationTime_antitone_failureTolerance
    (mu : Measure Omega)
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureToleranceSmall failureToleranceLarge : Real)
    (N : Nat) (hfailure : failureToleranceSmall ≤ failureToleranceLarge) :
    microscopicWindowThermalizationTime mu micro equilibrium
        threshold duration failureToleranceLarge N ≤
      microscopicWindowThermalizationTime mu micro equilibrium
        threshold duration failureToleranceSmall N := by
  unfold microscopicWindowThermalizationTime
  apply le_sInf
  intro start hstart
  apply sInf_le
  exact ⟨hstart.1, hstart.2.1, hstart.2.2.trans hfailure⟩

/-- If every positive finite start still has failure probability above the
admitted tolerance, the strict window thermalization time is infinite.  This
is the probabilistic counterpart of the fixed-volume recurrence obstruction. -/
theorem microscopicWindowThermalizationTime_eq_top_of_every_start_fails
    (mu : Measure Omega)
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance : Real) (N : Nat)
    (hfailure : ∀ start : ENNReal, 0 < start → start < ⊤ →
      failureTolerance <
        mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
          start.toReal (start.toReal + duration) threshold N)) :
    microscopicWindowThermalizationTime mu micro equilibrium
      threshold duration failureTolerance N = ⊤ := by
  unfold microscopicWindowThermalizationTime
  rw [show microscopicWindowThermalizationCandidates mu micro equilibrium
      threshold duration failureTolerance N = ∅ by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro start hstart
    exact (not_lt_of_ge hstart.2.2)
      (hfailure start hstart.1 hstart.2.1)]
  exact sInf_empty

/-- The equilibrium-window bad probability is bounded by the corresponding
half-threshold microscopic--kinetic bad probability.  No measurability of
either uncountable existential event is required. -/
theorem microscopicEquilibriumWindowBadProbability_le_halfKineticBadProbability
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (micro : Nat -> Omega -> Real -> E) (kinetic : Real -> E)
    (equilibrium : E) (start horizon threshold : Real) (N : Nat)
    (hkinetic : forall time : Real, start <= time ->
      dist (kinetic time) equilibrium < threshold / 2) :
    mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
        start horizon threshold N) <=
      mu.real (microscopicKineticWindowBadEvent micro kinetic
        start horizon (threshold / 2) N) := by
  apply measureReal_mono (h₂ := by finiteness)
  exact microscopicEquilibriumWindowBadEvent_subset_halfKineticBadEvent
    micro kinetic equilibrium start horizon threshold N hkinetic

/-- Fixed-window microscopic--kinetic convergence and a deterministic kinetic
tail within half the target tolerance imply fixed-window microscopic
equilibrium convergence. -/
theorem microscopicEquilibriumWindowBadProbability_tendsto_zero
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (micro : Nat -> Omega -> Real -> E) (kinetic : Real -> E)
    (equilibrium : E) (start horizon threshold : Real)
    (hkinetic : forall time : Real, start <= time ->
      dist (kinetic time) equilibrium < threshold / 2)
    (hmicroKinetic : Tendsto
      (fun N => mu.real (microscopicKineticWindowBadEvent micro kinetic
        start horizon (threshold / 2) N)) atTop (nhds 0)) :
    Tendsto
      (fun N => mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
        start horizon threshold N)) atTop (nhds 0) := by
  exact squeeze_zero'
    (Eventually.of_forall fun _N => measureReal_nonneg)
    (Eventually.of_forall fun N =>
      microscopicEquilibriumWindowBadProbability_le_halfKineticBadProbability
        mu micro kinetic equilibrium start horizon threshold N hkinetic)
    hmicroKinetic

/-! ## Diagonalization of arbitrary fixed integer horizons -/

/-- A horizon-dependent size cutoff built from fixed-horizon equilibrium bad
probabilities.  Above this cutoff the bad probability is smaller than the
existing two-scale tolerance `1 / (horizon + 1)`. -/
def equilibriumExpandingWindowSizeCutoff
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (start threshold : Real)
    (hfixed : forall horizon : Nat, Tendsto
      (fun N => mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
        start (horizon : Real) threshold N)) atTop (nhds 0)) :
    Nat -> Nat :=
  fun horizon => vanishingErrorCutoff
    (fun N => mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
      start (horizon : Real) threshold N))
    (hfixed horizon) (twoScaleProbabilityTolerance horizon)

/-- Above the equilibrium diagonal cutoff, the closed-window bad probability
is strictly smaller than `1 / (horizon + 1)`. -/
theorem equilibriumWindowBadProbability_lt_of_cutoff
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (start threshold : Real)
    (hfixed : forall horizon : Nat, Tendsto
      (fun N => mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
        start (horizon : Real) threshold N)) atTop (nhds 0))
    (horizon : Nat) {N : Nat}
    (hN : equilibriumExpandingWindowSizeCutoff mu micro equilibrium
      start threshold hfixed horizon <= N) :
    mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
        start (horizon : Real) threshold N) <
      twoScaleProbabilityTolerance horizon := by
  exact error_lt_of_vanishingErrorCutoff
    (fun M => mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
      start (horizon : Real) threshold M))
    (hfixed horizon) (twoScaleProbabilityTolerance_pos horizon) hN

/-- Every diverging integer-horizon path whose size is eventually above the
selected cutoff has vanishing microscopic equilibrium bad probability on its
expanding closed windows. -/
theorem equilibriumWindowBadProbability_tendsto_zero_along_expanding_windows
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (start threshold : Real)
    (hfixed : forall horizon : Nat, Tendsto
      (fun N => mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
        start (horizon : Real) threshold N)) atTop (nhds 0))
    (horizonIndex sizeIndex : Nat -> Nat)
    (hhorizon : Tendsto horizonIndex atTop atTop)
    (hsize : ∀ᶠ j in atTop,
      equilibriumExpandingWindowSizeCutoff mu micro equilibrium
        start threshold hfixed (horizonIndex j) <= sizeIndex j) :
    Tendsto
      (fun j => mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
        start (horizonIndex j : Real) threshold (sizeIndex j)))
      atTop (nhds 0) := by
  have htolerance : Tendsto
      (fun j => twoScaleProbabilityTolerance (horizonIndex j))
      atTop (nhds 0) :=
    twoScaleProbabilityTolerance_tendsto_zero.comp hhorizon
  have hupper : ∀ᶠ j in atTop,
      mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
          start (horizonIndex j : Real) threshold (sizeIndex j)) <=
        twoScaleProbabilityTolerance (horizonIndex j) := by
    filter_upwards [hsize] with j hj
    exact (equilibriumWindowBadProbability_lt_of_cutoff
      mu micro equilibrium start threshold hfixed (horizonIndex j) hj).le
  exact squeeze_zero'
    (Eventually.of_forall fun _j => measureReal_nonneg)
    hupper htolerance

/-- Bundled existential form: fixed-horizon convergence constructs one
horizon-dependent cutoff valid along every expanding-window sequence. -/
theorem exists_sizeCutoff_for_equilibrium_expanding_windows
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (start threshold : Real)
    (hfixed : forall horizon : Nat, Tendsto
      (fun N => mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
        start (horizon : Real) threshold N)) atTop (nhds 0)) :
    exists sizeCutoff : Nat -> Nat,
      forall horizonIndex sizeIndex : Nat -> Nat,
        Tendsto horizonIndex atTop atTop ->
        (∀ᶠ j in atTop,
          sizeCutoff (horizonIndex j) <= sizeIndex j) ->
        Tendsto
          (fun j => mu.real (microscopicEquilibriumWindowBadEvent
            micro equilibrium start (horizonIndex j : Real) threshold
              (sizeIndex j))) atTop (nhds 0) := by
  use equilibriumExpandingWindowSizeCutoff mu micro equilibrium
    start threshold hfixed
  intro horizonIndex sizeIndex hhorizon hsize
  exact equilibriumWindowBadProbability_tendsto_zero_along_expanding_windows
    mu micro equilibrium start threshold hfixed horizonIndex sizeIndex
      hhorizon hsize

/-! ## Direct microscopic--kinetic construction -/

/-- A horizon-dependent cutoff selected directly from the fixed-horizon
microscopic--kinetic approximation errors. -/
def kineticApproximationExpandingWindowSizeCutoff
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (micro : Nat -> Omega -> Real -> E) (kinetic : Real -> E)
    (start threshold : Real)
    (hmicroKinetic : forall horizon : Nat, Tendsto
      (fun N => mu.real (microscopicKineticWindowBadEvent micro kinetic
        start (horizon : Real) (threshold / 2) N)) atTop (nhds 0)) :
    Nat -> Nat :=
  fun horizon => vanishingErrorCutoff
    (fun N => mu.real (microscopicKineticWindowBadEvent micro kinetic
      start (horizon : Real) (threshold / 2) N))
    (hmicroKinetic horizon) (twoScaleProbabilityTolerance horizon)

/-- The direct cutoff makes the equilibrium bad probability smaller than the
two-scale tolerance, by composing the fixed-window triangle transfer with
`vanishingErrorCutoff`. -/
theorem equilibriumWindowBadProbability_lt_of_kineticApproximationCutoff
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (micro : Nat -> Omega -> Real -> E) (kinetic : Real -> E)
    (equilibrium : E) (start threshold : Real)
    (hkinetic : forall time : Real, start <= time ->
      dist (kinetic time) equilibrium < threshold / 2)
    (hmicroKinetic : forall horizon : Nat, Tendsto
      (fun N => mu.real (microscopicKineticWindowBadEvent micro kinetic
        start (horizon : Real) (threshold / 2) N)) atTop (nhds 0))
    (horizon : Nat) {N : Nat}
    (hN : kineticApproximationExpandingWindowSizeCutoff mu micro kinetic
      start threshold hmicroKinetic horizon <= N) :
    mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
        start (horizon : Real) threshold N) <
      twoScaleProbabilityTolerance horizon := by
  calc
    mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
        start (horizon : Real) threshold N) <=
        mu.real (microscopicKineticWindowBadEvent micro kinetic
          start (horizon : Real) (threshold / 2) N) :=
      microscopicEquilibriumWindowBadProbability_le_halfKineticBadProbability
        mu micro kinetic equilibrium start (horizon : Real) threshold N
          hkinetic
    _ < twoScaleProbabilityTolerance horizon :=
      error_lt_of_vanishingErrorCutoff
        (fun M => mu.real (microscopicKineticWindowBadEvent micro kinetic
          start (horizon : Real) (threshold / 2) M))
        (hmicroKinetic horizon) (twoScaleProbabilityTolerance_pos horizon) hN

/-- Long-time transfer in its direct microscopic--kinetic form.  Fixed-window
microscopic--kinetic convergence is diagonalized into convergence on every
admitted expanding window, provided the deterministic kinetic trajectory is
already uniformly within half the requested equilibrium tolerance after
`start`. -/
theorem equilibriumWindowBadProbability_tendsto_zero_along_expanding_windows_of_kinetic
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (micro : Nat -> Omega -> Real -> E) (kinetic : Real -> E)
    (equilibrium : E) (start threshold : Real)
    (hkinetic : forall time : Real, start <= time ->
      dist (kinetic time) equilibrium < threshold / 2)
    (hmicroKinetic : forall horizon : Nat, Tendsto
      (fun N => mu.real (microscopicKineticWindowBadEvent micro kinetic
        start (horizon : Real) (threshold / 2) N)) atTop (nhds 0))
    (horizonIndex sizeIndex : Nat -> Nat)
    (hhorizon : Tendsto horizonIndex atTop atTop)
    (hsize : ∀ᶠ j in atTop,
      kineticApproximationExpandingWindowSizeCutoff mu micro kinetic
        start threshold hmicroKinetic (horizonIndex j) <= sizeIndex j) :
    Tendsto
      (fun j => mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
        start (horizonIndex j : Real) threshold (sizeIndex j)))
      atTop (nhds 0) := by
  have htolerance : Tendsto
      (fun j => twoScaleProbabilityTolerance (horizonIndex j))
      atTop (nhds 0) :=
    twoScaleProbabilityTolerance_tendsto_zero.comp hhorizon
  have hupper : ∀ᶠ j in atTop,
      mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
          start (horizonIndex j : Real) threshold (sizeIndex j)) <=
        twoScaleProbabilityTolerance (horizonIndex j) := by
    filter_upwards [hsize] with j hj
    exact (equilibriumWindowBadProbability_lt_of_kineticApproximationCutoff
      mu micro kinetic equilibrium start threshold hkinetic hmicroKinetic
        (horizonIndex j) hj).le
  exact squeeze_zero'
    (Eventually.of_forall fun _j => measureReal_nonneg)
    hupper htolerance


/-! ## Joint shrinking-tolerance and expanding-duration limit -/

/-- A two-parameter size cutoff for the thermodynamic notion of strict
equipartition.  The precision index selects both a shrinking equilibrium
tolerance and the target failure probability, while duration selects the
length of the post-settling observation window.

The cutoff is deliberately allowed to depend on both parameters.  This is the
correct diagonal quantifier order: first prove the microscopic--kinetic limit
for every fixed precision and finite duration, and only then choose system
sizes while precision tends to infinity and the duration expands. -/
def shrinkingToleranceExpandingDurationSizeCutoff
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (micro : Nat -> Omega -> Real -> E) (kinetic : Real -> E)
    (start threshold : Nat -> Real)
    (hmicroKinetic : forall precision duration : Nat, Tendsto
      (fun N => mu.real (microscopicKineticWindowBadEvent micro kinetic
        (start precision) (start precision + (duration : Real))
          (threshold precision / 2) N)) atTop (nhds 0)) :
    Nat -> Nat -> Nat :=
  fun precision duration => vanishingErrorCutoff
    (fun N => mu.real (microscopicKineticWindowBadEvent micro kinetic
      (start precision) (start precision + (duration : Real))
        (threshold precision / 2) N))
    (hmicroKinetic precision duration)
    (twoScaleProbabilityTolerance precision)

/-- Above the joint cutoff, failure of equilibrium anywhere in the complete
post-settling window has probability smaller than 1 / (precision + 1). -/
theorem equilibriumDurationBadProbability_lt_of_jointKineticCutoff
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (micro : Nat -> Omega -> Real -> E) (kinetic : Real -> E)
    (equilibrium : E) (start threshold : Nat -> Real)
    (hkinetic : forall precision : Nat, forall time : Real,
      start precision <= time ->
        dist (kinetic time) equilibrium < threshold precision / 2)
    (hmicroKinetic : forall precision duration : Nat, Tendsto
      (fun N => mu.real (microscopicKineticWindowBadEvent micro kinetic
        (start precision) (start precision + (duration : Real))
          (threshold precision / 2) N)) atTop (nhds 0))
    (precision duration : Nat) {N : Nat}
    (hN : shrinkingToleranceExpandingDurationSizeCutoff mu micro kinetic
      start threshold hmicroKinetic precision duration <= N) :
    mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
        (start precision) (start precision + (duration : Real))
          (threshold precision) N) <
      twoScaleProbabilityTolerance precision := by
  calc
    mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
        (start precision) (start precision + (duration : Real))
          (threshold precision) N) <=
        mu.real (microscopicKineticWindowBadEvent micro kinetic
          (start precision) (start precision + (duration : Real))
            (threshold precision / 2) N) :=
      microscopicEquilibriumWindowBadProbability_le_halfKineticBadProbability
        mu micro kinetic equilibrium (start precision)
          (start precision + (duration : Real)) (threshold precision) N
          (hkinetic precision)
    _ < twoScaleProbabilityTolerance precision :=
      error_lt_of_vanishingErrorCutoff
        (fun M => mu.real (microscopicKineticWindowBadEvent micro kinetic
          (start precision) (start precision + (duration : Real))
            (threshold precision / 2) M))
        (hmicroKinetic precision duration)
        (twoScaleProbabilityTolerance_pos precision) hN

/-- Rigorous thermodynamic persistence with strict equipartition error.

Along every diagonal on which the precision index and the observation
duration tend to infinity, and the system size is eventually above the
two-parameter cutoff, both the admitted equilibrium error and the probability
of violating that error anywhere in the whole observation window tend to
zero.  This theorem does not interchange the thermodynamic limit with an
infinite-time limit at fixed finite size. -/
theorem equilibriumBadProbability_and_threshold_tendsto_zero_along_joint_limit
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (micro : Nat -> Omega -> Real -> E) (kinetic : Real -> E)
    (equilibrium : E) (start threshold : Nat -> Real)
    (hthreshold : Tendsto threshold atTop (nhds 0))
    (hkinetic : forall precision : Nat, forall time : Real,
      start precision <= time ->
        dist (kinetic time) equilibrium < threshold precision / 2)
    (hmicroKinetic : forall precision duration : Nat, Tendsto
      (fun N => mu.real (microscopicKineticWindowBadEvent micro kinetic
        (start precision) (start precision + (duration : Real))
          (threshold precision / 2) N)) atTop (nhds 0))
    (precisionIndex durationIndex sizeIndex : Nat -> Nat)
    (hprecision : Tendsto precisionIndex atTop atTop)
    (_hduration : Tendsto durationIndex atTop atTop)
    (hsize : ∀ᶠ j in atTop,
      shrinkingToleranceExpandingDurationSizeCutoff mu micro kinetic
        start threshold hmicroKinetic (precisionIndex j) (durationIndex j) <=
          sizeIndex j) :
    Tendsto (fun j => threshold (precisionIndex j)) atTop (nhds 0) /\
      Tendsto
        (fun j => mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
          (start (precisionIndex j))
          (start (precisionIndex j) + (durationIndex j : Real))
          (threshold (precisionIndex j)) (sizeIndex j)))
        atTop (nhds 0) := by
  constructor
  · exact hthreshold.comp hprecision
  · have htolerance : Tendsto
        (fun j => twoScaleProbabilityTolerance (precisionIndex j))
        atTop (nhds 0) :=
      twoScaleProbabilityTolerance_tendsto_zero.comp hprecision
    have hupper : ∀ᶠ j in atTop,
        mu.real (microscopicEquilibriumWindowBadEvent micro equilibrium
          (start (precisionIndex j))
          (start (precisionIndex j) + (durationIndex j : Real))
          (threshold (precisionIndex j)) (sizeIndex j)) <=
            twoScaleProbabilityTolerance (precisionIndex j) := by
      filter_upwards [hsize] with j hj
      exact (equilibriumDurationBadProbability_lt_of_jointKineticCutoff
        mu micro kinetic equilibrium start threshold hkinetic hmicroKinetic
          (precisionIndex j) (durationIndex j) hj).le
    exact squeeze_zero'
      (Eventually.of_forall fun _j => measureReal_nonneg)
      hupper htolerance

end

end ArchonPhysics.ArbitrarilyLongMicroscopicKineticPersistence
