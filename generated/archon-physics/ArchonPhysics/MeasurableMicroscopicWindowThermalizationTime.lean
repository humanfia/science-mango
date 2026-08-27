import ArchonPhysics.ArbitrarilyLongMicroscopicKineticPersistence
import ArchonPhysics.RandomMassPositiveLateWindowObservable

/-!
# Measurable strict finite-window thermalization time

The uncountable bad event in the generic microscopic window definition need
not be measurable without path regularity.  This module gives its countable,
strict counterpart: a sample is bad when the diagnostic is strictly above the
threshold at some rational time in the prescribed window.  Measurability then
uses only measurability of every rational-time evaluation.

For continuous sample paths and positive duration, density of the rationals
identifies this event exactly with the literal real-time strict bad event.  We
keep the word `strict` visible: the older microscopic bad event uses the
closed failure convention `threshold <= distance`, so equality with that
definition would additionally require control of threshold-boundary samples.
-/

namespace ArchonPhysics.MeasurableMicroscopicWindowThermalizationTime

open ArchonPhysics.ArbitrarilyLongMicroscopicKineticPersistence
open ArchonPhysics.RandomMassPositiveLateWindowObservable
open MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Strict failure at some rational point of a closed real-time window. -/
def RationalStrictBadFor
    (distance : Real -> Real) (threshold start duration : Real) : Prop :=
  exists q : Rat, start <= (q : Real) /\
    (q : Real) <= start + duration /\ threshold < distance (q : Real)

/-- Literal strict failure at some real point of a closed real-time window. -/
def RealStrictBadFor
    (distance : Real -> Real) (threshold start duration : Real) : Prop :=
  exists time : Real, start <= time /\
    time <= start + duration /\ threshold < distance time

/-- The rationally sampled strict bad event in the ensemble. -/
def rationalStrictWindowBadEvent
    (distance : Omega -> Real -> Real)
    (start duration threshold : Real) : Set Omega :=
  {omega | RationalStrictBadFor (distance omega) threshold start duration}

/-- The literal all-real-times strict bad event in the ensemble. -/
def realStrictWindowBadEvent
    (distance : Omega -> Real -> Real)
    (start duration threshold : Real) : Set Omega :=
  {omega | RealStrictBadFor (distance omega) threshold start duration}

theorem rationalStrictBadFor_iff_not_rationalClosedPersistsFor
    (distance : Real -> Real) (threshold start duration : Real) :
    RationalStrictBadFor distance threshold start duration <->
      Not (RationalClosedPersistsFor distance threshold start duration) := by
  simp [RationalStrictBadFor, RationalClosedPersistsFor]

theorem realStrictBadFor_iff_not_realClosedPersistsFor
    (distance : Real -> Real) (threshold start duration : Real) :
    RealStrictBadFor distance threshold start duration <->
      Not (RealClosedPersistsFor distance threshold start duration) := by
  simp [RealStrictBadFor, RealClosedPersistsFor]

omit [MeasurableSpace Omega] in
/-- The strict rational bad event is the complement of the measurable
rational closed-window good event. -/
theorem rationalStrictWindowBadEvent_eq_compl
    (distance : Omega -> Real -> Real)
    (start duration threshold : Real) :
    rationalStrictWindowBadEvent distance start duration threshold =
      {omega | RationalClosedPersistsFor
        (distance omega) threshold start duration}ᶜ := by
  ext omega
  exact rationalStrictBadFor_iff_not_rationalClosedPersistsFor
    (distance omega) threshold start duration

/-- Countability makes the strict bad event measurable from fixed rational
evaluation measurability alone. -/
theorem measurableSet_rationalStrictWindowBadEvent
    (distance : Omega -> Real -> Real)
    (start duration threshold : Real)
    (heval : forall q : Rat, Measurable fun omega => distance omega (q : Real)) :
    MeasurableSet
      (rationalStrictWindowBadEvent distance start duration threshold) := by
  rw [rationalStrictWindowBadEvent_eq_compl]
  exact (measurableSet_rationalClosedPersistsFor
    distance threshold start duration heval).compl

/-- Positive finite starts whose rational strict-window failure probability
is at most `failureTolerance`. -/
def rationalStrictWindowThermalizationCandidates
    (mu : Measure Omega) (distance : Omega -> Real -> Real)
    (threshold duration failureTolerance : Real) : Set ENNReal :=
  {start | 0 < start /\ start < (⊤ : ENNReal) /\
    mu.real (rationalStrictWindowBadEvent distance start.toReal
      duration threshold) <= failureTolerance}

/-- The infimum of the measurable rational strict-window candidates. -/
def rationalStrictWindowThermalizationTime
    (mu : Measure Omega) (distance : Omega -> Real -> Real)
    (threshold duration failureTolerance : Real) : ENNReal :=
  sInf (rationalStrictWindowThermalizationCandidates mu distance
    threshold duration failureTolerance)

/-- Every certified candidate is an upper bound for the strict time. -/
theorem rationalStrictWindowThermalizationTime_le_of_probability_le
    (mu : Measure Omega) (distance : Omega -> Real -> Real)
    (threshold duration failureTolerance : Real) {start : ENNReal}
    (hstart : 0 < start) (hfinite : start < (⊤ : ENNReal))
    (hprobability :
      mu.real (rationalStrictWindowBadEvent distance start.toReal
        duration threshold) <= failureTolerance) :
    rationalStrictWindowThermalizationTime mu distance
      threshold duration failureTolerance <= start := by
  apply sInf_le
  exact ⟨hstart, hfinite, hprobability⟩

omit [MeasurableSpace Omega] in
/-- Increasing the admitted distance removes rational bad samples. -/
theorem rationalStrictWindowBadEvent_mono_threshold
    (distance : Omega -> Real -> Real) (start duration : Real)
    {thresholdSmall thresholdLarge : Real}
    (hthreshold : thresholdSmall <= thresholdLarge) :
    rationalStrictWindowBadEvent distance start duration thresholdLarge ⊆
      rationalStrictWindowBadEvent distance start duration thresholdSmall := by
  rintro omega ⟨q, hleft, hright, hbad⟩
  exact ⟨q, hleft, hright, hthreshold.trans_lt hbad⟩

omit [MeasurableSpace Omega] in
/-- Increasing the required duration adds rational bad samples. -/
theorem rationalStrictWindowBadEvent_mono_duration
    (distance : Omega -> Real -> Real) (start threshold : Real)
    {durationSmall durationLarge : Real}
    (hduration : durationSmall <= durationLarge) :
    rationalStrictWindowBadEvent distance start durationSmall threshold ⊆
      rationalStrictWindowBadEvent distance start durationLarge threshold := by
  rintro omega ⟨q, hleft, hright, hbad⟩
  refine ⟨q, hleft, ?_, hbad⟩
  have hsum : start + durationSmall <= start + durationLarge := by linarith
  exact hright.trans hsum

/-- A looser distance threshold cannot increase the strict measurable time. -/
theorem rationalStrictWindowThermalizationTime_antitone_threshold
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (distance : Omega -> Real -> Real)
    (thresholdSmall thresholdLarge duration failureTolerance : Real)
    (hthreshold : thresholdSmall <= thresholdLarge) :
    rationalStrictWindowThermalizationTime mu distance
        thresholdLarge duration failureTolerance <=
      rationalStrictWindowThermalizationTime mu distance
        thresholdSmall duration failureTolerance := by
  unfold rationalStrictWindowThermalizationTime
  apply le_sInf
  intro start hstart
  apply sInf_le
  refine ⟨hstart.1, hstart.2.1, ?_⟩
  exact (measureReal_mono (h₂ := by finiteness)
    (rationalStrictWindowBadEvent_mono_threshold distance start.toReal
      duration hthreshold)).trans hstart.2.2

/-- Requiring a longer window cannot decrease the strict measurable time. -/
theorem rationalStrictWindowThermalizationTime_monotone_duration
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (distance : Omega -> Real -> Real)
    (threshold durationSmall durationLarge failureTolerance : Real)
    (hduration : durationSmall <= durationLarge) :
    rationalStrictWindowThermalizationTime mu distance
        threshold durationSmall failureTolerance <=
      rationalStrictWindowThermalizationTime mu distance
        threshold durationLarge failureTolerance := by
  unfold rationalStrictWindowThermalizationTime
  apply le_sInf
  intro start hstart
  apply sInf_le
  refine ⟨hstart.1, hstart.2.1, ?_⟩
  exact (measureReal_mono (h₂ := by finiteness)
    (rationalStrictWindowBadEvent_mono_duration distance start.toReal
      threshold hduration)).trans hstart.2.2

/-- Allowing more failure probability cannot increase the strict time. -/
theorem rationalStrictWindowThermalizationTime_antitone_failureTolerance
    (mu : Measure Omega) (distance : Omega -> Real -> Real)
    (threshold duration failureToleranceSmall failureToleranceLarge : Real)
    (hfailure : failureToleranceSmall <= failureToleranceLarge) :
    rationalStrictWindowThermalizationTime mu distance
        threshold duration failureToleranceLarge <=
      rationalStrictWindowThermalizationTime mu distance
        threshold duration failureToleranceSmall := by
  unfold rationalStrictWindowThermalizationTime
  apply le_sInf
  intro start hstart
  apply sInf_le
  exact ⟨hstart.1, hstart.2.1, hstart.2.2.trans hfailure⟩

/-- Continuous sample paths identify rational strict failure with literal
real-time strict failure on every positive-duration window. -/
theorem rationalStrictBadFor_iff_realStrictBadFor
    (distance : Real -> Real) (threshold start duration : Real)
    (hduration : 0 < duration) (hcontinuous : Continuous distance) :
    RationalStrictBadFor distance threshold start duration <->
      RealStrictBadFor distance threshold start duration := by
  rw [rationalStrictBadFor_iff_not_rationalClosedPersistsFor,
    realStrictBadFor_iff_not_realClosedPersistsFor,
    rationalClosedPersistsFor_iff_realClosedPersistsFor
      distance threshold start duration hduration hcontinuous]

omit [MeasurableSpace Omega] in
/-- Ensemble-level event equality under pathwise continuity. -/
theorem rationalStrictWindowBadEvent_eq_realStrictWindowBadEvent
    (distance : Omega -> Real -> Real)
    (start duration threshold : Real) (hduration : 0 < duration)
    (hcontinuous : forall omega, Continuous (distance omega)) :
    rationalStrictWindowBadEvent distance start duration threshold =
      realStrictWindowBadEvent distance start duration threshold := by
  ext omega
  exact rationalStrictBadFor_iff_realStrictBadFor
    (distance omega) threshold start duration hduration (hcontinuous omega)

/-- Thus candidate membership is exactly a literal continuous-time strict
window probability statement, not merely a sampled surrogate. -/
theorem mem_rationalStrictWindowThermalizationCandidates_iff_real
    (mu : Measure Omega) (distance : Omega -> Real -> Real)
    (threshold duration failureTolerance : Real) (hduration : 0 < duration)
    (hcontinuous : forall omega, Continuous (distance omega))
    (start : ENNReal) :
    start ∈ rationalStrictWindowThermalizationCandidates mu distance
        threshold duration failureTolerance <->
      0 < start /\ start < (⊤ : ENNReal) /\
        mu.real (realStrictWindowBadEvent distance start.toReal
          duration threshold) <= failureTolerance := by
  rw [rationalStrictWindowThermalizationCandidates]
  simp only [Set.mem_ofPred_eq]
  rw [rationalStrictWindowBadEvent_eq_realStrictWindowBadEvent
    distance start.toReal duration threshold hduration hcontinuous]

omit [MeasurableSpace Omega] in
/-- The rational strict event is contained in the older closed-failure event.
The converse can fail exactly on threshold equality. -/
theorem rationalStrictWindowBadEvent_subset_microscopicEquilibriumWindowBadEvent
    {E : Type*} [PseudoMetricSpace E]
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (start duration threshold : Real) (N : Nat) :
    rationalStrictWindowBadEvent
        (fun omega time => dist (micro N omega time) equilibrium)
        start duration threshold ⊆
      microscopicEquilibriumWindowBadEvent micro equilibrium
        start (start + duration) threshold N := by
  rintro omega ⟨q, hleft, hright, hbad⟩
  exact ⟨(q : Real), ⟨hleft, hright⟩, hbad.le⟩

/-- Consequently the measurable strict Tc is no later than the older Tc with
closed failure.  Equality needs an additional no-threshold-boundary input. -/
theorem rationalStrictWindowThermalizationTime_le_microscopicWindowThermalizationTime
    {E : Type*} [PseudoMetricSpace E]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance : Real) (N : Nat) :
    rationalStrictWindowThermalizationTime mu
        (fun omega time => dist (micro N omega time) equilibrium)
        threshold duration failureTolerance <=
      microscopicWindowThermalizationTime mu micro equilibrium
        threshold duration failureTolerance N := by
  unfold rationalStrictWindowThermalizationTime
    microscopicWindowThermalizationTime
  apply le_sInf
  intro start hstart
  apply sInf_le
  refine ⟨hstart.1, hstart.2.1, ?_⟩
  exact (measureReal_mono (h₂ := by finiteness)
    (rationalStrictWindowBadEvent_subset_microscopicEquilibriumWindowBadEvent
      micro equilibrium start.toReal duration threshold N)).trans hstart.2.2

end

end ArchonPhysics.MeasurableMicroscopicWindowThermalizationTime
