import ArchonPhysics.CanonicalFrozenProbabilisticThermalizationReduction
import ArchonPhysics.ProbabilisticHittingTransfer
import ArchonPhysics.R32SupervolumeJointLimit

/-!
# A persistence no-go for the R32 kinetic-window certificate

This file isolates a purely logical obstruction.  Suppose that along one
admissible joint limit the microscopic scaled distance at a fixed
nonnegative kinetic time stays at least `delta + eta` with probability
tending to one.  If the proposed kinetic distance is already strictly below
`delta` at that time, then no `KineticWindowApproximation` for that kinetic
distance can exist.

The proof uses no microscopic persistence estimate.  Such an estimate is an
explicit hypothesis.  The contradiction is only between two high-probability
events: the assumed persistent lower-bound event and the certificate's
vanishing local-uniform-error event.
-/

namespace ArchonPhysics.R32KineticWindowNoGo

open Filter MeasureTheory Set Topology
open ArchonPhysics
open ArchonPhysics.CanonicalFrozenClosedHittingRescaling
open ArchonPhysics.CanonicalFrozenProbabilisticThermalizationReduction
open ArchonPhysics.CanonicalRandomMassPhaseThermalizationObservable
open ArchonPhysics.ProbabilisticHittingTransfer
open ArchonPhysics.R32SupervolumeJointLimit
open ArchonPhysics.ThermalizationTransfer

noncomputable section

local instance canonicalProbabilityMeasure :
    IsProbabilityMeasure canonicalIIDMassPhaseEnsemble.probability :=
  ⟨canonicalIIDMassPhaseEnsemble.probability_univ⟩

/-- The fixed-kinetic-time event on which the microscopic scaled distance is
separated from the threshold by at least `eta`. -/
def persistentLowerEvent
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta eta tau0 : Real) {sizeCutoff : Real → Nat}
    (s : AdmissibleJointLimit sizeCutoff) (j : Nat) :
    Set RandomEnsemble.SampleSpace :=
  {omega |
    delta + eta ≤
      scaledDistance kappa beta hbeta mu
        (s.systemSize j) (s.coupling j) omega tau0}

/-- The persistence premise needed by the no-go: one admissible path and one
fixed kinetic time retain a positive separation above the threshold with
probability tending to one. -/
def HasPersistentMicroscopicLowerBound
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (sizeCutoff : Real → Nat)
    (s : AdmissibleJointLimit sizeCutoff) (tau0 eta : Real) : Prop :=
  0 ≤ tau0 ∧ 0 < eta ∧
    Tendsto
      (fun j => canonicalIIDMassPhaseEnsemble.probability
        (persistentLowerEvent kappa beta hbeta mu delta eta tau0 s j))
      atTop (nhds 1)

theorem measurableSet_persistentLowerEvent
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta eta tau0 : Real) {sizeCutoff : Real → Nat}
    (s : AdmissibleJointLimit sizeCutoff) (j : Nat) :
    MeasurableSet
      (persistentLowerEvent kappa beta hbeta mu delta eta tau0 s j) := by
  change MeasurableSet
    ((fun omega => scaledDistance kappa beta hbeta mu
      (s.systemSize j) (s.coupling j) omega tau0) ⁻¹' Ici (delta + eta))
  apply measurableSet_Ici.preimage
  simpa only [scaledDistance] using
    (measurable_canonicalFrozenLateWindowL1Distance
      (N := s.systemSize j + 3)
      kappa beta (s.coupling j) hbeta (1 / 4) mu
      (tau0 / s.coupling j ^ 2))

/-- A persistent microscopic lower bound at a time where the proposed kinetic
distance is below threshold rules out the corresponding kinetic-window
approximation certificate. -/
theorem not_kineticWindowApproximation_of_persistentLowerBound
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real} {sizeCutoff : Real → Nat}
    {kineticDistance : Real → Real}
    {s : AdmissibleJointLimit sizeCutoff} {tau0 eta : Real}
    (hpersistence : HasPersistentMicroscopicLowerBound
      kappa beta hbeta mu delta sizeCutoff s tau0 eta)
    (hkinetic : kineticDistance tau0 < delta) :
    ¬ Nonempty (KineticWindowApproximation
      kappa beta hbeta mu delta sizeCutoff kineticDistance) := by
  rintro ⟨certificate⟩
  let probability := canonicalIIDMassPhaseEnsemble.probability
  let T : Real := tau0 + 1
  let highEvent : Nat → Set RandomEnsemble.SampleSpace :=
    fun j => persistentLowerEvent
      kappa beta hbeta mu delta eta tau0 s j
  let smallErrorEvent : Nat → Set RandomEnsemble.SampleSpace :=
    fun j => errorBelowEvent
      (fun j omega => certificate.localUniformError T
        (s.systemSize j) (s.coupling j) omega)
      eta j
  have htau0 : 0 ≤ tau0 := hpersistence.1
  have heta : 0 < eta := hpersistence.2.1
  have hT : 0 < T := by
    dsimp [T]
    linarith
  have hsmall :
      Tendsto (fun j => probability (smallErrorEvent j))
        atTop (nhds 1) := by
    exact
      ConvergesInProbabilityTo.tendsto_measure_errorBelowEvent
        (certificate.localUniformError_convergesInProbability s T hT)
        heta
  have hsmall_subset : ∀ j, smallErrorEvent j ⊆ (highEvent j)ᶜ := by
    intro j omega homega
    have hclose := certificate.localUniformError_controls
      s T eta hT heta j omega homega
    have hatTau0 := hclose tau0 htau0 (by
      dsimp [T]
      linarith)
    have hupper := le_abs_self
      (scaledDistance kappa beta hbeta mu
        (s.systemSize j) (s.coupling j) omega tau0 -
          kineticDistance tau0)
    change omega ∉ highEvent j
    change ¬ delta + eta ≤
      scaledDistance kappa beta hbeta mu
        (s.systemSize j) (s.coupling j) omega tau0
    linarith
  have hcomplOne :
      Tendsto (fun j => probability ((highEvent j)ᶜ))
        atTop (nhds 1) := by
    exact tendsto_measure_superset_atTop_one probability
      smallErrorEvent (fun j => (highEvent j)ᶜ) hsmall hsmall_subset
  have hhigh :
      Tendsto (fun j => probability (highEvent j))
        atTop (nhds 1) := by
    simpa only [probability, highEvent] using hpersistence.2.2
  have hcomplZero :
      Tendsto (fun j => probability ((highEvent j)ᶜ))
        atTop (nhds 0) := by
    have hsub := ENNReal.Tendsto.sub
      (tendsto_const_nhds :
        Tendsto (fun _j : Nat => (1 : ENNReal)) atTop (nhds 1))
      hhigh (Or.inl ENNReal.one_ne_top)
    have hmeasureCompl :
        (fun j => probability ((highEvent j)ᶜ)) =
          (fun j => 1 - probability (highEvent j)) := by
      funext j
      rw [measure_compl
        (measurableSet_persistentLowerEvent
          kappa beta hbeta mu delta eta tau0 s j)
        (measure_ne_top probability (highEvent j)), measure_univ]
    rw [hmeasureCompl]
    simpa using hsub
  have hzero_eq_one : (0 : ENNReal) = 1 :=
    tendsto_nhds_unique hcomplZero hcomplOne
  exact zero_ne_one hzero_eq_one

/-- Existential form of the no-go, matching the statement that there is at
least one admissible schedule, time, and positive separation witnessing the
microscopic persistence obstruction. -/
theorem not_kineticWindowApproximation_of_exists_persistentLowerBound
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real} {sizeCutoff : Real → Nat}
    {kineticDistance : Real → Real}
    (hobstruction :
      ∃ (s : AdmissibleJointLimit sizeCutoff) (tau0 eta : Real),
        HasPersistentMicroscopicLowerBound
          kappa beta hbeta mu delta sizeCutoff s tau0 eta ∧
        kineticDistance tau0 < delta) :
    ¬ Nonempty (KineticWindowApproximation
      kappa beta hbeta mu delta sizeCutoff kineticDistance) := by
  rcases hobstruction with ⟨s, tau0, eta, hpersistence, hkinetic⟩
  exact not_kineticWindowApproximation_of_persistentLowerBound
    (s := s) (tau0 := tau0) (eta := eta) hpersistence hkinetic

/-- Specialization to the explicit R32 supervolume schedule.  A future
physical persistence theorem need only supply the displayed probability
limit; the logical incompatibility with `KineticWindowApproximation` is
already kernel-checked here. -/
theorem not_kineticWindowApproximation_of_supervolumePersistentLowerBound
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real} {sizeCutoff : Real → Nat}
    {kineticDistance : Real → Real} {tau0 eta : Real}
    (htau0 : 0 ≤ tau0) (heta : 0 < eta)
    (hpersistence :
      Tendsto
        (fun j => canonicalIIDMassPhaseEnsemble.probability
          (persistentLowerEvent kappa beta hbeta mu delta eta tau0
            (supervolumeJointLimit sizeCutoff) j))
        atTop (nhds 1))
    (hkinetic : kineticDistance tau0 < delta) :
    ¬ Nonempty (KineticWindowApproximation
      kappa beta hbeta mu delta sizeCutoff kineticDistance) := by
  exact not_kineticWindowApproximation_of_persistentLowerBound
    ⟨htau0, heta, hpersistence⟩ hkinetic

end

end ArchonPhysics.R32KineticWindowNoGo
