import ArchonPhysics.R32UniformWindowHittingTimeNoGoV2
import ArchonPhysics.R32SupervolumeMicroscopicPersistenceV2

/-!
# Generic uniform-window persistence event compositor

This module isolates the probability and quantifier shell needed by the
supervolume microscopic argument.  For every fixed finite kinetic window,
it assumes a measurable good event whose complement has vanishing real
measure, a deterministic loss tending to zero, and an eventually valid
almost-everywhere pathwise bridge.  The bridge keeps the universal time
quantifier inside the sample event.

No microscopic persistence statement is assumed: the conclusion is derived
from the quantitative lower bound `1 / 8 - loss T j`.
-/

namespace ArchonPhysics.R32UniformWindowPersistenceEventCompositor

open ArchonPhysics
open ArchonPhysics.CanonicalFrozenClosedHittingRescaling
open ArchonPhysics.R32SupervolumeMicroscopicPersistenceV2
open ArchonPhysics.R32UniformWindowHittingTimeNoGoV2
open ArchonPhysics.R32SupervolumeJointLimit
open ArchonPhysics.ThermalizationTransfer
open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

local instance canonicalProbabilityMeasure :
    IsProbabilityMeasure canonicalIIDMassPhaseEnsemble.probability :=
  ⟨canonicalIIDMassPhaseEnsemble.probability_univ⟩

/-- A measurable high-probability event and a vanishing quantitative loss
imply genuine uniform-in-time persistence.  Both the microscopic bridge and
the target event quantify over every `0 < tau <= T` before probability is
taken.

The microscopic bridge is allowed to hold only eventually in the volume
index and almost everywhere in the sample.  This is the natural interface
for Hamiltonian realizations that are themselves only available almost
surely. -/
theorem uniformWindowPersistence_of_good_events_and_vanishing_loss
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real} {sizeCutoff : Real -> Nat}
    {s : AdmissibleJointLimit sizeCutoff}
    (goodEvent : Real -> Nat -> Set RandomEnsemble.SampleSpace)
    (loss : Real -> Nat -> Real)
    (hgoodMeasurable : forall T j, MeasurableSet (goodEvent T j))
    (hgoodComplZero : forall T, 0 < T ->
      Tendsto
        (fun j => canonicalIIDMassPhaseEnsemble.probability.real
          (goodEvent T j)ᶜ)
        atTop (nhds 0))
    (hlossZero : forall T, 0 < T ->
      Tendsto (loss T) atTop (nhds 0))
    (hpathwise : forall T, 0 < T ->
      ∀ᶠ j in atTop,
        ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
          omega ∈ goodEvent T j ->
            forall tau : Real, 0 < tau -> tau <= T ->
              (1 : Real) / 8 - loss T j <=
                scaledDistance kappa beta hbeta mu
                  (s.systemSize j) (s.coupling j) omega tau)
    (hdelta : delta < (1 : Real) / 8) :
    UniformWindowPersistence
      kappa beta hbeta mu delta sizeCutoff s := by
  intro T hT
  let eta : Real := ((1 : Real) / 8 - delta) / 2
  have heta : 0 < eta := by
    dsimp only [eta]
    linarith
  refine ⟨eta, heta, ?_⟩
  let probability := canonicalIIDMassPhaseEnsemble.probability
  let targetEvent : Nat -> Set RandomEnsemble.SampleSpace :=
    fun j => uniformWindowLowerEvent
      kappa beta hbeta mu delta eta T s j
  have hgoodOne :
      Tendsto (fun j => probability (goodEvent T j))
        atTop (nhds 1) := by
    apply tendsto_measure_one_of_measureReal_compl_le_budget
      probability (goodEvent T)
      (fun j => probability.real (goodEvent T j)ᶜ)
      (hgoodMeasurable T) (fun _j => le_rfl)
    simpa only [probability] using hgoodComplZero T hT
  have hlossSmall : ∀ᶠ j in atTop, loss T j <= eta :=
    (hlossZero T hT).eventually
      (Iic_mem_nhds heta)
  have hgood_le_target : ∀ᶠ j in atTop,
      probability (goodEvent T j) <= probability (targetEvent j) := by
    filter_upwards [hlossSmall, hpathwise T hT] with j hjloss hjpath
    apply measure_mono_ae
    filter_upwards [hjpath] with omega homega
    intro hgood
    change forall tau : Real, 0 < tau -> tau <= T ->
      delta + eta <=
        scaledDistance kappa beta hbeta mu
          (s.systemSize j) (s.coupling j) omega tau
    intro tau htau htauT
    have hquantitative := homega hgood tau htau htauT
    have hmargin : delta + eta <= (1 : Real) / 8 - loss T j := by
      have hmidpoint :
          delta + eta = (1 : Real) / 8 - eta := by
        dsimp only [eta]
        ring
      rw [hmidpoint]
      exact sub_le_sub_left hjloss ((1 : Real) / 8)
    exact hmargin.trans hquantitative
  have htarget_le_one : forall j,
      probability (targetEvent j) <= (1 : ENNReal) := by
    intro j
    calc
      probability (targetEvent j) <=
          probability (Set.univ : Set RandomEnsemble.SampleSpace) :=
        measure_mono (subset_univ _)
      _ = 1 := measure_univ
  have htargetOne :
      Tendsto (fun j => probability (targetEvent j))
        atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hgoodOne
      (tendsto_const_nhds :
        Tendsto (fun _j : Nat => (1 : ENNReal)) atTop (nhds 1))
      hgood_le_target
      (Filter.Eventually.of_forall htarget_le_one)
  simpa only [probability, targetEvent] using htargetOne

/-- All-index specialization of
`uniformWindowPersistence_of_good_events_and_vanishing_loss`. -/
theorem uniformWindowPersistence_of_good_events_and_vanishing_loss_all
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real} {sizeCutoff : Real -> Nat}
    {s : AdmissibleJointLimit sizeCutoff}
    (goodEvent : Real -> Nat -> Set RandomEnsemble.SampleSpace)
    (loss : Real -> Nat -> Real)
    (hgoodMeasurable : forall T j, MeasurableSet (goodEvent T j))
    (hgoodComplZero : forall T, 0 < T ->
      Tendsto
        (fun j => canonicalIIDMassPhaseEnsemble.probability.real
          (goodEvent T j)ᶜ)
        atTop (nhds 0))
    (hlossZero : forall T, 0 < T ->
      Tendsto (loss T) atTop (nhds 0))
    (hpathwise : forall T, 0 < T -> forall j,
      ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
        omega ∈ goodEvent T j ->
          forall tau : Real, 0 < tau -> tau <= T ->
            (1 : Real) / 8 - loss T j <=
              scaledDistance kappa beta hbeta mu
                (s.systemSize j) (s.coupling j) omega tau)
    (hdelta : delta < (1 : Real) / 8) :
    UniformWindowPersistence
      kappa beta hbeta mu delta sizeCutoff s := by
  apply uniformWindowPersistence_of_good_events_and_vanishing_loss
    goodEvent loss hgoodMeasurable hgoodComplZero hlossZero
  · intro T hT
    exact Filter.Eventually.of_forall (hpathwise T hT)
  · exact hdelta

#print axioms uniformWindowPersistence_of_good_events_and_vanishing_loss
#print axioms uniformWindowPersistence_of_good_events_and_vanishing_loss_all

end

end ArchonPhysics.R32UniformWindowPersistenceEventCompositor
