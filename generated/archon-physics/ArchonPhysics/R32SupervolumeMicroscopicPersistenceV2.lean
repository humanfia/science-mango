import ArchonPhysics.R32KineticWindowNoGo
import ArchonPhysics.R32SupervolumeJointLimit

/-!
# R32 supervolume microscopic persistence compositor, V2

This module repairs the measure-theoretic base used by the quantitative
persistence compositor.  The complement estimate is first squeezed in
`measureReal`, then transported to `ENNReal` with `ENNReal.ofReal`.  Thus no
real-valued budget is compared directly with an `ENNReal` measure.

The event-level theorem is retained as a minimal splice interface.  The
non-circular final interface, which accepts a vanishing quantitative
late-window error instead of the target event inclusion, is in
`R32SupervolumeMicroscopicPersistenceQuantitativeV2`.
-/

namespace ArchonPhysics.R32SupervolumeMicroscopicPersistenceV2

open ArchonPhysics
open ArchonPhysics.CanonicalFrozenProbabilisticThermalizationReduction
open ArchonPhysics.R32KineticWindowNoGo
open ArchonPhysics.R32SupervolumeJointLimit
open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

local instance canonicalProbabilityMeasure :
    IsProbabilityMeasure canonicalIIDMassPhaseEnsemble.probability :=
  ⟨canonicalIIDMassPhaseEnsemble.probability_univ⟩

/-- A measurable good event has probability tending to one when the real
measure of its complement is bounded by an explicit real sequence tending
to zero. -/
theorem tendsto_measure_one_of_measureReal_compl_le_budget
    {Omega : Type*} [MeasurableSpace Omega]
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (goodEvent : Nat -> Set Omega) (badBudget : Nat -> Real)
    (hgoodMeasurable : forall j, MeasurableSet (goodEvent j))
    (hbad : forall j, probability.real (goodEvent j)ᶜ <= badBudget j)
    (hbudget : Tendsto badBudget atTop (nhds 0)) :
    Tendsto (fun j => probability (goodEvent j)) atTop (nhds 1) := by
  have hbadReal :
      Tendsto
        (fun j => probability.real (goodEvent j)ᶜ)
        atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun _j => measureReal_nonneg
    · exact Filter.Eventually.of_forall hbad
    · exact hbudget
  have hbadENNReal :
      Tendsto (fun j => probability (goodEvent j)ᶜ)
        atTop (nhds 0) := by
    have hofReal := ENNReal.tendsto_ofReal hbadReal
    have hfun :
        (fun j => ENNReal.ofReal
          (probability.real (goodEvent j)ᶜ)) =
        (fun j => probability (goodEvent j)ᶜ) := by
      funext j
      exact ofReal_measureReal (measure_ne_top probability _)
    rw [hfun, ENNReal.ofReal_zero] at hofReal
    exact hofReal
  have hsub := ENNReal.Tendsto.sub
    (tendsto_const_nhds :
      Tendsto (fun _j : Nat => (1 : ENNReal)) atTop (nhds 1))
    hbadENNReal (Or.inl ENNReal.one_ne_top)
  have hmeasureIdentity :
      (fun j => probability (goodEvent j)) =
        (fun j => 1 - probability (goodEvent j)ᶜ) := by
    funext j
    calc
      probability (goodEvent j) =
          probability ((goodEvent j)ᶜ)ᶜ := by
        simp only [compl_compl]
      _ = probability Set.univ - probability (goodEvent j)ᶜ :=
        measure_compl (hgoodMeasurable j).compl
          (measure_ne_top probability (goodEvent j)ᶜ)
      _ = 1 - probability (goodEvent j)ᶜ := by
        rw [measure_univ]
  rw [hmeasureIdentity]
  simpa using hsub

/-- Minimal event-level compositor along the explicit supervolume path.
This theorem is useful for splicing a separately named deterministic
late-window inclusion; the quantitative V2 theorem should be preferred for
the final non-circular interface. -/
theorem supervolume_microscopic_persistence_of_event_inclusions
    {kappa beta : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta)
    {mu delta : Real} (_hmu_nonneg : 0 <= mu) (_hmu_lt_one : mu < 1)
    (hdelta : delta < (1 : Real) / 8)
    (sizeCutoff : Real -> Nat) (tau : Real) (_htau : 0 < tau)
    (freeConcentrationGood exactFreeErrorGood :
      Nat -> Set RandomEnsemble.SampleSpace)
    (freeBadBudget : Nat -> Real)
    (hfreeMeasurable : forall j,
      MeasurableSet (freeConcentrationGood j))
    (hfreeConcentration : forall j,
      canonicalIIDMassPhaseEnsemble.probability.real
          (freeConcentrationGood j)ᶜ <=
        freeBadBudget j)
    (hfreeBadBudget_zero :
      Tendsto freeBadBudget atTop (nhds 0))
    (hexactFreeErrorEvent : forall j,
      freeConcentrationGood j ⊆ exactFreeErrorGood j)
    (hlateWindowBridge : forall j,
      exactFreeErrorGood j ⊆
        persistentLowerEvent kappa beta hbeta mu delta
          (((1 : Real) / 8 - delta) / 2) tau
          (supervolumeJointLimit sizeCutoff) j) :
    exists eta : Real, 0 < eta /\
      Tendsto
        (fun j => canonicalIIDMassPhaseEnsemble.probability
          (persistentLowerEvent kappa beta hbeta mu delta eta tau
            (supervolumeJointLimit sizeCutoff) j))
        atTop (nhds 1) := by
  let eta : Real := ((1 : Real) / 8 - delta) / 2
  have heta : 0 < eta := by
    dsimp [eta]
    linarith
  refine ⟨eta, heta, ?_⟩
  have hfreeOne :
      Tendsto
        (fun j => canonicalIIDMassPhaseEnsemble.probability
          (freeConcentrationGood j)) atTop (nhds 1) :=
    tendsto_measure_one_of_measureReal_compl_le_budget
      canonicalIIDMassPhaseEnsemble.probability
      freeConcentrationGood freeBadBudget hfreeMeasurable
      hfreeConcentration hfreeBadBudget_zero
  apply ProbabilisticHittingTransfer.tendsto_measure_superset_atTop_one
    canonicalIIDMassPhaseEnsemble.probability
    freeConcentrationGood
    (fun j => persistentLowerEvent kappa beta hbeta mu delta eta tau
      (supervolumeJointLimit sizeCutoff) j)
    hfreeOne
  intro j
  exact (hexactFreeErrorEvent j).trans (by
    simpa only [eta] using hlateWindowBridge j)

end

#print axioms tendsto_measure_one_of_measureReal_compl_le_budget
#print axioms supervolume_microscopic_persistence_of_event_inclusions

end ArchonPhysics.R32SupervolumeMicroscopicPersistenceV2
