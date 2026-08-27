import ArchonPhysics.RandomMassPositiveLateWindowObservable

/-!
# Consumer: measurable random-mass positive-mode late-window observable

This acceptance target checks the complete unconditional measurable-observable
chain.  It assumes a measurable ambient initial point and a measurable ambient
flow; it does not claim that a realization-dependent random initial datum has
already been inserted into the canonical coercive global-flow construction.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.RandomMassPositiveLateWindowObservable

noncomputable section

/-- Canonical iid masses: every fixed late window, its normalized `l1`
equipartition diagnostic, and both countable-time first-hit diagnostics are
measurable in the sample. -/
theorem problem_canonical_iid_positive_late_window_observable
    {N : Nat} [NeZero N]
    (initial : RandomEnsemble.SampleSpace → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hinitial : Measurable initial) (hflow : Measurable flow)
    (mu T delta duration : Real) :
    Measurable (sampledPositiveLateWindowAverage
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      initial flow mu T) ∧
    Measurable (sampledPositiveLateWindowTotalWeight
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      initial flow mu T) ∧
    Measurable (sampledPositiveLateWindowNormalizedWeights
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      initial flow mu T) ∧
    Measurable (sampledPositiveUniformWeights
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))) ∧
    Measurable (sampledPositiveLateWindowL1Distance
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      initial flow mu T) ∧
    Measurable (sampledPositiveLateWindowRationalStrictHittingTime
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      initial flow mu delta) ∧
    Measurable (sampledPositiveLateWindowRationalPersistentHittingTime
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      initial flow mu delta duration) := by
  let massSample :=
    canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N)
  have hmass : ∀ i, Measurable fun s ↦ (massSample s).mass i :=
    RandomMassOrderedProjectorBridge.measurable_restrictPositiveMass_coordinate
      canonicalIIDMassPhaseEnsemble
  exact ⟨
    measurable_sampledPositiveLateWindowAverage
      massSample initial flow hmass hinitial hflow mu T,
    measurable_sampledPositiveLateWindowTotalWeight
      massSample initial flow hmass hinitial hflow mu T,
    measurable_sampledPositiveLateWindowNormalizedWeights
      massSample initial flow hmass hinitial hflow mu T,
    measurable_sampledPositiveUniformWeights massSample hmass,
    measurable_sampledPositiveLateWindowL1Distance
      massSample initial flow hmass hinitial hflow mu T,
    measurable_sampledPositiveLateWindowRationalStrictHittingTime
      massSample initial flow hmass hinitial hflow mu delta,
    measurable_sampledPositiveLateWindowRationalPersistentHittingTime
      massSample initial flow hmass hinitial hflow mu delta duration⟩

/-- The integrated and averaged profiles are nonnegative on every genuine
late window, independently of any thermalization claim. -/
theorem problem_positive_late_window_nonnegative
    {S : Type*} {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (mu T : Real) (hmu : 0 ≤ mu) (hmuOne : mu < 1) (hT : 0 < T)
    (s : S) :
    (∀ k, 0 ≤ sampledPositiveLateWindowIntegral
      massSample initial flow mu T s k) ∧
    (∀ k, 0 ≤ sampledPositiveLateWindowAverage
      massSample initial flow mu T s k) ∧
    0 ≤ sampledPositiveLateWindowTotalWeight
      massSample initial flow mu T s := by
  exact ⟨
    fun k ↦ sampledPositiveLateWindowIntegral_nonneg
      massSample initial flow mu T hmu hmuOne.le hT.le s k,
    fun k ↦ sampledPositiveLateWindowAverage_nonneg
      massSample initial flow mu T hmu hmuOne hT s k,
    sampledPositiveLateWindowTotalWeight_nonneg
      massSample initial flow mu T hmu hmuOne hT s⟩


/-- The measurable rational-window predicate is the literal continuous-time
window predicate whenever the diagnostic is continuous and the duration is
positive. -/
theorem problem_rational_window_is_continuous_time_window
    (distance : Real → Real) (delta start duration : Real)
    (hduration : 0 < duration) (hcontinuous : Continuous distance) :
    RationalClosedPersistsFor distance delta start duration ↔
      RealClosedPersistsFor distance delta start duration :=
  rationalClosedPersistsFor_iff_realClosedPersistsFor
    distance delta start duration hduration hcontinuous

#print axioms problem_rational_window_is_continuous_time_window

end

end ArchonPhysicsConsumers.Thermalization
