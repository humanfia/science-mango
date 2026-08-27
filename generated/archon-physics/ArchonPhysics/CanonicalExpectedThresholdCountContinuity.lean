import ArchonPhysics.FiniteThresholdCountRightContinuity
import ArchonPhysics.CanonicalThresholdCountConcentrationInterface

/-!
# Continuity of canonical finite-block expected threshold counts

Local constancy of finite spectral counts is transported through the canonical
normalized observable and then through expectation by dominated convergence.
At a non-spectral energy this gives two-sided continuity; at every energy the
`<=` convention gives unconditional right continuity.
-/

namespace ArchonPhysics.CanonicalExpectedThresholdCountContinuity

open ArchonPhysics
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open ArchonPhysics.FiniteThresholdCountLocalConstancy
open ArchonPhysics.FiniteThresholdCountRightContinuity
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.RandomMassAcousticCountingComparison
open Filter MeasureTheory Set Topology

noncomputable section

theorem continuousAt_canonicalNormalizedHarmonicThresholdCount_of_charpoly
    (N : Nat) [NeZero N] (E : Real)
    (omega : RandomEnsemble.SampleSpace)
    (hEval : (Matrix.charpoly
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := N) omega)).1).eval E ≠ 0) :
    ContinuousAt
      (fun x => canonicalNormalizedHarmonicThresholdCount N x omega) E := by
  rw [show (fun x => canonicalNormalizedHarmonicThresholdCount N x omega) =
      fun x => (orderedEigenvalueThresholdCount
        (harmonicHermitian
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega)) x : Real) / (N : Real) by
    funext x
    exact canonicalNormalizedHarmonicThresholdCount_eq N x omega]
  exact (continuousAt_orderedEigenvalueThresholdCount_of_charpoly_eval_ne_zero
    (harmonicHermitian
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
        (N := N) omega)) E hEval).div_const _

theorem continuousWithinAt_canonicalNormalizedHarmonicThresholdCount_Ici
    (N : Nat) [NeZero N] (E : Real)
    (omega : RandomEnsemble.SampleSpace) :
    ContinuousWithinAt
      (fun x => canonicalNormalizedHarmonicThresholdCount N x omega)
      (Ici E) E := by
  rw [show (fun x => canonicalNormalizedHarmonicThresholdCount N x omega) =
      fun x => (orderedEigenvalueThresholdCount
        (harmonicHermitian
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega)) x : Real) / (N : Real) by
    funext x
    exact canonicalNormalizedHarmonicThresholdCount_eq N x omega]
  exact (continuousWithinAt_orderedEigenvalueThresholdCount_Ici
    (harmonicHermitian
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
        (N := N) omega)) E).div_const _

/-- If the fixed energy is almost surely off the finite-volume spectrum, the
expected normalized threshold count is continuous at that energy. -/
theorem continuousAt_expectedCanonicalNormalizedHarmonicThresholdCount
    (N : Nat) [NeZero N] (E : Real)
    (havoid : ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
      (Matrix.charpoly
        (harmonicHermitian
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega)).1).eval E ≠ 0) :
    ContinuousAt
      (fun x => ∫ omega, canonicalNormalizedHarmonicThresholdCount N x omega
        ∂(RandomEnsemble.canonicalLaw)) E := by
  refine continuousAt_of_dominated
    (μ := RandomEnsemble.canonicalLaw) (bound := fun _ => (1 : Real))
    ?_ ?_ (integrable_const 1) ?_
  · exact Eventually.of_forall fun x =>
      (measurable_canonicalNormalizedHarmonicThresholdCount N x).aestronglyMeasurable
  · exact Eventually.of_forall fun x =>
      ae_of_all _ fun omega => by
        have hmem :=
          canonicalNormalizedHarmonicThresholdCount_mem_Icc N x omega
        rw [Real.norm_eq_abs, abs_of_nonneg hmem.1]
        exact hmem.2
  · filter_upwards [havoid] with omega homega
    exact continuousAt_canonicalNormalizedHarmonicThresholdCount_of_charpoly
      N E omega homega

/-- Every finite-block expected CDF is continuous from the right, including
at the deterministic acoustic zero mode. -/
theorem continuousWithinAt_expectedCanonicalNormalizedHarmonicThresholdCount_Ici
    (N : Nat) [NeZero N] (E : Real) :
    ContinuousWithinAt
      (fun x => ∫ omega, canonicalNormalizedHarmonicThresholdCount N x omega
        ∂(RandomEnsemble.canonicalLaw)) (Ici E) E := by
  refine continuousWithinAt_of_dominated
    (μ := RandomEnsemble.canonicalLaw) (bound := fun _ => (1 : Real))
    ?_ ?_ (integrable_const 1) ?_
  · exact Eventually.of_forall fun x =>
      (measurable_canonicalNormalizedHarmonicThresholdCount N x).aestronglyMeasurable
  · exact Eventually.of_forall fun x =>
      ae_of_all _ fun omega => by
        have hmem :=
          canonicalNormalizedHarmonicThresholdCount_mem_Icc N x omega
        rw [Real.norm_eq_abs, abs_of_nonneg hmem.1]
        exact hmem.2
  · exact ae_of_all _ fun omega =>
      continuousWithinAt_canonicalNormalizedHarmonicThresholdCount_Ici
        N E omega

end

end ArchonPhysics.CanonicalExpectedThresholdCountContinuity
