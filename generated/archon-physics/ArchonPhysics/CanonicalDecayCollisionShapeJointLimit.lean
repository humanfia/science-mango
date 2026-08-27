import ArchonPhysics.CanonicalCollisionShapeConvergenceInProbability
import ArchonPhysics.ProbabilityJointLimitDiagonalization

/-!
# Frozen decay-channel collision-shape joint limit

This is the model-facing consumer of the scalar collision-shape convergence
theorem.  It fixes the actual three-wave decay sign channel and lets the
qualitative probability diagonalization choose a deterministic volume cutoff
`N_min(g)`.  Every admitted weak-coupling/thermodynamic path then misses the
weak-measure tolerance `g / 2` with probability tending to zero.

The amplification is deliberately the constant one.  Weak-topology distance
is not silently promoted to a quantitative estimate for a resonance kernel
whose Lipschitz norm grows with observation time.
-/

open scoped Topology

namespace ArchonPhysics.CanonicalDecayCollisionShapeJointLimit

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalCollisionShapeConvergenceInProbability
open ArchonPhysics.ProbabilityJointLimitDiagonalization
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.ThermalizationTransfer
open Filter MeasureTheory

noncomputable section

/-- The genuine normalized scalar collision shape in the frozen decay
channel, indexed by physical volume `N = n + 3`. -/
abbrev canonicalDecayCollisionShapeSequence :
    Nat -> RandomEnsemble.SampleSpace -> ProbabilityMeasure Real :=
  fun n omega => canonicalCollisionNormalizedMeasure
    canonicalIIDMassPhaseEnsemble decayInteractionSign n omega

/-- The deterministic scalar collision shape used as the thermodynamic
target for the frozen decay channel. -/
abbrev canonicalDecayCollisionShapeTarget :
    RandomEnsemble.SampleSpace -> ProbabilityMeasure Real :=
  fun _omega => canonicalCollisionMeasureLimit
    canonicalIIDMassPhaseEnsemble decayInteractionSign

/-- The frozen decay-channel shape converges in probability in its genuine
weak topology. -/
theorem canonicalDecayCollisionShapeSequence_tendstoInMeasure :
    let _ : PseudoMetricSpace (ProbabilityMeasure Real) :=
      TopologicalSpace.pseudoMetrizableSpacePseudoMetric _
    TendstoInMeasure RandomEnsemble.canonicalLaw
      canonicalDecayCollisionShapeSequence atTop
      canonicalDecayCollisionShapeTarget := by
  let _ : PseudoMetricSpace (ProbabilityMeasure Real) :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric _
  change TendstoInMeasure canonicalIIDMassPhaseEnsemble.probability
    (fun n omega => canonicalCollisionNormalizedMeasure
      canonicalIIDMassPhaseEnsemble decayInteractionSign n omega) atTop
    (fun _omega => canonicalCollisionMeasureLimit
      canonicalIIDMassPhaseEnsemble decayInteractionSign)
  exact
    canonicalCollisionNormalizedMeasure_tendstoInMeasure_limit
      canonicalIIDMassPhaseEnsemble decayInteractionSign

/-- A deterministic `N_min(g)` selected from the actual decay-channel
collision-shape convergence.  Constant-one amplification makes the selected
weak-measure tolerance exactly `g / 2` for positive `g`. -/
abbrev canonicalDecayCollisionShapeSizeCutoff : Real -> Nat :=
  let _ : PseudoMetricSpace (ProbabilityMeasure Real) :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric _
  probabilityJointSizeCutoff RandomEnsemble.canonicalLaw
    canonicalDecayCollisionShapeSequence canonicalDecayCollisionShapeTarget
    (fun _g => 1)
    (by
      change TendstoInMeasure canonicalIIDMassPhaseEnsemble.probability
        (fun n omega => canonicalCollisionNormalizedMeasure
          canonicalIIDMassPhaseEnsemble decayInteractionSign n omega) atTop
        (fun _omega => canonicalCollisionMeasureLimit
          canonicalIIDMassPhaseEnsemble decayInteractionSign)
      exact
        canonicalCollisionNormalizedMeasure_tendstoInMeasure_limit
          canonicalIIDMassPhaseEnsemble decayInteractionSign)

/-- Along every joint path admitted by the selected cutoff, the probability
of weak-measure error at least `g / 2` tends to zero. -/
theorem canonicalDecayCollisionShape_jointLimit_probability_control
    (s : AdmissibleJointLimit canonicalDecayCollisionShapeSizeCutoff) :
    let _ : PseudoMetricSpace (ProbabilityMeasure Real) :=
      TopologicalSpace.pseudoMetrizableSpacePseudoMetric _
    (forall j,
      probabilityDiagonalThreshold (fun _g => 1) (s.coupling j) =
        s.coupling j / 2) /\
    (forall j,
      probabilityDiagonalThreshold (fun _g => 1) (s.coupling j) <=
        s.coupling j) /\
    Tendsto
      (fun j => RandomEnsemble.canonicalLaw.real
        (probabilityDiagonalBadEvent canonicalDecayCollisionShapeSequence
          canonicalDecayCollisionShapeTarget (fun _g => 1)
          (s.systemSize j) (s.coupling j)))
      atTop (nhds 0) := by
  let _ : PseudoMetricSpace (ProbabilityMeasure Real) :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric _
  have hconv : TendstoInMeasure RandomEnsemble.canonicalLaw
      canonicalDecayCollisionShapeSequence atTop
      canonicalDecayCollisionShapeTarget := by
    change TendstoInMeasure canonicalIIDMassPhaseEnsemble.probability
      (fun n omega => canonicalCollisionNormalizedMeasure
        canonicalIIDMassPhaseEnsemble decayInteractionSign n omega) atTop
      (fun _omega => canonicalCollisionMeasureLimit
        canonicalIIDMassPhaseEnsemble decayInteractionSign)
    exact
      canonicalCollisionNormalizedMeasure_tendstoInMeasure_limit
        canonicalIIDMassPhaseEnsemble decayInteractionSign
  change AdmissibleJointLimit
    (probabilityJointSizeCutoff RandomEnsemble.canonicalLaw
      canonicalDecayCollisionShapeSequence canonicalDecayCollisionShapeTarget
      (fun _g => 1) hconv) at s
  refine ⟨?_, ?_, ?_⟩
  · intro j
    unfold probabilityDiagonalThreshold
    norm_num
  · intro j
    rw [show probabilityDiagonalThreshold (fun _g => 1) (s.coupling j) =
        s.coupling j / 2 by
      unfold probabilityDiagonalThreshold
      norm_num]
    exact div_le_self (s.coupling_pos j).le (by norm_num)
  · exact probabilityDiagonalBadEvent_probability_along_jointLimit_tendsto_zero
      RandomEnsemble.canonicalLaw canonicalDecayCollisionShapeSequence
      canonicalDecayCollisionShapeTarget (fun _g => 1) hconv
      (fun _g => by norm_num) s

end

end ArchonPhysics.CanonicalDecayCollisionShapeJointLimit
