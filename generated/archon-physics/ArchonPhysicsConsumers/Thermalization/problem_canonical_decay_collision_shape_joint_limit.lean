import ArchonPhysics.CanonicalCollisionShapeConvergenceInProbability
import ArchonPhysics.CanonicalDecayCollisionShapeJointLimit

/-!
# Consumer: canonical decay collision-shape joint limit

The actual frozen decay-channel collision shape converges in probability in
the weak topology.  The library-selected deterministic cutoff `N_min(g)`
therefore makes the probability of weak-measure error at least `g / 2` tend
to zero along every admitted weak-coupling/thermodynamic path.

This consumer preserves the library theorem's scope: no quantitative control
of an increasingly sharp finite-time resonance kernel is inferred from weak
convergence alone.
-/

open scoped Topology

namespace ArchonPhysicsConsumers.Thermalization.CanonicalDecayCollisionShapeJointLimit

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalCollisionShapeConvergenceInProbability
open ArchonPhysics.CanonicalDecayCollisionShapeJointLimit
open ArchonPhysics.ProbabilityJointLimitDiagonalization
open ArchonPhysics.ThermalizationTransfer
open Filter MeasureTheory

noncomputable section

/-- Consumer-facing convergence-in-probability statement for the actual
frozen decay collision shape. -/
theorem canonical_decayCollisionShape_tendstoInMeasure :
    let _ : PseudoMetricSpace (ProbabilityMeasure Real) :=
      TopologicalSpace.pseudoMetrizableSpacePseudoMetric _
    TendstoInMeasure RandomEnsemble.canonicalLaw
      canonicalDecayCollisionShapeSequence atTop
      canonicalDecayCollisionShapeTarget :=
  canonicalDecayCollisionShapeSequence_tendstoInMeasure

/-- Consumer-facing joint-limit endpoint.  At index `j`, the selected weak
distance tolerance is exactly `g_j / 2`, and its bad-event probability tends
to zero. -/
theorem canonical_decayCollisionShape_jointLimit_probability_control
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
      atTop (nhds 0) :=
  canonicalDecayCollisionShape_jointLimit_probability_control s

end

end ArchonPhysicsConsumers.Thermalization.CanonicalDecayCollisionShapeJointLimit
