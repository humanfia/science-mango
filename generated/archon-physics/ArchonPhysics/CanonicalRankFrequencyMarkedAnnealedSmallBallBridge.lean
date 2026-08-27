import ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedMismatchBridge
import ArchonPhysics.CanonicalRankFrequencyMarkedJointLimitSmallBallBridge

/-!
# Annealed canonical marked mismatch small-ball bridge

The finite-volume canonical mismatch measures are atomic, while the actual
coarea and localization estimates are naturally annealed.  A realization-wise
small-ball estimate is therefore stronger than needed.  The genuine annealed
barycenters already converge weakly to the deterministic canonical mismatch
target, so a linear annealed small-ball bound with a vanishing volume error is
enough to remove the target's exact-resonance atom.

No annealed estimate is upgraded to a quenched statement in this module.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedSmallBallBridge

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedMismatchBridge
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedJointLimitSmallBallBridge
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedProbabilityJointLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.FiniteMeasureVanishingErrorSmallBallWeakLimit
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ProbabilityJointLimitDiagonalization
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open ArchonPhysics.ThermalizationTransfer
open Filter MeasureTheory Set

noncomputable section

/-- The model-facing small-ball input at the honest annealed level.  The
finite-volume atomic measures need not satisfy a density estimate, and no
realization-wise inequality is required. -/
structure CanonicalMarkedMismatchAnnealedVanishingErrorSmallBallBound
    (sign : Fin 3 -> InteractionSign) where
  constant : Real
  constant_nonneg : 0 <= constant
  error : Nat -> Real
  error_nonneg : forall n, 0 <= error n
  error_tendsto_zero : Tendsto error atTop (nhds 0)
  bound : forall n : Nat, forall delta : Real,
    0 < delta -> delta <= 1 ->
    ((canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure sign n :
        Measure Real) (absoluteMismatchSublevel delta)).toReal <=
      constant * delta + error n

/-- An annealed linear small-ball bound removes exact resonance from the
deterministic canonical marked mismatch limit. -/
theorem canonicalMarkedMismatchPerSiteLimit_singleton_zero_eq_zero_of_annealedSmallBall
    {sign : Fin 3 -> InteractionSign}
    (smallBall :
      CanonicalMarkedMismatchAnnealedVanishingErrorSmallBallBound sign) :
    (canonicalMarkedMismatchPerSiteLimitFiniteMeasure sign : Measure Real)
        ({0} : Set Real) = 0 := by
  exact
    finiteMeasure_singleton_zero_eq_zero_of_linearSmallBall_with_vanishingError
      (canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure sign)
      (canonicalMarkedMismatchPerSiteLimitFiniteMeasure sign)
      (canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure_tendsto sign)
      smallBall.constant smallBall.constant_nonneg
      smallBall.error smallBall.error_nonneg smallBall.error_tendsto_zero
      smallBall.bound

/-- Equivalent scalar-collision form of the annealed small-ball endpoint. -/
theorem canonicalCollisionPerSiteMeasureLimit_singleton_zero_eq_zero_of_annealedSmallBall
    {sign : Fin 3 -> InteractionSign}
    (smallBall :
      CanonicalMarkedMismatchAnnealedVanishingErrorSmallBallBound sign) :
    (canonicalCollisionPerSiteMeasureLimit
      canonicalIIDMassPhaseEnsemble sign : Measure Real)
        ({0} : Set Real) = 0 := by
  have hzero :=
    canonicalMarkedMismatchPerSiteLimit_singleton_zero_eq_zero_of_annealedSmallBall
      smallBall
  simpa only [canonicalMarkedMismatchPerSiteLimitFiniteMeasure,
    map_canonicalRankFrequencyMarkedPerSiteMeasureLimit_eq_collision] using hzero

end

end ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedSmallBallBridge
