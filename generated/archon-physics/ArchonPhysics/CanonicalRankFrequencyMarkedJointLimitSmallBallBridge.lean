import ArchonPhysics.CanonicalRankFrequencyMarkedProbabilityJointLimit
import ArchonPhysics.FiniteMeasureVanishingErrorSmallBallWeakLimit

/-!
# Canonical marked joint limits from a uniform mismatch small-ball input

This module isolates the remaining model-side input needed to remove the
exact-resonance atom from the canonical marked thermodynamic limit.  The
input is a linear mismatch small-ball estimate, uniform in the finite-volume
index on one probability-one event, up to a nonnegative error tending to
zero.

The analytic bridge is independent of the canonical model: weak convergence
of finite measures, continuity of the mismatch map, and the vanishing-error
small-ball theorem imply that the mismatch pushforward of the weak limit has
no atom at zero.  The canonical specialization combines this conclusion with
the previously constructed probability joint-limit cutoff.
-/

open scoped Topology ENNReal BoundedContinuousFunction

namespace ArchonPhysics.CanonicalRankFrequencyMarkedJointLimitSmallBallBridge

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedCompactness
open ArchonPhysics.CanonicalRankFrequencyMarkedConvergenceInProbability
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedProbabilityJointLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.FiniteMeasureVanishingErrorSmallBallWeakLimit
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ProbabilityJointLimitDiagonalization
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open ArchonPhysics.ThermalizationTransfer
open Filter MeasureTheory Set Topology

noncomputable section

/-! ## Abstract marked-measure bridge -/

/-- A vanishing-error linear small-ball estimate for the mismatch pushforwards
of weakly convergent finite measures removes the zero atom from the mismatch
pushforward of the limit. -/
theorem finiteMeasure_map_singleton_zero_eq_zero_of_linearSmallBall_with_vanishingError
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X]
    (source : Nat -> FiniteMeasure X) (target : FiniteMeasure X)
    (mismatch : X -> Real) (hmismatch : Continuous mismatch)
    (hlimit : Tendsto source atTop (nhds target))
    (C : Real) (hC : 0 <= C)
    (error : Nat -> Real) (herror_nonneg : forall n, 0 <= error n)
    (herror : Tendsto error atTop (nhds 0))
    (hbound : forall n : Nat, forall delta : Real,
      0 < delta -> delta <= 1 ->
      ((((source n).map mismatch : FiniteMeasure Real) : Measure Real)
          (absoluteMismatchSublevel delta)).toReal <=
        C * delta + error n) :
    ((((target.map mismatch : FiniteMeasure Real) : Measure Real)
      ({0} : Set Real))) = 0 := by
  apply
    finiteMeasure_singleton_zero_eq_zero_of_linearSmallBall_with_vanishingError
      (fun n => (source n).map mismatch) (target.map mismatch)
      (FiniteMeasure.tendsto_map_of_tendsto_of_continuous
        source target hlimit hmismatch)
      C hC error herror_nonneg herror hbound

/-! ## The sole canonical model-side input -/

/-- The finite-volume input still required from the random-mass spectral
model.  On one full-probability event, every volume satisfies the same linear
small-ball constant, up to a nonnegative volume error tending to zero. -/
structure CanonicalMarkedMismatchVanishingErrorSmallBallBound
    (sign : Fin 3 -> InteractionSign) where
  constant : Real
  constant_nonneg : 0 <= constant
  error : Nat -> Real
  error_nonneg : forall n, 0 <= error n
  error_tendsto_zero : Tendsto error atTop (nhds 0)
  bound_ae :
    ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
      forall n : Nat, forall delta : Real,
        0 < delta -> delta <= 1 ->
        ((((canonicalMarkedPerSiteSequence n omega).map
            (markedFrequencyMismatch sign) : FiniteMeasure Real) :
              Measure Real) (absoluteMismatchSublevel delta)).toReal <=
          constant * delta + error n

/-- The uniform canonical small-ball input removes the zero atom from the
mismatch pushforward of the deterministic marked per-site weak limit. -/
theorem canonicalMarkedPerSiteMeasureLimit_mismatch_singleton_zero_eq_zero
    {sign : Fin 3 -> InteractionSign}
    (smallBall : CanonicalMarkedMismatchVanishingErrorSmallBallBound sign) :
    ((((canonicalRankFrequencyMarkedPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble).map
          (markedFrequencyMismatch sign) : FiniteMeasure Real) : Measure Real)
      ({0} : Set Real)) = 0 := by
  have hboth :
      ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
        Tendsto (fun n => canonicalMarkedPerSiteSequence n omega) atTop
          (nhds (canonicalRankFrequencyMarkedPerSiteMeasureLimit
            canonicalIIDMassPhaseEnsemble)) ∧
        (forall n : Nat, forall delta : Real,
          0 < delta -> delta <= 1 ->
          ((((canonicalMarkedPerSiteSequence n omega).map
              (markedFrequencyMismatch sign) : FiniteMeasure Real) :
                Measure Real) (absoluteMismatchSublevel delta)).toReal <=
            smallBall.constant * delta + smallBall.error n) := by
    filter_upwards
      [canonicalRankFrequencyTriplePerSiteFiniteMeasure_tendsto_limit_ae,
        smallBall.bound_ae] with omega hlimit hbound
    exact ⟨by simpa only [canonicalMarkedPerSiteSequence] using hlimit, hbound⟩
  obtain ⟨omega, hlimit, hbound⟩ := hboth.exists
  exact
    finiteMeasure_map_singleton_zero_eq_zero_of_linearSmallBall_with_vanishingError
      (fun n => canonicalMarkedPerSiteSequence n omega)
      (canonicalRankFrequencyMarkedPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble)
      (markedFrequencyMismatch sign)
      (continuous_markedFrequencyMismatch sign)
      hlimit smallBall.constant smallBall.constant_nonneg
      smallBall.error smallBall.error_nonneg smallBall.error_tendsto_zero
      hbound

/-- Equivalent scalar-collision form: the deterministic canonical collision
per-site measure has no atom at zero. -/
theorem canonicalCollisionPerSiteMeasureLimit_singleton_zero_eq_zero
    {sign : Fin 3 -> InteractionSign}
    (smallBall : CanonicalMarkedMismatchVanishingErrorSmallBallBound sign) :
    (canonicalCollisionPerSiteMeasureLimit
      canonicalIIDMassPhaseEnsemble sign : Measure Real)
        ({0} : Set Real) = 0 := by
  have hzero :=
    canonicalMarkedPerSiteMeasureLimit_mismatch_singleton_zero_eq_zero
      smallBall
  rw [map_canonicalRankFrequencyMarkedPerSiteMeasureLimit_eq_collision] at hzero
  exact hzero

/-! ## Combination with every admissible probability joint limit -/

/-- Under the sole uniform spectral small-ball input, every canonical
admissible joint limit simultaneously has the qualitative probability
control from diagonalization and a deterministic marked mismatch limit with
no atom at exact resonance. -/
theorem canonicalMarked_jointLimit_probability_control_and_mismatch_zeroAtom
    {sign : Fin 3 -> InteractionSign}
    (smallBall : CanonicalMarkedMismatchVanishingErrorSmallBallBound sign)
    (amplification : Real -> Real)
    (hamplification : forall g, 0 <= amplification g)
    (s : AdmissibleJointLimit
      (canonicalMarkedProbabilityJointSizeCutoff amplification)) :
    let _ : PseudoMetricSpace
        (FiniteMeasure (Fin 3 -> RankFrequencyMark)) :=
      canonicalRankFrequencyMarkedFiniteMeasureWeakPseudoMetricSpace
    ((∀ᶠ j in atTop,
      RandomEnsemble.canonicalLaw.real
        (probabilityDiagonalBadEvent canonicalMarkedPerSiteSequence
          canonicalMarkedPerSiteTarget amplification
          (s.systemSize j) (s.coupling j)) <= s.coupling j) ∧
      Tendsto
        (fun j => RandomEnsemble.canonicalLaw.real
          (probabilityDiagonalBadEvent canonicalMarkedPerSiteSequence
            canonicalMarkedPerSiteTarget amplification
            (s.systemSize j) (s.coupling j)))
        atTop (nhds 0) ∧
      forall j,
        probabilityDiagonalThreshold amplification (s.coupling j) *
            amplification (s.coupling j) <= s.coupling j) ∧
      ((((canonicalRankFrequencyMarkedPerSiteMeasureLimit
          canonicalIIDMassPhaseEnsemble).map
            (markedFrequencyMismatch sign) : FiniteMeasure Real) :
              Measure Real) ({0} : Set Real)) = 0 := by
  let _ : PseudoMetricSpace
      (FiniteMeasure (Fin 3 -> RankFrequencyMark)) :=
    canonicalRankFrequencyMarkedFiniteMeasureWeakPseudoMetricSpace
  exact ⟨canonicalMarked_jointLimit_probability_control
      amplification hamplification s,
    canonicalMarkedPerSiteMeasureLimit_mismatch_singleton_zero_eq_zero
      smallBall⟩

end

end ArchonPhysics.CanonicalRankFrequencyMarkedJointLimitSmallBallBridge
