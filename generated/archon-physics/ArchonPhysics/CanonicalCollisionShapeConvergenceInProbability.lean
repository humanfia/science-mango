import ArchonPhysics.CanonicalBroadenedMassTwoScaleDiagonalization
import ArchonPhysics.CanonicalRankFrequencyMarkedConvergenceInProbability
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Canonical scalar collision-shape convergence in probability

The complete rank--frequency marked collision measure already converges in
probability, and its signed mismatch pushforward is exactly the scalar
collision law used by the kinetic collision operator.  This file records the
direct scalar endpoint: the probability-normalized finite-volume collision
shapes converge in probability, in their genuine weak topology, to the
deterministic collision shape selected by the thermodynamic limit.

This is a qualitative weak-measure statement.  In particular, it does not
turn weak convergence into a volume-uniform estimate for the increasingly
sharp finite-time resonance kernel; that still requires the separate
small-ball/rate input.
-/

open scoped Topology

namespace ArchonPhysics.CanonicalCollisionShapeConvergenceInProbability

open ArchonPhysics
open ArchonPhysics.CanonicalBroadenedMassTwoScaleDiagonalization
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedCompactness
open ArchonPhysics.CanonicalRankFrequencyMarkedConvergenceInProbability
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open Filter MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- At a simple volume, pushing the normalized rank--frequency marked law
through the signed mismatch is exactly the normalized scalar collision law.
The indices are aligned so that both sides use physical volume `N = n + 3`.
-/
theorem map_canonicalNormalizedRankFrequencyMarkedMeasure_eq_collisionNormalized
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (n : Nat) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 3) omega))) :
    ProbabilityMeasure.map
        (canonicalNormalizedRankFrequencyMarkedMeasure
          ensemble (n + 1) omega)
        (measurable_markedFrequencyMismatch sign).aemeasurable =
      canonicalCollisionNormalizedMeasure ensemble sign n omega := by
  have hmarkedMass :
      (canonicalRankFrequencyTriplePerSiteFiniteMeasure
        ensemble (n + 1) omega).mass ≠ 0 := by
    apply canonicalRankFrequencyTriplePerSiteFiniteMeasure_mass_ne_zero
      ensemble sign (n + 1) omega
    · omega
    · simpa [Nat.add_assoc] using hsimple
  unfold canonicalNormalizedRankFrequencyMarkedMeasure
  rw [probabilityMeasure_map_finiteMeasure_normalize_eq
    (canonicalRankFrequencyTriplePerSiteFiniteMeasure
      ensemble (n + 1) omega)
    (markedFrequencyMismatch sign)
    (measurable_markedFrequencyMismatch sign) hmarkedMass]
  rw [map_canonicalRankFrequencyTriplePerSiteFiniteMeasure_markedMismatch]
  exact canonicalCollisionPerSiteFiniteMeasure_normalize_eq
    ensemble sign n omega hsimple

/-- At every canonical physical volume `N = n + 3`, the normalized scalar
collision shape is almost-everywhere strongly measurable for its weak
topology. -/
theorem aestronglyMeasurable_canonicalCollisionNormalizedMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (n : Nat) :
    AEStronglyMeasurable
      (fun omega => canonicalCollisionNormalizedMeasure
        ensemble sign n omega) ensemble.probability := by
  have hmarked : AEStronglyMeasurable
      (fun omega => canonicalNormalizedRankFrequencyMarkedMeasure
        ensemble (n + 1) omega) ensemble.probability :=
    aestronglyMeasurable_canonicalNormalizedRankFrequencyMarkedMeasure_succ
      ensemble n
  have hmapped : AEStronglyMeasurable
      (fun omega => ProbabilityMeasure.map
        (canonicalNormalizedRankFrequencyMarkedMeasure
          ensemble (n + 1) omega)
        (measurable_markedFrequencyMismatch sign).aemeasurable)
      ensemble.probability :=
    (ProbabilityMeasure.continuous_map
      (continuous_markedFrequencyMismatch sign)).comp_aestronglyMeasurable
        hmarked
  apply hmapped.congr
  filter_upwards
    [canonicalCollisionVolumes_simpleOrderedSpectrum_ae ensemble] with
      omega hsimple
  exact map_canonicalNormalizedRankFrequencyMarkedMeasure_eq_collisionNormalized
    ensemble sign n omega (hsimple n)

/-- The genuine finite-volume scalar collision shapes converge in
probability to the deterministic thermodynamic collision shape.  The chosen
pseudometric induces exactly the weak topology on probability measures over
`Real`. -/
theorem canonicalCollisionNormalizedMeasure_tendstoInMeasure_limit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    let _ : PseudoMetricSpace (ProbabilityMeasure Real) :=
      TopologicalSpace.pseudoMetrizableSpacePseudoMetric _
    TendstoInMeasure ensemble.probability
      (fun n omega => canonicalCollisionNormalizedMeasure
        ensemble sign n omega)
      atTop
      (fun _omega => canonicalCollisionMeasureLimit ensemble sign) := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  let _ : PseudoMetricSpace (ProbabilityMeasure Real) :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric _
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact aestronglyMeasurable_canonicalCollisionNormalizedMeasure
      ensemble sign n
  · exact canonicalCollisionNormalizedMeasure_tendsto_limit_ae ensemble sign

end

end ArchonPhysics.CanonicalCollisionShapeConvergenceInProbability
