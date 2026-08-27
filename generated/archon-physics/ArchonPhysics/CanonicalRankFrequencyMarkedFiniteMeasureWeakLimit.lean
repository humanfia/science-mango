import ArchonPhysics.CanonicalJointFrequencyFiniteMeasureWeakLimit
import ArchonPhysics.CanonicalRankFrequencyMarkedMeasureWeakLimit
import ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit

/-!
# Canonical rank-frequency marked finite-measure weak limit

The normalized canonical marked measures have a deterministic complete-
sequence weak limit.  This module restores their physical collision-density
mass.  The marked per-site mass is exactly the joint-frequency per-site mass,
so normalized convergence and the existing mass law combine through the
finite-measure normalization theorem.

The resulting unnormalized marked limit retains exactly the deterministic
Euclidean joint-frequency finite measure after forgetting ranks.  Consequently
every signed mismatch pushforward is the corresponding deterministic scalar
collision finite-measure limit.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalJointFrequencyEuclideanBridge
open ArchonPhysics.CanonicalJointFrequencyFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedCompactness
open ArchonPhysics.CanonicalRankFrequencyMarkedMarginalLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.ModalPhaseMismatch
open Filter MeasureTheory Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The deterministic unnormalized marked thermodynamic limit: the limiting
collision density times the graph-lift probability shape. -/
def canonicalRankFrequencyMarkedPerSiteMeasureLimit
    (ensemble : IIDMassPhaseEnsemble Omega) :
    FiniteMeasure (Fin 3 -> RankFrequencyMark) :=
  canonicalJointFrequencyPerSiteMassLimit ensemble •
    (canonicalRankFrequencyMarkedMeasureLimit ensemble).toFiniteMeasure

@[simp]
theorem canonicalRankFrequencyMarkedPerSiteMeasureLimit_mass
    (ensemble : IIDMassPhaseEnsemble Omega) :
    (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble).mass =
      canonicalJointFrequencyPerSiteMassLimit ensemble := by
  unfold canonicalRankFrequencyMarkedPerSiteMeasureLimit FiniteMeasure.mass
  rw [FiniteMeasure.smul_apply]
  simp

@[simp]
theorem canonicalRankFrequencyMarkedPerSiteMeasureLimit_normalize
    (ensemble : IIDMassPhaseEnsemble Omega) :
    (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble).normalize =
      canonicalRankFrequencyMarkedMeasureLimit ensemble := by
  let target := canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble
  have hmass : target.mass ≠ 0 := by
    rw [canonicalRankFrequencyMarkedPerSiteMeasureLimit_mass]
    exact (canonicalJointFrequencyPerSiteMassLimit_pos ensemble).ne'
  have htarget : target ≠ 0 := target.mass_nonzero_iff.mp hmass
  apply ProbabilityMeasure.eq_of_forall_apply_eq
  intro s hs
  rw [target.normalize_eq_of_nonzero htarget]
  dsimp only [target]
  rw [canonicalRankFrequencyMarkedPerSiteMeasureLimit_mass]
  unfold canonicalRankFrequencyMarkedPerSiteMeasureLimit
  rw [FiniteMeasure.smul_apply]
  simp [(canonicalJointFrequencyPerSiteMassLimit_pos ensemble).ne']

/-- The marked and unmarked joint per-site masses have the same almost-sure
thermodynamic limit. -/
theorem canonicalRankFrequencyTriplePerSiteFiniteMeasure_mass_tendsto_ae
    (ensemble : IIDMassPhaseEnsemble Omega) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat =>
          (canonicalRankFrequencyTriplePerSiteFiniteMeasure
            ensemble (n + 1) omega).mass)
        atTop (nhds (canonicalJointFrequencyPerSiteMassLimit ensemble)) := by
  filter_upwards
    [canonicalJointFrequencyPerSiteFiniteMeasure_mass_tendsto_ae ensemble] with
      omega hmass
  apply hmass.congr'
  exact Eventually.of_forall fun n =>
    (canonicalRankFrequencyTriplePerSiteFiniteMeasure_mass_eq_joint
      ensemble (n + 1) omega).symm

/-- Abstract deterministic bridge: convergence of the probability
normalizations and convergence of total masses imply convergence of the
unnormalized marked finite measures. -/
theorem canonicalRankFrequencyTriplePerSiteFiniteMeasure_tendsto_limit_of_normalize_of_mass
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (hnormalize : Tendsto
      (fun n : Nat => canonicalNormalizedRankFrequencyMarkedMeasure
        ensemble (n + 1) omega)
      atTop (nhds (canonicalRankFrequencyMarkedMeasureLimit ensemble)))
    (hmass : Tendsto
      (fun n : Nat =>
        (canonicalRankFrequencyTriplePerSiteFiniteMeasure
          ensemble (n + 1) omega).mass)
      atTop (nhds (canonicalJointFrequencyPerSiteMassLimit ensemble))) :
    Tendsto
      (fun n : Nat => canonicalRankFrequencyTriplePerSiteFiniteMeasure
        ensemble (n + 1) omega)
      atTop
      (nhds (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble)) := by
  apply
    FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
  · rw [canonicalRankFrequencyMarkedPerSiteMeasureLimit_normalize]
    simpa [canonicalNormalizedRankFrequencyMarkedMeasure] using hnormalize
  · rw [canonicalRankFrequencyMarkedPerSiteMeasureLimit_mass]
    exact hmass

/-- Almost surely, the complete unnormalized canonical marked sequence at
marked size `n + 1` (physical spectral volume `n + 3`) converges weakly to the
deterministic mass-scaled graph lift. -/
theorem canonicalRankFrequencyTriplePerSiteFiniteMeasure_tendsto_limit_ae :
    ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
      Tendsto
        (fun n : Nat => canonicalRankFrequencyTriplePerSiteFiniteMeasure
          canonicalIIDMassPhaseEnsemble (n + 1) omega)
        atTop
        (nhds (canonicalRankFrequencyMarkedPerSiteMeasureLimit
          canonicalIIDMassPhaseEnsemble)) := by
  filter_upwards
    [canonicalNormalizedRankFrequencyMarkedMeasure_tendsto_limit_ae,
      canonicalRankFrequencyTriplePerSiteFiniteMeasure_mass_tendsto_ae
        canonicalIIDMassPhaseEnsemble] with omega hnormalize hmass
  exact
    canonicalRankFrequencyTriplePerSiteFiniteMeasure_tendsto_limit_of_normalize_of_mass
      canonicalIIDMassPhaseEnsemble omega hnormalize hmass

/-- Forgetting ranks in the unnormalized marked limit gives exactly the
existing deterministic Euclidean joint-frequency per-site limit. -/
theorem map_canonicalRankFrequencyMarkedPerSiteMeasureLimit_forgetRankEuclidean
    (ensemble : IIDMassPhaseEnsemble Omega) :
    (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble).map
        forgetRankFrequencyTripleEuclidean =
      canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble := by
  apply FiniteMeasure.toMeasure_injective
  unfold canonicalRankFrequencyMarkedPerSiteMeasureLimit
    canonicalEuclideanJointFrequencyPerSiteMeasureLimit
  rw [FiniteMeasure.toMeasure_map, FiniteMeasure.toMeasure_smul,
    FiniteMeasure.toMeasure_smul, Measure.map_smul]
  congr 1
  exact congrArg ProbabilityMeasure.toMeasure
    (map_canonicalRankFrequencyMarkedMeasureLimit_forgetRankEuclidean ensemble)

/-- Every signed mismatch pushforward of the unnormalized marked limit is the
corresponding deterministic scalar collision per-site finite-measure limit. -/
theorem map_canonicalRankFrequencyMarkedPerSiteMeasureLimit_eq_collision
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble).map
        (markedFrequencyMismatch sign) =
      canonicalCollisionPerSiteMeasureLimit ensemble sign := by
  apply FiniteMeasure.toMeasure_injective
  rw [FiniteMeasure.toMeasure_map]
  change Measure.map
      (euclideanFrequencyTripleMismatch sign ∘
        forgetRankFrequencyTripleEuclidean)
      (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble : Measure _) = _
  rw [← Measure.map_map
    (continuous_euclideanFrequencyTripleMismatch sign).measurable
    measurable_forgetRankFrequencyTripleEuclidean]
  have hforget :
      Measure.map forgetRankFrequencyTripleEuclidean
          (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble : Measure _) =
        (canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble :
          Measure _) := by
    simpa only [FiniteMeasure.toMeasure_map] using
      congrArg FiniteMeasure.toMeasure
        (map_canonicalRankFrequencyMarkedPerSiteMeasureLimit_forgetRankEuclidean
          ensemble)
  rw [hforget]
  exact congrArg FiniteMeasure.toMeasure
    (map_canonicalEuclideanJointFrequencyPerSiteMeasureLimit_eq_collision
      ensemble sign)

end

end ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
