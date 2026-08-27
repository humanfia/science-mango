import ArchonPhysics.CanonicalRankFrequencyMarkedCompactness
import ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit

/-!
# Frequency-marginal identification for canonical rank-frequency marked limits

The compact marked family retains normalized ordered ranks, while the existing
thermodynamic theorem identifies only the three harmonic frequencies.  This
module proves that forgetting ranks and transporting the remaining frequency
triple to Euclidean coordinates recovers the existing joint-frequency measure
exactly at every finite volume.

Consequently every weakly convergent marked subsequence has the deterministic
joint-frequency limit as its frequency marginal.  Almost surely such a marked
subsequence exists by the common compact support.  This does not yet assert
uniqueness of the full rank-frequency marked limit.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalRankFrequencyMarkedMarginalLimit

open ArchonPhysics
open ArchonPhysics.CanonicalJointFrequencyEuclideanBridge
open ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit
open ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedCompactness
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open Filter MeasureTheory Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Forget normalized ranks and transport the remaining frequency triple to
the Euclidean space used by the deterministic joint weak limit. -/
def forgetRankFrequencyTripleEuclidean
    (marks : Fin 3 -> RankFrequencyMark) :
    EuclideanSpace Real (Fin 3) :=
  plainFrequencyTripleToEuclidean (forgetRankFrequencyTriple marks)

theorem continuous_forgetRankFrequencyTripleEuclidean :
    Continuous forgetRankFrequencyTripleEuclidean := by
  unfold forgetRankFrequencyTripleEuclidean
  exact continuous_plainFrequencyTripleToEuclidean.comp
    continuous_forgetRankFrequencyTriple

theorem measurable_forgetRankFrequencyTripleEuclidean :
    Measurable forgetRankFrequencyTripleEuclidean :=
  continuous_forgetRankFrequencyTripleEuclidean.measurable

/-- At every finite volume, the Euclidean frequency marginal of the marked
per-site finite measure is exactly the existing joint-frequency finite
measure. -/
theorem map_canonicalRankFrequencyTriplePerSiteFiniteMeasure_forgetRankEuclidean
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega) :
    (canonicalRankFrequencyTriplePerSiteFiniteMeasure
        ensemble n omega).map forgetRankFrequencyTripleEuclidean =
      canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
        ensemble n omega := by
  apply FiniteMeasure.toMeasure_injective
  unfold canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
  rw [FiniteMeasure.toMeasure_map, FiniteMeasure.toMeasure_map]
  change Measure.map
      (plainFrequencyTripleToEuclidean ∘ forgetRankFrequencyTriple)
      (canonicalRankFrequencyTriplePerSiteFiniteMeasure
        ensemble n omega : Measure _) =
    Measure.map plainFrequencyTripleToEuclidean
      (canonicalJointFrequencyPerSiteFiniteMeasure
        ensemble n omega : Measure _)
  rw [← Measure.map_map measurable_plainFrequencyTripleToEuclidean
    measurable_forgetRankFrequencyTriple]
  rw [← FiniteMeasure.toMeasure_map]
  rw [map_canonicalRankFrequencyTriplePerSiteFiniteMeasure_forgetRank]

/-- At every simple nondegenerate volume, probability normalization commutes
with forgetting ranks, and the exact marginal is the normalized Euclidean
joint-frequency measure. -/
theorem map_canonicalNormalizedRankFrequencyMarkedMeasure_forgetRankEuclidean
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (n : Nat) (omega : Omega) (hN : 3 <= n + 2)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    ProbabilityMeasure.map
        (canonicalNormalizedRankFrequencyMarkedMeasure ensemble n omega)
        measurable_forgetRankFrequencyTripleEuclidean.aemeasurable =
      canonicalEuclideanNormalizedJointFrequencyMeasure
        ensemble n omega := by
  have hjointMass :
      (canonicalJointFrequencyPerSiteFiniteMeasure
        ensemble n omega).mass ≠ 0 :=
    canonicalJointFrequencyPerSiteFiniteMeasure_mass_ne_zero
      ensemble sign n omega hN hsimple
  have hmarkedMass :
      (canonicalRankFrequencyTriplePerSiteFiniteMeasure
        ensemble n omega).mass ≠ 0 :=
    canonicalRankFrequencyTriplePerSiteFiniteMeasure_mass_ne_zero
      ensemble sign n omega hN hsimple
  unfold canonicalNormalizedRankFrequencyMarkedMeasure
  rw [probabilityMeasure_map_finiteMeasure_normalize_eq
    (canonicalRankFrequencyTriplePerSiteFiniteMeasure ensemble n omega)
    forgetRankFrequencyTripleEuclidean
    measurable_forgetRankFrequencyTripleEuclidean hmarkedMass]
  rw [map_canonicalRankFrequencyTriplePerSiteFiniteMeasure_forgetRankEuclidean]
  exact
    (canonicalEuclideanNormalizedJointFrequencyMeasure_eq_finite_normalize
      ensemble n omega hjointMass).symm

/-- Any marked weak limit along a cofinal volume subsequence has the already
identified deterministic joint-frequency limit as its frequency marginal. -/
theorem map_marked_limit_eq_canonicalJointFrequencyMeasureLimit_along
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (target : ProbabilityMeasure (Fin 3 -> RankFrequencyMark))
    (index : Nat -> Nat) (hindex : Tendsto index atTop atTop)
    (hsimple : forall n : Nat, SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 3) omega)))
    (hmarked : Tendsto
      (fun j : Nat => canonicalNormalizedRankFrequencyMarkedMeasure
        ensemble (index j + 1) omega)
      atTop (nhds target))
    (hjoint : Tendsto
      (fun n : Nat => canonicalEuclideanNormalizedJointFrequencyMeasure
        ensemble (n + 1) omega)
      atTop (nhds (canonicalJointFrequencyMeasureLimit ensemble))) :
    ProbabilityMeasure.map target
        measurable_forgetRankFrequencyTripleEuclidean.aemeasurable =
      canonicalJointFrequencyMeasureLimit ensemble := by
  have hmapped :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun j : Nat => canonicalNormalizedRankFrequencyMarkedMeasure
        ensemble (index j + 1) omega)
      target hmarked continuous_forgetRankFrequencyTripleEuclidean
  have hmappedJoint : Tendsto
      (fun j : Nat => ProbabilityMeasure.map
        (canonicalNormalizedRankFrequencyMarkedMeasure
          ensemble (index j + 1) omega)
        measurable_forgetRankFrequencyTripleEuclidean.aemeasurable)
      atTop (nhds (canonicalJointFrequencyMeasureLimit ensemble)) := by
    apply (hjoint.comp hindex).congr'
    exact Eventually.of_forall fun j =>
      (map_canonicalNormalizedRankFrequencyMarkedMeasure_forgetRankEuclidean
        ensemble (fun _ => InteractionSign.plus)
        (index j + 1) omega (by omega)
        (by simpa [Nat.add_assoc] using hsimple (index j))).symm
  exact tendsto_nhds_unique hmapped hmappedJoint

/-- Almost surely, the normalized marked measures admit a weakly convergent
subsequence whose frequency marginal is exactly the deterministic canonical
joint-frequency limit. -/
theorem exists_marked_subsequence_limit_with_jointFrequencyMarginal_ae
    (ensemble : IIDMassPhaseEnsemble Omega) :
    ∀ᵐ omega ∂ensemble.probability,
      ∃ target : ProbabilityMeasure (Fin 3 -> RankFrequencyMark),
        ∃ subsequence : Nat -> Nat,
          StrictMono subsequence ∧
          Tendsto
            (fun j : Nat => canonicalNormalizedRankFrequencyMarkedMeasure
              ensemble (subsequence j + 1) omega)
            atTop (nhds target) ∧
          ProbabilityMeasure.map target
              measurable_forgetRankFrequencyTripleEuclidean.aemeasurable =
            canonicalJointFrequencyMeasureLimit ensemble := by
  filter_upwards
    [canonicalJointFrequencyVolumes_simpleOrderedSpectrum_ae ensemble,
      canonicalEuclideanNormalizedJointFrequencyMeasure_tendsto_limit_ae
        ensemble] with omega hsimple hjoint
  obtain ⟨target, subsequence, hmono, htendsto⟩ :=
    exists_canonicalNormalizedRankFrequencyMarkedMeasure_weaklyConvergent_subsequence_of_simple
      ensemble (fun n => n + 1) (fun _n => omega)
      (fun _ => InteractionSign.plus)
      (fun _n => by omega)
      (fun n => by simpa [Nat.add_assoc] using hsimple n)
  refine ⟨target, subsequence, hmono, ?_, ?_⟩
  · simpa using htendsto
  · exact
      map_marked_limit_eq_canonicalJointFrequencyMeasureLimit_along
        ensemble omega target subsequence hmono.tendsto_atTop hsimple
        (by simpa using htendsto) hjoint

end

end ArchonPhysics.CanonicalRankFrequencyMarkedMarginalLimit
