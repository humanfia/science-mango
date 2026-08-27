import ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Compactness of canonical rank-frequency marked probability measures

The canonical marked per-site finite measure has the same total mass as its
rank-forgetting joint-frequency pushforward.  Consequently every positive-mass
instance admits genuine probability normalization.  Normalization preserves
the common compact marked box, so Prokhorov compactness extracts a weakly
convergent subsequence from every varying-volume family with positive mass.

This module uses the rank-frequency marked construction directly; it does not
depend on the legacy rank-frequency triple module.
-/

open scoped Topology

namespace ArchonPhysics.CanonicalRankFrequencyMarkedCompactness

open ArchonPhysics
open ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open Filter MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Probability normalization of the canonical marked per-site finite
measure.  All results using its compact support explicitly assume that the
original finite measure has nonzero mass. -/
def canonicalNormalizedRankFrequencyMarkedMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega) :
    ProbabilityMeasure (Fin 3 -> RankFrequencyMark) :=
  (canonicalRankFrequencyTriplePerSiteFiniteMeasure ensemble n omega).normalize

/-- Forgetting normalized ranks preserves the total mass of the marked
per-site finite measure. -/
theorem canonicalRankFrequencyTriplePerSiteFiniteMeasure_mass_eq_joint
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega) :
    (canonicalRankFrequencyTriplePerSiteFiniteMeasure ensemble n omega).mass =
      (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).mass := by
  calc
    (canonicalRankFrequencyTriplePerSiteFiniteMeasure ensemble n omega).mass =
        ((canonicalRankFrequencyTriplePerSiteFiniteMeasure ensemble n omega).map
          forgetRankFrequencyTriple).mass :=
      (finiteMeasure_mass_map_of_measurable
        (canonicalRankFrequencyTriplePerSiteFiniteMeasure ensemble n omega)
        forgetRankFrequencyTriple measurable_forgetRankFrequencyTriple).symm
    _ = (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).mass :=
      congrArg FiniteMeasure.mass
        (map_canonicalRankFrequencyTriplePerSiteFiniteMeasure_forgetRank
          ensemble n omega)

/-- The existing simple-spectrum collision lower bound gives positive total
mass to the canonical marked per-site finite measure. -/
theorem canonicalRankFrequencyTriplePerSiteFiniteMeasure_mass_ne_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (n : Nat) (omega : Omega)
    (hN : 3 <= n + 2)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    (canonicalRankFrequencyTriplePerSiteFiniteMeasure
      ensemble n omega).mass ≠ 0 := by
  rw [canonicalRankFrequencyTriplePerSiteFiniteMeasure_mass_eq_joint]
  exact canonicalJointFrequencyPerSiteFiniteMeasure_mass_ne_zero
    ensemble sign n omega hN hsimple

/-- The normalized marked object is, by construction, a probability
measure. -/
theorem canonicalNormalizedRankFrequencyMarkedMeasure_isProbabilityMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega) :
    IsProbabilityMeasure
      (canonicalNormalizedRankFrequencyMarkedMeasure ensemble n omega :
        Measure (Fin 3 -> RankFrequencyMark)) := by
  infer_instance

/-- Nonzero probability normalization retains the same compact marked box
`([0,1] x [0,sqrt 5])^3`. -/
theorem canonicalNormalizedRankFrequencyMarkedMeasure_compl_uniformSupport_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega)
    (hmass :
      (canonicalRankFrequencyTriplePerSiteFiniteMeasure
        ensemble n omega).mass ≠ 0) :
    (canonicalNormalizedRankFrequencyMarkedMeasure ensemble n omega :
        Measure (Fin 3 -> RankFrequencyMark))
      (collisionRankFrequencyTripleSupportᶜ) = 0 := by
  have hmeasure :
      canonicalRankFrequencyTriplePerSiteFiniteMeasure ensemble n omega ≠ 0 :=
    (canonicalRankFrequencyTriplePerSiteFiniteMeasure
      ensemble n omega).mass_nonzero_iff.mp hmass
  unfold canonicalNormalizedRankFrequencyMarkedMeasure
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hmeasure,
    Measure.smul_apply]
  simp [canonicalRankFrequencyTriplePerSiteFiniteMeasure_compl_uniformSupport_eq_zero
    ensemble n omega]

/-- Any varying-volume family whose marked finite measures have positive
total mass is tight after probability normalization, witnessed by one common
compact box. -/
theorem canonicalNormalizedRankFrequencyMarkedMeasure_range_isTight
    (ensemble : IIDMassPhaseEnsemble Omega)
    (size : Nat -> Nat) (omega : Nat -> Omega)
    (hmass : forall j,
      (canonicalRankFrequencyTriplePerSiteFiniteMeasure
        ensemble (size j) (omega j)).mass ≠ 0) :
    IsTightMeasureSet (Set.range fun j =>
      (canonicalNormalizedRankFrequencyMarkedMeasure
        ensemble (size j) (omega j) :
        Measure (Fin 3 -> RankFrequencyMark))) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro epsilon hepsilon
  refine ⟨collisionRankFrequencyTripleSupport,
    collisionRankFrequencyTripleSupport_isCompact, ?_⟩
  intro mu hmu
  rcases hmu with ⟨j, rfl⟩
  rw [canonicalNormalizedRankFrequencyMarkedMeasure_compl_uniformSupport_eq_zero
    ensemble (size j) (omega j) (hmass j)]
  exact hepsilon.le

/-- Prokhorov compactness for an arbitrary volume/realization sequence:
there is a strictly increasing subsequence of normalized marked probability
measures converging in the weak topology. -/
theorem exists_canonicalNormalizedRankFrequencyMarkedMeasure_weaklyConvergent_subsequence
    (ensemble : IIDMassPhaseEnsemble Omega)
    (size : Nat -> Nat) (omega : Nat -> Omega)
    (hmass : forall j,
      (canonicalRankFrequencyTriplePerSiteFiniteMeasure
        ensemble (size j) (omega j)).mass ≠ 0) :
    exists target : ProbabilityMeasure (Fin 3 -> RankFrequencyMark),
      exists subsequence : Nat -> Nat,
        StrictMono subsequence ∧
          Tendsto
            (fun j => canonicalNormalizedRankFrequencyMarkedMeasure
              ensemble (size (subsequence j)) (omega (subsequence j)))
            atTop (nhds target) := by
  let mu : Nat -> ProbabilityMeasure (Fin 3 -> RankFrequencyMark) :=
    fun j => canonicalNormalizedRankFrequencyMarkedMeasure
      ensemble (size j) (omega j)
  have hset :
      {((nu : ProbabilityMeasure (Fin 3 -> RankFrequencyMark)) :
          Measure (Fin 3 -> RankFrequencyMark)) |
        nu ∈ Set.range mu} =
        Set.range (fun j => (mu j : Measure (Fin 3 -> RankFrequencyMark))) := by
    ext measure
    simp
  have htight : IsTightMeasureSet
      {((nu : ProbabilityMeasure (Fin 3 -> RankFrequencyMark)) :
          Measure (Fin 3 -> RankFrequencyMark)) |
        nu ∈ Set.range mu} := by
    rw [hset]
    exact canonicalNormalizedRankFrequencyMarkedMeasure_range_isTight
      ensemble size omega hmass
  have hcompact : IsCompact (closure (Set.range mu)) :=
    isCompact_closure_of_isTightMeasureSet htight
  have hmem : forall j, mu j ∈ closure (Set.range mu) :=
    fun j => subset_closure (Set.mem_range_self j)
  obtain ⟨target, _htarget, subsequence, hsubsequence, htendsto⟩ :=
    hcompact.tendsto_subseq hmem
  refine ⟨target, subsequence, hsubsequence, ?_⟩
  exact htendsto

/-- Concrete positive-mass corollary: the existing simple-spectrum lower
bound discharges the mass premise along any canonical volume sequence with
at least three sites. -/
theorem exists_canonicalNormalizedRankFrequencyMarkedMeasure_weaklyConvergent_subsequence_of_simple
    (ensemble : IIDMassPhaseEnsemble Omega)
    (size : Nat -> Nat) (omega : Nat -> Omega)
    (sign : Fin 3 -> InteractionSign)
    (hN : forall j, 3 <= size j + 2)
    (hsimple : forall j, SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass
          (N := size j + 2) (omega j)))) :
    exists target : ProbabilityMeasure (Fin 3 -> RankFrequencyMark),
      exists subsequence : Nat -> Nat,
        StrictMono subsequence ∧
          Tendsto
            (fun j => canonicalNormalizedRankFrequencyMarkedMeasure
              ensemble (size (subsequence j)) (omega (subsequence j)))
            atTop (nhds target) := by
  apply exists_canonicalNormalizedRankFrequencyMarkedMeasure_weaklyConvergent_subsequence
    ensemble size omega
  intro j
  exact canonicalRankFrequencyTriplePerSiteFiniteMeasure_mass_ne_zero
    ensemble sign (size j) (omega j) (hN j) (hsimple j)

end

end ArchonPhysics.CanonicalRankFrequencyMarkedCompactness
