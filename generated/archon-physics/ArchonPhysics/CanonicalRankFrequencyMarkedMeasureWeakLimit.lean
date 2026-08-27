import ArchonPhysics.CanonicalRankFrequencyMarkedGraphLimit
import ArchonPhysics.CanonicalScalarIDSUpperBandSaturation

/-!
# Complete canonical rank-frequency marked-measure weak limit

The normalized canonical marked measure at marked size `n + 1` uses the
physical harmonic spectrum of volume `n + 3`.  Almost surely, its complete
sequence converges weakly to the deterministic graph lift of the canonical
joint-frequency limit.  The proof upgrades marked tightness to full
convergence: every cofinal subsequence has a weakly convergent subsubsequence,
and uniform convergence of the empirical scalar IDS identifies every such
cluster point with the same graph lift.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalRankFrequencyMarkedMeasureWeakLimit

open ArchonPhysics
open ArchonPhysics.CanonicalJointFrequencyEuclideanBridge
open ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedCompactness
open ArchonPhysics.CanonicalRankFrequencyMarkedGraphLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMarginalLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalScalarIDSContinuity
open ArchonPhysics.CanonicalScalarIDSBlockApproximation
open ArchonPhysics.CanonicalScalarIDSUpperBandSaturation
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open Filter MeasureTheory Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The deterministic marked thermodynamic limit: attach to each limiting
frequency triple the canonical decreasing spectral rank `1 - F(omega^2)`.
-/
def canonicalRankFrequencyMarkedMeasureLimit
    (ensemble : IIDMassPhaseEnsemble Omega) :
    ProbabilityMeasure (Fin 3 -> RankFrequencyMark) :=
  ProbabilityMeasure.map
    (canonicalJointFrequencyMeasureLimit ensemble)
    (measurable_liftEuclideanRankFrequencyTriple
      continuous_canonicalScalarIDSValue).aemeasurable

/-- Forgetting ranks in the deterministic graph lift recovers exactly the
deterministic Euclidean joint-frequency limit. -/
theorem map_canonicalRankFrequencyMarkedMeasureLimit_forgetRankEuclidean
    (ensemble : IIDMassPhaseEnsemble Omega) :
    ProbabilityMeasure.map
        (canonicalRankFrequencyMarkedMeasureLimit ensemble)
        measurable_forgetRankFrequencyTripleEuclidean.aemeasurable =
      canonicalJointFrequencyMeasureLimit ensemble := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [canonicalRankFrequencyMarkedMeasureLimit,
    ProbabilityMeasure.toMeasure_map]
  rw [AEMeasurable.map_map_of_aemeasurable
    measurable_forgetRankFrequencyTripleEuclidean.aemeasurable
    (measurable_liftEuclideanRankFrequencyTriple
      continuous_canonicalScalarIDSValue).aemeasurable]
  have hcomp : forgetRankFrequencyTripleEuclidean ∘
      liftEuclideanRankFrequencyTriple canonicalScalarIDSValue = id := by
    funext frequencies
    change plainFrequencyTripleToEuclidean
      (euclideanFrequencyTripleToPlain frequencies) = frequencies
    exact (PiLp.homeomorph 2 (fun _r : Fin 3 => Real)).symm_apply_apply
      frequencies
  rw [hcomp, Measure.map_id]

/-- The deterministic marked limit is carried by the scalar-IDS graph. -/
theorem canonicalRankFrequencyMarkedMeasureLimit_compl_graph_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega) :
    (canonicalRankFrequencyMarkedMeasureLimit ensemble :
      Measure (Fin 3 -> RankFrequencyMark))
        (rankFrequencyTripleGraph canonicalScalarIDSValue)ᶜ = 0 := by
  simp only [canonicalRankFrequencyMarkedMeasureLimit,
    ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply
    (measurable_liftEuclideanRankFrequencyTriple
      continuous_canonicalScalarIDSValue)
    (isClosed_rankFrequencyTripleGraph
      continuous_canonicalScalarIDSValue).measurableSet.compl]
  simp [rankFrequencyTripleGraph, liftEuclideanRankFrequencyTriple,
    liftRankFrequencyTriple]

/-- Uniform convergence remains uniform after restricting the index filter
along any cofinal map. -/
theorem tendstoUniformly_comp_index
    {I J A B : Type*} [UniformSpace B]
    {F : I -> A -> B} {f : A -> B}
    {p : Filter I} {q : Filter J} (hF : TendstoUniformly F f p)
    {index : J -> I} (hindex : Tendsto index q p) :
    TendstoUniformly (fun j => F (index j)) f q := by
  intro entourage hentourage
  exact hindex.eventually (hF entourage hentourage)

/-- The empirical scalar IDS used by the graph theorem is exactly the
canonical normalized harmonic threshold count. -/
theorem harmonicEmpiricalScalarIDS_canonical_eq
    (N : Nat) [NeZero N] (omega : RandomEnsemble.SampleSpace) :
    harmonicEmpiricalScalarIDS
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := N) omega) =
      (fun E => canonicalNormalizedHarmonicThresholdCount N E omega) := by
  funext E
  exact (canonicalNormalizedHarmonicThresholdCount_eq N E omega).symm

/-- Deterministic complete-sequence upgrade.  Tightness, the full frequency
marginal limit, simple spectra, and a uniform scalar empirical IDS force the
entire normalized marked sequence to converge to the graph lift. -/
theorem canonicalNormalizedRankFrequencyMarkedMeasure_tendsto_limit_of_uniform
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (hsimple : forall n : Nat, SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 3) omega)))
    (hjoint : Tendsto
      (fun n : Nat => canonicalEuclideanNormalizedJointFrequencyMeasure
        ensemble (n + 1) omega)
      atTop (nhds (canonicalJointFrequencyMeasureLimit ensemble)))
    (huniform : TendstoUniformly
      (fun n : Nat => harmonicEmpiricalScalarIDS
        (ensemble.restrictPositiveMass (N := n + 3) omega))
      canonicalScalarIDSValue atTop) :
    Tendsto
      (fun n : Nat => canonicalNormalizedRankFrequencyMarkedMeasure
        ensemble (n + 1) omega)
      atTop (nhds (canonicalRankFrequencyMarkedMeasureLimit ensemble)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro index hindex
  obtain ⟨target, subsequence, hsubsequence, hweak⟩ :=
    exists_canonicalNormalizedRankFrequencyMarkedMeasure_weaklyConvergent_subsequence_of_simple
      ensemble (fun j => index j + 1) (fun _j => omega)
      (fun _ => InteractionSign.plus)
      (fun _j => by omega)
      (fun j => by simpa [Nat.add_assoc] using hsimple (index j))
  have hsubindex : Tendsto (fun j => index (subsequence j)) atTop atTop :=
    hindex.comp hsubsequence.tendsto_atTop
  have hweak' : Tendsto
      (fun j => canonicalNormalizedRankFrequencyMarkedMeasure
        ensemble (index (subsequence j) + 1) omega)
      atTop (nhds target) := by
    simpa using hweak
  have huniform' : TendstoUniformly
      (fun j => harmonicEmpiricalScalarIDS
        (ensemble.restrictPositiveMass
          (N := index (subsequence j) + 3) omega))
      canonicalScalarIDSValue atTop :=
    tendstoUniformly_comp_index huniform hsubindex
  have hmarginal : ProbabilityMeasure.map target
        measurable_forgetRankFrequencyTripleEuclidean.aemeasurable =
      canonicalJointFrequencyMeasureLimit ensemble :=
    map_marked_limit_eq_canonicalJointFrequencyMeasureLimit_along
      ensemble omega target (fun j => index (subsequence j)) hsubindex
      hsimple hweak' hjoint
  have htarget : target = canonicalRankFrequencyMarkedMeasureLimit ensemble := by
    unfold canonicalRankFrequencyMarkedMeasureLimit
    apply canonicalMarkedWeakLimit_eq_lift_of_uniformEmpiricalIDS
      ensemble (fun j => index (subsequence j) + 1) (fun _j => omega)
      (fun _ => InteractionSign.plus) target
      (canonicalJointFrequencyMeasureLimit ensemble)
      canonicalScalarIDSValue continuous_canonicalScalarIDSValue
      (fun _j => by omega)
      (fun j => by
        simpa [Nat.add_assoc] using hsimple (index (subsequence j)))
      (by simpa [Nat.add_assoc] using huniform')
      (by simpa using hweak') hmarginal
  refine ⟨subsequence, ?_⟩
  rw [htarget] at hweak'
  exact hweak'

/-- Almost surely, the complete canonical normalized rank-frequency marked
measure sequence converges weakly to the deterministic graph lift.  Marked
size `n + 1` corresponds to physical spectral volume `n + 3`. -/
theorem canonicalNormalizedRankFrequencyMarkedMeasure_tendsto_limit_ae :
    ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
      Tendsto
        (fun n : Nat => canonicalNormalizedRankFrequencyMarkedMeasure
          canonicalIIDMassPhaseEnsemble (n + 1) omega)
        atTop
        (nhds (canonicalRankFrequencyMarkedMeasureLimit
          canonicalIIDMassPhaseEnsemble)) := by
  filter_upwards
    [canonicalJointFrequencyVolumes_simpleOrderedSpectrum_ae
      canonicalIIDMassPhaseEnsemble,
      canonicalEuclideanNormalizedJointFrequencyMeasure_tendsto_limit_ae
        canonicalIIDMassPhaseEnsemble,
      canonicalNormalizedHarmonicThresholdCount_tendstoUniformly_ae]
      with omega hsimple hjoint hcount
  apply canonicalNormalizedRankFrequencyMarkedMeasure_tendsto_limit_of_uniform
    canonicalIIDMassPhaseEnsemble omega hsimple hjoint
  have hshift := tendstoUniformly_comp_index hcount
    (tendsto_add_atTop_nat 2)
  rw [show (fun n : Nat => harmonicEmpiricalScalarIDS
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
        (N := n + 3) omega)) =
      (fun n E => canonicalNormalizedHarmonicThresholdCount
        (n + 3) E omega) from by
      funext n
      exact harmonicEmpiricalScalarIDS_canonical_eq (n + 3) omega]
  simpa [Nat.add_assoc] using hshift

end

end ArchonPhysics.CanonicalRankFrequencyMarkedMeasureWeakLimit
