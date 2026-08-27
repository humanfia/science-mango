import ArchonPhysics.CanonicalRankFrequencyMarkedMarginalLimit
import ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit
import ArchonPhysics.BroadenedResonanceMeasure
import ArchonPhysics.ResonantThreeWaveMeasure

/-!
# Resonance observables of canonical rank-frequency marked limits

The rank marks in a marked cluster point need not have a unique limiting
law.  Its already identified frequency marginal is nevertheless enough to
determine every observable which factors through a signed frequency
mismatch.  This module records that transport to the existing deterministic
scalar collision-measure limit.

The finite-time and broadened statements below are exact identities at one
fixed positive observation time.  In particular, no large-time limit and no
exact-resonance support property of a marked cluster point is asserted.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit

open ArchonPhysics
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalJointFrequencyEuclideanBridge
open ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedCompactness
open ArchonPhysics.CanonicalRankFrequencyMarkedMarginalLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.ResonantThreeWaveMeasure
open ArchonPhysics.UniformCollisionDensityTransfer
open Filter MeasureTheory Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The signed scalar mismatch retained by a marked frequency triple.  Rank
coordinates are forgotten before applying the Euclidean mismatch map. -/
def markedFrequencyMismatch
    (sign : Fin 3 -> InteractionSign)
    (marks : Fin 3 -> RankFrequencyMark) : Real :=
  euclideanFrequencyTripleMismatch sign
    (forgetRankFrequencyTripleEuclidean marks)

theorem continuous_markedFrequencyMismatch
    (sign : Fin 3 -> InteractionSign) :
    Continuous (markedFrequencyMismatch sign) := by
  unfold markedFrequencyMismatch
  exact (continuous_euclideanFrequencyTripleMismatch sign).comp
    continuous_forgetRankFrequencyTripleEuclidean

theorem measurable_markedFrequencyMismatch
    (sign : Fin 3 -> InteractionSign) :
    Measurable (markedFrequencyMismatch sign) :=
  (continuous_markedFrequencyMismatch sign).measurable

/-- Any marked probability measure whose frequency marginal is the canonical
joint limit has, for every sign pattern, the already constructed canonical
scalar collision limit as its mismatch marginal. -/
theorem map_marked_limit_eq_canonicalCollisionMeasureLimit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (target : ProbabilityMeasure (Fin 3 -> RankFrequencyMark))
    (hfrequency :
      ProbabilityMeasure.map target
          measurable_forgetRankFrequencyTripleEuclidean.aemeasurable =
        canonicalJointFrequencyMeasureLimit ensemble)
    (sign : Fin 3 -> InteractionSign) :
    ProbabilityMeasure.map target
        (measurable_markedFrequencyMismatch sign).aemeasurable =
      canonicalCollisionMeasureLimit ensemble sign := by
  have hfrequencyMeasure :
      Measure.map forgetRankFrequencyTripleEuclidean
          (target : Measure (Fin 3 -> RankFrequencyMark)) =
        (canonicalJointFrequencyMeasureLimit ensemble :
          Measure (EuclideanSpace Real (Fin 3))) := by
    exact congrArg ProbabilityMeasure.toMeasure hfrequency
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  change Measure.map
      (euclideanFrequencyTripleMismatch sign ∘
        forgetRankFrequencyTripleEuclidean)
      (target : Measure (Fin 3 -> RankFrequencyMark)) = _
  rw [← Measure.map_map
    (measurable_euclideanFrequencyTripleMismatch sign)
    measurable_forgetRankFrequencyTripleEuclidean]
  rw [hfrequencyMeasure]
  exact congrArg ProbabilityMeasure.toMeasure
    (map_canonicalJointFrequencyMeasureLimit_eq_canonicalCollisionMeasureLimit
      ensemble sign)

/-- Direct cluster-point form: weak convergence of marked measures and the
identified joint-frequency thermodynamic limit force every signed mismatch
pushforward of the cluster point to be deterministic. -/
theorem map_marked_clusterPoint_eq_canonicalCollisionMeasureLimit_along
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
      atTop (nhds (canonicalJointFrequencyMeasureLimit ensemble)))
    (sign : Fin 3 -> InteractionSign) :
    ProbabilityMeasure.map target
        (measurable_markedFrequencyMismatch sign).aemeasurable =
      canonicalCollisionMeasureLimit ensemble sign := by
  apply map_marked_limit_eq_canonicalCollisionMeasureLimit
    ensemble target _ sign
  exact map_marked_limit_eq_canonicalJointFrequencyMeasureLimit_along
    ensemble omega target index hindex hsimple hmarked hjoint

/-- Every continuous weak observable depending only on the marked frequency
mismatch is exactly its scalar collision-limit integral. -/
theorem integral_markedFrequencyMismatch_eq_canonicalCollisionMeasureLimit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (target : ProbabilityMeasure (Fin 3 -> RankFrequencyMark))
    (hfrequency :
      ProbabilityMeasure.map target
          measurable_forgetRankFrequencyTripleEuclidean.aemeasurable =
        canonicalJointFrequencyMeasureLimit ensemble)
    (sign : Fin 3 -> InteractionSign)
    (observable : Real -> E) (hobservable : Continuous observable) :
    (∫ marks, observable (markedFrequencyMismatch sign marks)
      ∂(target : Measure (Fin 3 -> RankFrequencyMark))) =
      ∫ mismatch, observable mismatch
        ∂(canonicalCollisionMeasureLimit ensemble sign : Measure Real) := by
  calc
    (∫ marks, observable (markedFrequencyMismatch sign marks)
        ∂(target : Measure (Fin 3 -> RankFrequencyMark))) =
        ∫ mismatch, observable mismatch
          ∂(ProbabilityMeasure.map target
            (measurable_markedFrequencyMismatch sign).aemeasurable :
              ProbabilityMeasure Real) := by
      change
        (∫ marks, observable (markedFrequencyMismatch sign marks)
          ∂(target : Measure (Fin 3 -> RankFrequencyMark))) =
          ∫ mismatch, observable mismatch
            ∂Measure.map (markedFrequencyMismatch sign)
              (target : Measure (Fin 3 -> RankFrequencyMark))
      rw [integral_map
        (measurable_markedFrequencyMismatch sign).aemeasurable
        hobservable.aestronglyMeasurable]
    _ = ∫ mismatch, observable mismatch
          ∂(canonicalCollisionMeasureLimit ensemble sign : Measure Real) := by
      rw [map_marked_limit_eq_canonicalCollisionMeasureLimit
        ensemble target hfrequency sign]

/-- At every fixed positive time, the normalized finite-time resonance
profile sees exactly the deterministic scalar collision limit. -/
theorem integral_normalizedFiniteTimeResonanceKernel_marked_eq_limit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (target : ProbabilityMeasure (Fin 3 -> RankFrequencyMark))
    (hfrequency :
      ProbabilityMeasure.map target
          measurable_forgetRankFrequencyTripleEuclidean.aemeasurable =
        canonicalJointFrequencyMeasureLimit ensemble)
    (sign : Fin 3 -> InteractionSign)
    {T : Real} (hT : 0 < T) :
    (∫ marks, normalizedFiniteTimeResonanceKernel
        (markedFrequencyMismatch sign marks) T
      ∂(target : Measure (Fin 3 -> RankFrequencyMark))) =
      ∫ mismatch, normalizedFiniteTimeResonanceKernel mismatch T
        ∂(canonicalCollisionMeasureLimit ensemble sign : Measure Real) := by
  exact integral_markedFrequencyMismatch_eq_canonicalCollisionMeasureLimit
    ensemble target hfrequency sign
    (fun mismatch => normalizedFiniteTimeResonanceKernel mismatch T)
    (continuous_normalizedFiniteTimeResonanceKernel hT)

/-- The fixed-time broadened finite measure built on a marked limit. -/
def markedBroadenedResonanceMeasure
    (target : ProbabilityMeasure (Fin 3 -> RankFrequencyMark))
    (sign : Fin 3 -> InteractionSign)
    (T : Real) (hT : 0 < T) :
    FiniteMeasure (Fin 3 -> RankFrequencyMark) :=
  broadenedResonanceMeasure target.toFiniteMeasure
    (markedFrequencyMismatch sign)
    (measurable_markedFrequencyMismatch sign) T hT

/-- The corresponding deterministic broadened scalar collision-limit
measure, using the identity scalar mismatch. -/
def canonicalBroadenedCollisionMeasureLimit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (T : Real) (hT : 0 < T) : FiniteMeasure Real :=
  broadenedResonanceMeasure
    (canonicalCollisionMeasureLimit ensemble sign).toFiniteMeasure
    id measurable_id T hT

/-- Every continuous mismatch-only test of the marked broadened measure is
the same test of the deterministic broadened scalar collision limit. -/
theorem integral_markedBroadenedResonanceMeasure_eq_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (target : ProbabilityMeasure (Fin 3 -> RankFrequencyMark))
    (hfrequency :
      ProbabilityMeasure.map target
          measurable_forgetRankFrequencyTripleEuclidean.aemeasurable =
        canonicalJointFrequencyMeasureLimit ensemble)
    (sign : Fin 3 -> InteractionSign)
    {T : Real} (hT : 0 < T)
    (test : Real -> E) (htest : Continuous test) :
    (∫ marks, test (markedFrequencyMismatch sign marks)
      ∂(markedBroadenedResonanceMeasure target sign T hT :
        Measure (Fin 3 -> RankFrequencyMark))) =
      ∫ mismatch, test mismatch
        ∂(canonicalBroadenedCollisionMeasureLimit
          ensemble sign T hT : Measure Real) := by
  rw [markedBroadenedResonanceMeasure,
    integral_broadenedResonanceMeasure]
  rw [canonicalBroadenedCollisionMeasureLimit,
    integral_broadenedResonanceMeasure]
  simpa only [id_eq,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure] using
    (integral_markedFrequencyMismatch_eq_canonicalCollisionMeasureLimit
      ensemble target hfrequency sign
      (fun mismatch =>
        normalizedFiniteTimeResonanceKernel mismatch T • test mismatch)
      ((continuous_normalizedFiniteTimeResonanceKernel hT).smul htest))

/-- The resonant-three-wave weak integrand is also identified whenever it
factors through the marked mismatch.  This is precisely the maximal bridge
available without asserting that the marked cluster point itself is supported
on the exact resonance surface. -/
theorem integral_triadWeakObservableIntegrand_eq_limit_of_mismatch
    (ensemble : IIDMassPhaseEnsemble Omega)
    (target : ProbabilityMeasure (Fin 3 -> RankFrequencyMark))
    (hfrequency :
      ProbabilityMeasure.map target
          measurable_forgetRankFrequencyTripleEuclidean.aemeasurable =
        canonicalJointFrequencyMeasureLimit ensemble)
    (sign : Fin 3 -> InteractionSign)
    (test action : RankFrequencyMark -> Real)
    (observable : Real -> Real) (hobservable : Continuous observable)
    (hdepends : forall marks : Fin 3 -> RankFrequencyMark,
      triadWeakObservableIntegrand test action marks =
        observable (markedFrequencyMismatch sign marks)) :
    (∫ marks, triadWeakObservableIntegrand test action marks
      ∂(target : Measure (Fin 3 -> RankFrequencyMark))) =
      ∫ mismatch, observable mismatch
        ∂(canonicalCollisionMeasureLimit ensemble sign : Measure Real) := by
  calc
    (∫ marks, triadWeakObservableIntegrand test action marks
        ∂(target : Measure (Fin 3 -> RankFrequencyMark))) =
        ∫ marks, observable (markedFrequencyMismatch sign marks)
          ∂(target : Measure (Fin 3 -> RankFrequencyMark)) := by
      apply integral_congr_ae
      exact ae_of_all _ hdepends
    _ = ∫ mismatch, observable mismatch
          ∂(canonicalCollisionMeasureLimit ensemble sign : Measure Real) :=
      integral_markedFrequencyMismatch_eq_canonicalCollisionMeasureLimit
        ensemble target hfrequency sign observable hobservable

/-- An actual `ResonantThreeWaveMeasure` whose collision measure is a
frequency-identified marked limit has the same deterministic weak form for
every integrand which factors through the marked mismatch. -/
theorem weakCollisionSlope_eq_limit_of_marked_mismatch
    (ensemble : IIDMassPhaseEnsemble Omega)
    (collision : ResonantThreeWaveMeasure RankFrequencyMark)
    (target : ProbabilityMeasure (Fin 3 -> RankFrequencyMark))
    (hcollision :
      (collision.collisionMeasure :
        Measure (Fin 3 -> RankFrequencyMark)) =
      (target : Measure (Fin 3 -> RankFrequencyMark)))
    (hfrequency :
      ProbabilityMeasure.map target
          measurable_forgetRankFrequencyTripleEuclidean.aemeasurable =
        canonicalJointFrequencyMeasureLimit ensemble)
    (sign : Fin 3 -> InteractionSign)
    (test action : RankFrequencyMark -> Real)
    (observable : Real -> Real) (hobservable : Continuous observable)
    (hdepends : forall marks : Fin 3 -> RankFrequencyMark,
      triadWeakObservableIntegrand test action marks =
        observable (markedFrequencyMismatch sign marks)) :
    weakCollisionSlope collision test action =
      ∫ mismatch, observable mismatch
        ∂(canonicalCollisionMeasureLimit ensemble sign : Measure Real) := by
  unfold weakCollisionSlope
  rw [hcollision]
  exact integral_triadWeakObservableIntegrand_eq_limit_of_mismatch
    ensemble target hfrequency sign test action observable hobservable hdepends

/-- Almost surely there is a marked cluster point, along a strictly
increasing subsequence, whose mismatch marginal is the deterministic
canonical collision limit simultaneously for every sign pattern. -/
theorem exists_marked_subsequence_limit_with_collisionMarginals_ae
    (ensemble : IIDMassPhaseEnsemble Omega) :
    ∀ᵐ omega ∂ensemble.probability,
      ∃ target : ProbabilityMeasure (Fin 3 -> RankFrequencyMark),
        ∃ subsequence : Nat -> Nat,
          StrictMono subsequence ∧
          Tendsto
            (fun j : Nat => canonicalNormalizedRankFrequencyMarkedMeasure
              ensemble (subsequence j + 1) omega)
            atTop (nhds target) ∧
          (forall sign : Fin 3 -> InteractionSign,
            ProbabilityMeasure.map target
                (measurable_markedFrequencyMismatch sign).aemeasurable =
              canonicalCollisionMeasureLimit ensemble sign) := by
  filter_upwards
    [exists_marked_subsequence_limit_with_jointFrequencyMarginal_ae
      ensemble] with omega hcluster
  obtain ⟨target, subsequence, hmono, htendsto, hfrequency⟩ := hcluster
  refine ⟨target, subsequence, hmono, htendsto, ?_⟩
  intro sign
  exact map_marked_limit_eq_canonicalCollisionMeasureLimit
    ensemble target hfrequency sign

end

end ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
