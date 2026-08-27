import ArchonPhysics.CanonicalRankFrequencyMarkedConvergenceInProbability
import ArchonPhysics.ProbabilityJointLimitDiagonalization

/-!
# Canonical marked-measure probability joint limit

The complete canonical unnormalized rank--frequency marked measure converges
in probability in a pseudometric inducing exactly its weak topology.  The
qualitative probability diagonalization theorem therefore selects, for any
nonnegative coupling amplification, a deterministic volume cutoff `N_min(g)`.

Along every weak-coupling/large-volume path admitted by that cutoff, the
probability of missing the coupling-dependent weak-measure tolerance tends to
zero.  This removes any need to postulate an explicit finite-volume rate for
the marked thermodynamic limit.
-/

open scoped Topology

namespace ArchonPhysics.CanonicalRankFrequencyMarkedProbabilityJointLimit

open ArchonPhysics
open ArchonPhysics.CanonicalRankFrequencyMarkedConvergenceInProbability
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ProbabilityJointLimitDiagonalization
open ArchonPhysics.ThermalizationTransfer
open Filter MeasureTheory

noncomputable section

/-- The complete positive-volume canonical marked finite-measure sequence,
indexed so that index `n` uses the strictly positive parameter `n + 1`. -/
abbrev canonicalMarkedPerSiteSequence :
    Nat -> RandomEnsemble.SampleSpace ->
      FiniteMeasure (Fin 3 -> RankFrequencyMark) :=
  fun n omega => canonicalRankFrequencyTriplePerSiteFiniteMeasure
    canonicalIIDMassPhaseEnsemble (n + 1) omega

/-- The deterministic thermodynamic marked target, viewed as a constant
random variable. -/
abbrev canonicalMarkedPerSiteTarget :
    RandomEnsemble.SampleSpace ->
      FiniteMeasure (Fin 3 -> RankFrequencyMark) :=
  fun _omega => canonicalRankFrequencyMarkedPerSiteMeasureLimit
    canonicalIIDMassPhaseEnsemble

/-- Canonical marked convergence in probability under the explicitly chosen
weak-topology-compatible pseudometric. -/
theorem canonicalMarkedPerSiteSequence_tendstoInMeasure :
    let _ : PseudoMetricSpace
        (FiniteMeasure (Fin 3 -> RankFrequencyMark)) :=
      canonicalRankFrequencyMarkedFiniteMeasureWeakPseudoMetricSpace
    TendstoInMeasure RandomEnsemble.canonicalLaw
      canonicalMarkedPerSiteSequence atTop canonicalMarkedPerSiteTarget := by
  simpa only [canonicalMarkedPerSiteSequence,
    canonicalMarkedPerSiteTarget] using
    canonicalRankFrequencyTriplePerSiteFiniteMeasure_tendstoInMeasure_limit

/-- Coupling-dependent volume cutoff obtained qualitatively from the marked
convergence in probability. -/
abbrev canonicalMarkedProbabilityJointSizeCutoff
    (amplification : Real -> Real) : Real -> Nat :=
  let _ : PseudoMetricSpace
      (FiniteMeasure (Fin 3 -> RankFrequencyMark)) :=
    canonicalRankFrequencyMarkedFiniteMeasureWeakPseudoMetricSpace
  probabilityJointSizeCutoff RandomEnsemble.canonicalLaw
    canonicalMarkedPerSiteSequence canonicalMarkedPerSiteTarget amplification
    (by
      simpa only [canonicalMarkedPerSiteSequence,
        canonicalMarkedPerSiteTarget] using
        canonicalRankFrequencyTriplePerSiteFiniteMeasure_tendstoInMeasure_limit)

/-- Above the canonical cutoff, the weak-measure bad-event probability is
smaller than the positive coupling that selected the cutoff. -/
theorem canonicalMarkedBadEvent_probability_lt_of_cutoff
    (amplification : Real -> Real)
    (hamplification : forall g, 0 <= amplification g)
    {g : Real} (hg : 0 < g) {N : Nat}
    (hN : canonicalMarkedProbabilityJointSizeCutoff amplification g <= N) :
    let _ : PseudoMetricSpace
        (FiniteMeasure (Fin 3 -> RankFrequencyMark)) :=
      canonicalRankFrequencyMarkedFiniteMeasureWeakPseudoMetricSpace
    RandomEnsemble.canonicalLaw.real
      (probabilityDiagonalBadEvent canonicalMarkedPerSiteSequence
        canonicalMarkedPerSiteTarget amplification N g) < g := by
  let _ : PseudoMetricSpace
      (FiniteMeasure (Fin 3 -> RankFrequencyMark)) :=
    canonicalRankFrequencyMarkedFiniteMeasureWeakPseudoMetricSpace
  have hconv : TendstoInMeasure RandomEnsemble.canonicalLaw
      canonicalMarkedPerSiteSequence atTop canonicalMarkedPerSiteTarget := by
    simpa only [canonicalMarkedPerSiteSequence,
      canonicalMarkedPerSiteTarget] using
      canonicalRankFrequencyTriplePerSiteFiniteMeasure_tendstoInMeasure_limit
  have hNinternal : probabilityJointSizeCutoff RandomEnsemble.canonicalLaw
      canonicalMarkedPerSiteSequence canonicalMarkedPerSiteTarget
        amplification hconv g <= N := by
    simpa only [canonicalMarkedProbabilityJointSizeCutoff] using hN
  exact probabilityDiagonalBadEvent_probability_lt_of_cutoff
    RandomEnsemble.canonicalLaw canonicalMarkedPerSiteSequence
    canonicalMarkedPerSiteTarget amplification
    hconv hamplification hg hNinternal

/-- Along every joint path admitted by the canonical marked cutoff, bad-event
probabilities vanish and the amplified tolerance is pointwise at most `g`. -/
theorem canonicalMarked_jointLimit_probability_control
    (amplification : Real -> Real)
    (hamplification : forall g, 0 <= amplification g)
    (s : AdmissibleJointLimit
      (canonicalMarkedProbabilityJointSizeCutoff amplification)) :
    let _ : PseudoMetricSpace
        (FiniteMeasure (Fin 3 -> RankFrequencyMark)) :=
      canonicalRankFrequencyMarkedFiniteMeasureWeakPseudoMetricSpace
    (∀ᶠ j in atTop,
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
            amplification (s.coupling j) <= s.coupling j := by
  let _ : PseudoMetricSpace
      (FiniteMeasure (Fin 3 -> RankFrequencyMark)) :=
    canonicalRankFrequencyMarkedFiniteMeasureWeakPseudoMetricSpace
  have hconv : TendstoInMeasure RandomEnsemble.canonicalLaw
      canonicalMarkedPerSiteSequence atTop canonicalMarkedPerSiteTarget := by
    simpa only [canonicalMarkedPerSiteSequence,
      canonicalMarkedPerSiteTarget] using
      canonicalRankFrequencyTriplePerSiteFiniteMeasure_tendstoInMeasure_limit
  have hresult := And.intro
    (eventually_probabilityDiagonalBadEvent_probability_le_coupling
      RandomEnsemble.canonicalLaw canonicalMarkedPerSiteSequence
      canonicalMarkedPerSiteTarget amplification hconv hamplification s)
    (And.intro
      (probabilityDiagonalBadEvent_probability_along_jointLimit_tendsto_zero
        RandomEnsemble.canonicalLaw canonicalMarkedPerSiteSequence
        canonicalMarkedPerSiteTarget amplification hconv hamplification s)
      (probabilityDiagonalThreshold_mul_amplification_along_jointLimit_le
        RandomEnsemble.canonicalLaw canonicalMarkedPerSiteSequence
        canonicalMarkedPerSiteTarget amplification hconv hamplification s))
  exact hresult

end


end ArchonPhysics.CanonicalRankFrequencyMarkedProbabilityJointLimit
