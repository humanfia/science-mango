import ArchonPhysics.CanonicalMarkedKernelIdentificationEndpoint
import ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
import ArchonPhysics.ParameterizedTestProbabilityDiagonalization

/-!
# Canonical marked resonance-action joint diagonalization

The complete canonical rank--frequency marked finite measures converge almost
surely in their weak topology.  At each fixed positive coupling `g`, testing
them against the bounded continuous squared-sinc resonance profile at the
possibly very large time `kineticTime g` therefore gives scalar convergence
in probability.

We diagonalize these *scalar test values* over `(N,g)`.  The resulting
deterministic cutoff makes the probability that the resonance-action error is
at least `g` smaller than `g`, hence makes those probabilities vanish along
every admitted joint limit.  No quantitative domination of this action by a
weak-topology pseudometric is asserted or used.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalMarkedResonanceActionJointDiagonalization

open ArchonPhysics
open ArchonPhysics.CanonicalMarkedKernelIdentificationEndpoint
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedConvergenceInProbability
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.ParameterizedTestProbabilityDiagonalization
open ArchonPhysics.ThermalizationTransfer
open Filter MeasureTheory Set Topology

noncomputable section

/-- The finite-volume marked resonance action at parameter `g`.  The marked
measure already contains the interaction weight; the displayed integral
tests it against the normalized squared-sinc mismatch profile.  Marked index
`N + 1` corresponds to physical spectral volume `N + 3`. -/
def canonicalMarkedResonanceActionSample
    (sign : Fin 3 -> InteractionSign)
    (kineticTime : Real -> Real)
    (g : Real) (N : Nat) (omega : RandomEnsemble.SampleSpace) : Real :=
  ∫ marks,
    normalizedFiniteTimeResonanceKernel
      (markedFrequencyMismatch sign marks) (kineticTime g)
    ∂(canonicalRankFrequencyTriplePerSiteFiniteMeasure
      canonicalIIDMassPhaseEnsemble (N + 1) omega)

/-- The deterministic thermodynamic marked resonance action tested at the
same parameter-dependent observation time. -/
def canonicalMarkedResonanceActionLimit
    (sign : Fin 3 -> InteractionSign)
    (kineticTime : Real -> Real) (g : Real) : Real :=
  ∫ marks,
    normalizedFiniteTimeResonanceKernel
      (markedFrequencyMismatch sign marks) (kineticTime g)
    ∂(canonicalRankFrequencyMarkedPerSiteMeasureLimit
      canonicalIIDMassPhaseEnsemble)

/-- The deterministic action viewed as a constant random variable, in the
form expected by the parameterized probability diagonalization. -/
abbrev canonicalMarkedResonanceActionTarget
    (sign : Fin 3 -> InteractionSign)
    (kineticTime : Real -> Real) :
    Real -> RandomEnsemble.SampleSpace -> Real :=
  fun g _omega => canonicalMarkedResonanceActionLimit sign kineticTime g

/-- At a fixed positive observation time, every finite-volume marked action
is a strongly measurable random variable. -/
theorem stronglyMeasurable_canonicalMarkedResonanceActionSample
    (sign : Fin 3 -> InteractionSign)
    (kineticTime : Real -> Real)
    {g : Real} (hT : 0 < kineticTime g) (N : Nat) :
    StronglyMeasurable
      (canonicalMarkedResonanceActionSample sign kineticTime g N) := by
  let test : BoundedContinuousFunction
      (Fin 3 -> RankFrequencyMark) Real :=
    normalizedFiniteTimeResonanceWeightBCF
      (markedFrequencyMismatch sign)
      (continuous_markedFrequencyMismatch sign)
      (kineticTime g) hT
  have hcontinuous : Continuous fun mu :
      FiniteMeasure (Fin 3 -> RankFrequencyMark) =>
        ∫ marks, test marks ∂mu :=
    FiniteMeasure.continuous_integral_boundedContinuousFunction test
  have hmeasure : StronglyMeasurable fun omega =>
      canonicalRankFrequencyTriplePerSiteFiniteMeasure
        canonicalIIDMassPhaseEnsemble (N + 1) omega :=
    stronglyMeasurable_canonicalRankFrequencyTriplePerSiteFiniteMeasure
      canonicalIIDMassPhaseEnsemble (N + 1)
  have hcomposition := hcontinuous.comp_stronglyMeasurable hmeasure
  unfold canonicalMarkedResonanceActionSample
  simpa only [test,
    normalizedFiniteTimeResonanceWeightBCF_apply, Function.comp_def] using hcomposition

/-- For every fixed positive parameter, the exact marked resonance-action
sample converges almost surely to its deterministic thermodynamic action.
This is continuous testing of the complete weak marked-kernel endpoint. -/
theorem canonicalMarkedResonanceAction_tendsto_limit_ae_fixedCoupling
    (sign : Fin 3 -> InteractionSign)
    (kineticTime : Real -> Real)
    {g : Real} (hT : 0 < kineticTime g) :
    ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
      Tendsto
        (fun N => canonicalMarkedResonanceActionSample
          sign kineticTime g N omega)
        atTop
        (nhds (canonicalMarkedResonanceActionLimit
          sign kineticTime g)) := by
  let test : BoundedContinuousFunction
      (Fin 3 -> RankFrequencyMark) Real :=
    normalizedFiniteTimeResonanceWeightBCF
      (markedFrequencyMismatch sign)
      (continuous_markedFrequencyMismatch sign)
      (kineticTime g) hT
  filter_upwards [canonicalFullMarkedKernel_tendsto_limit_ae] with omega hmarked
  have htest :=
    ((FiniteMeasure.continuous_integral_boundedContinuousFunction test).tendsto
      (canonicalRankFrequencyMarkedPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble)).comp hmarked
  unfold canonicalMarkedResonanceActionSample
  simpa only [test,
    canonicalMarkedResonanceActionLimit,
    normalizedFiniteTimeResonanceWeightBCF_apply, Function.comp_def] using htest

/-- Fixed-coupling convergence in probability for the resonance action.
The observation time may depend arbitrarily on `g`; it is held fixed while
`N -> infinity`. -/
theorem canonicalMarkedResonanceAction_tendstoInMeasure_fixedCoupling
    (sign : Fin 3 -> InteractionSign)
    (kineticTime : Real -> Real)
    {g : Real} (hT : 0 < kineticTime g) :
    TendstoInMeasure RandomEnsemble.canonicalLaw
      (canonicalMarkedResonanceActionSample sign kineticTime g)
      atTop
      (canonicalMarkedResonanceActionTarget sign kineticTime g) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro N
    exact (stronglyMeasurable_canonicalMarkedResonanceActionSample
      sign kineticTime hT N).aestronglyMeasurable
  · exact canonicalMarkedResonanceAction_tendsto_limit_ae_fixedCoupling
      sign kineticTime hT

/-- The deterministic volume cutoff obtained by diagonalizing the exact
marked resonance-action test at each positive coupling. -/
def canonicalMarkedResonanceActionSizeCutoff
    (sign : Fin 3 -> InteractionSign)
    (kineticTime : Real -> Real)
    (hkineticTime : forall g, 0 < g -> 0 < kineticTime g) : Real -> Nat :=
  parameterizedTestSizeCutoff RandomEnsemble.canonicalLaw
    (canonicalMarkedResonanceActionSample sign kineticTime)
    (canonicalMarkedResonanceActionTarget sign kineticTime)
    (fun g hg =>
      canonicalMarkedResonanceAction_tendstoInMeasure_fixedCoupling
        sign kineticTime (hkineticTime g hg))

/-- Above the exact action-test cutoff, the probability of action error at
least `g` is strictly smaller than `g`. -/
theorem canonicalMarkedResonanceActionBadEvent_probability_lt_of_cutoff
    (sign : Fin 3 -> InteractionSign)
    (kineticTime : Real -> Real)
    (hkineticTime : forall g, 0 < g -> 0 < kineticTime g)
    {g : Real} (hg : 0 < g) {N : Nat}
    (hN : canonicalMarkedResonanceActionSizeCutoff
      sign kineticTime hkineticTime g <= N) :
    RandomEnsemble.canonicalLaw.real
      {omega |
        g <= dist
          (canonicalMarkedResonanceActionSample
            sign kineticTime g N omega)
          (canonicalMarkedResonanceActionLimit
            sign kineticTime g)} < g := by
  exact parameterizedTestBadEvent_probability_lt_of_cutoff
    RandomEnsemble.canonicalLaw
    (canonicalMarkedResonanceActionSample sign kineticTime)
    (canonicalMarkedResonanceActionTarget sign kineticTime)
    (fun g hg =>
      canonicalMarkedResonanceAction_tendstoInMeasure_fixedCoupling
        sign kineticTime (hkineticTime g hg))
    hg hN

/-- Along every admitted joint `(N,g)` path, the probability that the exact
marked resonance-action error is at least the current coupling tends to
zero.  This is the desired honest test-level joint rate. -/
theorem canonicalMarkedResonanceActionBadEvent_probability_jointLimit_tendsto_zero
    (sign : Fin 3 -> InteractionSign)
    (kineticTime : Real -> Real)
    (hkineticTime : forall g, 0 < g -> 0 < kineticTime g)
    (s : AdmissibleJointLimit
      (canonicalMarkedResonanceActionSizeCutoff
        sign kineticTime hkineticTime)) :
    Tendsto
      (fun j => RandomEnsemble.canonicalLaw.real
        {omega |
          s.coupling j <= dist
            (canonicalMarkedResonanceActionSample sign kineticTime
              (s.coupling j) (s.systemSize j) omega)
            (canonicalMarkedResonanceActionLimit sign kineticTime
              (s.coupling j))})
      atTop (nhds 0) := by
  exact parameterizedTestBadEvent_probability_along_jointLimit_tendsto_zero
    RandomEnsemble.canonicalLaw
    (canonicalMarkedResonanceActionSample sign kineticTime)
    (canonicalMarkedResonanceActionTarget sign kineticTime)
    (fun g hg =>
      canonicalMarkedResonanceAction_tendstoInMeasure_fixedCoupling
        sign kineticTime (hkineticTime g hg))
    s

/-- The kinetic observation time `g^{-2}`. -/
def inverseSquareKineticTime (g : Real) : Real :=
  (g ^ 2)⁻¹

theorem inverseSquareKineticTime_pos {g : Real} (hg : 0 < g) :
    0 < inverseSquareKineticTime g := by
  unfold inverseSquareKineticTime
  positivity

/-- Canonical deterministic cutoff for the exact `T(g) = g^{-2}` marked
resonance action. -/
abbrev canonicalInverseSquareMarkedResonanceActionSizeCutoff
    (sign : Fin 3 -> InteractionSign) : Real -> Nat :=
  canonicalMarkedResonanceActionSizeCutoff sign inverseSquareKineticTime
    (fun _g hg => inverseSquareKineticTime_pos hg)

/-- Exact inverse-square kinetic-time specialization: every admitted joint
limit has vanishing probability of a marked resonance-action error at least
`g`. -/
theorem canonicalInverseSquareMarkedResonanceActionBadEvent_probability_jointLimit_tendsto_zero
    (sign : Fin 3 -> InteractionSign)
    (s : AdmissibleJointLimit
      (canonicalInverseSquareMarkedResonanceActionSizeCutoff sign)) :
    Tendsto
      (fun j => RandomEnsemble.canonicalLaw.real
        {omega |
          s.coupling j <= dist
            (canonicalMarkedResonanceActionSample sign
              inverseSquareKineticTime (s.coupling j)
              (s.systemSize j) omega)
            (canonicalMarkedResonanceActionLimit sign
              inverseSquareKineticTime (s.coupling j))})
      atTop (nhds 0) := by
  exact canonicalMarkedResonanceActionBadEvent_probability_jointLimit_tendsto_zero
    sign inverseSquareKineticTime
      (fun _g hg => inverseSquareKineticTime_pos hg) s

end

end ArchonPhysics.CanonicalMarkedResonanceActionJointDiagonalization
