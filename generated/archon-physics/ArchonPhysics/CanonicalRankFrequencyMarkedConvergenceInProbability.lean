import ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Canonical marked-measure convergence in probability

The canonical rank-frequency marked measures were previously shown to
converge almost surely in the weak topology.  This module supplies the
missing measure-valued measurability input and upgrades that result to
convergence in probability.

At a fixed volume the unnormalized marked finite measure is a finite sum of
continuously weighted Dirac finite measures.  This gives strong
measurability directly, without identifying the Giry sigma algebra with the
Borel sigma algebra of the weak topology.  Probability normalization is
handled by a vanishing positive Dirac regularization; normalization is
continuous away from the zero finite measure, and the canonical marked
measure is nonzero almost surely by the already proved simple-spectrum
event.
-/

open scoped Topology BoundedContinuousFunction

namespace ArchonPhysics.CanonicalRankFrequencyMarkedConvergenceInProbability

open ArchonPhysics
open ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedCompactness
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasureWeakLimit
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableHarmonicData
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomMassMeasurableModeCoupling
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassPositiveCollisionData
open Filter MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

private abbrev MarkedTriple := Fin 3 -> RankFrequencyMark

/-- A fixed ordered rank-frequency triple is measurable in the iid mass
sample.  Its rank coordinates are deterministic and its frequency
coordinates use the unconditional ordered-spectrum measurability theorem. -/
theorem measurable_orderedRankFrequencyTriple_sample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (modes : OrderedModeTriple N) :
    Measurable fun omega => orderedRankFrequencyTriple
      (ensemble.restrictPositiveMass (N := N) omega) modes := by
  unfold orderedRankFrequencyTriple orderedRankFrequencyMark
  apply measurable_pi_lambda
  intro r
  exact measurable_const.prodMk
    ((measurable_orderedModeFrequencies_unconditional
      (fun omega => harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega))
      (by
        apply Measurable.subtype_mk
        exact measurable_massWeightedHarmonicMatrix_of_coordinate
          _ (measurable_restrictPositiveMass_coordinate ensemble))).eval)

/-- Strong-measurability form of the fixed marked-triple result. -/
theorem stronglyMeasurable_orderedRankFrequencyTriple_sample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (modes : OrderedModeTriple N) :
    StronglyMeasurable fun omega => orderedRankFrequencyTriple
      (ensemble.restrictPositiveMass (N := N) omega) modes :=
  (measurable_orderedRankFrequencyTriple_sample ensemble modes).stronglyMeasurable

/-- A Dirac probability measure, viewed as a finite measure. -/
private def markedFiniteDirac (x : MarkedTriple) :
    FiniteMeasure MarkedTriple :=
  (diracProba x).toFiniteMeasure

private theorem continuous_markedFiniteDirac :
    Continuous markedFiniteDirac :=
  ProbabilityMeasure.toFiniteMeasure_continuous.comp continuous_diracProba

/-- The finite-measure summand attached to one ordered mode triple. -/
private def weightedMarkedAtomSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (modes : OrderedModeTriple N)
    (omega : Omega) : FiniteMeasure MarkedTriple :=
  Real.toNNReal
      (harmonicOrderedNormalizedInteractionWeight
        (ensemble.restrictPositiveMass (N := N) omega) modes) •
    markedFiniteDirac
      (orderedRankFrequencyTriple
        (ensemble.restrictPositiveMass (N := N) omega) modes)

private theorem stronglyMeasurable_weightedMarkedAtomSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (modes : OrderedModeTriple N) :
    StronglyMeasurable (weightedMarkedAtomSample ensemble modes) := by
  unfold weightedMarkedAtomSample
  change StronglyMeasurable
    ((fun omega => Real.toNNReal
      (harmonicOrderedNormalizedInteractionWeight
        (ensemble.restrictPositiveMass (N := N) omega) modes)) •
      (fun omega => markedFiniteDirac
        (orderedRankFrequencyTriple
          (ensemble.restrictPositiveMass (N := N) omega) modes)))
  apply StronglyMeasurable.smul
  · exact
      (measurable_orderedNormalizedInteractionWeightSample ensemble modes).real_toNNReal
        |>.stronglyMeasurable
  · exact continuous_markedFiniteDirac.comp_stronglyMeasurable
      (stronglyMeasurable_orderedRankFrequencyTriple_sample ensemble modes)

private def weightedMarkedAtomSum
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) :
    FiniteMeasure MarkedTriple := by
  classical
  exact ∑ modes : OrderedModeTriple N,
    if IsPositiveOrderedTriple
        (ensemble.restrictPositiveMass (N := N) omega) modes then
      weightedMarkedAtomSample ensemble modes omega
    else 0

private theorem positiveWeightedRankFrequencyTripleFiniteMeasure_eq_sum_atoms
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) :
    positiveWeightedRankFrequencyTripleFiniteMeasure
        (ensemble.restrictPositiveMass (N := N) omega) =
      weightedMarkedAtomSum (N := N) ensemble omega := by
  classical
  apply FiniteMeasure.toMeasure_injective
  unfold positiveWeightedRankFrequencyTripleFiniteMeasure
    positiveWeightedRankFrequencyTripleMeasure weightedMarkedAtomSum
    weightedMarkedAtomSample
    markedFiniteDirac
  rw [FiniteMeasure.toMeasure_sum]
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple
      (ensemble.restrictPositiveMass (N := N) omega) modes
  · simp only [if_pos hpositive, FiniteMeasure.toMeasure_smul,
      ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure]
    congr 1
  · simp [hpositive]

/-- At every fixed volume, the complete unnormalized marked finite measure is
strongly measurable for the weak topology. -/
theorem stronglyMeasurable_positiveWeightedRankFrequencyTripleFiniteMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] :
    StronglyMeasurable fun omega =>
      positiveWeightedRankFrequencyTripleFiniteMeasure
        (ensemble.restrictPositiveMass (N := N) omega) := by
  classical
  have hsum : StronglyMeasurable (weightedMarkedAtomSum (N := N) ensemble) := by
    unfold weightedMarkedAtomSum
    apply Finset.stronglyMeasurable_fun_sum
    intro modes _hmodes
    exact StronglyMeasurable.ite
      (measurableSet_isPositiveOrderedTripleSample ensemble modes)
      (stronglyMeasurable_weightedMarkedAtomSample ensemble modes)
      stronglyMeasurable_const
  have heq :
      (fun omega => positiveWeightedRankFrequencyTripleFiniteMeasure
        (ensemble.restrictPositiveMass (N := N) omega)) =
      weightedMarkedAtomSum (N := N) ensemble := by
    funext omega
    exact positiveWeightedRankFrequencyTripleFiniteMeasure_eq_sum_atoms
      (N := N) ensemble omega
  rw [heq]
  exact hsum

/-- The canonical per-site marked finite measure is strongly measurable at
every fixed volume. -/
theorem stronglyMeasurable_canonicalRankFrequencyTriplePerSiteFiniteMeasure
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) :
    StronglyMeasurable fun omega =>
      canonicalRankFrequencyTriplePerSiteFiniteMeasure ensemble n omega := by
  change StronglyMeasurable fun omega =>
    (((n + 2 : Nat) : NNReal)⁻¹) •
      positiveWeightedRankFrequencyTripleFiniteMeasure
        (ensemble.restrictPositiveMass (N := n + 2) omega)
  exact
    (stronglyMeasurable_positiveWeightedRankFrequencyTripleFiniteMeasure
      (ensemble := ensemble) (N := n + 2)).const_smul
        (((n + 2 : Nat) : NNReal)⁻¹)

/-- Positive Dirac regularization used to make normalization globally
continuous before the regularization is sent to zero. -/
private def regularizedNormalizeMarkedFiniteMeasure
    (j : Nat) (mu : FiniteMeasure MarkedTriple) :
    ProbabilityMeasure MarkedTriple :=
  (mu + ((((j + 1 : Nat) : NNReal)⁻¹) •
    markedFiniteDirac (fun _ => (0, 0)))).normalize

private theorem regularizedMarkedFiniteMeasure_ne_zero
    (j : Nat) (mu : FiniteMeasure MarkedTriple) :
    mu + ((((j + 1 : Nat) : NNReal)⁻¹) •
      markedFiniteDirac (fun _ => (0, 0))) ≠ 0 := by
  let c : NNReal := (((j + 1 : Nat) : NNReal)⁻¹)
  let rho : FiniteMeasure MarkedTriple :=
    markedFiniteDirac (fun _ => (0, 0))
  change mu + c • rho ≠ 0
  apply (FiniteMeasure.mass_nonzero_iff _).mp
  have hadd : (mu + c • rho).mass = mu.mass + (c • rho).mass := by
    unfold FiniteMeasure.mass
    simpa only [Pi.add_apply] using
      congrFun (FiniteMeasure.coeFn_add mu (c • rho)) Set.univ
  have hsmul : (c • rho).mass = c * rho.mass := by
    unfold FiniteMeasure.mass
    simpa only [Pi.smul_apply, smul_eq_mul] using
      congrFun (FiniteMeasure.coeFn_smul c rho) Set.univ
  have hrho : rho.mass = 1 := by
    unfold rho markedFiniteDirac
    exact ProbabilityMeasure.mass_toFiniteMeasure _
  rw [hadd, hsmul, hrho]
  simp only [mul_one]
  have hc : 0 < c := by
    unfold c
    positivity
  exact ne_of_gt (lt_of_lt_of_le hc (le_add_left (le_refl c)))

private theorem continuous_regularizedNormalizeMarkedFiniteMeasure
    (j : Nat) :
    Continuous (regularizedNormalizeMarkedFiniteMeasure j) := by
  rw [continuous_iff_continuousAt]
  intro mu
  unfold regularizedNormalizeMarkedFiniteMeasure
  apply FiniteMeasure.tendsto_normalize_of_tendsto
  · exact (continuous_id.add continuous_const).tendsto mu
  · exact regularizedMarkedFiniteMeasure_ne_zero j mu

private theorem regularizationCoefficient_tendsto_zero :
    Tendsto (fun j : Nat => (((j + 1 : Nat) : NNReal)⁻¹))
      atTop (nhds 0) := by
  apply tendsto_inv_atTop_zero.comp
  exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

private theorem regularizedMarkedFiniteMeasure_tendsto
    (mu : FiniteMeasure MarkedTriple) :
    Tendsto
      (fun j : Nat =>
        mu + ((((j + 1 : Nat) : NNReal)⁻¹) •
          markedFiniteDirac (fun _ => (0, 0))))
      atTop (nhds mu) := by
  have hdirac : Tendsto
      (fun _ : Nat => markedFiniteDirac (fun _ => (0, 0)))
      atTop (nhds (markedFiniteDirac (fun _ => (0, 0)))) :=
    tendsto_const_nhds
  simpa only [zero_smul, add_zero] using
    tendsto_const_nhds.add
      (regularizationCoefficient_tendsto_zero.smul hdirac)

private theorem regularizedNormalizeMarkedFiniteMeasure_tendsto_of_ne_zero
    (mu : FiniteMeasure MarkedTriple) (hmu : mu ≠ 0) :
    Tendsto (fun j => regularizedNormalizeMarkedFiniteMeasure j mu)
      atTop (nhds mu.normalize) := by
  exact FiniteMeasure.tendsto_normalize_of_tendsto
    (regularizedMarkedFiniteMeasure_tendsto mu) hmu

/-! ### A weak-topology pseudometric for the unnormalized finite measures

`FiniteMeasure` does not carry a generic pseudometric instance in Mathlib.
For the present Polish mark space, we metrize its weak topology through the
continuous map recording total mass and the probability normalization after
adding one fixed Dirac mass.  All nonnegative bounded-continuous test
integrals can be continuously reconstructed from that pair, so the map is
inducing. -/

private def unitRegularizedNormalizeMarkedFiniteMeasure
    (mu : FiniteMeasure MarkedTriple) : ProbabilityMeasure MarkedTriple :=
  (mu + markedFiniteDirac (fun _ => (0, 0))).normalize

private theorem markedFiniteDirac_zero_mass :
    (markedFiniteDirac (fun _ => (0, 0))).mass = 1 := by
  exact ProbabilityMeasure.mass_toFiniteMeasure _

private theorem markedFiniteMeasure_mass_add
    (mu nu : FiniteMeasure MarkedTriple) :
    (mu + nu).mass = mu.mass + nu.mass := by
  unfold FiniteMeasure.mass
  simpa only [Pi.add_apply] using
    congrFun (FiniteMeasure.coeFn_add mu nu) Set.univ

private theorem add_markedFiniteDirac_zero_ne_zero
    (mu : FiniteMeasure MarkedTriple) :
    mu + markedFiniteDirac (fun _ => (0, 0)) ≠ 0 := by
  apply (FiniteMeasure.mass_nonzero_iff _).mp
  rw [markedFiniteMeasure_mass_add, markedFiniteDirac_zero_mass]
  positivity

private theorem continuous_unitRegularizedNormalizeMarkedFiniteMeasure :
    Continuous unitRegularizedNormalizeMarkedFiniteMeasure := by
  rw [continuous_iff_continuousAt]
  intro mu
  unfold unitRegularizedNormalizeMarkedFiniteMeasure
  apply FiniteMeasure.tendsto_normalize_of_tendsto
  · exact (continuous_id.add continuous_const).tendsto mu
  · exact add_markedFiniteDirac_zero_ne_zero mu

private def markedFiniteMeasureWeakEmbedding
    (mu : FiniteMeasure MarkedTriple) :
    NNReal × ProbabilityMeasure MarkedTriple :=
  (mu.mass, unitRegularizedNormalizeMarkedFiniteMeasure mu)

private theorem continuous_markedFiniteMeasureWeakEmbedding :
    Continuous markedFiniteMeasureWeakEmbedding := by
  exact FiniteMeasure.continuous_mass.prodMk
    continuous_unitRegularizedNormalizeMarkedFiniteMeasure

private theorem markedFiniteMeasure_testAgainstNN_add
    (mu nu : FiniteMeasure MarkedTriple)
    (f : MarkedTriple →ᵇ NNReal) :
    (mu + nu).testAgainstNN f =
      mu.testAgainstNN f + nu.testAgainstNN f := by
  apply ENNReal.coe_inj.mp
  rw [ENNReal.coe_add,
    FiniteMeasure.testAgainstNN_coe_eq,
    FiniteMeasure.testAgainstNN_coe_eq,
    FiniteMeasure.testAgainstNN_coe_eq,
    FiniteMeasure.toMeasure_add, lintegral_add_measure]

private def reconstructMarkedFiniteMeasureTests
    (p : NNReal × ProbabilityMeasure MarkedTriple)
    (f : MarkedTriple →ᵇ NNReal) : NNReal :=
  ((p.1 + 1) * p.2.toFiniteMeasure.testAgainstNN f) -
    (markedFiniteDirac (fun _ => (0, 0))).testAgainstNN f

private theorem continuous_reconstructMarkedFiniteMeasureTests :
    Continuous reconstructMarkedFiniteMeasureTests := by
  apply continuous_pi
  intro f
  apply Continuous.sub
  · exact (continuous_fst.add continuous_const).mul
      ((FiniteMeasure.continuous_testAgainstNN_eval f).comp
        (ProbabilityMeasure.toFiniteMeasure_continuous.comp continuous_snd))
  · exact continuous_const

private theorem reconstructMarkedFiniteMeasureTests_embedding
    (mu : FiniteMeasure MarkedTriple) :
    reconstructMarkedFiniteMeasureTests
        (markedFiniteMeasureWeakEmbedding mu) =
      fun f => mu.testAgainstNN f := by
  funext f
  unfold reconstructMarkedFiniteMeasureTests
    markedFiniteMeasureWeakEmbedding
    unitRegularizedNormalizeMarkedFiniteMeasure
  have hself :=
    (mu + markedFiniteDirac (fun _ => (0, 0))).self_eq_mass_smul_normalize
  have htest := congrArg
    (fun nu : FiniteMeasure MarkedTriple => nu.testAgainstNN f) hself
  rw [markedFiniteMeasure_testAgainstNN_add,
    FiniteMeasure.smul_testAgainstNN_apply] at htest
  rw [markedFiniteMeasure_mass_add, markedFiniteDirac_zero_mass] at htest
  simp only [smul_eq_mul] at htest
  have hle :
      (markedFiniteDirac (fun _ => (0, 0))).testAgainstNN f ≤
        (mu.mass + 1) *
          (mu + markedFiniteDirac (fun _ => (0, 0))).normalize.toFiniteMeasure.testAgainstNN f := by
    rw [← htest]
    exact le_add_left (le_refl _)
  exact (tsub_eq_iff_eq_add_of_le hle).2 htest.symm

private theorem inducing_markedFiniteMeasure_testAgainstNN :
    Topology.IsInducing
      (fun mu : FiniteMeasure MarkedTriple =>
        fun f : MarkedTriple →ᵇ NNReal => mu.testAgainstNN f) := by
  have hmu : Topology.IsInducing
      (FiniteMeasure.toWeakDualBCNN : FiniteMeasure MarkedTriple →
        WeakDual NNReal (MarkedTriple →ᵇ NNReal)) := ⟨rfl⟩
  have hphi : Topology.IsInducing
      (fun phi : WeakDual NNReal (MarkedTriple →ᵇ NNReal) =>
        fun f => phi f) := ⟨rfl⟩
  change Topology.IsInducing
    ((fun phi : WeakDual NNReal (MarkedTriple →ᵇ NNReal) => fun f => phi f) ∘
      FiniteMeasure.toWeakDualBCNN)
  exact hphi.comp hmu

private theorem inducing_markedFiniteMeasureWeakEmbedding :
    Topology.IsInducing markedFiniteMeasureWeakEmbedding := by
  apply Topology.IsInducing.of_comp
    continuous_markedFiniteMeasureWeakEmbedding
    continuous_reconstructMarkedFiniteMeasureTests
  have hcomp :
      reconstructMarkedFiniteMeasureTests ∘ markedFiniteMeasureWeakEmbedding =
        (fun mu : FiniteMeasure MarkedTriple =>
          fun f : MarkedTriple →ᵇ NNReal => mu.testAgainstNN f) := by
    funext mu
    exact reconstructMarkedFiniteMeasureTests_embedding mu
  rw [hcomp]
  exact inducing_markedFiniteMeasure_testAgainstNN

/-- A pseudometric that induces precisely the weak topology on the marked
finite measures. -/
@[instance_reducible]
noncomputable def canonicalRankFrequencyMarkedFiniteMeasureWeakPseudoMetricSpace :
    PseudoMetricSpace (FiniteMeasure MarkedTriple) := by
  let _ : TopologicalSpace.PseudoMetrizableSpace
      (FiniteMeasure MarkedTriple) :=
    inducing_markedFiniteMeasureWeakEmbedding.pseudoMetrizableSpace
  exact TopologicalSpace.pseudoMetrizableSpacePseudoMetric _

/-- The complete unnormalized canonical marked finite-measure sequence
converges in probability, for a metric compatible with weak convergence, to
the deterministic per-site marked finite-measure limit. -/
theorem canonicalRankFrequencyTriplePerSiteFiniteMeasure_tendstoInMeasure_limit :
    let _ : PseudoMetricSpace (FiniteMeasure (Fin 3 -> RankFrequencyMark)) :=
      canonicalRankFrequencyMarkedFiniteMeasureWeakPseudoMetricSpace
    TendstoInMeasure RandomEnsemble.canonicalLaw
      (fun n omega => canonicalRankFrequencyTriplePerSiteFiniteMeasure
        canonicalIIDMassPhaseEnsemble (n + 1) omega)
      atTop
      (fun _omega => canonicalRankFrequencyMarkedPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble) := by
  let _ : PseudoMetricSpace (FiniteMeasure (Fin 3 -> RankFrequencyMark)) :=
    canonicalRankFrequencyMarkedFiniteMeasureWeakPseudoMetricSpace
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact
      (stronglyMeasurable_canonicalRankFrequencyTriplePerSiteFiniteMeasure
        canonicalIIDMassPhaseEnsemble (n + 1)).aestronglyMeasurable
  · exact canonicalRankFrequencyTriplePerSiteFiniteMeasure_tendsto_limit_ae

/-- At every canonical volume `n + 1` (physical volume `n + 3`), the
probability-normalized marked measure is almost-everywhere strongly
measurable. -/
theorem aestronglyMeasurable_canonicalNormalizedRankFrequencyMarkedMeasure_succ
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) :
    AEStronglyMeasurable
      (fun omega => canonicalNormalizedRankFrequencyMarkedMeasure
        ensemble (n + 1) omega) ensemble.probability := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun j omega => regularizedNormalizeMarkedFiniteMeasure j
      (canonicalRankFrequencyTriplePerSiteFiniteMeasure
        ensemble (n + 1) omega))
  · intro j
    exact
      (continuous_regularizedNormalizeMarkedFiniteMeasure j).comp_stronglyMeasurable
        (stronglyMeasurable_canonicalRankFrequencyTriplePerSiteFiniteMeasure
          ensemble (n + 1))
      |>.aestronglyMeasurable
  · filter_upwards
      [canonicalJointFrequencyVolumes_simpleOrderedSpectrum_ae ensemble]
        with omega hsimple
    unfold canonicalNormalizedRankFrequencyMarkedMeasure
    apply regularizedNormalizeMarkedFiniteMeasure_tendsto_of_ne_zero
    apply (FiniteMeasure.mass_nonzero_iff _).mp
    exact canonicalRankFrequencyTriplePerSiteFiniteMeasure_mass_ne_zero
      ensemble (fun _ => InteractionSign.plus) (n + 1) omega (by omega)
      (by simpa [Nat.add_assoc] using hsimple n)

/-- The complete canonical normalized marked sequence converges in
probability, in a metric compatible with the weak topology, to its
deterministic graph-lift probability measure. -/
theorem canonicalNormalizedRankFrequencyMarkedMeasure_tendstoInMeasure_limit :
    let _ : PseudoMetricSpace
        (ProbabilityMeasure (Fin 3 -> RankFrequencyMark)) :=
      TopologicalSpace.pseudoMetrizableSpacePseudoMetric _
    TendstoInMeasure RandomEnsemble.canonicalLaw
      (fun n omega => canonicalNormalizedRankFrequencyMarkedMeasure
        canonicalIIDMassPhaseEnsemble (n + 1) omega)
      atTop
      (fun _omega => canonicalRankFrequencyMarkedMeasureLimit
        canonicalIIDMassPhaseEnsemble) := by
  let _ : PseudoMetricSpace
      (ProbabilityMeasure (Fin 3 -> RankFrequencyMark)) :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric _
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact
      aestronglyMeasurable_canonicalNormalizedRankFrequencyMarkedMeasure_succ
        canonicalIIDMassPhaseEnsemble n
  · exact canonicalNormalizedRankFrequencyMarkedMeasure_tendsto_limit_ae

end

end ArchonPhysics.CanonicalRankFrequencyMarkedConvergenceInProbability
