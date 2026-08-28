import ArchonPhysics.PhyslibFPUTProbabilisticFullStateEndpointCertificate
import ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing

/-!
# Probabilistic full-state endpoints give all-mode energy-profile control

This module is the probabilistic counterpart of the full-state energy-profile
adapter. At every block and positive-frequency mode, the full-state coupling
may fail on a measurable bad event. The endpoint moment estimate therefore
retains both terms

`2 * M * delta + 2 * M ^ 2 * failureProbability`.

After multiplication by the positive mode frequency, the pointwise estimates
give a Pi sup-norm energy-profile estimate and hence construct the canonical
Haar energy-profile certificate without a scalar collision compatibility
condition.

The joint bad event over the first `K` blocks and every positive mode is also
kept explicitly. Its finite union bound contains
`Fintype.card (PositiveFrequencyMode m) * K`; in particular, no uniformity in
the lattice size is claimed.
-/

namespace ArchonPhysics.PhyslibFPUTProbabilisticFullStateEnergyProfileAdapter

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing
open ArchonPhysics.PhyslibFPUTProbabilisticFullStateEndpointCertificate

noncomputable section

/-- Second moment of an actual probabilistic full-state endpoint law. -/
def probabilisticFullStateActualSecondMoment
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {mu : Measure Omega} {M : Real}
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M)
    (endpoint : Nat) : Real :=
  ∫ z, Complex.normSq z ∂
    (data.toAmplitudeCouplingRestartCertificate.actualLaw endpoint)

/-- Second moment of a reference probabilistic full-state endpoint law. -/
def probabilisticFullStateReferenceSecondMoment
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {mu : Measure Omega} {M : Real}
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M)
    (endpoint : Nat) : Real :=
  ∫ z, Complex.normSq z ∂
    (data.toAmplitudeCouplingRestartCertificate.referenceLaw endpoint)

/-- Initial endpoint second-moment control, including the bad-event cost. -/
theorem probabilisticFullState_initial_secondMoment_error
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {M : Real}
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    |probabilisticFullStateActualSecondMoment data 0 -
        probabilisticFullStateReferenceSecondMoment data 0| ≤
      2 * M * data.initialDelta +
        2 * M ^ 2 * data.failureProbability := by
  simpa [probabilisticFullStateActualSecondMoment,
    probabilisticFullStateReferenceSecondMoment] using
    (data.endpoint_second_fourth_moment_errors).1.1

/-- Propagated endpoint second-moment control, including the bad-event cost. -/
theorem probabilisticFullState_final_secondMoment_error
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {M : Real}
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    |probabilisticFullStateActualSecondMoment data 1 -
        probabilisticFullStateReferenceSecondMoment data 1| ≤
      2 * M * data.finalDelta +
        2 * M ^ 2 * data.failureProbability := by
  simpa [probabilisticFullStateActualSecondMoment,
    probabilisticFullStateReferenceSecondMoment] using
    (data.endpoint_second_fourth_moment_errors).2.1

/-- Probabilistic full-state data for all blocks and all positive modes.

The frequency-weighted cost fields display exactly how the endpoint radius
and the failure probability enter the uniform profile coupling constant.
The actual/reference energy identifications enforce coherence between
successive blocks. -/
structure FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (M : Real)
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta T : Real)
    (g : Nat → Real)
    (E : Nat → Nat → PositiveEnergyProfile m)
    (Cref Ccoupling Cfailure : Real) where
  endpointData : ∀ _n _j (_mode : PositiveFrequencyMode m),
    ProbabilisticFullStateEndpointPropagationData Omega X mu M
  referenceEnergy : Nat → Nat → PositiveEnergyProfile m
  Cref_nonneg : 0 ≤ Cref
  Ccoupling_nonneg : 0 ≤ Ccoupling
  Cfailure_nonneg : 0 ≤ Cfailure
  referenceEnergy_nonneg : ∀ n j mode,
    0 ≤ referenceEnergy n j mode
  couplingWindow : ∀ n, |g n| ≤ 1
  failureProbability_cubic : ∀ n j (mode : PositiveFrequencyMode m),
    (endpointData n j mode).failureProbability ≤
      Cfailure * |g n| ^ 3
  actualInitialEnergy : ∀ n j mode,
    E n j mode = modeFrequency m mode *
      probabilisticFullStateActualSecondMoment (endpointData n j mode) 0
  actualFinalEnergy : ∀ n j mode,
    E n (j + 1) mode = modeFrequency m mode *
      probabilisticFullStateActualSecondMoment (endpointData n j mode) 1
  referenceInitialEnergy : ∀ n j mode,
    canonicalHaarEnergyBlockInitial m (referenceEnergy n j) mode =
      modeFrequency m mode *
        probabilisticFullStateReferenceSecondMoment
          (endpointData n j mode) 0
  referenceFinalEnergy : ∀ n j mode,
    canonicalHaarEnergyBlockFinal m kappa beta (g n)
        (referenceEnergy n j) T mode =
      modeFrequency m mode *
        probabilisticFullStateReferenceSecondMoment
          (endpointData n j mode) 1
  initialFrequencyWeightedCost : ∀ n j (mode : PositiveFrequencyMode m),
    modeFrequency m mode *
        (2 * M * (endpointData n j mode).initialDelta +
          2 * M ^ 2 * (endpointData n j mode).failureProbability) ≤
      Ccoupling * |g n| ^ 3
  finalFrequencyWeightedCost : ∀ n j (mode : PositiveFrequencyMode m),
    modeFrequency m mode *
        (2 * M * (endpointData n j mode).finalDelta +
          2 * M ^ 2 * (endpointData n j mode).failureProbability) ≤
      Ccoupling * |g n| ^ 3
  finiteCharacterEnergyEnvelope : ∀ n j (mode : PositiveFrequencyMode m),
    modeFrequency m mode *
        (PhyslibFPUTActualHaarSecondOrderEnergyDrift.physlibHaarEnergyDriftC3
            m kappa beta
            (FreeFPUTTensorPhaseExpansion.phaseEnergyRadius
              (extendPositiveEnergyProfile m (referenceEnergy n j))
              (modeFrequency m)) T mode +
          PhyslibFPUTActualHaarSecondOrderEnergyDrift.physlibHaarEnergyDriftC4
            m kappa beta
            (FreeFPUTTensorPhaseExpansion.phaseEnergyRadius
              (extendPositiveEnergyProfile m (referenceEnergy n j))
              (modeFrequency m)) T mode) ≤
      Cref

namespace FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter

variable {Omega X : Type*} [MeasurableSpace Omega]
  [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {mu : Measure Omega} [IsProbabilityMeasure mu] {M : Real}
  {N : Nat} [NeZero N]
  {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
  {g : Nat → Real}
  {E : Nat → Nat → PositiveEnergyProfile m}
  {Cref Ccoupling Cfailure : Real}

/-- The probabilistic full-state moment theorem implies the initial profile
sup-norm estimate. -/
theorem initial_endpoint_control
    (adapter : FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E
        Cref Ccoupling Cfailure)
    (n j : Nat) :
    ‖E n j - canonicalHaarEnergyBlockInitial m
        (adapter.referenceEnergy n j)‖ ≤
      Ccoupling * |g n| ^ 3 := by
  refine (pi_norm_le_iff_of_nonneg
    (mul_nonneg adapter.Ccoupling_nonneg (by positivity))).2 ?_
  intro mode
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [adapter.actualInitialEnergy n j mode,
    adapter.referenceInitialEnergy n j mode, ← mul_sub, abs_mul,
    abs_of_pos mode.property]
  exact (mul_le_mul_of_nonneg_left
      (probabilisticFullState_initial_secondMoment_error
        (adapter.endpointData n j mode)) mode.property.le).trans
    (adapter.initialFrequencyWeightedCost n j mode)

/-- The probabilistic full-state moment theorem implies the propagated
profile sup-norm estimate. -/
theorem final_endpoint_control
    (adapter : FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E
        Cref Ccoupling Cfailure)
    (n j : Nat) :
    ‖E n (j + 1) - canonicalHaarEnergyBlockFinal m kappa beta (g n)
        (adapter.referenceEnergy n j) T‖ ≤
      Ccoupling * |g n| ^ 3 := by
  refine (pi_norm_le_iff_of_nonneg
    (mul_nonneg adapter.Ccoupling_nonneg (by positivity))).2 ?_
  intro mode
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [adapter.actualFinalEnergy n j mode,
    adapter.referenceFinalEnergy n j mode, ← mul_sub, abs_mul,
    abs_of_pos mode.property]
  exact (mul_le_mul_of_nonneg_left
      (probabilisticFullState_final_secondMoment_error
        (adapter.endpointData n j mode)) mode.property.le).trans
    (adapter.finalFrequencyWeightedCost n j mode)

/-- Construct the compatibility-free all-mode kinetic certificate. -/
def toCanonicalHaarEnergyProfileBlockwiseCertificate
    (adapter : FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E
        Cref Ccoupling Cfailure) :
    FPUTCanonicalHaarEnergyProfileBlockwiseCertificate
      m kappa beta T g E Cref Ccoupling where
  referenceEnergy := adapter.referenceEnergy
  Cref_nonneg := adapter.Cref_nonneg
  Ccoupling_nonneg := adapter.Ccoupling_nonneg
  referenceEnergy_nonneg := adapter.referenceEnergy_nonneg
  couplingWindow := adapter.couplingWindow
  initial_endpoint_control := adapter.initial_endpoint_control
  final_endpoint_control := adapter.final_endpoint_control
  finiteCharacterEnergyEnvelope := adapter.finiteCharacterEnergyEnvelope

/-- The event that at least one coupling among all positive modes and the
first `K` blocks fails. The finite product index makes both union factors
visible. -/
def firstKAllModesBad
    (adapter : FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E
        Cref Ccoupling Cfailure)
    (n K : Nat) : Set Omega :=
  ⋃ index : Fin K × PositiveFrequencyMode m,
    (adapter.endpointData n index.1 index.2).bad

theorem firstKAllModesBad_measurable
    (adapter : FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E
        Cref Ccoupling Cfailure)
    (n K : Nat) : MeasurableSet (adapter.firstKAllModesBad n K) := by
  unfold firstKAllModesBad
  exact MeasurableSet.iUnion fun index ↦
    (adapter.endpointData n index.1 index.2).bad_measurable

/-- Outside the joint event, every modal coupling in each of the first `K`
blocks satisfies its good-event full-state estimate. -/
theorem initial_state_near_of_not_mem_firstKAllModesBad
    (adapter : FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E
        Cref Ccoupling Cfailure)
    {n K : Nat} {omega : Omega}
    (homega : omega ∉ adapter.firstKAllModesBad n K)
    {j : Nat} (hj : j < K) (mode : PositiveFrequencyMode m) :
    dist ((adapter.endpointData n j mode).actualInitial omega)
        ((adapter.endpointData n j mode).referenceInitial omega) ≤
      (adapter.endpointData n j mode).stateDelta := by
  apply (adapter.endpointData n j mode).initial_state_near_on_good
  intro hbad
  apply homega
  unfold firstKAllModesBad
  exact Set.mem_iUnion_of_mem (⟨j, hj⟩, mode) hbad

/-- Finite union bound over both blocks and positive-frequency modes. The
factor `card * K` is explicit and may grow with the lattice size. -/
theorem firstKAllModesBad_probability_le_abs_cube
    (adapter : FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E
        Cref Ccoupling Cfailure)
    (n K : Nat) :
    mu.real (adapter.firstKAllModesBad n K) ≤
      (Fintype.card (PositiveFrequencyMode m) : Real) * (K : Real) *
        Cfailure * |g n| ^ 3 := by
  unfold firstKAllModesBad
  calc
    mu.real (⋃ index : Fin K × PositiveFrequencyMode m,
        (adapter.endpointData n index.1 index.2).bad) ≤
      ∑ index : Fin K × PositiveFrequencyMode m,
        mu.real (adapter.endpointData n index.1 index.2).bad :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _index : Fin K × PositiveFrequencyMode m,
        Cfailure * |g n| ^ 3 := by
      exact Finset.sum_le_sum fun index _ ↦
        (adapter.endpointData n index.1 index.2).bad_probability.trans
          (adapter.failureProbability_cubic n index.1 index.2)
    _ = (Fintype.card (PositiveFrequencyMode m) : Real) * (K : Real) *
        Cfailure * |g n| ^ 3 := by
      simp [Fintype.card_prod]
      ring

end FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter

end

end ArchonPhysics.PhyslibFPUTProbabilisticFullStateEnergyProfileAdapter
