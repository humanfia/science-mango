import ArchonPhysics.PhyslibFPUTFullStateEndpointCertificate
import ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing

/-!
# Full-state endpoint couplings give all-mode energy-profile control

This module connects the full-state endpoint coupling theorem to the
compatibility-free, vector-valued FPUT kinetic certificate.  There is one
`FullStateEndpointPropagationData` for every block and every positive
frequency mode.  Its proved second-moment error is multiplied by the mode
frequency, exactly as required for modal energy.

The only uniform coupling input is a frequency-weighted bound on the
already-derived endpoint cost `2 * M * delta`.  This form is deliberately
transparent: it is the direct hypothesis needed to pass from pointwise
modal moment control to the finite-dimensional sup norm.  No scalar
collision map or collision-compatibility assumption occurs here.
-/

namespace ArchonPhysics.PhyslibFPUTFullStateEnergyProfileAdapter

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing
open ArchonPhysics.PhyslibFPUTFullStateEndpointCertificate

noncomputable section

/-- Second moment of the actual endpoint law carried by a full-state
coupling datum. -/
def fullStateActualSecondMoment
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {mu : Measure Omega} {M : Real}
    (data : FullStateEndpointPropagationData Omega X mu M)
    (endpoint : Nat) : Real :=
  ∫ z, Complex.normSq z ∂
    (data.toAmplitudeCouplingRestartCertificate.actualLaw endpoint)

/-- Second moment of the reference endpoint law carried by a full-state
coupling datum. -/
def fullStateReferenceSecondMoment
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {mu : Measure Omega} {M : Real}
    (data : FullStateEndpointPropagationData Omega X mu M)
    (endpoint : Nat) : Real :=
  ∫ z, Complex.normSq z ∂
    (data.toAmplitudeCouplingRestartCertificate.referenceLaw endpoint)

/-- The initial second-moment estimate extracted from the full-state
endpoint theorem. -/
theorem fullState_initial_secondMoment_error
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {M : Real}
    (data : FullStateEndpointPropagationData Omega X mu M) :
    |fullStateActualSecondMoment data 0 -
        fullStateReferenceSecondMoment data 0| ≤
      2 * M * data.initialDelta := by
  simpa [fullStateActualSecondMoment, fullStateReferenceSecondMoment] using
    (data.endpoint_second_fourth_moment_errors).1.1

/-- The propagated second-moment estimate extracted from the full-state
endpoint theorem. -/
theorem fullState_final_secondMoment_error
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {M : Real}
    (data : FullStateEndpointPropagationData Omega X mu M) :
    |fullStateActualSecondMoment data 1 -
        fullStateReferenceSecondMoment data 1| ≤
      2 * M * data.finalDelta := by
  simpa [fullStateActualSecondMoment, fullStateReferenceSecondMoment] using
    (data.endpoint_second_fourth_moment_errors).2.1

/-- All-positive-mode full-state endpoint data for every kinetic block.

The four identification fields say exactly which physical moments are the
actual and canonical reference modal energies.  The two weighted-cost
fields are uniform estimates, not endpoint-control conclusions: the latter
are proved below from the full-state moment theorem and the Pi sup norm.
-/
structure FPUTFullStateEnergyProfileBlockwiseAdapter
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (M : Real)
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta T : Real)
    (g : Nat → Real)
    (E : Nat → Nat → PositiveEnergyProfile m)
    (Cref Ccoupling : Real) where
  endpointData : ∀ _n _j (_mode : PositiveFrequencyMode m),
    FullStateEndpointPropagationData Omega X mu M
  referenceEnergy : Nat → Nat → PositiveEnergyProfile m
  Cref_nonneg : 0 ≤ Cref
  Ccoupling_nonneg : 0 ≤ Ccoupling
  referenceEnergy_nonneg : ∀ n j mode,
    0 ≤ referenceEnergy n j mode
  couplingWindow : ∀ n, |g n| ≤ 1
  actualInitialEnergy : ∀ n j mode,
    E n j mode = modeFrequency m mode *
      fullStateActualSecondMoment (endpointData n j mode) 0
  actualFinalEnergy : ∀ n j mode,
    E n (j + 1) mode = modeFrequency m mode *
      fullStateActualSecondMoment (endpointData n j mode) 1
  referenceInitialEnergy : ∀ n j mode,
    canonicalHaarEnergyBlockInitial m (referenceEnergy n j) mode =
      modeFrequency m mode *
        fullStateReferenceSecondMoment (endpointData n j mode) 0
  referenceFinalEnergy : ∀ n j mode,
    canonicalHaarEnergyBlockFinal m kappa beta (g n)
        (referenceEnergy n j) T mode =
      modeFrequency m mode *
        fullStateReferenceSecondMoment (endpointData n j mode) 1
  initialFrequencyWeightedCost : ∀ n j (mode : PositiveFrequencyMode m),
    modeFrequency m mode *
        (2 * M * (endpointData n j mode).initialDelta) ≤
      Ccoupling * |g n| ^ 3
  finalFrequencyWeightedCost : ∀ n j (mode : PositiveFrequencyMode m),
    modeFrequency m mode *
        (2 * M * (endpointData n j mode).finalDelta) ≤
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

namespace FPUTFullStateEnergyProfileBlockwiseAdapter

variable {Omega X : Type*} [MeasurableSpace Omega]
  [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {mu : Measure Omega} [IsProbabilityMeasure mu] {M : Real}
  {N : Nat} [NeZero N]
  {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
  {g : Nat → Real}
  {E : Nat → Nat → PositiveEnergyProfile m}
  {Cref Ccoupling : Real}

/-- Full-state endpoint moment control implies the initial all-mode
sup-norm estimate. -/
theorem initial_endpoint_control
    (adapter : FPUTFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E Cref Ccoupling)
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
      (fullState_initial_secondMoment_error (adapter.endpointData n j mode))
      mode.property.le).trans
    (adapter.initialFrequencyWeightedCost n j mode)

/-- Full-state endpoint moment control implies the propagated all-mode
sup-norm estimate. -/
theorem final_endpoint_control
    (adapter : FPUTFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E Cref Ccoupling)
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
      (fullState_final_secondMoment_error (adapter.endpointData n j mode))
      mode.property.le).trans
    (adapter.finalFrequencyWeightedCost n j mode)

/-- Construct the compatibility-free canonical Haar energy-profile
certificate.  Both endpoint-control fields are theorems of the full-state
coupling data. -/
def toCanonicalHaarEnergyProfileBlockwiseCertificate
    (adapter : FPUTFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E Cref Ccoupling) :
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

@[simp] theorem toCertificate_referenceEnergy
    (adapter : FPUTFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E Cref Ccoupling) :
    adapter.toCanonicalHaarEnergyProfileBlockwiseCertificate.referenceEnergy =
      adapter.referenceEnergy := rfl

/-- The constructed certificate's initial profile control is exactly the
one derived above. -/
theorem toCertificate_initial_endpoint_control
    (adapter : FPUTFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E Cref Ccoupling)
    (n j : Nat) :
    ‖E n j - canonicalHaarEnergyBlockInitial m
        (adapter.referenceEnergy n j)‖ ≤
      Ccoupling * |g n| ^ 3 :=
  adapter.toCanonicalHaarEnergyProfileBlockwiseCertificate
    |>.initial_endpoint_control n j

/-- The constructed certificate's final profile control is exactly the one
derived above. -/
theorem toCertificate_final_endpoint_control
    (adapter : FPUTFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E Cref Ccoupling)
    (n j : Nat) :
    ‖E n (j + 1) - canonicalHaarEnergyBlockFinal m kappa beta (g n)
        (adapter.referenceEnergy n j) T‖ ≤
      Ccoupling * |g n| ^ 3 :=
  adapter.toCanonicalHaarEnergyProfileBlockwiseCertificate
    |>.final_endpoint_control n j

end FPUTFullStateEnergyProfileBlockwiseAdapter

end

end ArchonPhysics.PhyslibFPUTFullStateEnergyProfileAdapter
