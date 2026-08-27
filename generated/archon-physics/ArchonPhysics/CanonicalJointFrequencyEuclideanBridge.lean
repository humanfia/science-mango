import ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure
import ArchonPhysics.DenseJointCharacteristicFunctionCompactness

/-!
# Euclidean bridge for canonical joint frequency measures

The finite-volume joint frequency measures are naturally written on the plain
coordinate space `Fin 3 -> Real`. Characteristic-function compactness uses
the Hilbert-space model `EuclideanSpace Real (Fin 3)`. This module transports
both the per-site finite measures and their normalized probability measures
through the canonical `PiLp` homeomorphism.

The transport preserves mass and the common compact support. Euclidean
characteristic functions agree exactly with the existing plain joint Fourier
integrals, including at the rational frequency grid. No limit is asserted.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalJointFrequencyEuclideanBridge

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier
open ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure
open ArchonPhysics.DenseJointCharacteristicFunctionCompactness
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Canonical coordinate homeomorphism from plain frequency triples to the
Euclidean three-frequency space. -/
def plainFrequencyTripleToEuclidean :
    (Fin 3 -> Real) -> EuclideanSpace Real (Fin 3) :=
  (PiLp.homeomorph 2 (fun _r : Fin 3 => Real)).symm

theorem continuous_plainFrequencyTripleToEuclidean :
    Continuous plainFrequencyTripleToEuclidean :=
  (PiLp.homeomorph 2 (fun _r : Fin 3 => Real)).symm.continuous

theorem measurable_plainFrequencyTripleToEuclidean :
    Measurable plainFrequencyTripleToEuclidean :=
  continuous_plainFrequencyTripleToEuclidean.measurable

theorem injective_plainFrequencyTripleToEuclidean :
    Function.Injective plainFrequencyTripleToEuclidean :=
  (PiLp.homeomorph 2 (fun _r : Fin 3 => Real)).symm.injective

/-- Inverse coordinate map from Euclidean triples to plain triples. -/
def euclideanFrequencyTripleToPlain :
    EuclideanSpace Real (Fin 3) -> (Fin 3 -> Real) :=
  PiLp.homeomorph 2 (fun _r : Fin 3 => Real)

theorem continuous_euclideanFrequencyTripleToPlain :
    Continuous euclideanFrequencyTripleToPlain :=
  (PiLp.homeomorph 2 (fun _r : Fin 3 => Real)).continuous

theorem measurable_euclideanFrequencyTripleToPlain :
    Measurable euclideanFrequencyTripleToPlain :=
  continuous_euclideanFrequencyTripleToPlain.measurable

@[simp] theorem euclideanFrequencyTripleToPlain_plainFrequencyTripleToEuclidean
    (frequency : Fin 3 -> Real) :
    euclideanFrequencyTripleToPlain
        (plainFrequencyTripleToEuclidean frequency) = frequency :=
  (PiLp.homeomorph 2 (fun _r : Fin 3 => Real)).apply_symm_apply frequency

/-- Signed mismatch observable on Euclidean frequency triples. -/
def euclideanFrequencyTripleMismatch
    (sign : Fin 3 -> InteractionSign)
    (frequency : EuclideanSpace Real (Fin 3)) : Real :=
  frequencyTripleMismatch sign
    (euclideanFrequencyTripleToPlain frequency)

theorem continuous_euclideanFrequencyTripleMismatch
    (sign : Fin 3 -> InteractionSign) :
    Continuous (euclideanFrequencyTripleMismatch sign) := by
  unfold euclideanFrequencyTripleMismatch frequencyTripleMismatch
  apply continuous_finsetSum
  intro r _hr
  exact continuous_const.mul
    ((continuous_apply r).comp continuous_euclideanFrequencyTripleToPlain)

theorem measurable_euclideanFrequencyTripleMismatch
    (sign : Fin 3 -> InteractionSign) :
    Measurable (euclideanFrequencyTripleMismatch sign) :=
  (measurable_frequencyTripleMismatch sign).comp
    measurable_euclideanFrequencyTripleToPlain

theorem euclideanFrequencyTripleMismatch_comp_plainFrequencyTripleToEuclidean
    (sign : Fin 3 -> InteractionSign) :
    euclideanFrequencyTripleMismatch sign ∘
        plainFrequencyTripleToEuclidean =
      frequencyTripleMismatch sign := by
  funext frequency
  simp [euclideanFrequencyTripleMismatch]

@[simp] theorem plainFrequencyTripleToEuclidean_apply
    (frequency : Fin 3 -> Real) (r : Fin 3) :
    plainFrequencyTripleToEuclidean frequency r = frequency r := by
  rfl

/-- The real Euclidean inner product is the expected coordinate sum. -/
theorem real_inner_plainFrequencyTripleToEuclidean
    (frequency parameter : Fin 3 -> Real) :
    ⟪plainFrequencyTripleToEuclidean frequency,
      plainFrequencyTripleToEuclidean parameter⟫_ℝ =
      ∑ r, frequency r * parameter r := by
  rw [PiLp.inner_apply]
  change (∑ r, parameter r * frequency r) = _
  apply Finset.sum_congr rfl
  intro r _hr
  ring

/-- The Euclidean characteristic-function integrand is exactly the existing
plain joint Fourier character. -/
theorem exp_inner_plainFrequencyTripleToEuclidean_eq_fourierCharacter
    (parameter frequency : Fin 3 -> Real) :
    Complex.exp
        (⟪plainFrequencyTripleToEuclidean frequency,
          plainFrequencyTripleToEuclidean parameter⟫_ℝ * Complex.I) =
      frequencyTripleFourierCharacter parameter frequency := by
  rw [real_inner_plainFrequencyTripleToEuclidean]
  unfold frequencyTripleFourierCharacter
  congr 1
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  ring

/-- The per-site finite joint measure transported to Euclidean space. -/
def canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega) :
    FiniteMeasure (EuclideanSpace Real (Fin 3)) :=
  (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).map
    plainFrequencyTripleToEuclidean

/-- Signed pushforward of the Euclidean finite measure recovers the original
canonical scalar per-site mismatch finite measure. -/
theorem map_canonicalEuclideanJointFrequencyPerSiteFiniteMeasure_eq_collisionPerSite
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (n : Nat) (omega : Omega) :
    (canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
        ensemble n omega).map (euclideanFrequencyTripleMismatch sign) =
      canonicalCollisionPerSiteFiniteMeasure ensemble sign n omega := by
  apply FiniteMeasure.toMeasure_injective
  change
    ((canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega :
      Measure (Fin 3 -> Real)).map plainFrequencyTripleToEuclidean).map
        (euclideanFrequencyTripleMismatch sign) =
      (canonicalCollisionPerSiteFiniteMeasure ensemble sign n omega :
        Measure Real)
  rw [Measure.map_map
    (measurable_euclideanFrequencyTripleMismatch sign)
    measurable_plainFrequencyTripleToEuclidean]
  rw [euclideanFrequencyTripleMismatch_comp_plainFrequencyTripleToEuclidean]
  exact
    map_canonicalJointFrequencyPerSiteMeasure_eq_collisionPerSiteMeasure
      ensemble sign n omega

/-- The normalized plain joint probability measure transported to Euclidean
space. -/
def canonicalEuclideanNormalizedJointFrequencyMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega) :
    ProbabilityMeasure (EuclideanSpace Real (Fin 3)) :=
  ProbabilityMeasure.map
    (canonicalNormalizedJointFrequencyMeasure ensemble n omega)
    measurable_plainFrequencyTripleToEuclidean.aemeasurable

theorem canonicalEuclideanNormalizedJointFrequencyMeasure_isProbability
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega) :
    IsProbabilityMeasure
      (canonicalEuclideanNormalizedJointFrequencyMeasure
        ensemble n omega :
        Measure (EuclideanSpace Real (Fin 3))) := by
  infer_instance

/-- Underlying-measure form of the normalized Euclidean pushforward. -/
theorem canonicalEuclideanNormalizedJointFrequencyMeasure_toMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega) :
    (canonicalEuclideanNormalizedJointFrequencyMeasure ensemble n omega :
        Measure (EuclideanSpace Real (Fin 3))) =
      (canonicalNormalizedJointFrequencyMeasure ensemble n omega :
        Measure (Fin 3 -> Real)).map plainFrequencyTripleToEuclidean := by
  rfl

/-- Euclidean transport preserves the exact per-site total mass. -/
theorem canonicalEuclideanJointFrequencyPerSiteFiniteMeasure_mass_eq
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega) :
    (canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
        ensemble n omega).mass =
      (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).mass :=
  finiteMeasure_mass_map_of_measurable
    (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega)
    plainFrequencyTripleToEuclidean
    measurable_plainFrequencyTripleToEuclidean

/-- Image of the plain common support box in Euclidean coordinates. -/
def euclideanCollisionFrequencyTripleSupport :
    Set (EuclideanSpace Real (Fin 3)) :=
  Set.image plainFrequencyTripleToEuclidean collisionFrequencyTripleSupport

theorem euclideanCollisionFrequencyTripleSupport_isCompact :
    IsCompact euclideanCollisionFrequencyTripleSupport :=
  collisionFrequencyTripleSupport_isCompact.image
    continuous_plainFrequencyTripleToEuclidean

private theorem preimage_euclideanCollisionFrequencyTripleSupport :
    Set.preimage plainFrequencyTripleToEuclidean
        euclideanCollisionFrequencyTripleSupport =
      collisionFrequencyTripleSupport := by
  apply Set.ext
  intro frequency
  simp only [euclideanCollisionFrequencyTripleSupport, Set.mem_preimage,
    Set.mem_image]
  constructor
  · rintro ⟨source, hsource, heq⟩
    have : source = frequency :=
      injective_plainFrequencyTripleToEuclidean heq
    simpa [this] using hsource
  · intro hfrequency
    exact ⟨frequency, hfrequency, rfl⟩

/-- The transported per-site finite measure has no mass outside the common
Euclidean compact support. -/
theorem canonicalEuclideanJointFrequencyPerSiteFiniteMeasure_compl_support_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega) :
    (canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
        ensemble n omega : Measure (EuclideanSpace Real (Fin 3)))
        (euclideanCollisionFrequencyTripleSupportᶜ) = 0 := by
  unfold canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
  rw [FiniteMeasure.toMeasure_map]
  rw [Measure.map_apply measurable_plainFrequencyTripleToEuclidean
    euclideanCollisionFrequencyTripleSupport_isCompact.isClosed.measurableSet.compl]
  rw [Set.preimage_compl,
    preimage_euclideanCollisionFrequencyTripleSupport]
  exact
    canonicalJointFrequencyPerSiteFiniteMeasure_compl_uniformSupport_eq_zero
      ensemble n omega

/-- Nonzero normalized Euclidean transports retain the same compact support. -/
theorem canonicalEuclideanNormalizedJointFrequencyMeasure_compl_support_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega)
    (hmass :
      (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).mass ≠ 0) :
    (canonicalEuclideanNormalizedJointFrequencyMeasure
        ensemble n omega : Measure (EuclideanSpace Real (Fin 3)))
        (euclideanCollisionFrequencyTripleSupportᶜ) = 0 := by
  rw [canonicalEuclideanNormalizedJointFrequencyMeasure_toMeasure]
  rw [Measure.map_apply measurable_plainFrequencyTripleToEuclidean
    euclideanCollisionFrequencyTripleSupport_isCompact.isClosed.measurableSet.compl]
  rw [Set.preimage_compl,
    preimage_euclideanCollisionFrequencyTripleSupport]
  exact
    canonicalNormalizedJointFrequencyMeasure_compl_uniformSupport_eq_zero
      ensemble n omega hmass

/-- Euclidean Fourier integral of the transported finite measure is exactly
the existing plain per-site joint Fourier integral. -/
theorem integral_canonicalEuclideanJointFrequencyPerSiteFiniteMeasure_eq
    (ensemble : IIDMassPhaseEnsemble Omega)
    (parameter : Fin 3 -> Real) (n : Nat) (omega : Omega) :
    (∫ frequency : EuclideanSpace Real (Fin 3),
        Complex.exp
          (⟪frequency, plainFrequencyTripleToEuclidean parameter⟫_ℝ *
            Complex.I)
      ∂(canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
        ensemble n omega : Measure (EuclideanSpace Real (Fin 3)))) =
      canonicalJointFrequencyPerSiteFourierIntegral
        ensemble parameter n omega := by
  unfold canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
  rw [FiniteMeasure.toMeasure_map]
  rw [integral_map
    measurable_plainFrequencyTripleToEuclidean.aemeasurable (by fun_prop)]
  unfold canonicalJointFrequencyPerSiteFourierIntegral
  apply integral_congr_ae
  exact ae_of_all _ fun frequency =>
    exp_inner_plainFrequencyTripleToEuclidean_eq_fourierCharacter
      parameter frequency

/-- Characteristic function of the normalized Euclidean transport is the
plain normalized joint Fourier integral. -/
theorem charFun_canonicalEuclideanNormalizedJointFrequencyMeasure_eq_integral
    (ensemble : IIDMassPhaseEnsemble Omega)
    (parameter : Fin 3 -> Real) (n : Nat) (omega : Omega) :
    charFun
        (canonicalEuclideanNormalizedJointFrequencyMeasure
          ensemble n omega : Measure (EuclideanSpace Real (Fin 3)))
        (plainFrequencyTripleToEuclidean parameter) =
      ∫ frequency : Fin 3 -> Real,
        frequencyTripleFourierCharacter parameter frequency
      ∂(canonicalNormalizedJointFrequencyMeasure ensemble n omega :
        Measure (Fin 3 -> Real)) := by
  rw [charFun_apply,
    canonicalEuclideanNormalizedJointFrequencyMeasure_toMeasure]
  rw [integral_map
    measurable_plainFrequencyTripleToEuclidean.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  exact ae_of_all _ fun frequency =>
    exp_inner_plainFrequencyTripleToEuclidean_eq_fourierCharacter
      parameter frequency

/-- Exact finite-volume Euclidean characteristic-function formula. -/
theorem charFun_canonicalEuclideanNormalizedJointFrequencyMeasure_eq_mass_inv_mul
    (ensemble : IIDMassPhaseEnsemble Omega)
    (parameter : Fin 3 -> Real) (n : Nat) (omega : Omega)
    (hmass :
      (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).mass ≠ 0) :
    charFun
        (canonicalEuclideanNormalizedJointFrequencyMeasure
          ensemble n omega : Measure (EuclideanSpace Real (Fin 3)))
        (plainFrequencyTripleToEuclidean parameter) =
      (((canonicalJointFrequencyPerSiteFiniteMeasure
        ensemble n omega).mass⁻¹ : NNReal) : Real) *
        canonicalJointFrequencyPerSiteFourierIntegral
          ensemble parameter n omega := by
  rw [charFun_canonicalEuclideanNormalizedJointFrequencyMeasure_eq_integral]
  exact integral_canonicalNormalizedJointFrequencyMeasure_eq_mass_inv_mul
    ensemble parameter n omega hmass

/-- The dense rational-grid parameter is exactly the Euclidean transport of
its coordinatewise real coercion. -/
theorem rationalFrequencyTriple_eq_plainFrequencyTripleToEuclidean
    (q : Fin 3 -> Rat) :
    rationalFrequencyTriple q =
      plainFrequencyTripleToEuclidean (fun r => (q r : Real)) := by
  rfl

/-- Rational-grid specialization for dense characteristic-function
compactness. -/
theorem charFun_canonicalEuclideanNormalizedJointFrequencyMeasure_rational_eq
    (ensemble : IIDMassPhaseEnsemble Omega)
    (q : Fin 3 -> Rat) (n : Nat) (omega : Omega)
    (hmass :
      (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).mass ≠ 0) :
    charFun
        (canonicalEuclideanNormalizedJointFrequencyMeasure
          ensemble n omega : Measure (EuclideanSpace Real (Fin 3)))
        (rationalFrequencyTriple q) =
      (((canonicalJointFrequencyPerSiteFiniteMeasure
        ensemble n omega).mass⁻¹ : NNReal) : Real) *
        canonicalJointFrequencyPerSiteFourierIntegral
          ensemble (fun r => (q r : Real)) n omega := by
  rw [rationalFrequencyTriple_eq_plainFrequencyTripleToEuclidean]
  exact
    charFun_canonicalEuclideanNormalizedJointFrequencyMeasure_eq_mass_inv_mul
      ensemble (fun r => (q r : Real)) n omega hmass

/-- Varying canonical-volume normalized Euclidean transports are tight under
the existing finite-volume nonzero-mass hypotheses. -/
theorem canonicalEuclideanNormalizedJointFrequencyMeasure_range_isTight
    (ensemble : IIDMassPhaseEnsemble Omega)
    (size : Nat -> Nat) (omega : Nat -> Omega)
    (sign : Fin 3 -> InteractionSign)
    (hN : ∀ j, 3 <= size j + 2)
    (hsimple : ∀ j, SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := size j + 2) (omega j)))) :
    IsTightMeasureSet (Set.range fun j =>
      (canonicalEuclideanNormalizedJointFrequencyMeasure
        ensemble (size j) (omega j) :
        Measure (EuclideanSpace Real (Fin 3)))) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro epsilon hepsilon
  refine ⟨euclideanCollisionFrequencyTripleSupport,
    euclideanCollisionFrequencyTripleSupport_isCompact, ?_⟩
  intro mu hmu
  rcases hmu with ⟨j, rfl⟩
  rw [canonicalEuclideanNormalizedJointFrequencyMeasure_compl_support_eq_zero
    ensemble (size j) (omega j)
      (canonicalJointFrequencyPerSiteFiniteMeasure_mass_ne_zero
        ensemble sign (size j) (omega j) (hN j) (hsimple j))]
  exact hepsilon.le

end

end ArchonPhysics.CanonicalJointFrequencyEuclideanBridge
