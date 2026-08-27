import ArchonPhysics.ActualThreeMassAllDistinctAnnealedFiniteVolumeTrace
import ArchonPhysics.ActualThreeMassLiftedPerSiteBudget

/-!
# Annealed finite-volume budgets for the all-distinct trace

The exact finite-volume complement formula is combined here with conditional
three-mass estimates.  The first theorem is a reusable Tonelli adapter.  The
second specializes it to the genuine all-distinct collision weight and the
actual lifted frequency chart, retaining the regular coarea budget and the
sinc-squared-weighted bad budget under the complementary iid integral.

This is an annealed statement.  It neither asserts a density for an atomic
fixed realization nor supplies the still-required volume-uniform bounds on
the two conditional budgets.
-/

namespace ArchonPhysics.ActualThreeMassAllDistinctAnnealedFiniteVolumeBudget

open ArchonPhysics
open ArchonPhysics.ActualLiftedMismatchSmallBall
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedFiniteVolumeTrace
open ArchonPhysics.ActualThreeMassLiftedPerSiteBudget
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.IIDMassTripleFiniteVolumeReconstruction
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A pointwise conditional bound transports through the exact iid-complement
formula without any measurability or supremum relaxation of the budget. -/
theorem lintegral_allDistinctPerSiteBroadenedTrace_le_of_conditional_bound
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N)
    (h₀₁ : site₀ ≠ site₁) (h₀₂ : site₀ ≠ site₂)
    (h₁₂ : site₁ ≠ site₂)
    (sign : Fin 3 → InteractionSign) {T : Real} (hT : 0 < T)
    (bound : FiniteMassVector
      (finiteVolumeMassComplement site₀ site₁ site₂) → ENNReal)
    (hbound : ∀ rest,
      actualThreeMassAllDistinctConditionalBroadenedChildMeasure
          (finiteEnvironmentPositiveMassConfig
            site₀ site₁ site₂ rest)
          site₀ site₁ site₂ sign T Set.univ ≤ bound rest) :
    (∫⁻ omega,
      allDistinctPerSiteBroadenedTrace
        (ensemble.restrictPositiveMass (N := N) omega) sign T
      ∂ensemble.probability) ≤
      ∫⁻ rest, bound rest
        ∂iidFiniteMassVectorLaw
          (finiteVolumeMassComplement site₀ site₁ site₂) := by
  rw [lintegral_allDistinctPerSiteBroadenedTrace_eq_complement
    ensemble site₀ site₁ site₂ h₀₁ h₀₂ h₁₂ sign hT]
  exact lintegral_mono hbound

/-- Actual-model conditional coarea and weighted-bad budgets, integrated over
the iid finite-volume complement.  Every chart, Jacobian, and collision
weight in the hypotheses is the one built from the reconstructed physical
mass matrix. -/
theorem lintegral_allDistinctPerSiteBroadenedTrace_le_of_actual_budgets
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N)
    (h₀₁ : site₀ ≠ site₁) (h₀₂ : site₀ ≠ site₂)
    (h₁₂ : site₁ ≠ site₂)
    (sign : Fin 3 → InteractionSign) {T : Real} (hT : 0 < T)
    (weightCeiling : FiniteMassVector
        (finiteVolumeMassComplement site₀ site₁ site₂) →
      OrderedModeTriple N → ENNReal)
    (good : FiniteMassVector
        (finiteVolumeMassComplement site₀ site₁ site₂) →
      OrderedModeTriple N → Set MassTriple)
    (detLower : FiniteMassVector
        (finiteVolumeMassComplement site₀ site₁ site₂) →
      OrderedModeTriple N → Real)
    (regularCeiling badCeiling : FiniteMassVector
        (finiteVolumeMassComplement site₀ site₁ site₂) → ENNReal)
    (hweight : ∀ rest modes, ∀ᵐ point ∂iidMassTripleLaw,
      actualThreeMassAllDistinctTupleWeight
          (finiteEnvironmentPositiveMassConfig
            site₀ site₁ site₂ rest)
          site₀ site₁ site₂ modes point ≤ weightCeiling rest modes)
    (hgood : ∀ rest modes, MeasurableSet (good rest modes))
    (hderivative : ∀ rest modes point, point ∈ good rest modes →
      HasFDerivWithinAt
        (actualThreeMassLiftedFrequencyChart
          (finiteEnvironmentPositiveMassConfig
            site₀ site₁ site₂ rest)
          site₀ site₁ site₂ sign modes)
        (actualThreeMassLiftedFrequencyJacobian
          (finiteEnvironmentPositiveMassConfig
            site₀ site₁ site₂ rest)
          site₀ site₁ site₂ sign modes point)
        (good rest modes) point)
    (hinjective : ∀ rest modes, Set.InjOn
      (actualThreeMassLiftedFrequencyChart
        (finiteEnvironmentPositiveMassConfig
          site₀ site₁ site₂ rest)
        site₀ site₁ site₂ sign modes) (good rest modes))
    (hdetLower : ∀ rest modes, 0 < detLower rest modes)
    (hdet : ∀ rest modes point, point ∈ good rest modes →
      detLower rest modes ≤
        |(actualThreeMassLiftedFrequencyJacobian
          (finiteEnvironmentPositiveMassConfig
            site₀ site₁ site₂ rest)
          site₀ site₁ site₂ sign modes point).det|)
    (hregular : ∀ rest,
      actualThreeMassRegularPerSiteBudget
          (weightCeiling rest) (detLower rest) ≤ regularCeiling rest)
    (hbad : ∀ rest,
      actualThreeMassWeightedBadPerSiteBudget
          (finiteEnvironmentPositiveMassConfig
            site₀ site₁ site₂ rest)
          site₀ site₁ site₂ sign
          (actualThreeMassAllDistinctTupleWeight
            (finiteEnvironmentPositiveMassConfig
              site₀ site₁ site₂ rest)
            site₀ site₁ site₂)
          (good rest) T ≤ badCeiling rest) :
    (∫⁻ omega,
      allDistinctPerSiteBroadenedTrace
        (ensemble.restrictPositiveMass (N := N) omega) sign T
      ∂ensemble.probability) ≤
      ∫⁻ rest,
        regularCeiling rest *
            (ENNReal.ofReal (Real.sqrt 5) *
              ENNReal.ofReal (Real.sqrt 5)) +
          badCeiling rest
        ∂iidFiniteMassVectorLaw
          (finiteVolumeMassComplement site₀ site₁ site₂) := by
  apply lintegral_allDistinctPerSiteBroadenedTrace_le_of_conditional_bound
    ensemble site₀ site₁ site₂ h₀₁ h₀₂ h₁₂ sign hT
  intro rest
  rw [actualThreeMassAllDistinctConditionalBroadenedChildMeasure_univ_eq
    (finiteEnvironmentPositiveMassConfig site₀ site₁ site₂ rest)
    (finiteEnvironmentPositiveMassConfig_mass_mem_support
      site₀ site₁ site₂ rest)
    site₀ site₁ site₂ sign hT]
  rw [← volume_childFrequencySquare]
  exact actualThreeMassConditionalPerSiteBroadenedChild_apply_le_of_budgets
    (finiteEnvironmentPositiveMassConfig site₀ site₁ site₂ rest)
    site₀ site₁ site₂ sign
    (actualThreeMassAllDistinctTupleWeight
      (finiteEnvironmentPositiveMassConfig site₀ site₁ site₂ rest)
      site₀ site₁ site₂)
    (weightCeiling rest) (hweight rest) (good rest) (hgood rest)
    (hderivative rest) (hinjective rest) (detLower rest) (hdetLower rest)
    (hdet rest) hT (regularCeiling rest) (badCeiling rest)
    (hregular rest) (hbad rest)
    (measurableSet_childFrequencySquare (Real.sqrt 5))

end

end ArchonPhysics.ActualThreeMassAllDistinctAnnealedFiniteVolumeBudget
