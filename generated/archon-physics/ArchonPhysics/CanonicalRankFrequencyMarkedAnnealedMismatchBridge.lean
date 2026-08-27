import ArchonPhysics.AnnealedFiniteMeasureWeakLimit
import ArchonPhysics.CanonicalRankFrequencyMarkedVolumeDominationBridge
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Annealed canonical marked mismatch bridge

This module constructs the actual barycenter of the random canonical marked
mismatch measure.  The construction is Giry-measurable, finite, and converges
weakly to the deterministic canonical mismatch target.

An annealed volume estimate therefore yields volume domination, a bounded
Radon--Nikodym density, and atomlessness for that deterministic target.  No
statement in this file upgrades an annealed estimate to a realization-wise
estimate: such an upgrade would require a separate disintegration or
concentration argument.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedMismatchBridge

open ArchonPhysics
open ArchonPhysics.AnnealedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier
open ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit
open ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedCompactness
open ArchonPhysics.CanonicalRankFrequencyMarkedConvergenceInProbability
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedProbabilityJointLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.FiniteMeasureVanishingErrorLInfinityWeakLimit
open ArchonPhysics.FiniteMeasureWeakLimitDominationDensity
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassMeasurableModeCoupling
open ArchonPhysics.RandomMassPositiveCollisionData
open Filter MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## Giry measurability and a uniform mass ceiling -/

/-- The unnormalized positive weighted rank--frequency measure is measurable
for the Giry sigma algebra.  This is stronger than merely being strongly
measurable for a chosen weak pseudometric. -/
theorem measurable_positiveWeightedRankFrequencyTripleMeasure_sample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] :
    Measurable fun omega ↦
      positiveWeightedRankFrequencyTripleMeasure
        (ensemble.restrictPositiveMass (N := N) omega) := by
  classical
  unfold positiveWeightedRankFrequencyTripleMeasure
  apply Finset.measurable_sum
  intro modes _hmodes
  apply Measurable.ite
    (measurableSet_isPositiveOrderedTripleSample ensemble modes)
  · have hcoefficient : Measurable fun omega ↦
        ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight
          (ensemble.restrictPositiveMass (N := N) omega) modes) :=
      (measurable_orderedNormalizedInteractionWeightSample
        ensemble modes).ennreal_ofReal
    have hdirac : Measurable fun omega ↦
        Measure.dirac (orderedRankFrequencyTriple
          (ensemble.restrictPositiveMass (N := N) omega) modes) :=
      Measure.measurable_dirac.comp
        (measurable_orderedRankFrequencyTriple_sample ensemble modes)
    refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact hcoefficient.mul ((Measure.measurable_coe hA).comp hdirac)
  · exact measurable_const

/-- Direct Giry measurability of the canonical per-site marked finite
measure. -/
theorem measurable_toMeasure_canonicalRankFrequencyTriplePerSiteFiniteMeasure
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) :
    Measurable fun omega ↦
      (canonicalRankFrequencyTriplePerSiteFiniteMeasure
        ensemble n omega : Measure (Fin 3 → RankFrequencyMark)) := by
  have hraw :=
    measurable_positiveWeightedRankFrequencyTripleMeasure_sample
      (ensemble := ensemble) (N := n + 2)
  refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
  simp only [canonicalRankFrequencyTriplePerSiteFiniteMeasure,
    positiveWeightedRankFrequencyTripleFiniteMeasure]
  exact measurable_const.mul ((Measure.measurable_coe hA).comp hraw)

/-- A deterministic finite ceiling for every canonical marked per-site
measure on the probability-one simple-spectrum event. -/
def canonicalMarkedAnnealedMassCeiling : NNReal :=
  ⟨canonicalCollisionPerSiteMassCeiling,
    canonicalCollisionPerSiteMassCeiling_nonneg⟩

theorem canonicalMarkedPerSiteSequence_mass_le_ae (n : Nat) :
    ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
      (canonicalMarkedPerSiteSequence n omega).mass ≤
        canonicalMarkedAnnealedMassCeiling := by
  filter_upwards
    [canonicalJointFrequencyVolumes_simpleOrderedSpectrum_ae
      canonicalIIDMassPhaseEnsemble] with omega hsimple
  rw [canonicalRankFrequencyTriplePerSiteFiniteMeasure_mass_eq_joint]
  rw [← NNReal.coe_le_coe]
  exact canonicalJointFrequencyPerSiteFiniteMeasure_mass_le
    canonicalIIDMassPhaseEnsemble (fun _ ↦ InteractionSign.plus)
      (n + 1) omega (hsimple n)

/-- Giry measurability survives the continuous mismatch pushforward. -/
theorem measurable_toMeasure_canonicalMarkedMismatchPerSiteSequence
    (sign : Fin 3 → InteractionSign) (n : Nat) :
    Measurable fun omega ↦
      (((canonicalMarkedPerSiteSequence n omega).map
        (markedFrequencyMismatch sign) : FiniteMeasure Real) : Measure Real) := by
  have hmap := Measure.measurable_map (markedFrequencyMismatch sign)
    (measurable_markedFrequencyMismatch sign)
  exact hmap.comp
    (measurable_toMeasure_canonicalRankFrequencyTriplePerSiteFiniteMeasure
      canonicalIIDMassPhaseEnsemble (n + 1))

theorem canonicalMarkedMismatchPerSiteSequence_mass_le_ae
    (sign : Fin 3 → InteractionSign) (n : Nat) :
    ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
      ((canonicalMarkedPerSiteSequence n omega).map
        (markedFrequencyMismatch sign)).mass ≤
        canonicalMarkedAnnealedMassCeiling := by
  filter_upwards [canonicalMarkedPerSiteSequence_mass_le_ae n]
    with omega hmass
  rw [finiteMeasure_mass_map_of_measurable _ _
    (measurable_markedFrequencyMismatch sign)]
  exact hmass

/-! ## The legal annealed mismatch measure and its deterministic limit -/

/-- The finite-volume annealed mismatch measure: the Giry barycenter of the
random canonical mismatch pushforward. -/
def canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure
    (sign : Fin 3 → InteractionSign) (n : Nat) : FiniteMeasure Real :=
  annealedFiniteMeasure RandomEnsemble.canonicalLaw
    (fun omega ↦ (canonicalMarkedPerSiteSequence n omega).map
      (markedFrequencyMismatch sign))
    (measurable_toMeasure_canonicalMarkedMismatchPerSiteSequence sign n)
    canonicalMarkedAnnealedMassCeiling
    (canonicalMarkedMismatchPerSiteSequence_mass_le_ae sign n)

/-- The deterministic canonical marked mismatch target. -/
abbrev canonicalMarkedMismatchPerSiteLimitFiniteMeasure
    (sign : Fin 3 → InteractionSign) : FiniteMeasure Real :=
  (canonicalRankFrequencyMarkedPerSiteMeasureLimit
    canonicalIIDMassPhaseEnsemble).map (markedFrequencyMismatch sign)

/-- Evaluation of the annealed measure is exactly the expectation of the
finite-volume random measure evaluation.  This identity is annealed only. -/
theorem canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure_apply
    (sign : Fin 3 → InteractionSign) (n : Nat)
    {A : Set Real} (hA : MeasurableSet A) :
    (canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure sign n :
      Measure Real) A =
      ∫⁻ omega,
        ((((canonicalMarkedPerSiteSequence n omega).map
          (markedFrequencyMismatch sign) : FiniteMeasure Real) :
            Measure Real) A) ∂ RandomEnsemble.canonicalLaw := by
  exact annealedFiniteMeasure_apply RandomEnsemble.canonicalLaw
    (fun omega ↦ (canonicalMarkedPerSiteSequence n omega).map
      (markedFrequencyMismatch sign))
    (measurable_toMeasure_canonicalMarkedMismatchPerSiteSequence sign n)
    canonicalMarkedAnnealedMassCeiling
    (canonicalMarkedMismatchPerSiteSequence_mass_le_ae sign n) hA

/-- The annealed mismatch measures converge weakly to the same deterministic
target as almost every realization. -/
theorem canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure_tendsto :
    ∀ sign : Fin 3 → InteractionSign,
      Tendsto
        (canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure sign)
        atTop
        (nhds (canonicalMarkedMismatchPerSiteLimitFiniteMeasure sign)) := by
  intro sign
  have hlimit :
      ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
        Tendsto
          (fun n ↦ (canonicalMarkedPerSiteSequence n omega).map
            (markedFrequencyMismatch sign))
          atTop
          (nhds (canonicalMarkedMismatchPerSiteLimitFiniteMeasure sign)) := by
    filter_upwards
      [canonicalRankFrequencyTriplePerSiteFiniteMeasure_tendsto_limit_ae]
      with omega homega
    exact FiniteMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n ↦ canonicalMarkedPerSiteSequence n omega)
      (canonicalRankFrequencyMarkedPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble)
      (by simpa only [canonicalMarkedPerSiteSequence] using homega)
      (continuous_markedFrequencyMismatch sign)
  exact annealedFiniteMeasure_tendsto_of_tendsto_ae_of_mass_le
    RandomEnsemble.canonicalLaw
    (fun n omega ↦ (canonicalMarkedPerSiteSequence n omega).map
      (markedFrequencyMismatch sign))
    (canonicalMarkedMismatchPerSiteLimitFiniteMeasure sign)
    (measurable_toMeasure_canonicalMarkedMismatchPerSiteSequence sign)
    canonicalMarkedAnnealedMassCeiling
    (canonicalMarkedMismatchPerSiteSequence_mass_le_ae sign)
    hlimit

/-! ## Honest annealed volume input and deterministic consequences -/

/-- A volume estimate for the *annealed* canonical measures.  It intentionally
contains no realization-wise assertion. -/
structure CanonicalMarkedMismatchAnnealedVanishingErrorVolumeDomination
    (sign : Fin 3 → InteractionSign) where
  constant : ENNReal
  constant_ne_top : constant ≠ ∞
  error : Nat → ENNReal
  error_tendsto_zero : Tendsto error atTop (nhds 0)
  bound : ∀ n : Nat, ∀ A : Set Real, MeasurableSet A →
    (canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure sign n :
      Measure Real) A ≤
      constant * (volume : Measure Real) A + error n

/-- An externally constructed annealed upper measure can supply the canonical
annealed estimate.  The required measure comparison is precisely the missing
model-side aggregation/identification input; it is not inferred from a
realization-wise statement. -/
def CanonicalMarkedMismatchAnnealedVanishingErrorVolumeDomination.of_dominatingSequence
    {sign : Fin 3 → InteractionSign}
    (constant : ENNReal) (constant_ne_top : constant ≠ ∞)
    (error : Nat → ENNReal)
    (error_tendsto_zero : Tendsto error atTop (nhds 0))
    (upper : Nat → FiniteMeasure Real)
    (hcanonical : ∀ n,
      (canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure sign n :
        Measure Real) ≤ (upper n : Measure Real))
    (hupper : ∀ n : Nat, ∀ A : Set Real, MeasurableSet A →
      (upper n : Measure Real) A ≤
        constant * (volume : Measure Real) A + error n) :
    CanonicalMarkedMismatchAnnealedVanishingErrorVolumeDomination sign where
  constant := constant
  constant_ne_top := constant_ne_top
  error := error
  error_tendsto_zero := error_tendsto_zero
  bound n A hA := (hcanonical n A).trans (hupper n A hA)

/-- An annealed vanishing-error estimate closes to exact Lebesgue domination
of the deterministic canonical mismatch target. -/
theorem canonicalMarkedMismatchPerSiteLimit_le_smul_volume
    {sign : Fin 3 → InteractionSign}
    (domination :
      CanonicalMarkedMismatchAnnealedVanishingErrorVolumeDomination sign) :
    (canonicalMarkedMismatchPerSiteLimitFiniteMeasure sign : Measure Real) ≤
      domination.constant • (volume : Measure Real) := by
  exact finiteMeasure_le_smul_of_tendsto_of_apply_le_add_vanishingError
    (canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure sign)
    (canonicalMarkedMismatchPerSiteLimitFiniteMeasure sign)
    (canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure_tendsto sign)
    volume domination.constant domination.constant_ne_top
    domination.error domination.error_tendsto_zero domination.bound

/-- Fixed-open-set trace of the annealed estimate on the deterministic
canonical target. -/
theorem canonicalMarkedMismatchPerSiteLimit_isOpen_le
    {sign : Fin 3 → InteractionSign}
    (domination :
      CanonicalMarkedMismatchAnnealedVanishingErrorVolumeDomination sign)
    {G : Set Real} (_hG : IsOpen G) :
    (canonicalMarkedMismatchPerSiteLimitFiniteMeasure sign : Measure Real) G ≤
      domination.constant * (volume : Measure Real) G := by
  simpa only [Measure.smul_apply, smul_eq_mul] using
    canonicalMarkedMismatchPerSiteLimit_le_smul_volume domination G

/-- The deterministic canonical mismatch target is absolutely continuous
with respect to Lebesgue measure under the annealed estimate. -/
theorem canonicalMarkedMismatchPerSiteLimit_absolutelyContinuous_volume
    {sign : Fin 3 → InteractionSign}
    (domination :
      CanonicalMarkedMismatchAnnealedVanishingErrorVolumeDomination sign) :
    (canonicalMarkedMismatchPerSiteLimitFiniteMeasure sign : Measure Real) ≪
      (volume : Measure Real) :=
  (canonicalMarkedMismatchPerSiteLimit_le_smul_volume domination).absolutelyContinuous.trans
    Measure.smul_absolutelyContinuous

/-- The deterministic target has an `L∞`-type density bounded by the same
annealed constant. -/
theorem canonicalMarkedMismatchPerSiteLimit_exists_density_le
    {sign : Fin 3 → InteractionSign}
    (domination :
      CanonicalMarkedMismatchAnnealedVanishingErrorVolumeDomination sign) :
    ∃ density : Real → ENNReal,
      Measurable density ∧
      density ≤ᵐ[(volume : Measure Real)]
        (fun _ ↦ domination.constant) ∧
      (volume : Measure Real).withDensity density =
        (canonicalMarkedMismatchPerSiteLimitFiniteMeasure sign :
          Measure Real) :=
  exists_density_le_const_of_le_smul _ volume _
    (canonicalMarkedMismatchPerSiteLimit_le_smul_volume domination)

/-- Every singleton, in particular exact resonance, is null for the
deterministic canonical mismatch target. -/
theorem canonicalMarkedMismatchPerSiteLimit_singleton_eq_zero
    {sign : Fin 3 → InteractionSign}
    (domination :
      CanonicalMarkedMismatchAnnealedVanishingErrorVolumeDomination sign)
    (x : Real) :
    (canonicalMarkedMismatchPerSiteLimitFiniteMeasure sign : Measure Real)
      ({x} : Set Real) = 0 :=
  canonicalMarkedMismatchPerSiteLimit_absolutelyContinuous_volume domination
    (by simp)

end

end ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedMismatchBridge
