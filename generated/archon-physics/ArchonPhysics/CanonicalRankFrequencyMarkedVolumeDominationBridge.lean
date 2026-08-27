import ArchonPhysics.CanonicalRankFrequencyMarkedJointLimitSmallBallBridge
import ArchonPhysics.FiniteMeasureVanishingErrorLInfinityWeakLimit
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Volume domination and density for the canonical marked mismatch limit

This module strengthens the vanishing-error weak-limit closure from measure
domination to a Radon--Nikodym certificate.  It then packages the remaining
canonical model input as one estimate on arbitrary measurable mismatch sets.

On a single probability-one event, assume

`mu_N A <= C * volume A + error_N`

for every volume and every measurable `A`, with `error_N -> 0`.  The canonical
mismatch limit is then dominated by `C * volume`, has a measurable density
bounded by `C` almost everywhere, and has no atoms.  The same input is also
converted to the earlier linear small-ball interface, with the sharp
one-dimensional interval factor `2`.
-/

open scoped Topology ENNReal BoundedContinuousFunction

namespace ArchonPhysics.FiniteMeasureWeakLimitDominationDensity

open ArchonPhysics.FiniteMeasureVanishingErrorLInfinityWeakLimit
open Filter MeasureTheory Set

noncomputable section

/-! ## Abstract density consequences of measure domination -/

/-- A dominated sigma-finite measure has Radon--Nikodym derivative bounded by
the same domination constant. -/
theorem rnDeriv_le_const_of_le_smul
    {X : Type*} [MeasurableSpace X]
    (mu reference : Measure X) [SigmaFinite mu] [SigmaFinite reference]
    (C : ENNReal) (hle : mu ≤ C • reference) :
    mu.rnDeriv reference ≤ᵐ[reference] (fun _ => C) := by
  have hac : mu ≪ reference :=
    hle.absolutelyContinuous.trans Measure.smul_absolutelyContinuous
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite
    (Measure.measurable_rnDeriv _ _) ?_
  intro s hs _hsFinite
  rw [Measure.setLIntegral_rnDeriv hac s, setLIntegral_const]
  simpa only [Measure.smul_apply, smul_eq_mul] using hle s

/-- Measure domination gives an explicit measurable `L∞`-type density
witness. -/
theorem exists_density_le_const_of_le_smul
    {X : Type*} [MeasurableSpace X]
    (mu reference : Measure X) [SigmaFinite mu] [SigmaFinite reference]
    (C : ENNReal) (hle : mu ≤ C • reference) :
    ∃ density : X → ENNReal,
      Measurable density ∧
      density ≤ᵐ[reference] (fun _ => C) ∧
      reference.withDensity density = mu := by
  have hac : mu ≪ reference :=
    hle.absolutelyContinuous.trans Measure.smul_absolutelyContinuous
  exact ⟨mu.rnDeriv reference, Measure.measurable_rnDeriv _ _,
    rnDeriv_le_const_of_le_smul mu reference C hle,
    Measure.withDensity_rnDeriv_eq _ _ hac⟩

/-- The full weak-limit hypothesis directly yields the essential density
bound for the finite-measure limit. -/
theorem finiteMeasure_rnDeriv_le_const_of_tendsto_of_apply_le_add_vanishingError
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X]
    (source : Nat → FiniteMeasure X) (target : FiniteMeasure X)
    (hlimit : Tendsto source atTop (nhds target))
    (reference : Measure X) [reference.OuterRegular] [SigmaFinite reference]
    (C : ENNReal) (hC : C ≠ ∞)
    (error : Nat → ENNReal) (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ n A, MeasurableSet A →
      (source n : Measure X) A ≤ C * reference A + error n) :
    (target : Measure X).rnDeriv reference ≤ᵐ[reference]
      (fun _ => C) := by
  apply rnDeriv_le_const_of_le_smul
  exact finiteMeasure_le_smul_of_tendsto_of_apply_le_add_vanishingError
    source target hlimit reference C hC error herror hbound

/-- The full weak-limit hypothesis directly yields a measurable density
representation whose density is essentially bounded by `C`. -/
theorem finiteMeasure_exists_density_le_const_of_tendsto_of_apply_le_add_vanishingError
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X]
    (source : Nat → FiniteMeasure X) (target : FiniteMeasure X)
    (hlimit : Tendsto source atTop (nhds target))
    (reference : Measure X) [reference.OuterRegular] [SigmaFinite reference]
    (C : ENNReal) (hC : C ≠ ∞)
    (error : Nat → ENNReal) (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ n A, MeasurableSet A →
      (source n : Measure X) A ≤ C * reference A + error n) :
    ∃ density : X → ENNReal,
      Measurable density ∧
      density ≤ᵐ[reference] (fun _ => C) ∧
      reference.withDensity density = (target : Measure X) := by
  apply exists_density_le_const_of_le_smul
  exact finiteMeasure_le_smul_of_tendsto_of_apply_le_add_vanishingError
    source target hlimit reference C hC error herror hbound

/-- Every reference-null set is null for the weak limit. -/
theorem finiteMeasure_apply_eq_zero_of_tendsto_of_apply_le_add_vanishingError
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X]
    (source : Nat → FiniteMeasure X) (target : FiniteMeasure X)
    (hlimit : Tendsto source atTop (nhds target))
    (reference : Measure X) [reference.OuterRegular]
    (C : ENNReal) (hC : C ≠ ∞)
    (error : Nat → ENNReal) (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ n A, MeasurableSet A →
      (source n : Measure X) A ≤ C * reference A + error n)
    {A : Set X} (hA : reference A = 0) :
    (target : Measure X) A = 0 := by
  exact
    (finiteMeasure_absolutelyContinuous_of_tendsto_of_apply_le_add_vanishingError
      source target hlimit reference C hC error herror hbound) hA

/-- In particular, reference-null singletons remain null in the weak limit. -/
theorem finiteMeasure_singleton_eq_zero_of_tendsto_of_apply_le_add_vanishingError
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X]
    (source : Nat → FiniteMeasure X) (target : FiniteMeasure X)
    (hlimit : Tendsto source atTop (nhds target))
    (reference : Measure X) [reference.OuterRegular]
    (C : ENNReal) (hC : C ≠ ∞)
    (error : Nat → ENNReal) (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ n A, MeasurableSet A →
      (source n : Measure X) A ≤ C * reference A + error n)
    (x : X) (hx : reference ({x} : Set X) = 0) :
    (target : Measure X) ({x} : Set X) = 0 :=
  finiteMeasure_apply_eq_zero_of_tendsto_of_apply_le_add_vanishingError
    source target hlimit reference C hC error herror hbound hx

end

end ArchonPhysics.FiniteMeasureWeakLimitDominationDensity

namespace ArchonPhysics.CanonicalRankFrequencyMarkedVolumeDominationBridge

open ArchonPhysics
open ArchonPhysics.CanonicalRankFrequencyMarkedCompactness
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedJointLimitSmallBallBridge
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedProbabilityJointLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.FiniteMeasureVanishingErrorLInfinityWeakLimit
open ArchonPhysics.FiniteMeasureWeakLimitDominationDensity
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open Filter MeasureTheory Set Topology

noncomputable section

/-! ## Canonical arbitrary-set model input -/

/-- A model-side volume-domination estimate for every measurable mismatch
set, uniform in the finite-volume index on one probability-one event.  This
is stronger than a small-ball estimate and is the only canonical input used
below. -/
structure CanonicalMarkedMismatchVanishingErrorVolumeDomination
    (sign : Fin 3 → InteractionSign) where
  constant : Real
  constant_nonneg : 0 ≤ constant
  error : Nat → Real
  error_nonneg : ∀ n, 0 ≤ error n
  error_tendsto_zero : Tendsto error atTop (nhds 0)
  bound_ae :
    ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
      ∀ n : Nat, ∀ A : Set Real, MeasurableSet A →
        ((((canonicalMarkedPerSiteSequence n omega).map
            (markedFrequencyMismatch sign) : FiniteMeasure Real) :
              Measure Real) A) ≤
          ENNReal.ofReal constant * (volume : Measure Real) A +
            ENNReal.ofReal (error n)

/-- Exact Lebesgue volume of the symmetric mismatch window. -/
theorem volume_absoluteMismatchSublevel_eq
    (delta : Real) :
    (volume : Measure Real) (absoluteMismatchSublevel delta) =
      ENNReal.ofReal (2 * delta) := by
  rw [show absoluteMismatchSublevel delta = Set.Icc (-delta) delta by
    ext x
    simp [absoluteMismatchSublevel, abs_le]]
  rw [Real.volume_Icc]
  congr 1
  ring

/-- Arbitrary-set volume domination supplies the earlier canonical linear
small-ball interface.  The constant changes from `C` to `2 * C`, exactly the
length of `[-delta, delta]`. -/
def CanonicalMarkedMismatchVanishingErrorVolumeDomination.toSmallBall
    {sign : Fin 3 → InteractionSign}
    (domination : CanonicalMarkedMismatchVanishingErrorVolumeDomination sign) :
    CanonicalMarkedMismatchVanishingErrorSmallBallBound sign where
  constant := 2 * domination.constant
  constant_nonneg := mul_nonneg (by norm_num) domination.constant_nonneg
  error := domination.error
  error_nonneg := domination.error_nonneg
  error_tendsto_zero := domination.error_tendsto_zero
  bound_ae := by
    filter_upwards [domination.bound_ae] with omega homega
    intro n delta hdelta _hdeltaOne
    have hENN := homega n (absoluteMismatchSublevel delta)
      (measurableSet_absoluteMismatchSublevel delta)
    have hmainNonneg :
        0 ≤ (2 * domination.constant) * delta :=
      mul_nonneg (mul_nonneg (by norm_num) domination.constant_nonneg)
        (le_of_lt hdelta)
    have hsumNonneg :
        0 ≤ (2 * domination.constant) * delta + domination.error n :=
      add_nonneg hmainNonneg (domination.error_nonneg n)
    have hupper :
        ENNReal.ofReal domination.constant *
              (volume : Measure Real) (absoluteMismatchSublevel delta) +
            ENNReal.ofReal (domination.error n) =
          ENNReal.ofReal
            ((2 * domination.constant) * delta + domination.error n) := by
      rw [volume_absoluteMismatchSublevel_eq]
      rw [← ENNReal.ofReal_mul domination.constant_nonneg]
      rw [← ENNReal.ofReal_add
        (mul_nonneg domination.constant_nonneg
          (mul_nonneg (by norm_num) (le_of_lt hdelta)))
        (domination.error_nonneg n)]
      congr 1
      ring
    rw [hupper] at hENN
    calc
      (((((canonicalMarkedPerSiteSequence n omega).map
          (markedFrequencyMismatch sign) : FiniteMeasure Real) :
            Measure Real) (absoluteMismatchSublevel delta))).toReal ≤
          (ENNReal.ofReal
            ((2 * domination.constant) * delta + domination.error n)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
      _ = (2 * domination.constant) * delta + domination.error n :=
        ENNReal.toReal_ofReal hsumNonneg

/-! ## Canonical weak-limit domination, density, and atomlessness -/

/-- The canonical mismatch pushforward is dominated by `C * volume`. -/
theorem canonicalMismatchTarget_le_smul_volume
    {sign : Fin 3 → InteractionSign}
    (domination : CanonicalMarkedMismatchVanishingErrorVolumeDomination sign) :
    ((((canonicalRankFrequencyMarkedPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble).map
          (markedFrequencyMismatch sign) : FiniteMeasure Real) : Measure Real)) ≤
      ENNReal.ofReal domination.constant • (volume : Measure Real) := by
  have hboth :
      ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
        Tendsto (fun n ↦ canonicalMarkedPerSiteSequence n omega) atTop
          (nhds (canonicalRankFrequencyMarkedPerSiteMeasureLimit
            canonicalIIDMassPhaseEnsemble)) ∧
        (∀ n : Nat, ∀ A : Set Real, MeasurableSet A →
          ((((canonicalMarkedPerSiteSequence n omega).map
              (markedFrequencyMismatch sign) : FiniteMeasure Real) :
                Measure Real) A) ≤
            ENNReal.ofReal domination.constant *
                (volume : Measure Real) A +
              ENNReal.ofReal (domination.error n)) := by
    filter_upwards
      [canonicalRankFrequencyTriplePerSiteFiniteMeasure_tendsto_limit_ae,
        domination.bound_ae] with omega hlimit hbound
    exact ⟨by simpa only [canonicalMarkedPerSiteSequence] using hlimit, hbound⟩
  obtain ⟨omega, hlimit, hbound⟩ := hboth.exists
  have herrorENN :
      Tendsto (fun n ↦ ENNReal.ofReal (domination.error n)) atTop
        (nhds (0 : ENNReal)) := by
    simpa using ENNReal.tendsto_ofReal domination.error_tendsto_zero
  apply finiteMeasure_le_smul_of_tendsto_of_apply_le_add_vanishingError
    (fun n ↦ (canonicalMarkedPerSiteSequence n omega).map
      (markedFrequencyMismatch sign))
    ((canonicalRankFrequencyMarkedPerSiteMeasureLimit
      canonicalIIDMassPhaseEnsemble).map
        (markedFrequencyMismatch sign))
    (FiniteMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n ↦ canonicalMarkedPerSiteSequence n omega)
      (canonicalRankFrequencyMarkedPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble)
      hlimit (continuous_markedFrequencyMismatch sign))
    volume (ENNReal.ofReal domination.constant) ENNReal.ofReal_ne_top
    (fun n ↦ ENNReal.ofReal (domination.error n)) herrorENN
  exact hbound

/-- Consequently the canonical mismatch pushforward is absolutely continuous
with respect to Lebesgue measure. -/
theorem canonicalMismatchTarget_absolutelyContinuous_volume
    {sign : Fin 3 → InteractionSign}
    (domination : CanonicalMarkedMismatchVanishingErrorVolumeDomination sign) :
    ((((canonicalRankFrequencyMarkedPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble).map
          (markedFrequencyMismatch sign) : FiniteMeasure Real) : Measure Real)) ≪
      (volume : Measure Real) :=
  (canonicalMismatchTarget_le_smul_volume domination).absolutelyContinuous.trans
    Measure.smul_absolutelyContinuous

/-- The canonical mismatch pushforward has a measurable density bounded by
the model constant almost everywhere. -/
theorem canonicalMismatchTarget_exists_density_le
    {sign : Fin 3 → InteractionSign}
    (domination : CanonicalMarkedMismatchVanishingErrorVolumeDomination sign) :
    ∃ density : Real → ENNReal,
      Measurable density ∧
      density ≤ᵐ[(volume : Measure Real)]
        (fun _ ↦ ENNReal.ofReal domination.constant) ∧
      (volume : Measure Real).withDensity density =
        (((canonicalRankFrequencyMarkedPerSiteMeasureLimit
          canonicalIIDMassPhaseEnsemble).map
            (markedFrequencyMismatch sign) : FiniteMeasure Real) :
              Measure Real) :=
  exists_density_le_const_of_le_smul _ volume _
    (canonicalMismatchTarget_le_smul_volume domination)

/-- Lebesgue domination removes every singleton atom, not only exact
resonance at zero. -/
theorem canonicalMismatchTarget_singleton_eq_zero
    {sign : Fin 3 → InteractionSign}
    (domination : CanonicalMarkedMismatchVanishingErrorVolumeDomination sign)
    (x : Real) :
    ((((canonicalRankFrequencyMarkedPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble).map
          (markedFrequencyMismatch sign) : FiniteMeasure Real) : Measure Real)
      ({x} : Set Real)) = 0 := by
  exact canonicalMismatchTarget_absolutelyContinuous_volume domination (by simp)

/-- Exact resonance is absent; this statement also records that the stronger
volume-domination input plugs into the existing small-ball bridge. -/
theorem canonicalMismatchTarget_singleton_zero_eq_zero
    {sign : Fin 3 → InteractionSign}
    (domination : CanonicalMarkedMismatchVanishingErrorVolumeDomination sign) :
    ((((canonicalRankFrequencyMarkedPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble).map
          (markedFrequencyMismatch sign) : FiniteMeasure Real) : Measure Real)
      ({0} : Set Real)) = 0 :=
  canonicalMarkedPerSiteMeasureLimit_mismatch_singleton_zero_eq_zero
    domination.toSmallBall

end

end ArchonPhysics.CanonicalRankFrequencyMarkedVolumeDominationBridge
