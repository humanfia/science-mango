import ArchonPhysics.ResonantThreeWaveKineticEntropy

/-!
# Equilibria of the Radon--Nikodym three-wave collision operator

This module identifies the equality case in the continuum algebraic
H-theorem.  For a bounded measurable action with a uniform positive floor,
the logarithmic-entropy integrand is integrable, and its integral vanishes
exactly when inverse action is balanced on almost every collision triad.

It also proves the complementary stationary-state statement.  If inverse
action is pointwise proportional to the resonant frequency, then the signed
collision measure vanishes and its Radon--Nikodym collision vector is zero
almost everywhere.  In particular, a positive-temperature Rayleigh--Jeans
action `T / frequency` is bounded measurable under a positive frequency
floor, has constant modal energy, and is RN-stationary.

The optional `AEFrequencyBalanceRigid` contract below isolates the additional
connectivity/rank input needed to turn almost-everywhere triad balance into a
global profile classification.  No such rigidity is asserted for any target
collision measure in this module.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticEquilibrium

open MeasureTheory
open ArchonPhysics.ResonantThreeWaveMeasure
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.ResonantThreeWaveKineticEntropy
open ArchonPhysics.ThreeWaveCollisionAlgebra
open scoped MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- The pointwise nonnegative integrand whose collision-measure integral is
the continuum logarithmic-entropy production. -/
def continuumLogEntropyIntegrand
    (action : Mode -> Real) (triad : Fin 3 -> Mode) : Real :=
  triadWeakObservableIntegrand (fun mode => (action mode)⁻¹) action triad

/-- A bounded measurable test and action give an integrable weak collision
integrand on every finite collision measure. -/
theorem integrable_triadWeakObservableIntegrand
    (collision : ResonantThreeWaveMeasure Mode)
    {test action : Mode -> Real}
    (htest : IsBoundedMeasurable test)
    (haction : IsBoundedMeasurable action) :
    Integrable (triadWeakObservableIntegrand test action)
      collision.collisionMeasure := by
  obtain ⟨bound, hbound⟩ := htest.exists_norm_bound
  have htestDifferenceMeasurable : Measurable
      (fun triad : Fin 3 -> Mode =>
        test (triad 0) - test (triad 1) - test (triad 2)) := by
    exact ((htest.measurable.comp (measurable_triadLeg 0)).sub
      (htest.measurable.comp (measurable_triadLeg 1))).sub
      (htest.measurable.comp (measurable_triadLeg 2))
  have htestDifferenceBound (triad : Fin 3 -> Mode) :
      norm (test (triad 0) - test (triad 1) - test (triad 2)) <=
        3 * bound := by
    have hboundNonneg : 0 <= bound :=
      (norm_nonneg (test (triad 0))).trans (hbound (triad 0))
    calc
      norm (test (triad 0) - test (triad 1) - test (triad 2)) <=
          norm (test (triad 0)) + norm (test (triad 1)) +
            norm (test (triad 2)) := by
        calc
          _ <= norm (test (triad 0) - test (triad 1)) +
              norm (test (triad 2)) := norm_sub_le _ _
          _ <= _ := by gcongr; exact norm_sub_le _ _
      _ <= bound + bound + bound := by
        gcongr <;> apply hbound
      _ = 3 * bound := by ring
  change Integrable
    (fun triad : Fin 3 -> Mode =>
      collisionFlux
          (action (triad 0)) (action (triad 1)) (action (triad 2)) *
        (test (triad 0) - test (triad 1) - test (triad 2)))
    collision.collisionMeasure
  simpa only [triadFlux] using
    (integrable_triadFlux collision haction).mul_bdd
      htestDifferenceMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall htestDifferenceBound)

/-- A uniformly positive bounded measurable action has an integrable
continuum logarithmic-entropy integrand. -/
theorem integrable_continuumLogEntropyIntegrand
    (collision : ResonantThreeWaveMeasure Mode)
    {action : Mode -> Real} (haction : IsBoundedMeasurable action)
    (floor : Real) (hfloor : 0 < floor)
    (hactionFloor : forall mode, floor <= action mode) :
    Integrable (continuumLogEntropyIntegrand action)
      collision.collisionMeasure := by
  exact integrable_triadWeakObservableIntegrand collision
    (inverseAction_isBoundedMeasurable haction floor hfloor hactionFloor)
    haction

/-- The continuum entropy production is the integral of its explicit triad
integrand. -/
theorem continuumLogEntropyProduction_eq_integral
    (collision : ResonantThreeWaveMeasure Mode) (action : Mode -> Real) :
    continuumLogEntropyProduction collision action =
      ∫ triad, continuumLogEntropyIntegrand action triad
        ∂collision.collisionMeasure := by
  rfl

omit [MeasurableSpace Mode] in
/-- Strictly positive actions make the explicit continuum entropy integrand
nonnegative at every triad. -/
theorem continuumLogEntropyIntegrand_nonneg
    {action : Mode -> Real} (haction : forall mode, 0 < action mode)
    (triad : Fin 3 -> Mode) :
    0 <= continuumLogEntropyIntegrand action triad := by
  simpa only [continuumLogEntropyIntegrand, triadWeakObservableIntegrand,
    entropyProduction, inverseActionMismatch, one_mul] using
    (entropyProduction_nonneg (by norm_num : (0 : Real) <= 1)
      (haction (triad 0)) (haction (triad 1)) (haction (triad 2)))

/-- Equality in the continuum H-theorem is exactly inverse-action balance on
collision-almost-every triad. -/
theorem continuumLogEntropyProduction_eq_zero_iff_inverseActionMismatch_ae
    (collision : ResonantThreeWaveMeasure Mode)
    {action : Mode -> Real} (haction : IsBoundedMeasurable action)
    (floor : Real) (hfloor : 0 < floor)
    (hactionFloor : forall mode, floor <= action mode) :
    continuumLogEntropyProduction collision action = 0 ↔
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        inverseActionMismatch
          (action (triad 0)) (action (triad 1)) (action (triad 2)) = 0 := by
  rw [continuumLogEntropyProduction_eq_integral]
  have hactionPos : forall mode, 0 < action mode := fun mode =>
    hfloor.trans_le (hactionFloor mode)
  have hintegrable := integrable_continuumLogEntropyIntegrand
    collision haction floor hfloor hactionFloor
  have hnonneg : forall triad, 0 <= continuumLogEntropyIntegrand action triad :=
    continuumLogEntropyIntegrand_nonneg hactionPos
  constructor
  · intro hzero
    have hzeroAE : continuumLogEntropyIntegrand action =ᵐ[
        (collision.collisionMeasure : Measure (Fin 3 -> Mode))] 0 :=
      (integral_eq_zero_iff_of_nonneg hnonneg hintegrable).mp hzero
    filter_upwards [hzeroAE] with triad htriad
    apply (entropyProduction_eq_zero_iff_inverseActionMismatch_eq_zero
      (by norm_num : (0 : Real) < 1)
      (hactionPos (triad 0)) (hactionPos (triad 1))
      (hactionPos (triad 2))).mp
    simpa only [continuumLogEntropyIntegrand, triadWeakObservableIntegrand,
      entropyProduction, inverseActionMismatch, one_mul, Pi.zero_apply] using
      htriad
  · intro hbalance
    apply integral_eq_zero_of_ae
    filter_upwards [hbalance] with triad htriad
    have hentropyZero :=
      (entropyProduction_eq_zero_iff_inverseActionMismatch_eq_zero
        (by norm_num : (0 : Real) < 1)
        (hactionPos (triad 0)) (hactionPos (triad 1))
        (hactionPos (triad 2))).mpr htriad
    simpa only [continuumLogEntropyIntegrand, triadWeakObservableIntegrand,
      entropyProduction, inverseActionMismatch, one_mul, Pi.zero_apply] using
      hentropyZero

/-- Transparent additional rigidity contract: an almost-everywhere balanced
triad weight must be proportional to frequency almost everywhere for the
canonical three-leg reference measure.  This is an assumption, not a property
proved here for a target collision measure. -/
def AEFrequencyBalanceRigid
    (collision : ResonantThreeWaveMeasure Mode) : Prop :=
  forall weight : Mode -> Real,
    (∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
      weight (triad 0) = weight (triad 1) + weight (triad 2)) ->
      ∃ scale : Real,
        ∀ᵐ mode ∂collisionReferenceMeasure collision,
          weight mode = scale * collision.frequency mode

/-- Under the explicit AE frequency-balance rigidity contract, zero entropy
production forces inverse action to be frequency-proportional almost
everywhere for the canonical reference measure. -/
theorem inverseAction_ae_proportional_of_continuumLogEntropyProduction_eq_zero
    (collision : ResonantThreeWaveMeasure Mode)
    (hrigid : AEFrequencyBalanceRigid collision)
    {action : Mode -> Real} (haction : IsBoundedMeasurable action)
    (floor : Real) (hfloor : 0 < floor)
    (hactionFloor : forall mode, floor <= action mode)
    (hzero : continuumLogEntropyProduction collision action = 0) :
    ∃ scale : Real,
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        (action mode)⁻¹ = scale * collision.frequency mode := by
  apply hrigid (fun mode => (action mode)⁻¹)
  have hbalance :=
    (continuumLogEntropyProduction_eq_zero_iff_inverseActionMismatch_ae
      collision haction floor hfloor hactionFloor).mp hzero
  filter_upwards [hbalance] with triad htriad
  exact (inverseActionMismatch_eq_zero_iff
    (action (triad 0)) (action (triad 1)) (action (triad 2))).mp htriad

/-- A pointwise frequency-proportional inverse action is balanced on
collision-almost-every resonant triad. -/
theorem inverseActionMismatch_ae_eq_zero_of_inverseAction_eq_scale_frequency
    (collision : ResonantThreeWaveMeasure Mode) (action : Mode -> Real)
    (scale : Real)
    (hprofile : forall mode,
      (action mode)⁻¹ = scale * collision.frequency mode) :
    ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
      inverseActionMismatch
        (action (triad 0)) (action (triad 1)) (action (triad 2)) = 0 := by
  filter_upwards [collision.resonance_ae] with triad hresonance
  unfold inverseActionMismatch
  rw [hprofile, hprofile, hprofile, hresonance]
  ring

/-- A frequency-proportional inverse action has zero continuum entropy
production, without an integrability hypothesis: its integrand is zero almost
everywhere by resonance. -/
theorem continuumLogEntropyProduction_eq_zero_of_inverseAction_eq_scale_frequency
    (collision : ResonantThreeWaveMeasure Mode) (action : Mode -> Real)
    (scale : Real)
    (hprofile : forall mode,
      (action mode)⁻¹ = scale * collision.frequency mode) :
    continuumLogEntropyProduction collision action = 0 := by
  rw [continuumLogEntropyProduction_eq_integral]
  apply integral_eq_zero_of_ae
  have hbalance :=
    inverseActionMismatch_ae_eq_zero_of_inverseAction_eq_scale_frequency
      collision action scale hprofile
  filter_upwards [hbalance] with triad htriad
  simp only [continuumLogEntropyIntegrand, triadWeakObservableIntegrand,
    inverseActionMismatch, Pi.zero_apply] at htriad ⊢
  rw [htriad, mul_zero]

/-- For positive actions, a frequency-proportional inverse action makes the
triad flux vanish collision-almost-everywhere. -/
theorem triadFlux_ae_eq_zero_of_inverseAction_eq_scale_frequency
    (collision : ResonantThreeWaveMeasure Mode) (action : Mode -> Real)
    (scale : Real) (haction : forall mode, 0 < action mode)
    (hprofile : forall mode,
      (action mode)⁻¹ = scale * collision.frequency mode) :
    triadFlux action =ᵐ[
      (collision.collisionMeasure : Measure (Fin 3 -> Mode))] 0 := by
  have hbalance :=
    inverseActionMismatch_ae_eq_zero_of_inverseAction_eq_scale_frequency
      collision action scale hprofile
  filter_upwards [hbalance] with triad htriad
  have hflux :=
    (collisionFlux_eq_zero_iff_inverseActionMismatch_eq_zero
      (haction (triad 0)) (haction (triad 1))
      (haction (triad 2))).mpr htriad
  simpa only [triadFlux, Pi.zero_apply] using hflux

/-- A positive action whose inverse is proportional to resonant frequency has
zero net signed collision measure. -/
theorem signedCollisionMeasure_eq_zero_of_inverseAction_eq_scale_frequency
    (collision : ResonantThreeWaveMeasure Mode) (action : Mode -> Real)
    (scale : Real) (haction : forall mode, 0 < action mode)
    (hprofile : forall mode,
      (action mode)⁻¹ = scale * collision.frequency mode) :
    signedCollisionMeasure collision action = 0 := by
  have hflux := triadFlux_ae_eq_zero_of_inverseAction_eq_scale_frequency
    collision action scale haction hprofile
  have hfluxMeasure : fluxSignedTriadMeasure collision action = 0 := by
    unfold fluxSignedTriadMeasure
    calc
      (collision.collisionMeasure : Measure (Fin 3 -> Mode)).withDensityᵥ
          (triadFlux action) =
          (collision.collisionMeasure : Measure (Fin 3 -> Mode)).withDensityᵥ
            (0 : (Fin 3 -> Mode) -> Real) :=
        WithDensityᵥEq.congr_ae hflux
      _ = 0 := withDensityᵥ_zero
  unfold signedCollisionMeasure legFluxSignedMeasure
  rw [hfluxMeasure]
  simp

/-- The RN collision vector of a positive frequency-proportional inverse
action is zero almost everywhere for the canonical reference measure. -/
theorem collisionVector_ae_eq_zero_of_inverseAction_eq_scale_frequency
    (collision : ResonantThreeWaveMeasure Mode) (action : Mode -> Real)
    (scale : Real) (haction : forall mode, 0 < action mode)
    (hprofile : forall mode,
      (action mode)⁻¹ = scale * collision.frequency mode) :
    ∀ᵐ mode ∂collisionReferenceMeasure collision,
      collisionVector collision action mode = 0 := by
  have hsigned :=
    signedCollisionMeasure_eq_zero_of_inverseAction_eq_scale_frequency
      collision action scale haction hprofile
  have hdensity :
      (collisionReferenceMeasure collision).withDensityᵥ
          (collisionVector collision action) =
        (collisionReferenceMeasure collision).withDensityᵥ
          (0 : Mode -> Real) := by
    rw [withDensity_collisionVector_eq_signedCollisionMeasure, hsigned]
    exact withDensityᵥ_zero.symm
  simpa only [Filter.EventuallyEq, Pi.zero_apply] using
    (integrable_collisionVector collision action).ae_eq_of_withDensityᵥ_eq
      (integrable_zero Mode Real (collisionReferenceMeasure collision))
      hdensity

/-- Frequency-proportional inverse action is stationary both as a signed
measure and as a canonical pointwise RN collision vector. -/
theorem rn_stationary_of_inverseAction_eq_scale_frequency
    (collision : ResonantThreeWaveMeasure Mode) (action : Mode -> Real)
    (scale : Real) (haction : forall mode, 0 < action mode)
    (hprofile : forall mode,
      (action mode)⁻¹ = scale * collision.frequency mode) :
    signedCollisionMeasure collision action = 0 ∧
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        collisionVector collision action mode = 0 := by
  exact ⟨signedCollisionMeasure_eq_zero_of_inverseAction_eq_scale_frequency
      collision action scale haction hprofile,
    collisionVector_ae_eq_zero_of_inverseAction_eq_scale_frequency
      collision action scale haction hprofile⟩

/-- Rayleigh--Jeans action at temperature `temperature` for a supplied
frequency profile. -/
def rayleighJeansAction
    (temperature : Real) (frequency : Mode -> Real) : Mode -> Real :=
  fun mode => temperature / frequency mode

/-- A positive frequency floor makes the Rayleigh--Jeans action bounded and
measurable.  No upper frequency bound is needed. -/
theorem rayleighJeansAction_isBoundedMeasurable
    (collision : ResonantThreeWaveMeasure Mode) (temperature : Real)
    (frequencyFloor : Real) (hfrequencyFloor : 0 < frequencyFloor)
    (hfrequency : forall mode,
      frequencyFloor <= collision.frequency mode) :
    IsBoundedMeasurable
      (rayleighJeansAction temperature collision.frequency) := by
  constructor
  · change Measurable
      (fun mode => temperature / collision.frequency mode)
    exact measurable_const.div collision.measurable_frequency
  · refine ⟨norm temperature / frequencyFloor, ?_⟩
    intro mode
    have hfrequencyPos : 0 < collision.frequency mode :=
      hfrequencyFloor.trans_le (hfrequency mode)
    rw [rayleighJeansAction, norm_div]
    simp only [Real.norm_eq_abs, abs_of_pos hfrequencyPos]
    exact div_le_div_of_nonneg_left (norm_nonneg temperature)
      hfrequencyFloor (hfrequency mode)

/-- Positive temperature and frequency give a positive Rayleigh--Jeans
action. -/
theorem rayleighJeansAction_pos
    (collision : ResonantThreeWaveMeasure Mode) (temperature : Real)
    (htemperature : 0 < temperature)
    (frequencyFloor : Real) (hfrequencyFloor : 0 < frequencyFloor)
    (hfrequency : forall mode,
      frequencyFloor <= collision.frequency mode) (mode : Mode) :
    0 < rayleighJeansAction temperature collision.frequency mode := by
  exact div_pos htemperature (hfrequencyFloor.trans_le (hfrequency mode))

/-- Rayleigh--Jeans action has the constant modal energy
`frequency * action = temperature`. -/
theorem frequency_mul_rayleighJeansAction
    (collision : ResonantThreeWaveMeasure Mode) (temperature : Real)
    (frequencyFloor : Real) (hfrequencyFloor : 0 < frequencyFloor)
    (hfrequency : forall mode,
      frequencyFloor <= collision.frequency mode) (mode : Mode) :
    collision.frequency mode *
        rayleighJeansAction temperature collision.frequency mode =
      temperature := by
  have hfrequencyNe : collision.frequency mode ≠ 0 :=
    ne_of_gt (hfrequencyFloor.trans_le (hfrequency mode))
  unfold rayleighJeansAction
  calc
    collision.frequency mode * (temperature / collision.frequency mode) =
        (temperature / collision.frequency mode) * collision.frequency mode :=
      mul_comm _ _
    _ = temperature := div_mul_cancel₀ temperature hfrequencyNe

omit [MeasurableSpace Mode] in
/-- The inverse Rayleigh--Jeans action is frequency times inverse
temperature. -/
theorem inverse_rayleighJeansAction
    (temperature : Real) (frequency : Mode -> Real) (mode : Mode) :
    (rayleighJeansAction temperature frequency mode)⁻¹ =
      temperature⁻¹ * frequency mode := by
  unfold rayleighJeansAction
  rw [inv_div, div_eq_mul_inv, mul_comm]

/-- Under positive temperature and a positive frequency floor, the
Rayleigh--Jeans profile is bounded measurable, has constant modal energy,
zero entropy production, and is RN-stationary almost everywhere. -/
theorem rayleighJeans_rn_equilibrium
    (collision : ResonantThreeWaveMeasure Mode) (temperature : Real)
    (htemperature : 0 < temperature)
    (frequencyFloor : Real) (hfrequencyFloor : 0 < frequencyFloor)
    (hfrequency : forall mode,
      frequencyFloor <= collision.frequency mode) :
    IsBoundedMeasurable
        (rayleighJeansAction temperature collision.frequency) ∧
      (forall mode,
        collision.frequency mode *
            rayleighJeansAction temperature collision.frequency mode =
          temperature) ∧
      continuumLogEntropyProduction collision
          (rayleighJeansAction temperature collision.frequency) = 0 ∧
      signedCollisionMeasure collision
          (rayleighJeansAction temperature collision.frequency) = 0 ∧
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        collisionVector collision
          (rayleighJeansAction temperature collision.frequency) mode = 0 := by
  have hactionPos : forall mode,
      0 < rayleighJeansAction temperature collision.frequency mode :=
    rayleighJeansAction_pos collision temperature htemperature
      frequencyFloor hfrequencyFloor hfrequency
  have hprofile : forall mode,
      (rayleighJeansAction temperature collision.frequency mode)⁻¹ =
        temperature⁻¹ * collision.frequency mode :=
    inverse_rayleighJeansAction temperature collision.frequency
  exact ⟨rayleighJeansAction_isBoundedMeasurable collision temperature
      frequencyFloor hfrequencyFloor hfrequency,
    frequency_mul_rayleighJeansAction collision temperature
      frequencyFloor hfrequencyFloor hfrequency,
    continuumLogEntropyProduction_eq_zero_of_inverseAction_eq_scale_frequency
      collision (rayleighJeansAction temperature collision.frequency)
      temperature⁻¹ hprofile,
    signedCollisionMeasure_eq_zero_of_inverseAction_eq_scale_frequency
      collision (rayleighJeansAction temperature collision.frequency)
      temperature⁻¹ hactionPos hprofile,
    collisionVector_ae_eq_zero_of_inverseAction_eq_scale_frequency
      collision (rayleighJeansAction temperature collision.frequency)
      temperature⁻¹ hactionPos hprofile⟩

end

end ArchonPhysics.ResonantThreeWaveKineticEquilibrium
