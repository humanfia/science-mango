import ArchonPhysics.CanonicalOnShellRayleighJeansDistanceF2
import ArchonPhysics.HardSoftRayleighJeansL1Gluing

/-!
# A non-vacuous hard-band Rayleigh--Jeans F3 core

The acoustic profile `temperature / frequency` need not belong to canonical
`L-infinity` on the full spectrum.  After restricting every collision leg to
a strictly positive frequency cutoff, the same profile is pointwise bounded
by `‖temperature‖ / cutoff`.  This file records the resulting genuine
canonical `L-infinity` class, proves that it lies in the concrete
Rayleigh--Jeans equilibrium set and hence has zero concrete distance, and
connects that class to the existing finite hard/soft normalized-energy
`L1` bridge.

No relaxation statement for a nonstationary exact collision trajectory is
asserted here.  Such a statement still requires a dynamical hard-band
relaxation input.
-/

namespace ArchonPhysics.HardBandRayleighJeansF3Core

open MeasureTheory
open ArchonPhysics.CanonicalOnShellRayleighJeansDistanceF2
open ArchonPhysics.HardSoftRayleighJeansL1Gluing
open ArchonPhysics.ResonantThreeWaveHardFrequencyRestriction
open ArchonPhysics.ResonantThreeWaveHardFrequencyRayleighJeansEquilibrium
open ArchonPhysics.ResonantThreeWaveKineticEquilibrium
open ArchonPhysics.ResonantThreeWaveKineticLInfinityEquilibrium
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- The hard-band Rayleigh--Jeans representative has the explicit global
bound `‖temperature‖ / cutoff`. -/
theorem norm_hardBandRayleighJeansAction_le
    (collision : ResonantThreeWaveMeasure Mode)
    (temperature : Real) {cutoff : Real} (hcutoff : 0 < cutoff)
    (mode : Mode) :
    ‖rayleighJeansAction temperature
        (hardFrequencyRestriction collision cutoff).frequency mode‖ ≤
      ‖temperature‖ / cutoff := by
  have hfrequency : cutoff ≤
      (hardFrequencyRestriction collision cutoff).frequency mode :=
    cutoff_le_hardFrequencyRestriction_frequency collision cutoff mode
  have hfrequencyPos : 0 <
      (hardFrequencyRestriction collision cutoff).frequency mode :=
    hcutoff.trans_le hfrequency
  simp only [rayleighJeansAction, norm_div, Real.norm_eq_abs]
  rw [abs_of_pos hfrequencyPos]
  exact div_le_div_of_nonneg_left (norm_nonneg temperature) hcutoff hfrequency

/-- Consequently the hard-band representative genuinely belongs to the
canonical `L-infinity` space. -/
theorem hardBandRayleighJeansAction_memLp_top
    (collision : ResonantThreeWaveMeasure Mode)
    (temperature : Real) {cutoff : Real} (hcutoff : 0 < cutoff) :
    MemLp
      (rayleighJeansAction temperature
        (hardFrequencyRestriction collision cutoff).frequency)
      ∞ (collisionReferenceMeasure
        (hardFrequencyRestriction collision cutoff)) := by
  exact rayleighJeansMemLpTop
    (hardFrequencyRestriction collision cutoff) temperature cutoff hcutoff
    (cutoff_le_hardFrequencyRestriction_frequency collision cutoff)

/-- The genuine hard-band quotient class is one of the equilibria used by
the concrete canonical Rayleigh--Jeans distance. -/
theorem hardBandRayleighJeansClass_mem_equilibriumSet
    (collision : ResonantThreeWaveMeasure Mode)
    (temperature : Real) {cutoff : Real} (hcutoff : 0 < cutoff) :
    hardBandRayleighJeansClass collision cutoff temperature hcutoff ∈
      rayleighJeansEquilibriumSet
        (hardFrequencyRestriction collision cutoff) := by
  refine ⟨temperature⁻¹, ?_⟩
  unfold hardBandRayleighJeansClass rayleighJeansClass
  filter_upwards [MemLp.coeFn_toLp
      (hardBandRayleighJeansAction_memLp_top
        collision temperature hcutoff)] with mode hmode
  rw [hmode]
  exact inverse_rayleighJeansAction temperature
    (hardFrequencyRestriction collision cutoff).frequency mode

/-- Unlike the full acoustic positive class, the hard-band concrete
equilibrium set has an explicit nonzero-frequency representative and is
therefore nonempty. -/
theorem hardBand_rayleighJeansEquilibriumSet_nonempty
    (collision : ResonantThreeWaveMeasure Mode)
    (temperature : Real) {cutoff : Real} (hcutoff : 0 < cutoff) :
    (rayleighJeansEquilibriumSet
      (hardFrequencyRestriction collision cutoff)).Nonempty :=
  ⟨hardBandRayleighJeansClass collision cutoff temperature hcutoff,
    hardBandRayleighJeansClass_mem_equilibriumSet
      collision temperature hcutoff⟩

/-- The concrete canonical distance of the hard-band Rayleigh--Jeans class
to the equilibrium set is exactly zero. -/
theorem hardBandRayleighJeansDistance_eq_zero
    (collision : ResonantThreeWaveMeasure Mode)
    (temperature : Real) {cutoff : Real} (hcutoff : 0 < cutoff) :
    rayleighJeansDistance (hardFrequencyRestriction collision cutoff)
      (hardBandRayleighJeansClass collision cutoff temperature hcutoff) = 0 :=
  rayleighJeansDistance_eq_zero_of_equilibrium
    (hardFrequencyRestriction collision cutoff)
    (hardBandRayleighJeansClass collision cutoff temperature hcutoff)
    (hardBandRayleighJeansClass_mem_equilibriumSet
      collision temperature hcutoff)

/-- A finite-mode certificate joining the genuine hard-band `L-infinity`
target and its concrete zero distance to the exact normalized modal-energy
target consumed by the hard/soft `L1` gluing theorem. -/
theorem hardBandRayleighJeans_f3_core_certificate
    {FiniteMode : Type} [MeasurableSpace FiniteMode] [Fintype FiniteMode]
    (collision : ResonantThreeWaveMeasure FiniteMode)
    {cutoff temperature : Real} (hcutoff : 0 < cutoff)
    (htemperature : 0 < temperature)
    (hard : Finset FiniteMode) (hhard : hard.Nonempty) :
    MemLp
        (rayleighJeansAction temperature
          (hardFrequencyRestriction collision cutoff).frequency)
        ∞ (collisionReferenceMeasure
          (hardFrequencyRestriction collision cutoff)) ∧
      (∀ mode, ‖rayleighJeansAction temperature
          (hardFrequencyRestriction collision cutoff).frequency mode‖ ≤
        ‖temperature‖ / cutoff) ∧
      hardBandRayleighJeansClass collision cutoff temperature hcutoff ∈
        rayleighJeansEquilibriumSet
          (hardFrequencyRestriction collision cutoff) ∧
      rayleighJeansDistance (hardFrequencyRestriction collision cutoff)
          (hardBandRayleighJeansClass
            collision cutoff temperature hcutoff) = 0 ∧
      normalizedSectorL1Deficit hard
        (fun mode ↦
          (hardFrequencyRestriction collision cutoff).frequency mode *
            rayleighJeansAction temperature
              (hardFrequencyRestriction collision cutoff).frequency mode) = 0 := by
  exact ⟨hardBandRayleighJeansAction_memLp_top
      collision temperature hcutoff,
    norm_hardBandRayleighJeansAction_le collision temperature hcutoff,
    hardBandRayleighJeansClass_mem_equilibriumSet
      collision temperature hcutoff,
    hardBandRayleighJeansDistance_eq_zero collision temperature hcutoff,
    hardBandRayleighJeans_normalizedSectorL1Deficit_eq_zero
      collision hcutoff htemperature hard hhard⟩

end

end ArchonPhysics.HardBandRayleighJeansF3Core
