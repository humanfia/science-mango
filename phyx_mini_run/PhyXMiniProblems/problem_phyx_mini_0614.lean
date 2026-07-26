import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0614

open Dimension

/-!
# Current produced by a narrow-band blackbody photocell shell

A spherical perfect blackbody of radius `1.23 m` is maintained at `5000 K`.
An enclosing spherical shell of photocells accepts every photon whose energy
lies in `E₀ ± ΔE`, where `E₀` is the peak of the blackbody's energy spectrum
and `ΔE / E₀ = 0.0100`.  Across that narrow band the spectral radiant
exitance is treated as constant.  The captured radiation is converted to
electrical power delivered to a `1.00 kΩ` motor.

Physical energy uses Physlib's `DimEnergy`, and the vacuum speed is calibrated
against Physlib's dimensionful `DimSpeed.speedOfLight`.  The other physical
quantities below use Physlib's unit-covariant
`Dimensionful (WithDim ...)` representation.  Reals occur only as explicit SI
readouts, dimensionless ratios, and displayed numerical data.

Assumption/target split:

* `MatchesProblemStatement` contains the supplied source, energy-window, and
  motor data, including that `E₀` maximizes the spectrum;
* `MatchesPrimaryBlackbodyPhotocellFigure` contains only labels and geometry
  read from image 614;
* `UsesStandardRadiationConstants` calibrates `h`, `k_B`, and `c`;
* `SatisfiesBlackbodyPhotocellMotorLaws` states Planck's energy spectrum, the
  narrow-band power approximation, ideal conversion, `P = V I`, and Ohm's
  law; and
* `motorCurrent_matches_answer_A` alone concludes the requested numerical
  current and nearest displayed choice.  No premise contains that conclusion.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- Radiant or electrical power, with SI unit watt. -/
abbrev PowerQuantity : Type :=
  Dimensionful
    (WithDim
      (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹)
      NNReal)

/-!
Spectral radiant exitance per unit photon energy, with SI unit
`W / (m² J)` and hence physical dimension `L⁻² T⁻¹`.
-/
abbrev SpectralRadiantExitancePerEnergyQuantity : Type :=
  Dimensionful
    (WithDim (L𝓭⁻¹ * L𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Planck's constant, with SI unit joule-second. -/
abbrev PlanckConstantQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹) NNReal)

/-- Boltzmann's constant, with SI unit joule per kelvin. -/
abbrev BoltzmannConstantQuantity : Type :=
  Dimensionful
    (WithDim
      (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹)
      NNReal)

/-!
A physical speed.  This uses a real carrier to match the actual type of
Physlib's dimensionful `DimSpeed.speedOfLight` constant.
-/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Electric current, with SI unit ampere and dimension charge per time. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim (C𝓭 * T𝓭⁻¹) NNReal)

/-- Electric potential difference or emf, with SI unit volt. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful
    (WithDim
      (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹)
      NNReal)

/-- Electrical resistance, with SI unit ohm. -/
abbrev ElectricalResistanceQuantity : Type :=
  Dimensionful
    (WithDim
      (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹)
      NNReal)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a Physlib energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read a physical power in watts. -/
def powerInWatts (power : PowerQuantity) : ℝ :=
  ((power UnitChoices.SI).val : ℝ)

/-- Read spectral radiant exitance in `W / (m² J)`. -/
def spectralRadiantExitancePerJouleInSI
    (exitance : SpectralRadiantExitancePerEnergyQuantity) : ℝ :=
  ((exitance UnitChoices.SI).val : ℝ)

/-- Read Planck's constant in joule-seconds. -/
def planckConstantInJouleSeconds
    (constant : PlanckConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-- Read Boltzmann's constant in joules per kelvin. -/
def boltzmannConstantInJoulesPerKelvin
    (constant : BoltzmannConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-- Read a dimensionful speed in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  (speed UnitChoices.SI).val

/-- Read electric current in amperes. -/
def currentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  ((current UnitChoices.SI).val : ℝ)

/-- Read emf or potential difference in volts. -/
def potentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  ((potential UnitChoices.SI).val : ℝ)

/-- Read electrical resistance in ohms. -/
def resistanceInOhms (resistance : ElectricalResistanceQuantity) : ℝ :=
  ((resistance UnitChoices.SI).val : ℝ)

/-!
Read a Physlib absolute temperature in kelvins.  The storage unit is explicit
because `Temperature` stores a nonnegative magnitude in an arbitrary
zero-preserving temperature unit.
-/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-! ## Physical source, apparatus, and primary-figure vocabulary -/

/-- The radiation model assigned to the central hot sphere. -/
inductive ThermalEmitterModel where
  | perfectBlackbody
  deriving DecidableEq, Repr

/-- Component names printed in the supplied figure. -/
inductive FigureComponentLabel where
  | blackbody
  | photocells
  deriving DecidableEq, Fintype, Repr

/-- The radius symbol printed beside the central blackbody. -/
inductive FigureRadiusSymbol where
  | r
  deriving DecidableEq, Repr

/-!
Typed information carried by image 614.  The quantitative radius is supplied
by the prose; the bitmap contributes the component placement, labels, radius
symbol, enclosing photocell lining, and outward radiation arrows.
-/
structure BlackbodyPhotocellFigure where
  centralComponent : FigureComponentLabel
  surroundingComponent : FigureComponentLabel
  componentLabelShown : FigureComponentLabel → Bool
  blackbodyRadiusSymbol : FigureRadiusSymbol
  radiationArrowCount : ℕ
  photocellLiningEnclosesCentralSphere : Bool

/-!
The spherical source.  Its spectral radiant exitance is an independent
physical observable indexed by a genuine physical photon energy; Planck's
law is imposed separately below.
-/
structure SphericalBlackbody where
  model : ThermalEmitterModel
  temperatureStorageUnit : TemperatureUnit
  temperature : Temperature
  radius : LengthQuantity
  spectralRadiantExitancePerEnergy :
    DimEnergy → SpectralRadiantExitancePerEnergyQuantity

/-!
The enclosing photocell shell.  `capturesPhotonAtEnergy` records its response
window, while captured power remains independent until the narrow-band law is
assumed.
-/
structure PhotocellShell where
  centralAcceptedEnergy : DimEnergy
  acceptanceHalfWidth : DimEnergy
  capturesPhotonAtEnergy : DimEnergy → Prop
  capturedRadiantPower : PowerQuantity

/-! The motor's independent circuit observables. -/
structure ResistiveMotor where
  resistance : ElectricalResistanceQuantity
  current : ElectricCurrentQuantity
  emfAcrossMotor : ElectricPotentialQuantity
  deliveredElectricalPower : PowerQuantity

/-- Dimensionful constants occurring in Planck's law. -/
structure BlackbodyRadiationConstants where
  planckConstant : PlanckConstantQuantity
  boltzmannConstant : BoltzmannConstantQuantity
  speedOfLight : SpeedQuantity

/-- Complete physical and diagrammatic setup for the problem. -/
structure BlackbodyPhotocellMotorSetup where
  blackbody : SphericalBlackbody
  photocells : PhotocellShell
  motor : ResistiveMotor
  constants : BlackbodyRadiationConstants
  figure : BlackbodyPhotocellFigure

/-! ## Problem data, figure readouts, and governing laws -/

/-!
Numerical data and qualitative facts supplied by the prose.  In particular,
the central accepted energy maximizes the spectrum, but neither its numerical
value nor the requested motor current is assumed.
-/
structure MatchesProblemStatement
    (setup : BlackbodyPhotocellMotorSetup) : Prop where
  sourceIsPerfectBlackbody : setup.blackbody.model = .perfectBlackbody
  temperatureStoredInKelvins :
    setup.blackbody.temperatureStorageUnit = TemperatureUnit.kelvin
  blackbodyTemperatureKelvins :
    temperatureInKelvins setup.blackbody.temperatureStorageUnit
      setup.blackbody.temperature = 5000
  blackbodyRadiusMeters :
    lengthInMeters setup.blackbody.radius = 123 / 100
  centralEnergyIsSpectrumPeak :
    ∀ photonEnergy : DimEnergy,
      0 < energyInJoules photonEnergy →
      spectralRadiantExitancePerJouleInSI
          (setup.blackbody.spectralRadiantExitancePerEnergy photonEnergy) ≤
        spectralRadiantExitancePerJouleInSI
          (setup.blackbody.spectralRadiantExitancePerEnergy
            setup.photocells.centralAcceptedEnergy)
  acceptanceHalfWidthIsOnePercent :
    energyInJoules setup.photocells.acceptanceHalfWidth =
      (1 / 100 : ℝ) *
        energyInJoules setup.photocells.centralAcceptedEnergy
  capturesExactlyTheAcceptedEnergyBand :
    ∀ photonEnergy : DimEnergy,
      setup.photocells.capturesPhotonAtEnergy photonEnergy ↔
        |energyInJoules photonEnergy -
            energyInJoules setup.photocells.centralAcceptedEnergy| ≤
          energyInJoules setup.photocells.acceptanceHalfWidth
  motorResistanceOhms :
    resistanceInOhms setup.motor.resistance = 1000

/-!
Primary-image evidence: the blackbody is central, the photocells surround it,
both names and the radius symbol `r` are shown, and eight wavy radiation
arrows point from the source toward the shell.
-/
structure MatchesPrimaryBlackbodyPhotocellFigure
    (setup : BlackbodyPhotocellMotorSetup) : Prop where
  blackbodyAtCenter : setup.figure.centralComponent = .blackbody
  photocellsSurroundSource : setup.figure.surroundingComponent = .photocells
  blackbodyLabelShown : setup.figure.componentLabelShown .blackbody = true
  photocellsLabelShown : setup.figure.componentLabelShown .photocells = true
  sourceRadiusLabeledR : setup.figure.blackbodyRadiusSymbol = .r
  eightOutwardRadiationArrows : setup.figure.radiationArrowCount = 8
  shellEnclosesBlackbody :
    setup.figure.photocellLiningEnclosesCentralSphere = true

/-!
Standard SI calibrations.  Physlib supplies the reduced Planck constant and
the dimensionful speed of light; the full Planck constant is `h = 2πℏ`.
-/
structure UsesStandardRadiationConstants
    (setup : BlackbodyPhotocellMotorSetup) : Prop where
  planckConstantCalibration :
    planckConstantInJouleSeconds setup.constants.planckConstant =
      2 * Real.pi * (Constants.ℏ : ℝ)
  boltzmannConstantCalibration :
    boltzmannConstantInJoulesPerKelvin
        setup.constants.boltzmannConstant =
      1380649 / 10 ^ 29
  speedOfLightCalibration :
    setup.constants.speedOfLight = DimSpeed.speedOfLight

/-- Positivity and nondegeneracy conditions for the physical apparatus. -/
structure HasPhysicalBlackbodyPhotocellParameters
    (setup : BlackbodyPhotocellMotorSetup) : Prop where
  temperaturePositive :
    0 < temperatureInKelvins setup.blackbody.temperatureStorageUnit
      setup.blackbody.temperature
  radiusPositive : 0 < lengthInMeters setup.blackbody.radius
  centralEnergyPositive :
    0 < energyInJoules setup.photocells.centralAcceptedEnergy
  acceptanceHalfWidthPositive :
    0 < energyInJoules setup.photocells.acceptanceHalfWidth
  planckConstantPositive :
    0 < planckConstantInJouleSeconds setup.constants.planckConstant
  boltzmannConstantPositive :
    0 < boltzmannConstantInJoulesPerKelvin
      setup.constants.boltzmannConstant
  speedOfLightPositive :
    0 < speedInMetersPerSecond setup.constants.speedOfLight
  motorResistancePositive : 0 < resistanceInOhms setup.motor.resistance

/-!
Governing physical laws.  The first field is Planck's blackbody spectral
radiant exitance per unit photon energy.  The second implements exactly the
narrow-window approximation stated in the problem.  The final three fields
model ideal energy conversion and the ordinary resistive circuit.  None of
these laws mentions `91.1 A` or any answer label.
-/
structure SatisfiesBlackbodyPhotocellMotorLaws
    (setup : BlackbodyPhotocellMotorSetup) : Prop where
  planckEnergySpectrum :
    ∀ photonEnergy : DimEnergy,
      0 < energyInJoules photonEnergy →
      spectralRadiantExitancePerJouleInSI
          (setup.blackbody.spectralRadiantExitancePerEnergy photonEnergy) =
        (2 * Real.pi * energyInJoules photonEnergy ^ 3) /
          (planckConstantInJouleSeconds setup.constants.planckConstant ^ 3 *
            speedInMetersPerSecond setup.constants.speedOfLight ^ 2 *
            (Real.exp
                (energyInJoules photonEnergy /
                  (boltzmannConstantInJoulesPerKelvin
                      setup.constants.boltzmannConstant *
                    temperatureInKelvins
                      setup.blackbody.temperatureStorageUnit
                      setup.blackbody.temperature)) - 1))
  narrowBandCapturedPower :
    powerInWatts setup.photocells.capturedRadiantPower =
      4 * Real.pi * lengthInMeters setup.blackbody.radius ^ 2 *
        spectralRadiantExitancePerJouleInSI
          (setup.blackbody.spectralRadiantExitancePerEnergy
            setup.photocells.centralAcceptedEnergy) *
        (2 * energyInJoules setup.photocells.acceptanceHalfWidth)
  allCapturedPowerBecomesElectricalPower :
    powerInWatts setup.motor.deliveredElectricalPower =
      powerInWatts setup.photocells.capturedRadiantPower
  electricalPowerLaw :
    powerInWatts setup.motor.deliveredElectricalPower =
      potentialInVolts setup.motor.emfAcrossMotor *
        currentInAmperes setup.motor.current
  ohmsLaw :
    potentialInVolts setup.motor.emfAcrossMotor =
      currentInAmperes setup.motor.current *
        resistanceInOhms setup.motor.resistance

/-! ## Derived physical relations -/

/-!
The energy-spectrum maximum satisfies the dimensionless Wien peak equation
`3 (1 - exp (-x₀)) = x₀`, where `x₀ = E₀/(k_B T)`.  This is derived from the
given peak condition and Planck's law; no numerical root is assumed.
-/
lemma centralAcceptedEnergy_satisfies_wienPeakEquation
    (setup : BlackbodyPhotocellMotorSetup)
    (_problem : MatchesProblemStatement setup)
    (_physical : HasPhysicalBlackbodyPhotocellParameters setup)
    (_laws : SatisfiesBlackbodyPhotocellMotorLaws setup) :
    let x₀ : ℝ :=
      energyInJoules setup.photocells.centralAcceptedEnergy /
        (boltzmannConstantInJoulesPerKelvin
            setup.constants.boltzmannConstant *
          temperatureInKelvins setup.blackbody.temperatureStorageUnit
            setup.blackbody.temperature)
    3 * (1 - Real.exp (-x₀)) = x₀ := by
  dsimp
  set E : ℝ :=
    energyInJoules setup.photocells.centralAcceptedEnergy with hE_def
  set K : ℝ :=
    boltzmannConstantInJoulesPerKelvin
        setup.constants.boltzmannConstant *
      temperatureInKelvins setup.blackbody.temperatureStorageUnit
        setup.blackbody.temperature with hK_def
  set h : ℝ :=
    planckConstantInJouleSeconds setup.constants.planckConstant with hh_def
  set c : ℝ :=
    speedInMetersPerSecond setup.constants.speedOfLight with hc_def
  have hE : 0 < E := by
    simpa [E] using _physical.centralEnergyPositive
  have hK : 0 < K := by
    exact mul_pos _physical.boltzmannConstantPositive
      _physical.temperaturePositive
  have hh : 0 < h := by
    simpa [h] using _physical.planckConstantPositive
  have hc : 0 < c := by
    simpa [c] using _physical.speedOfLightPositive
  have hread (x : ℝ) :
      energyInJoules
          ((CarriesDimension.toDimensionful UnitChoices.SI)
            (⟨x⟩ :
              WithDim
                (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)) = x := by
    simp [energyInJoules, CarriesDimension.toDimensionful_apply_apply]
  have hcomparison (u : ℝ) (hu : 0 < E + K * u) :
      (E + K * u) ^ 3 * (Real.exp (E / K) - 1) ≤
        E ^ 3 * (Real.exp (E / K + u) - 1) := by
    let perturbedEnergy : DimEnergy :=
      (CarriesDimension.toDimensionful UnitChoices.SI)
        (⟨E + K * u⟩ :
          WithDim
            (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)
    have hperturbedRead :
        energyInJoules perturbedEnergy = E + K * u := by
      simp [perturbedEnergy, hread]
    have hpeak :=
      _problem.centralEnergyIsSpectrumPeak perturbedEnergy
        (hperturbedRead ▸ hu)
    have hcentralSpectrum :=
      _laws.planckEnergySpectrum setup.photocells.centralAcceptedEnergy
        (by simpa [E] using hE)
    have hperturbedSpectrum :=
      _laws.planckEnergySpectrum perturbedEnergy
        (hperturbedRead ▸ hu)
    rw [hcentralSpectrum, hperturbedSpectrum] at hpeak
    rw [hperturbedRead] at hpeak
    change
      (2 * Real.pi * (E + K * u) ^ 3) /
            (h ^ 3 * c ^ 2 *
              (Real.exp ((E + K * u) / K) - 1)) ≤
        (2 * Real.pi * E ^ 3) /
            (h ^ 3 * c ^ 2 * (Real.exp (E / K) - 1)) at hpeak
    have hEK : (E + K * u) / K = E / K + u := by
      field_simp
    rw [hEK] at hpeak
    have hdenCentral :
        0 < h ^ 3 * c ^ 2 * (Real.exp (E / K) - 1) := by
      have : 1 < Real.exp (E / K) := Real.one_lt_exp_iff.mpr (div_pos hE hK)
      positivity
    have hdenPerturbed :
        0 < h ^ 3 * c ^ 2 * (Real.exp (E / K + u) - 1) := by
      have hx : 0 < E / K + u := by
        rw [← hEK]
        exact div_pos hu hK
      have : 1 < Real.exp (E / K + u) := Real.one_lt_exp_iff.mpr hx
      positivity
    have hcross :=
      (div_le_div_iff₀ hdenPerturbed hdenCentral).mp hpeak
    have hfactor : 0 < 2 * Real.pi * (h ^ 3 * c ^ 2) := by
      positivity
    apply (mul_le_mul_iff_of_pos_left hfactor).mp
    calc
      (2 * Real.pi * (h ^ 3 * c ^ 2)) *
          ((E + K * u) ^ 3 * (Real.exp (E / K) - 1)) =
          (2 * Real.pi * (E + K * u) ^ 3) *
            (h ^ 3 * c ^ 2 * (Real.exp (E / K) - 1)) := by ring
      _ ≤
          (2 * Real.pi * E ^ 3) *
            (h ^ 3 * c ^ 2 * (Real.exp (E / K + u) - 1)) := hcross
      _ =
          (2 * Real.pi * (h ^ 3 * c ^ 2)) *
            (E ^ 3 * (Real.exp (E / K + u) - 1)) := by ring
  have hexpRemainder :
      Filter.Tendsto
        (fun u : ℝ => (Real.exp u - 1 - u) / u)
        (nhds 0) (nhds 0) := by
    have hsmall := Real.exp_sub_sum_range_succ_isLittleO_pow 1
    simp [Finset.sum_range_succ, Nat.factorial] at hsmall
    rw [Asymptotics.isLittleO_iff_tendsto] at hsmall
    · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsmall
    · intro z hz
      subst z
      simp
  have hexpRemainderPunctured :
      Filter.Tendsto
        (fun u : ℝ => (Real.exp u - 1 - u) / u)
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 0) :=
    hexpRemainder.mono_left inf_le_left
  have hid :
      Filter.Tendsto (fun u : ℝ => u)
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 0) := by
    exact
      (show Filter.Tendsto (fun u : ℝ => u) (nhds 0) (nhds 0) from
        Filter.tendsto_id).mono_left inf_le_left
  have hpoly :
      Filter.Tendsto
        (fun u : ℝ =>
          3 * K * E ^ 2 + 3 * K ^ 2 * E * u + K ^ 3 * u ^ 2)
        (nhdsWithin 0 ({0}ᶜ : Set ℝ))
        (nhds (3 * K * E ^ 2 + 3 * K ^ 2 * E * 0 + K ^ 3 * 0 ^ 2)) :=
    ((tendsto_const_nhds.add
        (hid.const_mul (3 * K ^ 2 * E))).add
      ((hid.pow 2).const_mul (K ^ 3)))
  have hleft :
      Filter.Tendsto
        (fun u : ℝ =>
          (3 * K * E ^ 2 + 3 * K ^ 2 * E * u + K ^ 3 * u ^ 2) *
            (Real.exp (E / K) - 1))
        (nhdsWithin 0 ({0}ᶜ : Set ℝ))
        (nhds ((3 * K * E ^ 2) * (Real.exp (E / K) - 1))) := by
    simpa using hpoly.mul_const (Real.exp (E / K) - 1)
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 1) :=
    tendsto_const_nhds
  have hright :
      Filter.Tendsto
        (fun u : ℝ =>
          E ^ 3 * Real.exp (E / K) *
            (1 + (Real.exp u - 1 - u) / u))
        (nhdsWithin 0 ({0}ᶜ : Set ℝ))
        (nhds (E ^ 3 * Real.exp (E / K))) := by
    simpa using
      (hone.add hexpRemainderPunctured).const_mul
        (E ^ 3 * Real.exp (E / K))
  have hmodel :
      Filter.Tendsto
        (fun u : ℝ =>
          (3 * K * E ^ 2 + 3 * K ^ 2 * E * u + K ^ 3 * u ^ 2) *
              (Real.exp (E / K) - 1) -
            E ^ 3 * Real.exp (E / K) *
              (1 + (Real.exp u - 1 - u) / u))
        (nhdsWithin 0 ({0}ᶜ : Set ℝ))
        (nhds
          ((3 * K * E ^ 2) * (Real.exp (E / K) - 1) -
            E ^ 3 * Real.exp (E / K))) :=
    hleft.sub hright
  have hquotient :
      Filter.Tendsto
        (fun u : ℝ =>
          ((E + K * u) ^ 3 * (Real.exp (E / K) - 1) -
              E ^ 3 * (Real.exp (E / K + u) - 1)) / u)
        (nhdsWithin 0 ({0}ᶜ : Set ℝ))
        (nhds
          ((3 * K * E ^ 2) * (Real.exp (E / K) - 1) -
            E ^ 3 * Real.exp (E / K))) := by
    apply hmodel.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu
    rw [Real.exp_add]
    field_simp [hu]
    ring
  have hrightSubset : Set.Ioi (0 : ℝ) ⊆ {0}ᶜ := by
    intro u hu
    change 0 < u at hu
    simp [hu.ne']
  have hleftSubset : Set.Iio (0 : ℝ) ⊆ {0}ᶜ := by
    intro u hu
    change u < 0 at hu
    simp [hu.ne]
  have hquotientRight :=
    hquotient.mono_left (nhdsWithin_mono 0 hrightSubset)
  have hquotientLeft :=
    hquotient.mono_left (nhdsWithin_mono 0 hleftSubset)
  have hquotientNonpositive :
      ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ((E + K * u) ^ 3 * (Real.exp (E / K) - 1) -
            E ^ 3 * (Real.exp (E / K + u) - 1)) / u ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    change 0 < u at hu
    exact
      div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr
          (hcomparison u (by nlinarith [mul_pos hK hu]))) hu.le
  have hEKpos : 0 < E / K := div_pos hE hK
  have hnegativeBoundary : -E / K < 0 := by
    rw [show -E / K = -(E / K) by ring]
    linarith
  have hnearAtZero : ∀ᶠ u : ℝ in nhds 0, -E / K < u :=
    eventually_gt_nhds hnegativeBoundary
  have hnear : ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Iio 0), -E / K < u :=
    hnearAtZero.filter_mono inf_le_left
  have hquotientNonnegative :
      ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Iio 0), 0 ≤
        ((E + K * u) ^ 3 * (Real.exp (E / K) - 1) -
            E ^ 3 * (Real.exp (E / K + u) - 1)) / u := by
    filter_upwards [self_mem_nhdsWithin, hnear] with u hu hnear_u
    change u < 0 at hu
    apply div_nonneg_iff.mpr
    right
    refine ⟨sub_nonpos.mpr (hcomparison u ?_), hu.le⟩
    have hx : 0 < E / K + u := by
      rw [show -E / K = -(E / K) by ring] at hnear_u
      linarith
    have hscaled : 0 < K * (E / K + u) := mul_pos hK hx
    convert hscaled using 1
    field_simp
  have hcoefficientLe :
      (3 * K * E ^ 2) * (Real.exp (E / K) - 1) -
          E ^ 3 * Real.exp (E / K) ≤ 0 :=
    le_of_tendsto hquotientRight hquotientNonpositive
  have hcoefficientGe :
      0 ≤ (3 * K * E ^ 2) * (Real.exp (E / K) - 1) -
          E ^ 3 * Real.exp (E / K) :=
    ge_of_tendsto hquotientLeft hquotientNonnegative
  have hcoefficient :
      (3 * K * E ^ 2) * (Real.exp (E / K) - 1) -
          E ^ 3 * Real.exp (E / K) = 0 :=
    le_antisymm hcoefficientLe hcoefficientGe
  change 3 * (1 - Real.exp (-(E / K))) = E / K
  rw [Real.exp_neg]
  field_simp [hK.ne', Real.exp_ne_zero]
  nlinarith [sq_pos_of_pos hE]

/-!
Combining the narrow-band radiation approximation with ideal conversion,
`P = V I`, and Ohm's law yields the current-squared power balance.  This is a
derived relation, not a premise of the final numerical result.
-/
lemma motorCurrent_squared_times_resistance_eq_narrowBandPower
    (setup : BlackbodyPhotocellMotorSetup)
    (_laws : SatisfiesBlackbodyPhotocellMotorLaws setup) :
    currentInAmperes setup.motor.current ^ 2 *
        resistanceInOhms setup.motor.resistance =
      4 * Real.pi * lengthInMeters setup.blackbody.radius ^ 2 *
        spectralRadiantExitancePerJouleInSI
          (setup.blackbody.spectralRadiantExitancePerEnergy
            setup.photocells.centralAcceptedEnergy) *
        (2 * energyInJoules setup.photocells.acceptanceHalfWidth) := by
  rw [← _laws.narrowBandCapturedPower]
  rw [← _laws.allCapturedPowerBecomesElectricalPower]
  rw [_laws.electricalPowerLaw, _laws.ohmsLaw]
  ring

/-! ## Displayed choices and final formalization target -/

/-- Labels of the four displayed answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Current in amperes printed beside each answer label. -/
def displayedAnswerCurrentInAmperes : AnswerChoice → ℝ
  | .A => 911 / 10
  | .B => 933 / 10
  | .C => 862 / 10
  | .D => 886 / 10

/-- The dataset records choice A; this metadata is not accepted as a premise. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-!
The circuit current lies within `0.2 A` of the displayed `91.1 A`, and choice
A is at least as close as every displayed alternative.  The tolerance records
the narrow-band approximation and the limited precision of the supplied
physical data; the substantive conclusion is selection of answer A.

This declaration corresponds to blueprint label
`thm:physics:phyx_mini_0614:target`.
-/
theorem motorCurrent_matches_answer_A
    (setup : BlackbodyPhotocellMotorSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryBlackbodyPhotocellFigure setup)
    (_constants : UsesStandardRadiationConstants setup)
    (_physical : HasPhysicalBlackbodyPhotocellParameters setup)
    (_laws : SatisfiesBlackbodyPhotocellMotorLaws setup) :
    |currentInAmperes setup.motor.current -
        displayedAnswerCurrentInAmperes .A| ≤ 1 / 5 ∧
      ∀ alternative : AnswerChoice,
        |currentInAmperes setup.motor.current -
            displayedAnswerCurrentInAmperes .A| ≤
          |currentInAmperes setup.motor.current -
            displayedAnswerCurrentInAmperes alternative| := by
  set I : ℝ := currentInAmperes setup.motor.current with hI_def
  set E : ℝ :=
    energyInJoules setup.photocells.centralAcceptedEnergy with hE_def
  set K : ℝ :=
    boltzmannConstantInJoulesPerKelvin
        setup.constants.boltzmannConstant *
      temperatureInKelvins setup.blackbody.temperatureStorageUnit
        setup.blackbody.temperature with hK_def
  set h : ℝ :=
    planckConstantInJouleSeconds setup.constants.planckConstant with hh_def
  set c : ℝ :=
    speedInMetersPerSecond setup.constants.speedOfLight with hc_def
  set x : ℝ := E / K with hx_def
  have hI : 0 ≤ I := by
    change 0 ≤
      ((setup.motor.current UnitChoices.SI).val : ℝ)
    positivity
  have hE : 0 < E := by
    simpa [E] using _physical.centralEnergyPositive
  have hK : 0 < K := by
    exact mul_pos _physical.boltzmannConstantPositive
      _physical.temperaturePositive
  have hh : 0 < h := by
    simpa [h] using _physical.planckConstantPositive
  have hc : 0 < c := by
    simpa [c] using _physical.speedOfLightPositive
  have hx : 0 < x := div_pos hE hK
  have hpeak :=
    centralAcceptedEnergy_satisfies_wienPeakEquation
      setup _problem _physical _laws
  change 3 * (1 - Real.exp (-x)) = x at hpeak
  have hxlt3 : x < 3 := by
    nlinarith only [hpeak, Real.exp_pos (-x)]
  have hplanck :=
    _laws.planckEnergySpectrum setup.photocells.centralAcceptedEnergy
      (by simpa [E] using hE)
  have hbalance :=
    motorCurrent_squared_times_resistance_eq_narrowBandPower setup _laws
  have hhCalibration :
      h = 2 * Real.pi * (Constants.ℏ : ℝ) := by
    simpa [h] using _constants.planckConstantCalibration
  have hcCalibration : c = 299792458 := by
    rw [hc_def, _constants.speedOfLightCalibration]
    simp [speedInMetersPerSecond, DimSpeed.speedOfLight_in_SI]
  have hKCalibration :
      K = (1380649 / 10 ^ 29 : ℝ) * 5000 := by
    rw [hK_def, _constants.boltzmannConstantCalibration,
      _problem.blackbodyTemperatureKelvins]
  have hECalibration : E = x * K := by
    rw [hx_def]
    field_simp
  have hexpRelation : Real.exp x - 1 = x / (3 - x) := by
    have hpeak' := hpeak
    rw [Real.exp_neg] at hpeak'
    field_simp [Real.exp_ne_zero] at hpeak'
    rw [eq_div_iff (sub_ne_zero.mpr (by linarith only [hxlt3]))]
    nlinarith only [hpeak']
  have hxge2 : 2 ≤ x := by
    have hexact : Real.exp x = 3 / (3 - x) := by
      have hpeak' := hpeak
      rw [Real.exp_neg] at hpeak'
      field_simp [Real.exp_ne_zero] at hpeak'
      rw [eq_div_iff (sub_ne_zero.mpr (by linarith only [hxlt3]))]
      nlinarith only [hpeak']
    by_contra hnot
    have hxlt2 : x < 2 := lt_of_not_ge hnot
    have hexplower : 1 + x < Real.exp x := by
      simpa [add_comm] using Real.add_one_lt_exp (ne_of_gt hx)
    rw [hexact] at hexplower
    have hcross := (lt_div_iff₀ (sub_pos.mpr hxlt3)).mp hexplower
    nlinarith only [hcross,
      mul_pos hx (sub_pos.mpr (by linarith only [hxlt2] : x < 2))]
  have hgStrict :
      ∀ {a b : ℝ}, 2 ≤ a → a < b →
        Real.exp (-a) - (1 - a / 3) <
          Real.exp (-b) - (1 - b / 3) := by
    intro a b ha hab
    have hexpTwoPositive : (3 : ℝ) < Real.exp 2 := by
      have htwo := Real.add_one_lt_exp (x := (2 : ℝ)) (by norm_num)
      norm_num at htwo ⊢
      exact htwo
    have hexpTwo : Real.exp (-2) < (1 : ℝ) / 3 := by
      rw [Real.exp_neg, one_div]
      exact
        (inv_lt_inv₀ (Real.exp_pos 2) (by norm_num)).mpr
          hexpTwoPositive
    have hexpa : Real.exp (-a) < (1 : ℝ) / 3 :=
      lt_of_le_of_lt (Real.exp_le_exp.mpr (by linarith only [ha])) hexpTwo
    have hd : 0 < b - a := sub_pos.mpr hab
    have hlinear :=
      Real.one_sub_lt_exp_neg (x := b - a) (ne_of_gt hd)
    have hmul :=
      mul_lt_mul_of_pos_left hlinear (Real.exp_pos (-a))
    rw [← Real.exp_add] at hmul
    have hadd : -a + -(b - a) = -b := by ring
    rw [hadd] at hmul
    nlinarith only [hmul, mul_pos hd (sub_pos.mpr hexpa)]
  have hroot :
      Real.exp (-x) - (1 - x / 3) = 0 := by
    nlinarith only [hpeak]
  have hExpLowerEndpoint :
      (3 : ℝ) / (3 - 28214 / 10000) <
        Real.exp (28214 / 10000) := by
    have hlower := Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ 14107 / 20000 by norm_num) 7
    have hpow := pow_le_pow_left₀
      (by
        norm_num [Finset.sum_range_succ, Nat.factorial] :
        (0 : ℝ) ≤
          ∑ i ∈ Finset.range 7,
            (14107 / 20000 : ℝ) ^ i / i.factorial)
      hlower 4
    rw [← Real.exp_nat_mul] at hpow
    norm_num [Finset.sum_range_succ, Nat.factorial] at hpow ⊢
    exact lt_of_lt_of_le (by norm_num) hpow
  have hgLowerEndpoint :
      Real.exp (-(28214 / 10000 : ℝ)) -
          (1 - (28214 / 10000 : ℝ) / 3) < 0 := by
    have hinv :=
      (inv_lt_inv₀
        (Real.exp_pos (28214 / 10000 : ℝ))
        (by norm_num :
          (0 : ℝ) < 3 / (3 - 28214 / 10000))).mpr
        hExpLowerEndpoint
    rw [← Real.exp_neg] at hinv
    norm_num at hinv ⊢
    exact hinv
  have hExpUpperEndpoint :
      Real.exp (28215 / 10000 : ℝ) <
        3 / (3 - 28215 / 10000) := by
    have hupper := Real.exp_bound'
      (show (0 : ℝ) ≤ 5643 / 8000 by norm_num)
      (show (5643 / 8000 : ℝ) ≤ 1 by norm_num)
      (show 0 < 5 by norm_num)
    have hpow :=
      pow_le_pow_left₀ (Real.exp_nonneg _) hupper 4
    rw [← Real.exp_nat_mul] at hpow
    norm_num [Finset.sum_range_succ, Nat.factorial] at hpow ⊢
    exact lt_of_le_of_lt hpow (by norm_num)
  have hgUpperEndpoint :
      0 < Real.exp (-(28215 / 10000 : ℝ)) -
          (1 - (28215 / 10000 : ℝ) / 3) := by
    have hinv :=
      (inv_lt_inv₀
        (by norm_num :
          (0 : ℝ) < 3 / (3 - 28215 / 10000))
        (Real.exp_pos (28215 / 10000 : ℝ))).mpr
        hExpUpperEndpoint
    rw [← Real.exp_neg] at hinv
    norm_num at hinv ⊢
    exact hinv
  have hxLower : (28214 / 10000 : ℝ) < x := by
    by_contra hnot
    have hxle : x ≤ (28214 / 10000 : ℝ) := le_of_not_gt hnot
    rcases eq_or_lt_of_le hxle with hxeq | hxlt
    · rw [← hxeq] at hgLowerEndpoint
      linarith only [hroot, hgLowerEndpoint]
    · have hmono := hgStrict hxge2 hxlt
      linarith only [hroot, hmono, hgLowerEndpoint]
  have hxUpper : x < (28215 / 10000 : ℝ) := by
    by_contra hnot
    have hle : (28215 / 10000 : ℝ) ≤ x := le_of_not_gt hnot
    rcases eq_or_lt_of_le hle with hxeq | hlt
    · rw [← hxeq] at hroot
      linarith only [hroot, hgUpperEndpoint]
    · have hmono :=
        hgStrict (by norm_num : (2 : ℝ) ≤ 28215 / 10000) hlt
      linarith only [hroot, hmono, hgUpperEndpoint]
  rw [_problem.motorResistanceOhms, _problem.blackbodyRadiusMeters,
    hplanck, _problem.acceptanceHalfWidthIsOnePercent] at hbalance
  change
    I ^ 2 * 1000 =
      4 * Real.pi * (123 / 100) ^ 2 *
          ((2 * Real.pi * E ^ 3) /
            (h ^ 3 * c ^ 2 * (Real.exp x - 1))) *
        (2 * ((1 / 100 : ℝ) * E)) at hbalance
  have hpower :
      I ^ 2 * 1000 =
        (123 / 100 : ℝ) ^ 2 *
          ((1380649 / 10 ^ 29 : ℝ) * 5000) ^ 4 *
          x ^ 3 * (3 - x) /
          (50 * Real.pi * (Constants.ℏ : ℝ) ^ 3 *
            299792458 ^ 2) := by
    rw [hbalance, hhCalibration,
      hcCalibration, hECalibration, hKCalibration, hexpRelation]
    field_simp [Real.pi_ne_zero, Constants.ℏ_ne_zero, hx.ne',
      (sub_ne_zero.mpr (by linarith only [hxlt3] : x ≠ 3))]
    ring
  have hPiLower : (3.14 : ℝ) < Real.pi := by
    have hseries : Real.sqrtTwoAddSeries 0 4 ≤
        (2 : ℝ) - ((314 / 100 : ℝ) / 2 ^ (4 + 1)) ^ 2 := by
      rw [Real.sqrtTwoAddSeries_succ]
      apply le_trans (Real.sqrtTwoAddSeries_monotone_left
        (show Real.sqrt (2 + 0) ≤ (338 / 239 : ℝ) by
          rw [Real.sqrt_le_iff]
          constructor <;> norm_num) 3)
      rw [Real.sqrtTwoAddSeries_succ]
      apply le_trans (Real.sqrtTwoAddSeries_monotone_left
        (show Real.sqrt (2 + (338 / 239 : ℝ)) ≤
            (704 / 381 : ℝ) by
          rw [Real.sqrt_le_iff]
          constructor <;> norm_num) 2)
      rw [Real.sqrtTwoAddSeries_succ]
      apply le_trans (Real.sqrtTwoAddSeries_monotone_left
        (show Real.sqrt (2 + (704 / 381 : ℝ)) ≤
            (1940 / 989 : ℝ) by
          rw [Real.sqrt_le_iff]
          constructor <;> norm_num) 1)
      rw [Real.sqrtTwoAddSeries_succ]
      apply le_trans (Real.sqrtTwoAddSeries_monotone_left
        (show Real.sqrt (2 + (1940 / 989 : ℝ)) ≤
            (1447 / 727 : ℝ) by
          rw [Real.sqrt_le_iff]
          constructor <;> norm_num) 0)
      simp [Real.sqrtTwoAddSeries]
      norm_num
    have hsqrt : (314 / 100 : ℝ) / 2 ^ (4 + 1) ≤
        Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) := by
      apply Real.le_sqrt_of_sq_le
      linarith only [hseries]
    have hscale : (314 / 100 : ℝ) ≤
        2 ^ (4 + 1) *
          Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) := by
      nlinarith only [hsqrt]
    have htpos : 0 < Real.pi / 2 ^ (4 + 2) := by positivity
    have htle : Real.pi / 2 ^ (4 + 2) ≤ 1 := by
      have hpi := Real.pi_le_four
      norm_num at hpi ⊢
      linarith only [hpi]
    have hsinBound :=
      Real.sin_bound (x := Real.pi / 2 ^ (4 + 2))
        (abs_le.mpr ⟨by linarith only [htpos], htle⟩)
    rw [abs_of_nonneg htpos.le] at hsinBound
    have hsineLt :
        Real.sin (Real.pi / 2 ^ (4 + 2)) <
          Real.pi / 2 ^ (4 + 2) := by
      have hupper := (abs_sub_le_iff.mp hsinBound).1
      nlinarith only [hupper, mul_pos (pow_pos htpos 3)
        (by
          nlinarith only [htle] :
          0 < (1 / 6 : ℝ) -
            (Real.pi / 2 ^ (4 + 2)) * (5 / 96))]
    rw [Real.sin_pi_over_two_pow_succ] at hsineLt
    norm_num only [Nat.reduceAdd, Nat.reducePow] at hscale hsineLt ⊢
    exact lt_of_le_of_lt hscale (by nlinarith only [hsineLt])
  have hPiUpper : Real.pi < (3.15 : ℝ) := by
    have hseries :
        (2 : ℝ) -
            (((315 / 100 : ℝ) - 1 / (4 : ℝ) ^ 4) /
              (2 : ℝ) ^ (4 + 1)) ^ 2 ≤
          Real.sqrtTwoAddSeries 0 4 := by
      rw [Real.sqrtTwoAddSeries_succ]
      apply le_trans ?_ (Real.sqrtTwoAddSeries_monotone_left
        (show (41 / 29 : ℝ) ≤ Real.sqrt (2 + 0) by
          apply Real.le_sqrt_of_sq_le
          norm_num) 3)
      rw [Real.sqrtTwoAddSeries_succ]
      apply le_trans ?_ (Real.sqrtTwoAddSeries_monotone_left
        (show (109 / 59 : ℝ) ≤ Real.sqrt (2 + (41 / 29 : ℝ)) by
          apply Real.le_sqrt_of_sq_le
          norm_num) 2)
      rw [Real.sqrtTwoAddSeries_succ]
      apply le_trans ?_ (Real.sqrtTwoAddSeries_monotone_left
        (show (865 / 441 : ℝ) ≤ Real.sqrt (2 + (109 / 59 : ℝ)) by
          apply Real.le_sqrt_of_sq_le
          norm_num) 1)
      rw [Real.sqrtTwoAddSeries_succ]
      apply le_trans ?_ (Real.sqrtTwoAddSeries_monotone_left
        (show (412 / 207 : ℝ) ≤
            Real.sqrt (2 + (865 / 441 : ℝ)) by
          apply Real.le_sqrt_of_sq_le
          norm_num) 0)
      simp [Real.sqrtTwoAddSeries]
      norm_num
    have hypos : 0 ≤
        ((315 / 100 : ℝ) - 1 / (4 : ℝ) ^ 4) /
          (2 : ℝ) ^ (4 + 1) := by
      norm_num
    have hsqrt :
        Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) ≤
          ((315 / 100 : ℝ) - 1 / (4 : ℝ) ^ 4) /
            (2 : ℝ) ^ (4 + 1) := by
      rw [Real.sqrt_le_left hypos]
      linarith only [hseries]
    have hscale :
        (2 : ℝ) ^ (4 + 1) *
              Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) +
            1 / (4 : ℝ) ^ 4 ≤
          315 / 100 := by
      nlinarith only [hsqrt]
    have htpos : 0 < Real.pi / 2 ^ (4 + 2) := by positivity
    have htle : Real.pi / 2 ^ (4 + 2) ≤ 1 := by
      have hpi := Real.pi_le_four
      norm_num at hpi ⊢
      linarith only [hpi]
    have hsinBound :=
      Real.sin_bound (x := Real.pi / 2 ^ (4 + 2))
        (abs_le.mpr ⟨by linarith only [htpos], htle⟩)
    rw [abs_of_nonneg htpos.le] at hsinBound
    have hsineGt :
        Real.pi / 2 ^ (4 + 2) -
              (Real.pi / 2 ^ (4 + 2)) ^ 3 / 4 <
            Real.sin (Real.pi / 2 ^ (4 + 2)) := by
      have hlower := (abs_sub_le_iff.mp hsinBound).2
      nlinarith only [hlower, mul_pos (pow_pos htpos 3)
        (by
          nlinarith only [htle] :
          0 < (1 / 4 : ℝ) -
            (1 / 6 + (Real.pi / 2 ^ (4 + 2)) * (5 / 96)))]
    have htcube :
        (Real.pi / 2 ^ (4 + 2)) ^ 3 / 4 ≤
          (4 / 2 ^ (4 + 2) : ℝ) ^ 3 / 4 := by
      gcongr
      exact Real.pi_le_four
    rw [Real.sin_pi_over_two_pow_succ] at hsineGt
    have hpiSeries :
        Real.pi <
          (2 : ℝ) ^ (4 + 1) *
              Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) +
            1 / (4 : ℝ) ^ 4 := by
      norm_num only [Nat.reduceAdd, Nat.reducePow] at hsineGt htcube ⊢
      nlinarith only [hsineGt, htcube]
    norm_num only [Nat.reduceAdd, Nat.reducePow] at hpiSeries hscale
    norm_num only [OfScientific.ofScientific, HPow.hPow, Pow.pow,
      Nat.cast_ofNat] at ⊢
    exact lt_of_lt_of_le hpiSeries hscale
  have hshapeLower :
      (28215 / 10000 : ℝ) ^ 3 * (3 - 28215 / 10000) <
        x ^ 3 * (3 - x) := by
    have hd : 0 < (28215 / 10000 : ℝ) - x := by
      linarith only [hxUpper]
    have hp : 0 <
        x ^ 3 + x ^ 2 * (28215 / 10000 : ℝ) +
            x * (28215 / 10000 : ℝ) ^ 2 +
            (28215 / 10000 : ℝ) ^ 3 -
          3 * (x ^ 2 + x * (28215 / 10000 : ℝ) +
            (28215 / 10000 : ℝ) ^ 2) := by
      nlinarith only [hxLower, hxUpper, sq_nonneg (x - 5 / 2)]
    nlinarith only [mul_pos hd hp]
  have hshapeUpper :
      x ^ 3 * (3 - x) <
        (28214 / 10000 : ℝ) ^ 3 * (3 - 28214 / 10000) := by
    have hd : 0 < x - (28214 / 10000 : ℝ) := by
      linarith only [hxLower]
    have hp : 0 <
        (28214 / 10000 : ℝ) ^ 3 +
            (28214 / 10000 : ℝ) ^ 2 * x +
            (28214 / 10000 : ℝ) * x ^ 2 + x ^ 3 -
          3 * ((28214 / 10000 : ℝ) ^ 2 +
            (28214 / 10000 : ℝ) * x + x ^ 2) := by
      nlinarith only [hxLower, hxUpper, sq_nonneg (x - 5 / 2)]
    nlinarith only [mul_pos hd hp]
  let A : ℝ :=
    (123 / 100 : ℝ) ^ 2 *
      ((1380649 / 10 ^ 29 : ℝ) * 5000) ^ 4
  have hA : 0 < A := by norm_num [A]
  have hPlanckCube : 0 < (Constants.ℏ : ℝ) ^ 3 :=
    pow_pos Constants.ℏ_pos 3
  have hdenominator :
      0 < 50 * Real.pi * (Constants.ℏ : ℝ) ^ 3 *
        299792458 ^ 2 := by
    positivity
  have hnumerator :
      (123 / 100 : ℝ) ^ 2 *
            ((1380649 / 10 ^ 29 : ℝ) * 5000) ^ 4 *
            x ^ 3 * (3 - x) =
        A * (x ^ 3 * (3 - x)) := by
    simp [A]
    ring
  have hpowerLower :
      (8262810 : ℝ) <
        (123 / 100 : ℝ) ^ 2 *
          ((1380649 / 10 ^ 29 : ℝ) * 5000) ^ 4 *
          x ^ 3 * (3 - x) /
          (50 * Real.pi * (Constants.ℏ : ℝ) ^ 3 *
            299792458 ^ 2) := by
    rw [hnumerator]
    apply (lt_div_iff₀ hdenominator).mpr
    calc
      (8262810 : ℝ) *
            (50 * Real.pi * (Constants.ℏ : ℝ) ^ 3 *
              299792458 ^ 2) <
          8262810 *
            (50 * (315 / 100 : ℝ) * (Constants.ℏ : ℝ) ^ 3 *
              299792458 ^ 2) := by
        gcongr <;> norm_num [Constants.ℏ] <;>
          linarith only [hPiUpper]
      _ < A *
          ((28215 / 10000 : ℝ) ^ 3 *
            (3 - 28215 / 10000)) := by
        norm_num [A, Constants.ℏ]
      _ < A * (x ^ 3 * (3 - x)) :=
        mul_lt_mul_of_pos_left hshapeLower hA
  have hpowerUpper :
      (123 / 100 : ℝ) ^ 2 *
            ((1380649 / 10 ^ 29 : ℝ) * 5000) ^ 4 *
            x ^ 3 * (3 - x) /
            (50 * Real.pi * (Constants.ℏ : ℝ) ^ 3 *
              299792458 ^ 2) <
        8335690 := by
    rw [hnumerator]
    apply (div_lt_iff₀ hdenominator).mpr
    calc
      A * (x ^ 3 * (3 - x)) <
          A * ((28214 / 10000 : ℝ) ^ 3 *
            (3 - 28214 / 10000)) :=
        mul_lt_mul_of_pos_left hshapeUpper hA
      _ < (8335690 : ℝ) *
          (50 * (314 / 100 : ℝ) * (Constants.ℏ : ℝ) ^ 3 *
            299792458 ^ 2) := by
        norm_num [A, Constants.ℏ]
      _ < 8335690 *
          (50 * Real.pi * (Constants.ℏ : ℝ) ^ 3 *
            299792458 ^ 2) := by
        gcongr <;> norm_num [Constants.ℏ] <;>
          linarith only [hPiLower]
  have hIsquaredLower : (8262810 : ℝ) < I ^ 2 * 1000 := by
    rw [hpower]
    exact hpowerLower
  have hIsquaredUpper : I ^ 2 * 1000 < (8335690 : ℝ) := by
    rw [hpower]
    exact hpowerUpper
  have hILower : (909 / 10 : ℝ) < I := by
    nlinarith only [hI, hIsquaredLower,
      sq_nonneg (I - 909 / 10), sq_nonneg (I - 913 / 10)]
  have hIUpper : I < (913 / 10 : ℝ) := by
    nlinarith only [hI, hIsquaredUpper,
      sq_nonneg (I - 909 / 10), sq_nonneg (I - 913 / 10)]
  constructor
  · change |I - (911 / 10 : ℝ)| ≤ 1 / 5
    rw [abs_le]
    constructor <;> linarith only [hILower, hIUpper]
  · intro alternative
    change
      |I - (911 / 10 : ℝ)| ≤
        |I - displayedAnswerCurrentInAmperes alternative|
    by_cases hsign : I - (911 / 10 : ℝ) ≤ 0
    · rw [abs_of_nonpos hsign]
      cases alternative with
      | A =>
          simpa [displayedAnswerCurrentInAmperes,
            abs_of_nonpos hsign]
      | B =>
          simp only [displayedAnswerCurrentInAmperes]
          rw [abs_of_nonpos (by linarith only [hIUpper])]
          linarith only [hILower, hIUpper, hsign]
      | C =>
          simp only [displayedAnswerCurrentInAmperes]
          rw [abs_of_nonneg (by linarith only [hILower])]
          linarith only [hILower, hIUpper, hsign]
      | D =>
          simp only [displayedAnswerCurrentInAmperes]
          rw [abs_of_nonneg (by linarith only [hILower])]
          linarith only [hILower, hIUpper, hsign]
    · rw [abs_of_nonneg (le_of_not_ge hsign)]
      cases alternative with
      | A =>
          simpa [displayedAnswerCurrentInAmperes,
            abs_of_nonneg (le_of_not_ge hsign)]
      | B =>
          simp only [displayedAnswerCurrentInAmperes]
          rw [abs_of_nonpos (by linarith only [hIUpper])]
          linarith only [hILower, hIUpper, hsign]
      | C =>
          simp only [displayedAnswerCurrentInAmperes]
          rw [abs_of_nonneg (by linarith only [hILower])]
          linarith only [hILower, hIUpper, hsign]
      | D =>
          simp only [displayedAnswerCurrentInAmperes]
          rw [abs_of_nonneg (by linarith only [hILower])]
          linarith only [hILower, hIUpper, hsign]

end PhyXMiniProblems.ProblemPhyXMini0614
