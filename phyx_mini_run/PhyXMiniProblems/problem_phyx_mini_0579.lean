import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0579

open Dimension

/-!
# Natural carbon-dioxide laser action in the Martian atmosphere

Sunlight pumps carbon-dioxide molecules near an altitude of about `75 km` on
Mars.  The supplied energy-level diagram shows levels `E₀ = 0 eV`,
`E₁ = 0.165 eV`, and `E₂ = 0.289 eV`, an upward pump arrow from `E₀` to `E₂`,
and a downward lasing arrow from `E₂` to `E₁`.  Population inversion occurs
between `E₂` and `E₁`.

Energies, altitude, wavelength, frequency, and Planck's constant below are
unit-independent physical quantities.  Real numbers are used only for named
unit readouts, approximate-data tolerances, and values printed in the figure
or answer choices.  In particular, the lasing wavelength is an independent
field of the setup and is not defined from the recorded answer.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical length, used for altitude and wavelength. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical frequency, carrying inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- The physical dimension of action, `energy * time`. -/
def actionDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative physical quantity with the dimension of Planck's constant. -/
abbrev PlanckConstantQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in kilometres. -/
def lengthInKilometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.kilometers length

/-- Read a physical wavelength in micrometres. -/
def lengthInMicrometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.micrometers length

/-- Read a physical energy in coherent-SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- The joule readout of Physlib's exact dimensionful electron volt. -/
def electronVoltInJoules : ℝ :=
  energyInJoules DimEnergy.electronVolt

/-- Read a physical energy in electron volts. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / electronVoltInJoules

/-- Read a physical frequency in hertz. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Read a physical action in joule-seconds. -/
def planckConstantInJouleSeconds
    (constant : PlanckConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-- The exact SI value assigned to the ordinary Planck constant. -/
def planckConstantSIValue : ℝ :=
  (6.62607015 : ℝ) * 10 ^ (-34 : ℤ)

/-- Physlib's exact speed of light, read in metres per second. -/
def speedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-! ## Physical roles and the supplied energy-level figure -/

/-- Planet on which the illuminated atmospheric molecules are located. -/
inductive Planet where
  | Mars
  | other
  deriving DecidableEq, Repr

/-- Environment occupied by the illuminated molecules. -/
inductive MolecularEnvironment where
  | atmosphere
  | other
  deriving DecidableEq, Repr

/-- Molecular species undergoing the natural laser action. -/
inductive MoleculeSpecies where
  | carbonDioxide
  | other
  deriving DecidableEq, Repr

/-- External mechanism that pumps the molecular energy levels. -/
inductive PumpSource where
  | sunlight
  | other
  deriving DecidableEq, Repr

/-- The three horizontal molecular energy levels in the supplied diagram. -/
inductive MolecularEnergyLevel where
  | E0
  | E1
  | E2
  deriving DecidableEq, Fintype, Repr

/-- The two arrows visible in the supplied energy-level diagram. -/
inductive FigureTransitionArrow where
  | pumpE0ToE2
  | laserE2ToE1
  deriving DecidableEq, Fintype, Repr

/-- Vertical direction in which an arrow is drawn. -/
inductive ArrowDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- The initial level of each transition represented in the figure. -/
def expectedArrowInitialLevel : FigureTransitionArrow → MolecularEnergyLevel
  | .pumpE0ToE2 => .E0
  | .laserE2ToE1 => .E2

/-- The final level of each transition represented in the figure. -/
def expectedArrowFinalLevel : FigureTransitionArrow → MolecularEnergyLevel
  | .pumpE0ToE2 => .E2
  | .laserE2ToE1 => .E1

/-- The direction in which each transition arrow is drawn. -/
def expectedArrowDirection : FigureTransitionArrow → ArrowDirection
  | .pumpE0ToE2 => .upward
  | .laserE2ToE1 => .downward

/-!
Literal data carried by image 579.  The printed energies are scalar
electron-volt readouts, separate from the physical energies in the setup.
-/
structure CO2EnergyLevelFigure where
  levelLineShown : MolecularEnergyLevel → Bool
  printedEnergyInElectronVolts : MolecularEnergyLevel → ℝ
  arrowShown : FigureTransitionArrow → Bool
  arrowInitialLevel : FigureTransitionArrow → MolecularEnergyLevel
  arrowFinalLevel : FigureTransitionArrow → MolecularEnergyLevel
  arrowDirection : FigureTransitionArrow → ArrowDirection

/-! ## Independent physical setup -/

/-!
The wavelength, frequency, and photon energy of the lasing radiation are
independent observables.  The hypotheses below relate them through physical
laws; no answer-choice wavelength is stored in this structure.
-/
structure MarsCO2LaserSetup where
  planet : Planet
  environment : MolecularEnvironment
  molecule : MoleculeSpecies
  pumpSource : PumpSource
  altitude : LengthQuantity
  statedAltitudeToleranceInKilometers : ℝ
  energyAtLevel : MolecularEnergyLevel → DimEnergy
  populationCountAtLevel : MolecularEnergyLevel → ℕ
  naturalLaserActionOccurs : Bool
  emittedPhotonEnergy : DimEnergy
  emittedFrequency : FrequencyQuantity
  emittedWavelength : LengthQuantity
  planckConstant : PlanckConstantQuantity
  figure : CO2EnergyLevelFigure

/-! ## Scenario, figure evidence, admissibility, and governing laws -/

/-- A scalar readout lies within a stated nonnegative tolerance of a value. -/
def IsAbout (actual nominal tolerance : ℝ) : Prop :=
  0 ≤ tolerance ∧ |actual - nominal| ≤ tolerance

/-!
The prose data: illuminated carbon dioxide in the Martian atmosphere near
`75 km`, with a population inversion from `E₁` to `E₂` and natural laser
action present.  These are scenario assumptions, not conclusions about the
wavelength.
-/
structure MatchesMarsCO2LaserScenario
    (setup : MarsCO2LaserSetup) : Prop where
  onMars : setup.planet = .Mars
  inAtmosphere : setup.environment = .atmosphere
  isCarbonDioxide : setup.molecule = .carbonDioxide
  pumpedBySunlight : setup.pumpSource = .sunlight
  altitudeAboutSeventyFiveKilometers :
    IsAbout (lengthInKilometers setup.altitude) 75
      setup.statedAltitudeToleranceInKilometers
  populationInversionBetweenE2AndE1 :
    setup.populationCountAtLevel .E1 < setup.populationCountAtLevel .E2
  laserActionOccurs : setup.naturalLaserActionOccurs = true

/-!
Primary-image evidence: all three level lines and both arrows are present;
the level labels are `0`, `0.165`, and `0.289 eV`; and the physical level
energies agree with those printed readouts.
-/
structure MatchesSuppliedCO2EnergyLevelFigure
    (setup : MarsCO2LaserSetup) : Prop where
  everyLevelLineShown :
    ∀ level, setup.figure.levelLineShown level = true
  groundLevelLabel :
    setup.figure.printedEnergyInElectronVolts .E0 = 0
  lowerLaserLevelLabel :
    setup.figure.printedEnergyInElectronVolts .E1 = (165 : ℝ) / 1000
  upperLaserLevelLabel :
    setup.figure.printedEnergyInElectronVolts .E2 = (289 : ℝ) / 1000
  labelsRepresentPhysicalEnergies : ∀ level,
    energyInElectronVolts (setup.energyAtLevel level) =
      setup.figure.printedEnergyInElectronVolts level
  everyArrowShown :
    ∀ arrow, setup.figure.arrowShown arrow = true
  arrowInitialLevels : ∀ arrow,
    setup.figure.arrowInitialLevel arrow = expectedArrowInitialLevel arrow
  arrowFinalLevels : ∀ arrow,
    setup.figure.arrowFinalLevel arrow = expectedArrowFinalLevel arrow
  arrowDirections : ∀ arrow,
    setup.figure.arrowDirection arrow = expectedArrowDirection arrow

/-- Positivity and ordering conditions for the physical quantities. -/
structure HasPhysicalCO2LaserQuantities
    (setup : MarsCO2LaserSetup) : Prop where
  altitudeNonnegative :
    0 ≤ lengthInMeters setup.altitude
  levelEnergiesNonnegative :
    ∀ level, 0 ≤ energyInJoules (setup.energyAtLevel level)
  laserLevelsStrictlyOrdered :
    energyInJoules (setup.energyAtLevel .E1) <
      energyInJoules (setup.energyAtLevel .E2)
  emittedPhotonEnergyPositive :
    0 < energyInJoules setup.emittedPhotonEnergy
  emittedFrequencyPositive :
    0 < frequencyInHertz setup.emittedFrequency
  emittedWavelengthPositive :
    0 < lengthInMeters setup.emittedWavelength
  planckConstantPositive :
    0 < planckConstantInJouleSeconds setup.planckConstant

/-!
The exact SI calibration of ordinary Planck's constant.  Physlib provides a
scalar reduced Planck constant, but no dimensionful ordinary `h` suitable for
this photon-wavelength model.
-/
structure UsesOrdinaryPlanckConstant
    (setup : MarsCO2LaserSetup) : Prop where
  planckConstantCalibration :
    planckConstantInJouleSeconds setup.planckConstant =
      planckConstantSIValue

/-!
Governing laws for the `E₂ → E₁` laser emission:

* the photon carries the molecular level-energy drop;
* the Planck--Einstein relation is `E = h ν`;
* the vacuum light-wave relation is `c = λ ν`.

These are general modeling relations among independent observables.  None
contains `10.0 μm` or an answer-choice label.
-/
structure SatisfiesCO2LaserLaws
    (setup : MarsCO2LaserSetup) : Prop where
  photonCarriesLevelEnergyDrop :
    energyInJoules setup.emittedPhotonEnergy =
      energyInJoules (setup.energyAtLevel .E2) -
        energyInJoules (setup.energyAtLevel .E1)
  planckEinsteinPhotonLaw :
    energyInJoules setup.emittedPhotonEnergy =
      planckConstantInJouleSeconds setup.planckConstant *
        frequencyInHertz setup.emittedFrequency
  vacuumLightWaveRelation :
    speedOfLightInMetersPerSecond =
      lengthInMeters setup.emittedWavelength *
        frequencyInHertz setup.emittedFrequency

/-! ## Derived wavelength and displayed answer -/

/-- Labels of the four wavelength choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Wavelength in micrometres printed beside each answer label. -/
def displayedWavelengthInMicrometers : AnswerChoice → ℝ
  | .A => (429 : ℝ) / 100
  | .B => (591 : ℝ) / 100
  | .C => 10
  | .D => (860 : ℝ) / 100

/-- The answer label recorded by the source dataset, retained as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
Half of the `0.1 μm` precision displayed by choice C.  This represents the
rounding implicit in the requested multiple-choice wavelength.
-/
def displayedWavelengthToleranceInMicrometers : ℝ :=
  (1 : ℝ) / 20

/-- The physical lasing wavelength rounds to the wavelength of a choice. -/
def MatchesDisplayedWavelength
    (setup : MarsCO2LaserSetup) (choice : AnswerChoice) : Prop :=
  |lengthInMicrometers setup.emittedWavelength -
      displayedWavelengthInMicrometers choice| ≤
    displayedWavelengthToleranceInMicrometers

/-- Exactly one printed choice agrees with the modeled wavelength. -/
def IsUniqueMatchingDisplayedWavelength
    (setup : MarsCO2LaserSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedWavelength setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedWavelength setup other → other = choice

/-!
The `E₂ → E₁` transition has energy gap
`0.289 eV - 0.165 eV = 0.124 eV`.
-/
lemma laserPhotonEnergyInElectronVolts_eq
    (setup : MarsCO2LaserSetup)
    (h_figure : MatchesSuppliedCO2EnergyLevelFigure setup)
    (h_laws : SatisfiesCO2LaserLaws setup) :
    energyInElectronVolts setup.emittedPhotonEnergy =
      (31 : ℝ) / 250 := by
  have hE1 := h_figure.labelsRepresentPhysicalEnergies .E1
  trans energyInElectronVolts (setup.energyAtLevel .E2) -
      energyInElectronVolts (setup.energyAtLevel .E1)
  · rw [energyInElectronVolts, energyInElectronVolts,
      energyInElectronVolts, h_laws.photonCarriesLevelEnergyDrop]
    ring
  · rw [hE1, h_figure.lowerLaserLevelLabel,
      h_figure.labelsRepresentPhysicalEnergies .E2,
      h_figure.upperLaserLevelLabel]
    norm_num

/-!
Combining the energy drop, `E = h ν`, and `c = λ ν` gives the exact
coherent-SI expression for the lasing wavelength.
-/
lemma lasingWavelengthInMeters_eq
    (setup : MarsCO2LaserSetup)
    (h_figure : MatchesSuppliedCO2EnergyLevelFigure setup)
    (h_physical : HasPhysicalCO2LaserQuantities setup)
    (h_planck : UsesOrdinaryPlanckConstant setup)
    (h_laws : SatisfiesCO2LaserLaws setup) :
    lengthInMeters setup.emittedWavelength =
      planckConstantSIValue * speedOfLightInMetersPerSecond /
        (((31 : ℝ) / 250) * electronVoltInJoules) := by
  have hν : frequencyInHertz setup.emittedFrequency ≠ 0 :=
    ne_of_gt h_physical.emittedFrequencyPositive
  calc
    lengthInMeters setup.emittedWavelength =
        speedOfLightInMetersPerSecond /
          frequencyInHertz setup.emittedFrequency := by
      exact (eq_div_iff hν).2 h_laws.vacuumLightWaveRelation.symm
    _ = _ := by
      rw [← h_planck.planckConstantCalibration]
      have hE := laserPhotonEnergyInElectronVolts_eq setup h_figure h_laws
      have hev : electronVoltInJoules ≠ 0 := by
        norm_num [electronVoltInJoules, energyInJoules, DimEnergy.electronVolt,
          CarriesDimension.toDimensionful_apply_apply, UnitChoices.dimScale_self]
      rw [energyInElectronVolts] at hE
      field_simp [hev] at hE
      have hE' : energyInJoules setup.emittedPhotonEnergy =
          ((31 : ℝ) / 250) * electronVoltInJoules := by
        linarith [hE]
      have hgap : ((31 : ℝ) / 250) * electronVoltInJoules ≠ 0 :=
        mul_ne_zero (by norm_num) hev
      apply (div_eq_div_iff hν hgap).2
      calc
        speedOfLightInMetersPerSecond *
            (((31 : ℝ) / 250) * electronVoltInJoules) =
            speedOfLightInMetersPerSecond *
              energyInJoules setup.emittedPhotonEnergy := by rw [hE']
        _ = speedOfLightInMetersPerSecond *
            (planckConstantInJouleSeconds setup.planckConstant *
              frequencyInHertz setup.emittedFrequency) := by
          rw [h_laws.planckEinsteinPhotonLaw]
        _ = (planckConstantInJouleSeconds setup.planckConstant *
            speedOfLightInMetersPerSecond) *
              frequencyInHertz setup.emittedFrequency := by ring

/-!
The `E₂ → E₁` gap is `0.124 eV`.  The photon and wave laws therefore give a
wavelength about `9.999 μm`, which rounds to `10.0 μm` and uniquely selects
choice C.

This formalizes `thm:physics:phyx_mini_0579:target`.  Neither the numerical
wavelength nor choice C occurs in any scenario, figure, admissibility,
constant-calibration, or governing-law premise.
-/
theorem problem_phyx_mini_0579
    (setup : MarsCO2LaserSetup)
    (h_scenario : MatchesMarsCO2LaserScenario setup)
    (h_figure : MatchesSuppliedCO2EnergyLevelFigure setup)
    (h_physical : HasPhysicalCO2LaserQuantities setup)
    (h_planck : UsesOrdinaryPlanckConstant setup)
    (h_laws : SatisfiesCO2LaserLaws setup) :
    energyInElectronVolts setup.emittedPhotonEnergy =
        (31 : ℝ) / 250 ∧
      lengthInMeters setup.emittedWavelength =
        planckConstantSIValue * speedOfLightInMetersPerSecond /
          (((31 : ℝ) / 250) * electronVoltInJoules) ∧
      IsUniqueMatchingDisplayedWavelength setup .C := by
  have h_energy := laserPhotonEnergyInElectronVolts_eq setup h_figure h_laws
  have h_wavelength :=
    lasingWavelengthInMeters_eq setup h_figure h_physical h_planck h_laws
  have h_scale :
      UnitChoices.SI.dimScale
        {UnitChoices.SI with length := LengthUnit.micrometers} L𝓭 =
          (1000000 : NNReal) := by
    simp only [UnitChoices.dimScale_apply, Dimension.L𝓭_length,
      Dimension.L𝓭_time, Dimension.L𝓭_mass, Dimension.L𝓭_charge,
      Dimension.L𝓭_temperature, Rat.cast_one, Rat.cast_zero,
      NNReal.rpow_one, NNReal.rpow_zero, mul_one]
    change LengthUnit.meters / LengthUnit.micrometers = (1000000 : NNReal)
    rw [LengthUnit.micrometers, LengthUnit.self_div_scale]
    congr
    norm_num
  have h_units := setup.emittedWavelength.2 UnitChoices.SI
    {UnitChoices.SI with length := LengthUnit.micrometers}
  simp only [WithDim.dim_apply] at h_units
  rw [h_scale] at h_units
  have h_SI_meters :
      {UnitChoices.SI with length := LengthUnit.meters} = UnitChoices.SI := by
    rfl
  have h_conversion :
      lengthInMicrometers setup.emittedWavelength =
        1000000 * lengthInMeters setup.emittedWavelength := by
    rw [lengthInMicrometers, lengthInMeters, lengthReadout, lengthReadout,
      h_SI_meters]
    have h := congrArg WithDim.val h_units
    change (setup.emittedWavelength
        {UnitChoices.SI with length := LengthUnit.micrometers}).val =
      1000000 * (setup.emittedWavelength UnitChoices.SI).val at h
    exact_mod_cast h
  have h_value :
      lengthInMicrometers setup.emittedWavelength =
        1000000 *
          (planckConstantSIValue * speedOfLightInMetersPerSecond /
            (((31 : ℝ) / 250) * electronVoltInJoules)) := by
    rw [h_conversion, h_wavelength]
  norm_num [planckConstantSIValue, speedOfLightInMetersPerSecond,
    electronVoltInJoules, energyInJoules, DimEnergy.electronVolt,
    CarriesDimension.toDimensionful_apply_apply, UnitChoices.dimScale_self,
    DimSpeed.speedOfLight_in_SI] at h_value
  refine ⟨h_energy, h_wavelength, ?_⟩
  constructor
  · rw [MatchesDisplayedWavelength, h_value]
    norm_num [displayedWavelengthInMicrometers,
      displayedWavelengthToleranceInMicrometers]
  · intro other h_other
    fin_cases other
    · norm_num [MatchesDisplayedWavelength, h_value,
        displayedWavelengthInMicrometers,
        displayedWavelengthToleranceInMicrometers] at h_other
    · norm_num [MatchesDisplayedWavelength, h_value,
        displayedWavelengthInMicrometers,
        displayedWavelengthToleranceInMicrometers] at h_other
    · rfl
    · norm_num [MatchesDisplayedWavelength, h_value,
        displayedWavelengthInMicrometers,
        displayedWavelengthToleranceInMicrometers] at h_other

end PhyXMiniProblems.ProblemPhyXMini0579
