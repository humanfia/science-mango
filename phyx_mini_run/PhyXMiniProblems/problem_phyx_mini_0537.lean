import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0537

open Dimension

/-!
# Energy of the lower green-laser level in a helium--neon laser

The primary raster shows four neon energy levels. Both emission arrows begin at
`E4*`: the red arrow ends at `E3`, and the green arrow ends at `E2`. The printed
level readouts are `E1 = 0 eV`, `E3 = 18.70 eV`, and `E4* = 20.66 eV`. The prose
supplies wavelengths `632.8 nm` and `543 nm` for the red and green photons.

Physical energies, wavelengths, Planck's constant, and optical intensities are
dimensionful Physlib quantities. Real numbers occur only at explicit unit
readout boundaries and for dimensionless optical data.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- The physical dimension of energy, `M L^2 T^-2`. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of action, energy multiplied by time. -/
def actionDimension : Dimension :=
  energyDimension * T𝓭

/-- A nonnegative, unit-independent physical wavelength. -/
abbrev WavelengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative dimensionful quantity with the units of Planck's constant. -/
abbrev PlanckConstantQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Optical intensity, with physical dimension `M T^-3`. -/
abbrev OpticalIntensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical wavelength in a selected length unit. -/
def wavelengthReadout
    (unit : LengthUnit) (wavelength : WavelengthQuantity) : ℝ :=
  ((wavelength { UnitChoices.SI with length := unit }).val : ℝ)

/-- Read a wavelength in coherent-SI metres. -/
def wavelengthInMeters (wavelength : WavelengthQuantity) : ℝ :=
  wavelengthReadout LengthUnit.meters wavelength

/-- Read a wavelength in nanometres. -/
def wavelengthInNanometers (wavelength : WavelengthQuantity) : ℝ :=
  wavelengthReadout LengthUnit.nanometers wavelength

/-- Read a physical energy in coherent-SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read an energy in electron volts using Physlib's electron-volt quantity. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-- Read a dimensionful Planck constant in coherent-SI joule-seconds. -/
def planckConstantInJouleSeconds
    (constant : PlanckConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-- Physlib's dimensionful speed of light, read in SI metres per second. -/
def speedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-- Read a physical optical intensity in coherent SI units. -/
def opticalIntensityInSI (intensity : OpticalIntensityQuantity) : ℝ :=
  ((intensity UnitChoices.SI).val : ℝ)

/-- The exact coherent-SI calibration of the ordinary Planck constant. -/
def ordinaryPlanckConstantSIValue : ℝ :=
  (6.62607015 : ℝ) * 10 ^ (-34 : ℤ)

/-!
The displayed level energies have two digits after the decimal point, the red
wavelength has one, and the green wavelength is printed to the nearest
nanometre. These half-unit tolerances represent the precision of those labels.
-/
def energyLevelDisplayToleranceInElectronVolts : ℝ := 0.005

def redWavelengthDisplayToleranceInNanometers : ℝ := 0.05

def greenWavelengthDisplayToleranceInNanometers : ℝ := 0.5

/-! ## Atomic levels, transitions, and primary-raster labels -/

/-- The four horizontal neon energy levels named in the figure. -/
inductive AtomicEnergyLevel where
  | e1
  | e2
  | e3
  | e4Star
  deriving DecidableEq, Fintype, Repr

/-- The two competing downward transitions described by the problem. -/
inductive EmissionTransition where
  | red
  | green
  deriving DecidableEq, Fintype, Repr

/-- The color label printed beside an emission arrow. -/
inductive LaserColor where
  | red
  | green
  deriving DecidableEq, Fintype, Repr

/-- Both depicted emission transitions start from the populated `E4*` level. -/
def transitionInitialLevel : EmissionTransition → AtomicEnergyLevel
  | .red => .e4Star
  | .green => .e4Star

/-- The red transition ends at `E3`; the green transition ends at `E2`. -/
def transitionFinalLevel : EmissionTransition → AtomicEnergyLevel
  | .red => .e3
  | .green => .e2

/-- Color associated with each of the two transitions. -/
def transitionColor : EmissionTransition → LaserColor
  | .red => .red
  | .green => .green

/-!
Presentation data visible in image 537. An optional printed energy records that
the raster deliberately does not print the requested energy of `E2`.
-/
structure NeonEnergyLevelFigure where
  levelLineShown : AtomicEnergyLevel → Bool
  printedEnergyInElectronVolts : AtomicEnergyLevel → Option ℝ
  groundStateCaptionAt : AtomicEnergyLevel
  emissionArrowShown : EmissionTransition → Bool
  emissionArrowColor : EmissionTransition → LaserColor
  emissionArrowInitialLevel : EmissionTransition → AtomicEnergyLevel
  emissionArrowFinalLevel : EmissionTransition → AtomicEnergyLevel
  upwardEnergyAxisShown : Bool

/-! ## Laser medium and resonant-cavity data -/

/-- The gain medium named in the problem statement. -/
inductive LaserMediumKind where
  | heliumNeon
  | other
  deriving DecidableEq, Repr

/-- Dielectric materials named for the multilayer cavity mirrors. -/
inductive MirrorLayerMaterial where
  | siliconDioxide
  | titaniumDioxide
  deriving DecidableEq, Fintype, Repr

/-!
Material and optical data for the resonant cavity. Reflectivity, transmittance,
and refractive index are dimensionless. Boolean fields retain qualitative
phrases for which the source gives no numerical threshold.
-/
structure ResonantCavityData where
  layerMaterialPresent : MirrorLayerMaterial → Bool
  refractiveIndex : MirrorLayerMaterial → ℝ
  mirrorReflectivity : LaserColor → ℝ
  mirrorTransmittance : LaserColor → ℝ
  reflectsGreenWithHighEfficiency : Bool
  permitsSmallGreenOutputFraction : Bool
  permitsRedToLeaveImmediately : Bool

/-!
Independent physical data for the laser. In particular, `energyAtLevel .e2`
has no fixed value in this structure.
-/
structure HeliumNeonGreenLaserSetup where
  mediumKind : LaserMediumKind
  populationInversionEstablished : Bool
  eventuallyDecaysToGroundLevel : Bool
  energyAtLevel : AtomicEnergyLevel → DimEnergy
  transitionAllowed : EmissionTransition → Bool
  emittedPhotonEnergy : EmissionTransition → DimEnergy
  transitionWavelength : EmissionTransition → WavelengthQuantity
  ordinaryPlanckConstant : PlanckConstantQuantity
  intracavityIntensity : LaserColor → OpticalIntensityQuantity
  greenBeamCollimated : Bool
  cavity : ResonantCavityData
  figure : NeonEnergyLevelFigure

/-! ## Scenario, figure evidence, calibrated data, and governing laws -/

/-- The qualitative atomic and laser behavior stated in the prose. -/
structure MatchesHeliumNeonLaserScenario
    (setup : HeliumNeonGreenLaserSetup) : Prop where
  isHeliumNeonLaser : setup.mediumKind = .heliumNeon
  populationInversion : setup.populationInversionEstablished = true
  eventualGroundStateDecay : setup.eventuallyDecaysToGroundLevel = true
  bothTransitionsOccur : ∀ transition, setup.transitionAllowed transition = true
  collimatedGreenBeam : setup.greenBeamCollimated = true
  greenIntensityExceedsRed :
    opticalIntensityInSI (setup.intracavityIntensity .red) <
      opticalIntensityInSI (setup.intracavityIntensity .green)

/-!
Primary-raster evidence. The arrow endpoints record that green is `E4* -> E2`,
as shown in the image, rather than `E3 -> E2` from the inconsistent auxiliary
caption. The unknown `E2` has no printed numerical label.
-/
structure MatchesSuppliedEnergyLevelFigure
    (setup : HeliumNeonGreenLaserSetup) : Prop where
  everyLevelLineShown : ∀ level, setup.figure.levelLineShown level = true
  groundStateCaption : setup.figure.groundStateCaptionAt = .e1
  groundEnergyLabel :
    setup.figure.printedEnergyInElectronVolts .e1 = some 0
  e2EnergyIsNotPrinted :
    setup.figure.printedEnergyInElectronVolts .e2 = none
  e3EnergyLabel :
    setup.figure.printedEnergyInElectronVolts .e3 = some 18.70
  e4StarEnergyLabel :
    setup.figure.printedEnergyInElectronVolts .e4Star = some 20.66
  groundEnergyReference :
    energyInElectronVolts (setup.energyAtLevel .e1) = 0
  printedLabelsRepresentPhysicalEnergies : ∀ level reading,
    setup.figure.printedEnergyInElectronVolts level = some reading →
      |energyInElectronVolts (setup.energyAtLevel level) - reading| ≤
        energyLevelDisplayToleranceInElectronVolts
  everyEmissionArrowShown : ∀ transition,
    setup.figure.emissionArrowShown transition = true
  emissionArrowColors : ∀ transition,
    setup.figure.emissionArrowColor transition = transitionColor transition
  emissionArrowInitialLevels : ∀ transition,
    setup.figure.emissionArrowInitialLevel transition =
      transitionInitialLevel transition
  emissionArrowFinalLevels : ∀ transition,
    setup.figure.emissionArrowFinalLevel transition =
      transitionFinalLevel transition
  energyAxisPointsUp : setup.figure.upwardEnergyAxisShown = true

/-- The two vacuum wavelengths stated in the problem prose. -/
structure MatchesTransitionWavelengthReadouts
    (setup : HeliumNeonGreenLaserSetup) : Prop where
  redWavelengthNanometers :
    |wavelengthInNanometers (setup.transitionWavelength .red) - 632.8| ≤
      redWavelengthDisplayToleranceInNanometers
  greenWavelengthNanometers :
    |wavelengthInNanometers (setup.transitionWavelength .green) - 543| ≤
      greenWavelengthDisplayToleranceInNanometers

/-- The stated dielectric materials and their qualitative cavity behavior. -/
structure MatchesCavityDescription
    (setup : HeliumNeonGreenLaserSetup) : Prop where
  bothMaterialsPresent : ∀ material,
    setup.cavity.layerMaterialPresent material = true
  siliconDioxideIndex :
    setup.cavity.refractiveIndex .siliconDioxide = 1.458
  titaniumDioxideIndexRange :
    1.9 ≤ setup.cavity.refractiveIndex .titaniumDioxide ∧
      setup.cavity.refractiveIndex .titaniumDioxide ≤ 2.6
  reflectivitiesArePhysical : ∀ color,
    0 ≤ setup.cavity.mirrorReflectivity color ∧
      setup.cavity.mirrorReflectivity color ≤ 1
  transmittancesArePhysical : ∀ color,
    0 ≤ setup.cavity.mirrorTransmittance color ∧
      setup.cavity.mirrorTransmittance color ≤ 1
  greenIsReflectedMoreStrongly :
    setup.cavity.mirrorReflectivity .red <
      setup.cavity.mirrorReflectivity .green
  redIsTransmittedMoreStrongly :
    setup.cavity.mirrorTransmittance .green <
      setup.cavity.mirrorTransmittance .red
  highEfficiencyGreenReflection :
    setup.cavity.reflectsGreenWithHighEfficiency = true
  smallGreenOutputIsPermitted :
    setup.cavity.permitsSmallGreenOutputFraction = true
  redLeavesImmediately :
    setup.cavity.permitsRedToLeaveImmediately = true

/-- Positivity and ordering conditions for the physical quantities. -/
structure HasPhysicalLaserQuantities
    (setup : HeliumNeonGreenLaserSetup) : Prop where
  levelEnergiesNonnegative : ∀ level,
    0 ≤ energyInJoules (setup.energyAtLevel level)
  levelsAreOrdered :
    energyInJoules (setup.energyAtLevel .e1) <
        energyInJoules (setup.energyAtLevel .e2) ∧
      energyInJoules (setup.energyAtLevel .e2) <
        energyInJoules (setup.energyAtLevel .e3) ∧
      energyInJoules (setup.energyAtLevel .e3) <
        energyInJoules (setup.energyAtLevel .e4Star)
  photonEnergiesNonnegative : ∀ transition,
    0 ≤ energyInJoules (setup.emittedPhotonEnergy transition)
  wavelengthsPositive : ∀ transition,
    0 < wavelengthInMeters (setup.transitionWavelength transition)
  planckConstantPositive :
    0 < planckConstantInJouleSeconds setup.ordinaryPlanckConstant

/-- The ordinary Planck constant with its standard coherent-SI calibration. -/
structure UsesOrdinaryPlanckConstant
    (setup : HeliumNeonGreenLaserSetup) : Prop where
  planckConstantCalibration :
    planckConstantInJouleSeconds setup.ordinaryPlanckConstant =
      ordinaryPlanckConstantSIValue

/-!
Uniform laws for every allowed transition: the photon carries the atomic
energy drop and obeys `E_gamma = h c / lambda`. Neither law singles out `E2`
or contains an answer-choice value.
-/
structure SatisfiesRadiativeTransitionLaws
    (setup : HeliumNeonGreenLaserSetup) : Prop where
  photonCarriesLevelEnergyDrop : ∀ transition,
    setup.transitionAllowed transition = true →
      energyInJoules (setup.emittedPhotonEnergy transition) =
        energyInJoules
            (setup.energyAtLevel (transitionInitialLevel transition)) -
          energyInJoules
            (setup.energyAtLevel (transitionFinalLevel transition))
  photonEnergyWavelengthLaw : ∀ transition,
    setup.transitionAllowed transition = true →
      energyInJoules (setup.emittedPhotonEnergy transition) =
        planckConstantInJouleSeconds setup.ordinaryPlanckConstant *
            speedOfLightInMetersPerSecond /
          wavelengthInMeters (setup.transitionWavelength transition)

/-! ## Answer choices and target -/

/-- Labels of the four energy choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Energy in electron volts printed beside each answer label. -/
def displayedEnergyInElectronVolts : AnswerChoice → ℝ
  | .A => 24.16
  | .B => 22.01
  | .C => 15.31
  | .D => 18.37

/-- The answer label recorded in the source dataset, retained as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
The rounded `20.66 eV` and `543 nm` readouts propagate to less than two
hundredths of an electron volt in the derived `E2` value.
-/
def displayedEnergyCompatibilityTolerance : ℝ := 0.02

/-- The physical `E2` energy is compatible with a printed energy choice. -/
def MatchesDisplayedEnergy
    (setup : HeliumNeonGreenLaserSetup) (choice : AnswerChoice) : Prop :=
  |energyInElectronVolts (setup.energyAtLevel .e2) -
      displayedEnergyInElectronVolts choice| <
    displayedEnergyCompatibilityTolerance

/-- A choice is the unique displayed energy compatible with physical `E2`. -/
def IsUniqueMatchingDisplayedEnergy
    (setup : HeliumNeonGreenLaserSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedEnergy setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedEnergy setup other → other = choice

/-!
The green transition gives the symbolic value of `E2` by subtracting the
green photon's `h c / lambda` energy from the upper level.
-/
lemma e2_energyInJoules_exact
    (setup : HeliumNeonGreenLaserSetup)
    (h_scenario : MatchesHeliumNeonLaserScenario setup)
    (h_laws : SatisfiesRadiativeTransitionLaws setup) :
    energyInJoules (setup.energyAtLevel .e2) =
      energyInJoules (setup.energyAtLevel .e4Star) -
        planckConstantInJouleSeconds setup.ordinaryPlanckConstant *
            speedOfLightInMetersPerSecond /
          wavelengthInMeters (setup.transitionWavelength .green) := by
  rcases h_scenario with ⟨_, _, _, h_transitions, _, _⟩
  have h_allowed := h_transitions EmissionTransition.green
  have h_drop :=
    h_laws.photonCarriesLevelEnergyDrop EmissionTransition.green h_allowed
  have h_wave :=
    h_laws.photonEnergyWavelengthLaw EmissionTransition.green h_allowed
  simp only [transitionInitialLevel, transitionFinalLevel] at h_drop
  linarith

/-!
For the pictured helium--neon laser, the green-transition law and calibrated
readouts place `E2` within `0.02 eV` of `18.37 eV`; no other displayed choice
is compatible. This formalizes `thm:physics:phyx_mini_0537:target`.
-/
theorem problem_phyx_mini_0537
    (setup : HeliumNeonGreenLaserSetup)
    (h_scenario : MatchesHeliumNeonLaserScenario setup)
    (h_figure : MatchesSuppliedEnergyLevelFigure setup)
    (h_wavelengths : MatchesTransitionWavelengthReadouts setup)
    (h_cavity : MatchesCavityDescription setup)
    (h_physical : HasPhysicalLaserQuantities setup)
    (h_planck : UsesOrdinaryPlanckConstant setup)
    (h_laws : SatisfiesRadiativeTransitionLaws setup) :
    energyInJoules (setup.energyAtLevel .e2) =
        energyInJoules (setup.energyAtLevel .e4Star) -
          planckConstantInJouleSeconds setup.ordinaryPlanckConstant *
              speedOfLightInMetersPerSecond /
            wavelengthInMeters (setup.transitionWavelength .green) ∧
      |energyInElectronVolts (setup.energyAtLevel .e2) - 18.37| < 0.02 ∧
      IsUniqueMatchingDisplayedEnergy setup .D := by
  have h_exact := e2_energyInJoules_exact setup h_scenario h_laws
  refine ⟨h_exact, ?_⟩
  have nanometers_eq_meters (wavelength : WavelengthQuantity) :
      wavelengthInNanometers wavelength =
        1000000000 * wavelengthInMeters wavelength := by
    have hscale :
        ({ UnitChoices.SI with length := LengthUnit.meters } :
            UnitChoices).dimScale
          ({ UnitChoices.SI with length := LengthUnit.nanometers } :
            UnitChoices) L𝓭 =
          (1000000000 : NNReal) := by
      apply NNReal.eq
      norm_num [UnitChoices.dimScale, LengthUnit.nanometers,
        LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
      rfl
    have hunit := wavelength.property
      ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices)
    simp only [WithDim.dim_apply] at hunit
    rw [hscale] at hunit
    have hval := congrArg WithDim.val hunit
    change (wavelength
        ({ UnitChoices.SI with length := LengthUnit.nanometers } :
          UnitChoices)).val =
      (1000000000 : NNReal) *
        (wavelength
          ({ UnitChoices.SI with length := LengthUnit.meters } :
            UnitChoices)).val at hval
    change ((wavelength
        ({ UnitChoices.SI with length := LengthUnit.nanometers } :
          UnitChoices)).val : ℝ) =
      1000000000 *
        ((wavelength
          ({ UnitChoices.SI with length := LengthUnit.meters } :
            UnitChoices)).val : ℝ)
    exact_mod_cast hval
  have h_nm :=
    nanometers_eq_meters (setup.transitionWavelength .green)
  have h_green := h_wavelengths.greenWavelengthNanometers
  norm_num [greenWavelengthDisplayToleranceInNanometers] at h_green
  rw [abs_le] at h_green
  have h_meters_pos := h_physical.wavelengthsPositive .green
  have h_nanometers_pos :
      0 < wavelengthInNanometers (setup.transitionWavelength .green) := by
    nlinarith
  have h_e4 :=
    h_figure.printedLabelsRepresentPhysicalEnergies .e4Star 20.66
      h_figure.e4StarEnergyLabel
  norm_num [energyLevelDisplayToleranceInElectronVolts] at h_e4
  rw [abs_le] at h_e4
  have h_electronVolt :
      energyInJoules DimEnergy.electronVolt =
        (801088317 / 5000000000000000000000000000 : ℝ) := by
    norm_num [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
  have h_scaled := congrArg
    (fun x : ℝ => x / energyInJoules DimEnergy.electronVolt) h_exact
  rw [sub_div] at h_scaled
  change energyInElectronVolts (setup.energyAtLevel .e2) =
    energyInElectronVolts (setup.energyAtLevel .e4Star) - _ at h_scaled
  rw [h_planck.planckConstantCalibration] at h_scaled
  norm_num [ordinaryPlanckConstantSIValue, speedOfLightInMetersPerSecond,
    DimSpeed.speedOfLight_in_SI, h_electronVolt] at h_scaled
  have h_meters :
      wavelengthInMeters (setup.transitionWavelength .green) =
        wavelengthInNanometers (setup.transitionWavelength .green) /
          1000000000 := by
    nlinarith
  rw [h_meters] at h_scaled
  field_simp [ne_of_gt h_nanometers_pos] at h_scaled
  have h_close :
      |energyInElectronVolts (setup.energyAtLevel .e2) - 18.37| < 0.02 := by
    rw [abs_lt]
    constructor <;> nlinarith [h_scaled]
  refine ⟨h_close, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [MatchesDisplayedEnergy, displayedEnergyInElectronVolts,
      displayedEnergyCompatibilityTolerance] using h_close
  · intro other h_other
    unfold MatchesDisplayedEnergy at h_other
    rw [abs_lt] at h_close h_other
    cases other <;>
      norm_num [displayedEnergyInElectronVolts,
        displayedEnergyCompatibilityTolerance] at h_other ⊢ <;>
      nlinarith

end PhyXMiniProblems.ProblemPhyXMini0537
