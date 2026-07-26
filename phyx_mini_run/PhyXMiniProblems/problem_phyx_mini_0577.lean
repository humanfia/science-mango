import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0577

open Dimension

/-!
# Energy gap of the cometary OH stimulated-emission line

Solar heating creates a thin water-vapor atmosphere around a comet.  Sunlight
dissociates some water into hydrogen atoms and OH molecules and excites the OH
molecules.  Far from the Sun, excitation to levels `E1` and `E2` is equal.  As
the comet approaches, a Doppler-shifted Fraunhofer line overlaps the wavelength
needed to excite `E1`; excitation to `E1` decreases, producing an `E2` over
`E1` population inversion.  The resulting `E2 -> E1` stimulated emission is
observed at about `1666 MHz`.

The primary raster, rather than its conflicting auxiliary caption, shows two
absorption arrows from `E0`: a long left arrow from `E0` to `E2` and a shorter
right arrow from `E0` to `E1`.

Energy levels, photon energy, frequency, wavelength, speed, and Planck's
constant remain dimensionful quantities.  Real numbers below are only
coherent-SI readouts, rates, populations, or displayed multiple-choice values.

Assumption/target split:

* `MatchesCometOHScenario` records the stated chemistry, excitation and
  population behavior, stimulated transition, and approximate frequency;
* `MatchesPrimaryEnergyLevelFigure` records only labels, lines, and arrows
  visible in the primary raster;
* `MatchesFraunhoferDopplerMechanism` records the qualitative approach shift
  and its overlap with the `E1` excitation wavelength;
* `UsesStandardPlanckConstant` supplies the independent SI calibration of `h`;
* `SatisfiesStimulatedEmissionLaws` states `E_photon = E_initial - E_final`
  and `E_photon = h f`; and
* `problem_phyx_mini_0577` alone concludes that the energy gap is about
  `6.87 micro-eV` and uniquely selects answer C.
-/

/-! ## Dimensionful physical quantities and calibrated readouts -/

/-- The MLT dimension of energy. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Action has the dimension energy times time. -/
def actionDimension : Dimension := energyDimension * T𝓭

/-- A nonnegative, unit-independent physical frequency. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative, unit-independent physical wavelength. -/
abbrev WavelengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical value of the ordinary Planck constant `h`. -/
abbrev PlanckConstantQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Read a signed physical energy in coherent SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Read a frequency in coherent SI hertz. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Read a frequency in megahertz. -/
def frequencyInMegahertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyInHertz frequency / 10 ^ (6 : ℕ)

/-- Read a wavelength in coherent SI metres. -/
def wavelengthInMeters (wavelength : WavelengthQuantity) : ℝ :=
  ((wavelength UnitChoices.SI).val : ℝ)

/-- Read a speed in coherent SI metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  (speed UnitChoices.SI).val

/-- Read a physical action in coherent SI joule-seconds. -/
def planckConstantInJouleSeconds
    (constant : PlanckConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-! ## OH levels, comet environment, and the primary figure -/

/-- The three energy levels printed in the supplied diagram. -/
inductive EnergyLevelLabel where
  | E0
  | E1
  | E2
  deriving DecidableEq, Fintype, Repr

/-- Chemical species explicitly named in the comet scenario. -/
inductive ChemicalSpecies where
  | water
  | hydrogenAtom
  | hydroxyl
  deriving DecidableEq, Fintype, Repr

/-- The two comet regimes compared in the prose. -/
inductive CometRegime where
  | farFromSun
  | approachingSun
  deriving DecidableEq, Fintype, Repr

/-- The emission mechanism named by the problem. -/
inductive EmissionMode where
  | spontaneous
  | stimulated
  deriving DecidableEq, Repr

/-- The two black excitation arrows visible in the primary raster. -/
inductive FigureArrow where
  | longLeft
  | shortRight
  deriving DecidableEq, Fintype, Repr

/-- Qualitative chemical content and sunlight interactions in the coma. -/
structure CometChemicalEnvironment where
  waterIceOnNucleusSurface : Bool
  thinWaterVaporAtmosphere : Bool
  sunlightDissociationProduct : ChemicalSpecies → Bool
  sunlightExcitable : ChemicalSpecies → Bool

/-- A downward radiative transition from an initial to a final level. -/
structure EmissionTransition where
  initialLevel : EnergyLevelLabel
  finalLevel : EnergyLevelLabel

/-- Literal line, label, and arrow information carried by the primary image. -/
structure OHPrimaryEnergyLevelFigure where
  levelLineVisible : EnergyLevelLabel → Bool
  levelLineHorizontal : EnergyLevelLabel → Bool
  printedLabelVisible : EnergyLevelLabel → Bool
  arrowVisible : FigureArrow → Bool
  arrowStart : FigureArrow → EnergyLevelLabel
  arrowFinish : FigureArrow → EnergyLevelLabel

/-!
The independent physical state used by the model.  In particular, the three
energies and the emitted photon energy are fields; none is defined from an
answer choice or from the requested `6.87 micro-eV` value.
-/
structure CometOHEmissionSetup where
  environment : CometChemicalEnvironment
  radiatingSpecies : ChemicalSpecies
  energyAt : EnergyLevelLabel → DimEnergy
  excitationRate : CometRegime → EnergyLevelLabel → ℝ
  levelPopulation : CometRegime → EnergyLevelLabel → ℝ
  relativeSunSpeed : DimSpeed
  solarFraunhoferWavelength : WavelengthQuantity
  shiftedFraunhoferWavelength : WavelengthQuantity
  requiredE1ExcitationWavelength : WavelengthQuantity
  emissionMode : EmissionMode
  emissionTransition : EmissionTransition
  emittedFrequency : FrequencyQuantity
  emittedPhotonEnergy : DimEnergy
  planckConstant : PlanckConstantQuantity
  figure : OHPrimaryEnergyLevelFigure

/-! ## Scenario, image, and physical-law assumptions -/

/-- Absolute-error agreement of a scalar readout with a nominal value. -/
def WithinAbsoluteTolerance
    (tolerance actual nominal : ℝ) : Prop :=
  |actual - nominal| < tolerance

/-!
Direct transcription of the physical narrative.  The one-megahertz window
makes the word "about" explicit; it is an observational premise, not an
assumption about the energy gap sought in the question.
-/
structure MatchesCometOHScenario
    (setup : CometOHEmissionSetup) : Prop where
  surfaceContainsWaterIce :
    setup.environment.waterIceOnNucleusSurface = true
  atmosphereIsThinWaterVapor :
    setup.environment.thinWaterVaporAtmosphere = true
  sunlightProducesHydrogenAtoms :
    setup.environment.sunlightDissociationProduct .hydrogenAtom = true
  sunlightProducesHydroxyl :
    setup.environment.sunlightDissociationProduct .hydroxyl = true
  sunlightExcitesHydroxyl :
    setup.environment.sunlightExcitable .hydroxyl = true
  radiatingMoleculeIsHydroxyl : setup.radiatingSpecies = .hydroxyl
  farExcitationsAreEqual :
    setup.excitationRate .farFromSun .E2 =
      setup.excitationRate .farFromSun .E1
  farPopulationsAreNotInverted :
    setup.levelPopulation .farFromSun .E2 =
      setup.levelPopulation .farFromSun .E1
  approachingE1ExcitationDecreases :
    setup.excitationRate .approachingSun .E1 <
      setup.excitationRate .farFromSun .E1
  approachingPopulationIsInverted :
    setup.levelPopulation .approachingSun .E1 <
      setup.levelPopulation .approachingSun .E2
  modeIsStimulatedEmission : setup.emissionMode = .stimulated
  transitionStartsAtE2 : setup.emissionTransition.initialLevel = .E2
  transitionEndsAtE1 : setup.emissionTransition.finalLevel = .E1
  emissionFrequencyIsAbout1666MHz :
    WithinAbsoluteTolerance 1
      (frequencyInMegahertz setup.emittedFrequency) 1666

/-!
The primary bitmap has three horizontal red level lines and two upward black
arrows.  Contrary to the auxiliary caption, both arrows start at `E0`.
-/
structure MatchesPrimaryEnergyLevelFigure
    (figure : OHPrimaryEnergyLevelFigure) : Prop where
  everyLevelLineVisible : ∀ level, figure.levelLineVisible level = true
  everyLevelLineHorizontal : ∀ level, figure.levelLineHorizontal level = true
  everyLevelLabelVisible : ∀ level, figure.printedLabelVisible level = true
  everyArrowVisible : ∀ arrow, figure.arrowVisible arrow = true
  longArrowStartsAtE0 : figure.arrowStart .longLeft = .E0
  longArrowEndsAtE2 : figure.arrowFinish .longLeft = .E2
  shortArrowStartsAtE0 : figure.arrowStart .shortRight = .E0
  shortArrowEndsAtE1 : figure.arrowFinish .shortRight = .E1

/-!
Qualitative Doppler/Fraunhofer mechanism stated in the problem: approach
produces a shorter shifted wavelength and that line overlaps the wavelength
needed for excitation to `E1`.  No numerical energy answer occurs here.
-/
structure MatchesFraunhoferDopplerMechanism
    (setup : CometOHEmissionSetup) : Prop where
  cometIsApproaching : 0 < speedInMetersPerSecond setup.relativeSunSpeed
  approachShiftsLineToShorterWavelength :
    wavelengthInMeters setup.shiftedFraunhoferWavelength <
      wavelengthInMeters setup.solarFraunhoferWavelength
  shiftedLineOverlapsE1Excitation :
    wavelengthInMeters setup.shiftedFraunhoferWavelength =
      wavelengthInMeters setup.requiredE1ExcitationWavelength

/-- Positivity and ordering conditions selecting a physical OH-level model. -/
structure HasPhysicalOHEmissionParameters
    (setup : CometOHEmissionSetup) : Prop where
  orderedEnergyLevels :
    energyInJoules (setup.energyAt .E0) <
        energyInJoules (setup.energyAt .E1) ∧
      energyInJoules (setup.energyAt .E1) <
        energyInJoules (setup.energyAt .E2)
  nonnegativeExcitationRates : ∀ regime level,
    0 ≤ setup.excitationRate regime level
  nonnegativePopulations : ∀ regime level,
    0 ≤ setup.levelPopulation regime level
  positiveEmissionFrequency :
    0 < frequencyInHertz setup.emittedFrequency
  positivePhotonEnergy :
    0 < energyInJoules setup.emittedPhotonEnergy
  positivePlanckConstant :
    0 < planckConstantInJouleSeconds setup.planckConstant
  positiveFraunhoferWavelength :
    0 < wavelengthInMeters setup.solarFraunhoferWavelength
  positiveShiftedWavelength :
    0 < wavelengthInMeters setup.shiftedFraunhoferWavelength
  positiveE1ExcitationWavelength :
    0 < wavelengthInMeters setup.requiredE1ExcitationWavelength

/-- Exact SI calibration of the independently known ordinary Planck constant. -/
structure UsesStandardPlanckConstant
    (setup : CometOHEmissionSetup) : Prop where
  planckConstantCalibration :
    planckConstantInJouleSeconds setup.planckConstant =
      (6.62607015 : ℝ) * 10 ^ (-34 : ℤ)

/-!
The two governing stimulated-emission relations.  They apply to the selected
transition but contain no numerical energy gap or answer label.
-/
structure SatisfiesStimulatedEmissionLaws
    (setup : CometOHEmissionSetup) : Prop where
  photonEnergyIsTransitionEnergy :
    energyInJoules setup.emittedPhotonEnergy =
      energyInJoules
          (setup.energyAt setup.emissionTransition.initialLevel) -
        energyInJoules
          (setup.energyAt setup.emissionTransition.finalLevel)
  planckEinsteinPhotonLaw :
    energyInJoules setup.emittedPhotonEnergy =
      planckConstantInJouleSeconds setup.planckConstant *
        frequencyInHertz setup.emittedFrequency

/-! ## Displayed answers and the current target -/

/-- Energy-level gap `E2 - E1`, read in micro-electron-volts. -/
def e2MinusE1InMicroElectronVolts
    (setup : CometOHEmissionSetup) : ℝ :=
  ((energyInJoules (setup.energyAt .E2) -
      energyInJoules (setup.energyAt .E1)) /
      energyInJoules DimEnergy.electronVolt) * 10 ^ (6 : ℕ)

/-- Labels of the four choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Micro-electron-volt value printed beside each answer label. -/
def displayedEnergyDifferenceInMicroElectronVolts : AnswerChoice → ℝ
  | .A => 12.80
  | .B => 1.67
  | .C => 6.87
  | .D => 3.43

/-- Answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
The `0.03 micro-eV` tolerance accommodates the word "about" in `1666 MHz`
and the small mismatch between that rounded frequency and the displayed
answer.  It is far smaller than the separation between answer choices.
-/
def MatchesDisplayedEnergyDifference
    (setup : CometOHEmissionSetup) (choice : AnswerChoice) : Prop :=
  WithinAbsoluteTolerance (3 / 100)
    (e2MinusE1InMicroElectronVolts setup)
    (displayedEnergyDifferenceInMicroElectronVolts choice)

/-- The selected choice is strictly closer to the modeled gap than each rival. -/
def IsUniqueClosestEnergyDifferenceChoice
    (setup : CometOHEmissionSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |e2MinusE1InMicroElectronVolts setup -
        displayedEnergyDifferenceInMicroElectronVolts choice| <
      |e2MinusE1InMicroElectronVolts setup -
        displayedEnergyDifferenceInMicroElectronVolts other|

/-!
The `E2 - E1` gap is about `6.87 micro-eV`, the value displayed by recorded
answer C, and C is uniquely closest among the four choices.

This formalizes blueprint label `thm:physics:phyx_mini_0577:target`.
-/
theorem problem_phyx_mini_0577
    (setup : CometOHEmissionSetup)
    (hscenario : MatchesCometOHScenario setup)
    (hfigure : MatchesPrimaryEnergyLevelFigure setup.figure)
    (hdoppler : MatchesFraunhoferDopplerMechanism setup)
    (hphysical : HasPhysicalOHEmissionParameters setup)
    (hplanck : UsesStandardPlanckConstant setup)
    (hlaws : SatisfiesStimulatedEmissionLaws setup) :
    WithinAbsoluteTolerance (3 / 100)
        (e2MinusE1InMicroElectronVolts setup) (6.87 : ℝ) ∧
      MatchesDisplayedEnergyDifference setup recordedDatasetAnswer ∧
      IsUniqueClosestEnergyDifferenceChoice setup recordedDatasetAnswer := by
  have hfrequency := hscenario.emissionFrequencyIsAbout1666MHz
  change
    |frequencyInHertz setup.emittedFrequency / 10 ^ (6 : ℕ) - 1666| < 1
      at hfrequency
  rw [abs_lt] at hfrequency
  norm_num at hfrequency
  have htransition := hlaws.photonEnergyIsTransitionEnergy
  rw [hscenario.transitionStartsAtE2, hscenario.transitionEndsAtE1] at htransition
  have hplanckEinstein := hlaws.planckEinsteinPhotonLaw
  rw [hplanck.planckConstantCalibration] at hplanckEinstein
  have hgap :
      energyInJoules (setup.energyAt .E2) -
          energyInJoules (setup.energyAt .E1) =
        ((6.62607015 : ℝ) * 10 ^ (-34 : ℤ)) *
          frequencyInHertz setup.emittedFrequency :=
    htransition.symm.trans hplanckEinstein
  have helectronVolt :
      energyInJoules DimEnergy.electronVolt = (1.602176634e-19 : ℝ) := by
    norm_num [energyInJoules, DimEnergy.electronVolt, DimEnergy.joule,
      CarriesDimension.toDimensionful_apply_apply]
  have hclose :
      WithinAbsoluteTolerance (3 / 100)
        (e2MinusE1InMicroElectronVolts setup) (6.87 : ℝ) := by
    unfold WithinAbsoluteTolerance e2MinusE1InMicroElectronVolts
    rw [hgap, helectronVolt, abs_lt]
    norm_num at *
    constructor <;> nlinarith
  have hcloseBounds := hclose
  unfold WithinAbsoluteTolerance at hcloseBounds
  rw [abs_lt] at hcloseBounds
  refine ⟨hclose, ?_, ?_⟩
  · simpa [MatchesDisplayedEnergyDifference, recordedDatasetAnswer,
      displayedEnergyDifferenceInMicroElectronVolts] using hclose
  · unfold IsUniqueClosestEnergyDifferenceChoice
    intro other hother
    cases other with
    | A =>
        have hfar :
            e2MinusE1InMicroElectronVolts setup - (64 / 5 : ℝ) < 0 := by
          nlinarith [hcloseBounds.1, hcloseBounds.2]
        norm_num [recordedDatasetAnswer,
          displayedEnergyDifferenceInMicroElectronVolts] at hother ⊢
        rw [abs_of_neg hfar]
        unfold WithinAbsoluteTolerance at hclose
        nlinarith [hcloseBounds.1, hcloseBounds.2]
    | B =>
        have hfar :
            0 <
              e2MinusE1InMicroElectronVolts setup - (167 / 100 : ℝ) := by
          nlinarith [hcloseBounds.1, hcloseBounds.2]
        norm_num [recordedDatasetAnswer,
          displayedEnergyDifferenceInMicroElectronVolts] at hother ⊢
        rw [abs_of_pos hfar]
        unfold WithinAbsoluteTolerance at hclose
        nlinarith [hcloseBounds.1, hcloseBounds.2]
    | C =>
        exact (hother rfl).elim
    | D =>
        have hfar :
            0 <
              e2MinusE1InMicroElectronVolts setup - (343 / 100 : ℝ) := by
          nlinarith [hcloseBounds.1, hcloseBounds.2]
        norm_num [recordedDatasetAnswer,
          displayedEnergyDifferenceInMicroElectronVolts] at hother ⊢
        rw [abs_of_pos hfar]
        unfold WithinAbsoluteTolerance at hclose
        nlinarith [hcloseBounds.1, hcloseBounds.2]

end PhyXMiniProblems.ProblemPhyXMini0577
