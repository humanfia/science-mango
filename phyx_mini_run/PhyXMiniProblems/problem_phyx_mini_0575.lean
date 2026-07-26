import Mathlib
import Physlib.StatisticalMechanics.BoltzmannConstant
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0575

/-!
# Occupation of a donor level in doped silicon

At `300 K`, donor doping moves the Fermi level of silicon close to the
conduction-band edge.  The donor state is `0.15 eV` below that edge, while the
doped Fermi level is `0.11 eV` below it.  The requested quantity is the
Fermi--Dirac occupation probability of the donor state.

Band edges and electronic levels are represented by Physlib's dimensionful
energy type, and the absolute temperature by Physlib's `Temperature`.  Real
numbers below are only calibrated unit readouts, schematic figure coordinates,
dimensionless probabilities, and displayed multiple-choice values.  In
particular, the donor occupation probability is an independent observable
constrained by the general Fermi--Dirac law; it is not defined to be answer C.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- Coherent-SI readout of an energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-!
Read a dimensionful energy in electron-volts.  The denominator is Physlib's
physical one-electron-volt energy, so this is a unit readout rather than a
scalar replacement for energy.
-/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-!
Read an absolute temperature in kelvins.  Physlib stores a nonnegative
temperature in an arbitrary absolute scale; the unit ratio performs the
calibration to `TemperatureUnit.kelvin`.
-/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-!
Boltzmann's constant expressed in electron-volts per kelvin.  Physlib supplies
`Constants.kB` in coherent SI joules per kelvin, so division by the joule
readout of one electron-volt gives the required calibrated scalar.
-/
def boltzmannConstantInElectronVoltsPerKelvin : ℝ :=
  Constants.kB / energyInJoules DimEnergy.electronVolt

/-!
The Fermi--Dirac occupation function in consistent `eV` and `K` readouts.
This is a general distribution law and is not specialized to the donor level
or to any displayed answer.
-/
def fermiDiracOccupationProbability
    (stateEnergyElectronVolts fermiEnergyElectronVolts
      absoluteTemperatureKelvins : ℝ) : ℝ :=
  1 /
    (Real.exp
      ((stateEnergyElectronVolts - fermiEnergyElectronVolts) /
        (boltzmannConstantInElectronVoltsPerKelvin *
          absoluteTemperatureKelvins)) + 1)

/-! ## Semiconductor and energy-level roles -/

/-- Semiconductor material named in the problem. -/
inductive SemiconductorMaterial where
  | silicon
  | other
  deriving DecidableEq, Repr

/-- Kind of impurity introduced into the semiconductor. -/
inductive DopantKind where
  | donor
  | acceptor
  deriving DecidableEq, Repr

/-- Physical energy references appearing in the prose and diagram. -/
inductive EnergyReference where
  | valenceBandTop
  | conductionBandBottom
  | intrinsicFermiLevel
  | dopedFermiLevel
  | donorLevel
  deriving DecidableEq, Fintype, Repr

/-- Features explicitly visible in the supplied energy-level diagram. -/
inductive DiagramFeature where
  | valenceBandTop
  | donorLevel
  | fermiLevel
  | conductionBandBottom
  deriving DecidableEq, Fintype, Repr

/-- Rendering style used for a feature in the supplied diagram. -/
inductive DiagramMarkStyle where
  | filledBand
  | dashedLevel
  deriving DecidableEq, Repr

/-!
Primary-image data.  Vertical coordinates are schematic dimensionless drawing
coordinates increasing upward; they are not physical energies.  The numerical
gap annotation is an electron-volt readout printed beside the arrow.
-/
structure SemiconductorEnergyDiagram where
  printedLabel : DiagramFeature → String
  markStyle : DiagramFeature → DiagramMarkStyle
  verticalCoordinate : DiagramFeature → ℝ
  energyIncreasesUpward : Bool
  gapArrowShown : Bool
  gapAnnotationElectronVolts : ℝ

/-!
Independent physical data for the pure and donor-doped silicon samples.  The
energy function retains all levels as dimensionful quantities.  The tolerance
parameter gives quantitative meaning to the prose word "nearly" without
inventing a fixed numerical tolerance not stated by the source.
-/
structure DonorDopedSemiconductorSetup where
  material : SemiconductorMaterial
  dopantKind : DopantKind
  absoluteTemperature : Temperature
  temperatureStorageUnit : TemperatureUnit
  energyAt : EnergyReference → DimEnergy
  intrinsicNearMidgapToleranceElectronVolts : ℝ
  occupationProbabilityAtEnergy : DimEnergy → ℝ
  figure : SemiconductorEnergyDiagram

/-- The dimensionless probability requested by the question. -/
def donorLevelOccupationProbability
    (setup : DonorDopedSemiconductorSetup) : ℝ :=
  setup.occupationProbabilityAtEnergy (setup.energyAt .donorLevel)

/-!
An energy is near the midpoint of two band edges when its electron-volt
readout lies within a nonnegative tolerance smaller than half the gap.  The
tolerance remains scenario data because the source says only "nearly".
-/
def IsNearBandGapMidpointWithin
    (lowerEdge upperEdge level : DimEnergy)
    (toleranceElectronVolts : ℝ) : Prop :=
  0 ≤ toleranceElectronVolts ∧
    toleranceElectronVolts <
      (energyInElectronVolts upperEdge -
        energyInElectronVolts lowerEdge) / 2 ∧
    |energyInElectronVolts level -
        (energyInElectronVolts lowerEdge +
          energyInElectronVolts upperEdge) / 2| ≤
      toleranceElectronVolts

/-! ## Scenario, figure readouts, and physical data -/

/-!
The material, donor doping, temperature, qualitative intrinsic-level
placement, and the statement that doping raises the Fermi level.  None of
these fields asserts the requested occupation probability.
-/
structure MatchesDonorDopedSiliconScenario
    (setup : DonorDopedSemiconductorSetup) : Prop where
  materialIsSilicon : setup.material = .silicon
  impurityIsDonor : setup.dopantKind = .donor
  temperatureScaleIsKelvin :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  temperatureIs300Kelvin :
    temperatureInKelvins setup.temperatureStorageUnit
      setup.absoluteTemperature = 300
  intrinsicFermiLevelNearlyAtMidgap :
    IsNearBandGapMidpointWithin
      (setup.energyAt .valenceBandTop)
      (setup.energyAt .conductionBandBottom)
      (setup.energyAt .intrinsicFermiLevel)
      setup.intrinsicNearMidgapToleranceElectronVolts
  dopingRaisesFermiLevel :
    energyInElectronVolts (setup.energyAt .intrinsicFermiLevel) <
      energyInElectronVolts (setup.energyAt .dopedFermiLevel)

/-!
Labels, drawing styles, gap annotation, and bottom-to-top order read from the
primary image `575.png`.  The bitmap places the donor dashed line below the
Fermi dashed line, consistently with the stated `0.15 eV` and `0.11 eV`
depths; this takes precedence over the contradictory auxiliary caption.
-/
structure MatchesSuppliedSemiconductorEnergyDiagram
    (figure : SemiconductorEnergyDiagram) : Prop where
  valenceBandLabel :
    figure.printedLabel .valenceBandTop = "Valence band"
  donorLevelLabel : figure.printedLabel .donorLevel = "Donor level"
  fermiLevelLabel : figure.printedLabel .fermiLevel = "Fermi level"
  conductionBandLabel :
    figure.printedLabel .conductionBandBottom = "Conduction band"
  valenceShownAsBand :
    figure.markStyle .valenceBandTop = .filledBand
  conductionShownAsBand :
    figure.markStyle .conductionBandBottom = .filledBand
  donorShownAsDashedLevel :
    figure.markStyle .donorLevel = .dashedLevel
  fermiShownAsDashedLevel :
    figure.markStyle .fermiLevel = .dashedLevel
  energyDirection : figure.energyIncreasesUpward = true
  gapArrowVisible : figure.gapArrowShown = true
  printedGapValue : figure.gapAnnotationElectronVolts = 111 / 100
  bottomToTopOrder :
    figure.verticalCoordinate .valenceBandTop <
        figure.verticalCoordinate .donorLevel ∧
      figure.verticalCoordinate .donorLevel <
        figure.verticalCoordinate .fermiLevel ∧
      figure.verticalCoordinate .fermiLevel <
        figure.verticalCoordinate .conductionBandBottom

/-!
The calibrated physical energy differences stated in the problem.  They
relate independent dimensionful levels and do not mention an occupation
probability or answer choice.
-/
structure MatchesProblemEnergyReadouts
    (setup : DonorDopedSemiconductorSetup) : Prop where
  siliconBandGap :
    energyInElectronVolts (setup.energyAt .conductionBandBottom) -
        energyInElectronVolts (setup.energyAt .valenceBandTop) =
      111 / 100
  donorLevelBelowConductionBand :
    energyInElectronVolts (setup.energyAt .conductionBandBottom) -
        energyInElectronVolts (setup.energyAt .donorLevel) =
      15 / 100
  dopedFermiLevelBelowConductionBand :
    energyInElectronVolts (setup.energyAt .conductionBandBottom) -
        energyInElectronVolts (setup.energyAt .dopedFermiLevel) =
      11 / 100

/-!
Positivity, in-gap placement, and probability bounds selecting the physical
branch of the model.  These conditions contain no numerical value for the
donor occupation probability.
-/
structure HasPhysicalSemiconductorParameters
    (setup : DonorDopedSemiconductorSetup) : Prop where
  positiveAbsoluteTemperature :
    0 < temperatureInKelvins setup.temperatureStorageUnit
      setup.absoluteTemperature
  intrinsicFermiLevelInsideGap :
    energyInElectronVolts (setup.energyAt .valenceBandTop) <
        energyInElectronVolts (setup.energyAt .intrinsicFermiLevel) ∧
      energyInElectronVolts (setup.energyAt .intrinsicFermiLevel) <
        energyInElectronVolts (setup.energyAt .conductionBandBottom)
  dopedFermiLevelInsideGap :
    energyInElectronVolts (setup.energyAt .valenceBandTop) <
        energyInElectronVolts (setup.energyAt .dopedFermiLevel) ∧
      energyInElectronVolts (setup.energyAt .dopedFermiLevel) <
        energyInElectronVolts (setup.energyAt .conductionBandBottom)
  donorLevelInsideGap :
    energyInElectronVolts (setup.energyAt .valenceBandTop) <
        energyInElectronVolts (setup.energyAt .donorLevel) ∧
      energyInElectronVolts (setup.energyAt .donorLevel) <
        energyInElectronVolts (setup.energyAt .conductionBandBottom)
  occupationProbabilityBounds : ∀ energy : DimEnergy,
    0 ≤ setup.occupationProbabilityAtEnergy energy ∧
      setup.occupationProbabilityAtEnergy energy ≤ 1

/-!
The governing Fermi--Dirac law for every electronic-state energy in the doped
sample.  It relates the independent occupation observable to the doped Fermi
level and temperature generally; it is not specialized to the donor state or
to the recorded answer.
-/
structure SatisfiesFermiDiracOccupationLaw
    (setup : DonorDopedSemiconductorSetup) : Prop where
  occupationLaw : ∀ stateEnergy : DimEnergy,
    setup.occupationProbabilityAtEnergy stateEnergy =
      fermiDiracOccupationProbability
        (energyInElectronVolts stateEnergy)
        (energyInElectronVolts (setup.energyAt .dopedFermiLevel))
        (temperatureInKelvins setup.temperatureStorageUnit
          setup.absoluteTemperature)

/-! ## Derived relation and answer semantics -/

/-!
Subtracting the two stated depths below the conduction-band edge places the
donor state `0.04 eV` below the doped Fermi level.  This is a derived
intermediate relation, not a premise.
-/
lemma donorEnergyRelativeToDopedFermi
    (setup : DonorDopedSemiconductorSetup)
    (hReadouts : MatchesProblemEnergyReadouts setup) :
    energyInElectronVolts (setup.energyAt .donorLevel) -
        energyInElectronVolts (setup.energyAt .dopedFermiLevel) =
      (-1 / 25 : ℝ) := by
  norm_num at hReadouts ⊢
  linarith [hReadouts.donorLevelBelowConductionBand,
    hReadouts.dopedFermiLevelBelowConductionBand]

/-- Labels attached to the four displayed occupation probabilities. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless probability printed beside each answer label. -/
def displayedOccupationProbability : AnswerChoice → ℝ
  | .A => 14 / 1000
  | .B => 176 / 1000
  | .C => 824 / 1000
  | .D => 986 / 1000

/-- Dataset metadata recording answer C; this is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
The exact standard-constant calculation differs from the displayed `0.824` by
less than `0.001`.  This tolerance describes agreement with the supplied
three-decimal answer without falsely claiming exact equality or conventional
rounding at the half-thousandth boundary.
-/
def AgreesWithinOneThousandth
    (probability : ℝ) (choice : AnswerChoice) : Prop :=
  |probability - displayedOccupationProbability choice| < 1 / 1000

/-- A choice is strictly closer than every distinct displayed alternative. -/
def IsUniqueNearestDisplayedProbability
    (probability : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |probability - displayedOccupationProbability choice| <
      |probability - displayedOccupationProbability other|

/-!
Blueprint: `thm:physics:phyx_mini_0575:target`.

At `300 K`, the donor energy is `0.04 eV` below the doped Fermi level.
Substitution in the general Fermi--Dirac law gives the exact standard-constant
expression below, which is within `0.001` of `0.824` and uniquely selects
choice C.
-/
theorem donorLevelOccupation_matches_recordedAnswerC
    (setup : DonorDopedSemiconductorSetup)
    (hScenario : MatchesDonorDopedSiliconScenario setup)
    (hFigure : MatchesSuppliedSemiconductorEnergyDiagram setup.figure)
    (hReadouts : MatchesProblemEnergyReadouts setup)
    (hPhysical : HasPhysicalSemiconductorParameters setup)
    (hFermiDirac : SatisfiesFermiDiracOccupationLaw setup) :
    donorLevelOccupationProbability setup =
        1 /
          (Real.exp
            ((-1 / 25 : ℝ) /
              (boltzmannConstantInElectronVoltsPerKelvin * 300)) + 1) ∧
      AgreesWithinOneThousandth
        (donorLevelOccupationProbability setup) .C ∧
      IsUniqueNearestDisplayedProbability
        (donorLevelOccupationProbability setup) .C := by
  have hExact :
      donorLevelOccupationProbability setup =
        1 /
          (Real.exp
            ((-1 / 25 : ℝ) /
              (boltzmannConstantInElectronVoltsPerKelvin * 300)) + 1) := by
    rw [donorLevelOccupationProbability, hFermiDirac.occupationLaw,
      fermiDiracOccupationProbability,
      donorEnergyRelativeToDopedFermi setup hReadouts,
      hScenario.temperatureIs300Kelvin]
  have hExponent :
      ((-1 / 25 : ℝ) /
          (boltzmannConstantInElectronVoltsPerKelvin * 300)) =
        -(267029439 : ℝ) / 172581125 := by
    norm_num [boltzmannConstantInElectronVoltsPerKelvin, Constants.kB,
      Constants.kBAx, energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale_self]
  have hExpHalf :
      (461 / 1000 : ℝ) <
          Real.exp (-(267029439 : ℝ) / 345162250) ∧
        Real.exp (-(267029439 : ℝ) / 345162250) <
          (462 / 1000 : ℝ) := by
    have hTaylor := Real.exp_bound
      (x := -(267029439 : ℝ) / 345162250)
      (n := 8)
      (by norm_num : |-(267029439 : ℝ) / 345162250| ≤ 1)
      (by norm_num : 0 < (8 : ℕ))
    norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg,
      abs_of_neg] at hTaylor ⊢
    rw [abs_sub_le_iff] at hTaylor
    constructor <;> linarith
  have hExp :
      (7 / 33 : ℝ) <
          Real.exp (-(267029439 : ℝ) / 172581125) ∧
        Real.exp (-(267029439 : ℝ) / 172581125) <
          (177 / 823 : ℝ) := by
    rw [show (-(267029439 : ℝ) / 172581125) =
        (-(267029439 : ℝ) / 345162250) +
          (-(267029439 : ℝ) / 345162250) by norm_num,
      Real.exp_add]
    constructor
    · nlinarith [sq_nonneg
        (Real.exp (-(267029439 : ℝ) / 345162250) - 461 / 1000)]
    · nlinarith [sq_nonneg
        (Real.exp (-(267029439 : ℝ) / 345162250) - 462 / 1000)]
  have hProbabilityBounds :
      (823 / 1000 : ℝ) < donorLevelOccupationProbability setup ∧
        donorLevelOccupationProbability setup < (825 / 1000 : ℝ) := by
    rw [hExact, hExponent]
    have hDenominator :
        0 < Real.exp (-(267029439 : ℝ) / 172581125) + 1 := by
      positivity
    constructor
    · rw [lt_div_iff₀ hDenominator]
      norm_num at hExp ⊢
      linarith
    · rw [div_lt_iff₀ hDenominator]
      norm_num at hExp ⊢
      linarith
  have hAgreement :
      AgreesWithinOneThousandth
        (donorLevelOccupationProbability setup) .C := by
    rw [AgreesWithinOneThousandth, displayedOccupationProbability, abs_lt]
    constructor <;> linarith [hProbabilityBounds.1, hProbabilityBounds.2]
  refine ⟨hExact, hAgreement, ?_⟩
  intro other hOther
  fin_cases other
  · norm_num [displayedOccupationProbability] at hOther ⊢
    calc
      |donorLevelOccupationProbability setup - 103 / 125| <
          1 / 1000 := by
        norm_num [AgreesWithinOneThousandth,
          displayedOccupationProbability] at hAgreement
        exact hAgreement
      _ < |donorLevelOccupationProbability setup - 7 / 500| := by
        rw [abs_of_pos]
        · linarith [hProbabilityBounds.1]
        · linarith [hProbabilityBounds.1]
  · norm_num [displayedOccupationProbability] at hOther ⊢
    calc
      |donorLevelOccupationProbability setup - 103 / 125| <
          1 / 1000 := by
        norm_num [AgreesWithinOneThousandth,
          displayedOccupationProbability] at hAgreement
        exact hAgreement
      _ < |donorLevelOccupationProbability setup - 22 / 125| := by
        rw [abs_of_pos]
        · linarith [hProbabilityBounds.1]
        · linarith [hProbabilityBounds.1]
  · exact (hOther rfl).elim
  · norm_num [displayedOccupationProbability] at hOther ⊢
    calc
      |donorLevelOccupationProbability setup - 103 / 125| <
          1 / 1000 := by
        norm_num [AgreesWithinOneThousandth,
          displayedOccupationProbability] at hAgreement
        exact hAgreement
      _ < |donorLevelOccupationProbability setup - 493 / 500| := by
        rw [abs_of_neg]
        · linarith [hProbabilityBounds.2]
        · linarith [hProbabilityBounds.2]

end PhyXMiniProblems.ProblemPhyXMini0575
