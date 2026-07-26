import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0380

open Dimension

/-!
# Average mass density of a filled container

A one-cubic-metre container is partitioned into granite, sand, liquid water,
and air.  Volume, mass, and mass density are represented by unit-independent
Physlib quantities.  Real numbers occur only as readouts in explicitly named
units and as printed answer metadata.

Although the source calls the requested quantity "specific density", its
printed unit is `kg / m³`; consequently the quantity formalized here is mass
density rather than the dimensionless ratio usually called specific gravity.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- A nonnegative physical volume, carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical mass density, carrying dimension `M L⁻³`. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) NNReal)

/-- Read a physical volume in SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical mass in SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical mass density in SI kilograms per cubic metre. -/
def densityInKilogramsPerCubicMeter (density : MassDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Read an absolute temperature in kelvin. -/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Read an absolute temperature in degrees Celsius. -/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvin storageUnit temperature - (5463 / 20 : ℝ)

/-! ## Materials, phases, and primary-image vocabulary -/

/-- The four constituents named in the problem text. -/
inductive Constituent where
  | granite
  | sand
  | water
  | air
  deriving DecidableEq, Fintype, Repr

/-- Macroscopic phase or material form of a constituent. -/
inductive MaterialPhase where
  | solid
  | granularSolid
  | liquid
  | gas
  deriving DecidableEq, Repr

/-- Vertical regions distinguished in the left-hand container sketch. -/
inductive ContainerFigureRegion where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- Incidental objects visible in the right-hand portion of the image. -/
inductive FigureObject where
  | protectiveWorker
  | suspendedMetalBucket
  | craneHook
  deriving DecidableEq, Fintype, Repr

/-!
Readout of the supplied raster.  It records the literal `Air` label and the
upper/lower geometry without pretending that the unlabeled lower texture
separately identifies granite, sand, and water.
-/
structure FilledContainerFigure where
  airLabelVisible : Bool
  airLabelRegion : ContainerFigureRegion
  granularTextureVisible : Bool
  granularTextureRegion : ContainerFigureRegion
  airRegionAboveGranularRegion : Bool
  objectVisible : FigureObject → Bool

/-!
Independent physical quantities for the filled container.  In particular,
the total mass and average density are observables, not definitions containing
the requested numerical answer.
-/
structure FilledContainerSetup where
  containerVolume : VolumeQuantity
  occupiedVolume : Constituent → VolumeQuantity
  constituentMass : Constituent → MassQuantity
  constituentMassDensity : Constituent → MassDensityQuantity
  totalMass : MassQuantity
  overallAverageMassDensity : MassDensityQuantity
  phase : Constituent → MaterialPhase
  waterTemperatureStorageUnit : TemperatureUnit
  waterTemperature : Temperature
  figure : FilledContainerFigure

/-- Celsius readout of the water temperature stated in the prose. -/
def waterTemperatureInDegreesCelsius (setup : FilledContainerSetup) : ℝ :=
  temperatureInDegreesCelsius setup.waterTemperatureStorageUnit
    setup.waterTemperature

/-! ## Supplied scenario and primary-figure data -/

/-!
Problem-text data.  The exact fractions are the decimal volume and air-density
readouts printed in the source.  The source does not give the granite, sand, or
water density, and no total mass or average-density answer occurs here.
-/
structure MatchesProblemData
    (setup : FilledContainerSetup) : Prop where
  containerVolumeIsOneCubicMeter :
    volumeInCubicMeters setup.containerVolume = 1
  graniteVolume :
    volumeInCubicMeters (setup.occupiedVolume .granite) = (3 / 25 : ℝ)
  sandVolume :
    volumeInCubicMeters (setup.occupiedVolume .sand) = (3 / 20 : ℝ)
  waterVolume :
    volumeInCubicMeters (setup.occupiedVolume .water) = (1 / 5 : ℝ)
  airVolume :
    volumeInCubicMeters (setup.occupiedVolume .air) = (53 / 100 : ℝ)
  occupiedVolumesFillContainer :
    (∑ constituent : Constituent,
        volumeInCubicMeters (setup.occupiedVolume constituent)) =
      volumeInCubicMeters setup.containerVolume
  airDensity :
    densityInKilogramsPerCubicMeter
        (setup.constituentMassDensity .air) = (23 / 20 : ℝ)
  graniteIsSolid : setup.phase .granite = .solid
  sandIsGranularSolid : setup.phase .sand = .granularSolid
  waterIsLiquid : setup.phase .water = .liquid
  airIsGas : setup.phase .air = .gas
  waterTemperatureIsTwentyFiveCelsius :
    waterTemperatureInDegreesCelsius setup = 25

/-!
Literal transcription of the primary image, kept separate from the numerical
problem data.  The lower texture is unlabeled, so this structure does not claim
that the image distinguishes granite, sand, and water from one another.
-/
structure MatchesPrimaryFigure
    (setup : FilledContainerSetup) : Prop where
  airLabelIsVisible : setup.figure.airLabelVisible = true
  airLabelIsInUpperRegion : setup.figure.airLabelRegion = .upper
  granularTextureIsVisible : setup.figure.granularTextureVisible = true
  granularTextureIsInLowerRegion :
    setup.figure.granularTextureRegion = .lower
  airIsDrawnAboveGranularRegion :
    setup.figure.airRegionAboveGranularRegion = true
  rightHandObjectsAreVisible :
    ∀ object : FigureObject, setup.figure.objectVisible object = true

/-- Strict positivity conditions selecting a physically nondegenerate setup. -/
structure HasPhysicalParameters (setup : FilledContainerSetup) : Prop where
  positiveContainerVolume : 0 < volumeInCubicMeters setup.containerVolume
  positiveOccupiedVolume :
    ∀ constituent : Constituent,
      0 < volumeInCubicMeters (setup.occupiedVolume constituent)
  positiveConstituentDensity :
    ∀ constituent : Constituent,
      0 < densityInKilogramsPerCubicMeter
        (setup.constituentMassDensity constituent)
  positiveAbsoluteWaterTemperature :
    0 < temperatureInKelvin setup.waterTemperatureStorageUnit
      setup.waterTemperature

/-! ## Governing laws -/

/-!
Mass-density laws for a partitioned container.  The first field is the general
relation `m = ρV` for every constituent, the second is additivity of mass, and
the third defines average density as total mass divided by total volume.  The
laws contain neither `775` nor any answer-choice label.
-/
structure SatisfiesAverageDensityLaws
    (setup : FilledContainerSetup) : Prop where
  constituentMassFromDensityAndVolume :
    ∀ constituent : Constituent,
      massInKilograms (setup.constituentMass constituent) =
        densityInKilogramsPerCubicMeter
            (setup.constituentMassDensity constituent) *
          volumeInCubicMeters (setup.occupiedVolume constituent)
  totalMassIsAdditive :
    massInKilograms setup.totalMass =
      ∑ constituent : Constituent,
        massInKilograms (setup.constituentMass constituent)
  averageDensityIsTotalMassPerContainerVolume :
    densityInKilogramsPerCubicMeter setup.overallAverageMassDensity =
      massInKilograms setup.totalMass /
        volumeInCubicMeters setup.containerVolume

/-! ## Printed-answer metadata and source-supported target -/

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Printed density readout, in kilograms per cubic metre, for each choice. -/
def displayedDensityInKilogramsPerCubicMeter : AnswerChoice → ℝ
  | .A => 775
  | .B => 115
  | .C => 815
  | .D => 125

/-!
The answer label recorded by the dataset.  It is metadata only: neither this
definition nor the displayed values occur in the governing laws or theorem
conclusion, because the source omits three material densities needed to derive
a numerical choice.
-/
def recordedDatasetAnswer : AnswerChoice := .A

/-!
Blueprint label: `thm:physics:phyx_mini_0380:target`.

The source-supported conclusion is the volume-weighted density formula.  The
granite, sand, and water densities remain explicit free physical readouts,
because the problem supplies none of them.  Thus the theorem does not assert a
numerical answer choice from uncited calibration data.
-/
theorem overall_average_mass_density_from_supplied_data
    (setup : FilledContainerSetup)
    (problemData : MatchesProblemData setup)
    (figureData : MatchesPrimaryFigure setup)
    (physical : HasPhysicalParameters setup)
    (laws : SatisfiesAverageDensityLaws setup) :
    densityInKilogramsPerCubicMeter setup.overallAverageMassDensity =
      densityInKilogramsPerCubicMeter
          (setup.constituentMassDensity .granite) * (3 / 25 : ℝ) +
        densityInKilogramsPerCubicMeter
          (setup.constituentMassDensity .sand) * (3 / 20 : ℝ) +
        densityInKilogramsPerCubicMeter
          (setup.constituentMassDensity .water) * (1 / 5 : ℝ) +
        (23 / 20 : ℝ) * (53 / 100 : ℝ) := by
  classical
  rw [laws.averageDensityIsTotalMassPerContainerVolume,
    problemData.containerVolumeIsOneCubicMeter, div_one,
    laws.totalMassIsAdditive]
  simp_rw [laws.constituentMassFromDensityAndVolume]
  have constituent_univ :
      (Finset.univ : Finset Constituent) =
        {.granite, .sand, .water, .air} := by
    ext constituent
    cases constituent <;> simp
  rw [constituent_univ]
  simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_singleton, or_self,
    not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, one_div,
    problemData.graniteVolume, problemData.sandVolume,
    problemData.waterVolume, problemData.airVolume, problemData.airDensity,
    add_assoc]

end PhyXMiniProblems.ProblemPhyXMini0380
