import Mathlib
import Physlib.Units.WithDim.Area

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0945

open Dimension

/-!
# Average solar power absorbed by satellite panels

An Earth-orbiting satellite carries two solar-panel wings whose total collecting
area is `4.0 m²`.  The incident sunlight is normal to the panel surfaces and is
completely absorbed.  The standard average near-Earth solar irradiance, together
with projected-area collection and absorption power balance, determines the
average absorbed power.

Area, irradiance, and power are represented by unit-independent Physlib
`Dimensionful` quantities.  Real numbers below occur only as coherent-SI
readouts, the dimensionless absorptivity, and displayed multiple-choice values.

Assumption/target split:

* `MatchesProblemStatement` records Earth orbit, the total `4.0 m²` area,
  normal incidence, and the complete-absorption model;
* `MatchesPrimarySatelliteFigure` records the two panel wings, central body,
  sun sensor, and two arrows labeled by the sunlight vector `S`;
* `UsesTextbookAverageNearEarthIrradiance` supplies the standard average solar
  irradiance `1400 W/m²`, which is implicit in the recorded numerical answer;
* there are no previous-part results for this standalone problem;
* `SatisfiesSolarPanelPowerLaws` states projected-area collection and absorbed
  power balance; and
* `averageSolarPowerAbsorbed_matches_answer_B` concludes `5.6 kW` and the
  unique answer choice B.

In particular, the absorbed power is an independent setup field.  Neither its
requested readout nor answer B occurs in any premise structure.
-/

/-! ## Dimensionful radiometric quantities and coherent-SI readouts -/

/-- The physical dimension `M T⁻³` of irradiance (watt per square metre). -/
def irradianceDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L² T⁻³` of power (watt). -/
def powerDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent solar irradiance. -/
abbrev IrradianceQuantity : Type :=
  Dimensionful (WithDim irradianceDimension NNReal)

/-- A nonnegative, unit-independent radiant power. -/
abbrev RadiantPowerQuantity : Type :=
  Dimensionful (WithDim powerDimension NNReal)

/-- Read a physical area in coherent-SI square metres. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read a solar irradiance in coherent-SI watts per square metre. -/
def irradianceInWattsPerSquareMeter
    (irradiance : IrradianceQuantity) : ℝ :=
  ((irradiance UnitChoices.SI).val : ℝ)

/-- Read a radiant power in coherent-SI watts. -/
def powerInWatts (power : RadiantPowerQuantity) : ℝ :=
  ((power UnitChoices.SI).val : ℝ)

/-- Read a radiant power in kilowatts. -/
def powerInKilowatts (power : RadiantPowerQuantity) : ℝ :=
  powerInWatts power / 1000

/-! ## Satellite, panel, and primary-figure vocabulary -/

/-- Orbital environment specified by the problem. -/
inductive OrbitalRegion where
  | earthOrbit
  | other
  deriving DecidableEq, Repr

/-- Relation between the sunlight propagation direction and a panel surface. -/
inductive RadiationIncidence where
  | normalToPanelSurface
  | oblique
  deriving DecidableEq, Repr

/-- Optical absorption model of the collecting surface. -/
inductive SurfaceAbsorptionModel where
  | completeAbsorption
  | partialAbsorption
  deriving DecidableEq, Repr

/-- The two panel wings visible on opposite sides of the satellite body. -/
inductive PanelWing where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Symbol attached to each sunlight-direction arrow in the primary figure. -/
inductive SunlightVectorLabel where
  | S
  deriving DecidableEq, Repr

/-- Purpose stated by the annotation attached to the sun sensor. -/
inductive SunSensorPurpose where
  | keepPanelsFacingSun
  deriving DecidableEq, Repr

/-!
Literal content of image `945.png`.  This stores only labels and qualitative
geometry visible in the raster; it does not store a power value.
-/
structure SatelliteSolarPanelFigure where
  centralSatelliteBodyShown : Bool
  panelWingShown : PanelWing → Bool
  panelWingExtendsFromCentralBody : PanelWing → Bool
  solarPanelsAnnotationShown : Bool
  sunSensorShown : Bool
  sunSensorAnnotationShown : Bool
  sunSensorPurpose : SunSensorPurpose
  sunlightArrowCount : ℕ
  sunlightArrowLabel : SunlightVectorLabel
  sunlightArrowsPointTowardPanels : Bool

/-!
The physical panel array.  Incident and absorbed average powers are independent
observables; their relation is supplied only by the governing laws below.
-/
structure SolarPanelArray where
  totalCollectingArea : DimArea
  absorptionModel : SurfaceAbsorptionModel
  absorptivity : ℝ
  incidentAverageSolarPower : RadiantPowerQuantity
  absorbedAverageSolarPower : RadiantPowerQuantity

/-- All physical quantities and figure data in the satellite setup. -/
structure SatelliteSolarPowerSetup where
  orbitalRegion : OrbitalRegion
  radiationIncidence : RadiationIncidence
  incidentAverageSolarIrradiance : IrradianceQuantity
  panels : SolarPanelArray
  figure : SatelliteSolarPanelFigure

/-! ## Problem data, primary-figure readouts, and governing laws -/

/-- Numerical and qualitative facts stated in the problem prose. -/
structure MatchesProblemStatement
    (setup : SatelliteSolarPowerSetup) : Prop where
  satelliteIsEarthOrbiting : setup.orbitalRegion = .earthOrbit
  totalPanelAreaSquareMeters :
    areaInSquareMeters setup.panels.totalCollectingArea = 4.0
  sunlightPerpendicularToPanels :
    setup.radiationIncidence = .normalToPanelSurface
  sunlightCompletelyAbsorbed :
    setup.panels.absorptionModel = .completeAbsorption

/-!
Primary-image evidence: a central body has a panel wing on each side; a
labeled sun sensor keeps them facing the Sun; and two arrows labeled `S` point
toward the panels.
-/
structure MatchesPrimarySatelliteFigure
    (setup : SatelliteSolarPowerSetup) : Prop where
  centralBodyShown : setup.figure.centralSatelliteBodyShown = true
  bothPanelWingsShown : ∀ wing, setup.figure.panelWingShown wing = true
  bothPanelWingsExtendFromBody : ∀ wing,
    setup.figure.panelWingExtendsFromCentralBody wing = true
  solarPanelsLabeled : setup.figure.solarPanelsAnnotationShown = true
  sunSensorShown : setup.figure.sunSensorShown = true
  sunSensorLabeled : setup.figure.sunSensorAnnotationShown = true
  sensorKeepsPanelsFacingSun :
    setup.figure.sunSensorPurpose = .keepPanelsFacingSun
  twoSunlightArrows : setup.figure.sunlightArrowCount = 2
  arrowsLabeledS : setup.figure.sunlightArrowLabel = .S
  arrowsPointTowardPanels :
    setup.figure.sunlightArrowsPointTowardPanels = true

/-!
The textbook average solar irradiance near Earth's orbit is approximately
`1.4 kW/m² = 1400 W/m²`.  The source problem omits this necessary environmental
calibration, so it is exposed as a separate data premise rather than hidden in
a definition or in the requested power conclusion.
-/
structure UsesTextbookAverageNearEarthIrradiance
    (setup : SatelliteSolarPowerSetup) : Prop where
  averageIrradianceReadout :
    irradianceInWattsPerSquareMeter
        setup.incidentAverageSolarIrradiance = 1400

/-!
The governing power relations.  At normal incidence the intercepted average
power is irradiance times total collecting area.  Complete absorption means
unit absorptivity, and absorbed power is the absorptivity fraction of incident
power.  None of these laws mentions `5.6 kW` or an answer label.
-/
structure SatisfiesSolarPanelPowerLaws
    (setup : SatelliteSolarPowerSetup) : Prop where
  normalIncidenceCollection :
    setup.radiationIncidence = .normalToPanelSurface →
      powerInWatts setup.panels.incidentAverageSolarPower =
        irradianceInWattsPerSquareMeter
            setup.incidentAverageSolarIrradiance *
          areaInSquareMeters setup.panels.totalCollectingArea
  completeAbsorptionHasUnitAbsorptivity :
    setup.panels.absorptionModel = .completeAbsorption →
      setup.panels.absorptivity = 1
  absorbedPowerBalance :
    powerInWatts setup.panels.absorbedAverageSolarPower =
      setup.panels.absorptivity *
        powerInWatts setup.panels.incidentAverageSolarPower

/-! ## Displayed alternatives and current target -/

/-- Labels of the four answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Power in kilowatts printed beside each answer label. -/
def displayedPowerInKilowatts : AnswerChoice → ℝ
  | .A => 5.5
  | .B => 5.6
  | .C => 7.5
  | .D => 5.9

/-- A displayed choice exactly matches the computed absorbed-power readout. -/
def MatchesDisplayedAbsorbedPower
    (setup : SatelliteSolarPowerSetup) (choice : AnswerChoice) : Prop :=
  powerInKilowatts setup.panels.absorbedAverageSolarPower =
    displayedPowerInKilowatts choice

/-- Exactly one displayed answer matches the absorbed-power readout. -/
def IsUniqueMatchingAbsorbedPower
    (setup : SatelliteSolarPowerSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedAbsorbedPower setup choice ∧
    ∀ other : AnswerChoice, other ≠ choice →
      ¬ MatchesDisplayedAbsorbedPower setup other

/-!
The average absorbed solar power is `5.6 kW`, uniquely selecting answer B.

Blueprint: `thm:physics:phyx_mini_0945:target`.
-/
theorem averageSolarPowerAbsorbed_matches_answer_B
    (setup : SatelliteSolarPowerSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimarySatelliteFigure setup)
    (_irradiance : UsesTextbookAverageNearEarthIrradiance setup)
    (_laws : SatisfiesSolarPanelPowerLaws setup) :
    powerInKilowatts setup.panels.absorbedAverageSolarPower = 5.6 ∧
      MatchesDisplayedAbsorbedPower setup .B ∧
      IsUniqueMatchingAbsorbedPower setup .B := by
  have hIncidentWatts :
      powerInWatts setup.panels.incidentAverageSolarPower = 5600 := by
    calc
      powerInWatts setup.panels.incidentAverageSolarPower =
          irradianceInWattsPerSquareMeter
              setup.incidentAverageSolarIrradiance *
            areaInSquareMeters setup.panels.totalCollectingArea :=
        _laws.normalIncidenceCollection
          _problem.sunlightPerpendicularToPanels
      _ = 1400 * 4.0 := by
        rw [_irradiance.averageIrradianceReadout,
          _problem.totalPanelAreaSquareMeters]
      _ = 5600 := by norm_num
  have hAbsorptivity : setup.panels.absorptivity = 1 :=
    _laws.completeAbsorptionHasUnitAbsorptivity
      _problem.sunlightCompletelyAbsorbed
  have hAbsorbedWatts :
      powerInWatts setup.panels.absorbedAverageSolarPower = 5600 := by
    rw [_laws.absorbedPowerBalance, hAbsorptivity, hIncidentWatts]
    norm_num
  have hAbsorbedKilowatts :
      powerInKilowatts setup.panels.absorbedAverageSolarPower = 5.6 := by
    unfold powerInKilowatts
    rw [hAbsorbedWatts]
    norm_num
  refine ⟨hAbsorbedKilowatts, ?_, ?_⟩
  · simpa [MatchesDisplayedAbsorbedPower, displayedPowerInKilowatts] using
      hAbsorbedKilowatts
  · constructor
    · simpa [MatchesDisplayedAbsorbedPower, displayedPowerInKilowatts] using
        hAbsorbedKilowatts
    · intro other hOtherNe hOtherMatches
      unfold MatchesDisplayedAbsorbedPower at hOtherMatches
      rw [hAbsorbedKilowatts] at hOtherMatches
      cases other with
      | A => norm_num [displayedPowerInKilowatts] at hOtherMatches
      | B => exact (hOtherNe rfl).elim
      | C => norm_num [displayedPowerInKilowatts] at hOtherMatches
      | D => norm_num [displayedPowerInKilowatts] at hOtherMatches

end PhyXMiniProblems.ProblemPhyXMini0945
