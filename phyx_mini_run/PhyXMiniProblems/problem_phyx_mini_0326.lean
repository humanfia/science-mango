import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0326

open Dimension

/-!
# Surface-wave intensity from the 1996 Yosemite rockfall

The event launches two seismic-wave species from one impact point.  The body
wave spreads through an expanding hemisphere, while the surface wave spreads
along the ground through a shallow vertical cylindrical wavefront of depth
`d`.  The requested observable is the surface-wave intensity at a seismograph
`200 km` from the impact.

Basic physical magnitudes are represented by Physlib dimensionful quantities.
Real scalars below are only coherent-unit readouts, dimensionless energy
fractions, calendar data, or displayed multiple-choice values.
-/

/-! ## Dimensionful physical quantities and coherent-unit readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Mechanical or seismic energy, using Physlib's dimensional energy type. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Wavefront area, using Physlib's dimensional area type. -/
abbrev AreaQuantity : Type := DimArea

/-- A nonnegative power, with coherent SI unit watt. -/
abbrev PowerQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-!
Intensity is power per area, so its physical dimension is
`(M L² T⁻³) / L² = M T⁻³`; its coherent SI unit is watt per square metre.
-/
abbrev IntensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a nonnegative dimensional quantity in a coherent unit system. -/
def nonnegativeQuantityReadout {d : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  nonnegativeQuantityReadout {UnitChoices.SI with length := unit} length

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Kilometre readout of a physical length. -/
def lengthInKilometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.kilometers length

/-- Second readout of a physical duration. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  nonnegativeQuantityReadout
    {UnitChoices.SI with time := TimeUnit.seconds} duration

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI mass

/-- Metre-per-second-squared readout of an acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI acceleration

/-- Joule readout of an energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-- Square-metre readout of a wavefront area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI area

/-- Watt readout of a wave power. -/
def powerInWatts (power : PowerQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI power

/-- Watt-per-square-metre readout of a wave intensity. -/
def intensityInWattsPerSquareMeter (intensity : IntensityQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI intensity

/-- Kilowatt-per-square-metre readout used by the answer choices. -/
def intensityInKilowattsPerSquareMeter
    (intensity : IntensityQuantity) : ℝ :=
  intensityInWattsPerSquareMeter intensity / 1000

/-! ## Event, wave, and primary-figure vocabulary -/

/-- The historical event named in the problem statement. -/
inductive RockfallEvent where
  | yosemiteValley1996July10
  deriving DecidableEq, Repr

/-- Material of the falling block. -/
inductive BlockMaterial where
  | granite
  deriving DecidableEq, Repr

/-- The two seismic-wave species produced by the impact. -/
inductive SeismicWaveKind where
  | body
  | surface
  deriving DecidableEq, Repr

/-- Idealized wavefront shapes stated in the prose and shown in the image. -/
inductive WavefrontGeometry where
  | expandingHemisphere
  | expandingShallowVerticalCylinder
  deriving DecidableEq, Repr

/-- Qualitative propagation directions displayed by the arrows in the image. -/
inductive FigurePropagationDirection where
  | downwardAndOutward
  | horizontalAlongGroundBothDirections
  deriving DecidableEq, Repr

/-- Named locations or markers visible in the primary image. -/
inductive FigureFeature where
  | impactPoint
  | groundSurface
  | depthMarkerD
  deriving DecidableEq, Repr

/-!
Primary-image evidence is stored separately from the physical laws.  The
figure carries the depth label `d` but does not itself assign its numerical
value; that value comes from the prose data predicate below.
-/
structure SeismicPropagationFigure where
  wavefrontGeometry : SeismicWaveKind → WavefrontGeometry
  propagationDirection : SeismicWaveKind → FigurePropagationDirection
  originFeature : SeismicWaveKind → FigureFeature
  depthLabelD : LengthQuantity
  featureShown : FigureFeature → Bool
  outwardArrowsShown : SeismicWaveKind → Bool

/-!
The independent quantities and observables in the rockfall model.  The actual
block mass is distinct from the two measured endpoints.  Wave energy, power,
area, and intensity are also stored independently, then related by governing
laws rather than by answer-producing definitions.
-/
structure YosemiteRockfallSetup where
  event : RockfallEvent
  blockMaterial : BlockMaterial
  measuredMassLower : MassQuantity
  measuredMassUpper : MassQuantity
  blockMass : MassQuantity
  verticalDrop : LengthQuantity
  horizontalDisplacement : LengthQuantity
  gravitationalAcceleration : AccelerationQuantity
  impactDuration : TimeQuantity
  surfaceCylinderDepth : LengthQuantity
  stationDistance : LengthQuantity
  impactEnergyJustBeforeCollision : EnergyQuantity
  waveEnergyFraction : SeismicWaveKind → ℝ
  waveEnergy : SeismicWaveKind → EnergyQuantity
  wavePowerDuringImpact : SeismicWaveKind → PowerQuantity
  transportedPowerAtDistance : SeismicWaveKind → LengthQuantity → PowerQuantity
  wavefrontAreaAtDistance : SeismicWaveKind → LengthQuantity → AreaQuantity
  intensityAtDistance : SeismicWaveKind → LengthQuantity → IntensityQuantity
  figure : SeismicPropagationFigure

/-! ## Assumption-side scenario, data, and governing laws -/

/-- Positivity and nondegeneracy of the independent physical parameters. -/
structure HasPhysicalRockfallParameters
    (setup : YosemiteRockfallSetup) : Prop where
  measuredMassLowerPositive : 0 < massInKilograms setup.measuredMassLower
  measuredMassUpperPositive : 0 < massInKilograms setup.measuredMassUpper
  blockMassPositive : 0 < massInKilograms setup.blockMass
  verticalDropPositive : 0 < lengthInMeters setup.verticalDrop
  impactDurationPositive : 0 < timeInSeconds setup.impactDuration
  surfaceCylinderDepthPositive : 0 < lengthInMeters setup.surfaceCylinderDepth
  stationDistancePositive : 0 < lengthInMeters setup.stationDistance
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  impactEnergyPositive : 0 < energyInJoules setup.impactEnergyJustBeforeCollision
  waveEnergyPositive :
    ∀ wave, 0 < energyInJoules (setup.waveEnergy wave)
  wavePowerPositive :
    ∀ wave, 0 < powerInWatts (setup.wavePowerDuringImpact wave)

/-!
Textual measurements and qualitative data, together with the labels and
geometry read from the primary image.  The actual mass is constrained by the
reported interval but is not replaced by either endpoint.
-/
structure MatchesYosemiteRockfallStatementAndFigure
    (setup : YosemiteRockfallSetup) : Prop where
  eventReadout : setup.event = .yosemiteValley1996July10
  materialReadout : setup.blockMaterial = .granite
  measuredMassLowerKilograms :
    massInKilograms setup.measuredMassLower = 73 * 10 ^ 6
  measuredMassUpperKilograms :
    massInKilograms setup.measuredMassUpper = 17 * 10 ^ 7
  actualMassWithinMeasuredRange :
    massInKilograms setup.measuredMassLower ≤
        massInKilograms setup.blockMass ∧
      massInKilograms setup.blockMass ≤
        massInKilograms setup.measuredMassUpper
  verticalDropMeters : lengthInMeters setup.verticalDrop = 500
  horizontalDisplacementMeters :
    lengthInMeters setup.horizontalDisplacement = 30
  standardEarthGravityReadout :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      98 / 10
  impactDurationSeconds : timeInSeconds setup.impactDuration = 1 / 2
  surfaceCylinderDepthMeters :
    lengthInMeters setup.surfaceCylinderDepth = 5
  stationDistanceKilometers : lengthInKilometers setup.stationDistance = 200
  eachWaveReceivesTwentyPercent :
    ∀ wave, setup.waveEnergyFraction wave = 1 / 5
  impactPointAndDepthMarkerShown :
    setup.figure.featureShown .impactPoint = true ∧
      setup.figure.featureShown .groundSurface = true ∧
      setup.figure.featureShown .depthMarkerD = true
  allOutwardArrowsShown :
    ∀ wave, setup.figure.outwardArrowsShown wave = true
  bothWavesOriginateAtImpact :
    ∀ wave, setup.figure.originFeature wave = .impactPoint
  bodyWaveIsHemispherical :
    setup.figure.wavefrontGeometry .body = .expandingHemisphere
  surfaceWaveIsCylindrical :
    setup.figure.wavefrontGeometry .surface =
      .expandingShallowVerticalCylinder
  bodyWaveDirectionReadout :
    setup.figure.propagationDirection .body = .downwardAndOutward
  surfaceWaveDirectionReadout :
    setup.figure.propagationDirection .surface =
      .horizontalAlongGroundBothDirections
  figureDepthMatchesPhysicalDepth :
    lengthInMeters setup.figure.depthLabelD =
      lengthInMeters setup.surfaceCylinderDepth

/-!
Mechanical-energy conservation in the intended rockfall approximation: the
impact energy just before collision is the gravitational energy released over
the vertical drop.  The equation is parameter-generic and contains no wave
intensity or answer-choice value.
-/
structure SatisfiesRockfallImpactEnergyLaw
    (setup : YosemiteRockfallSetup) : Prop where
  impactEnergyFromVerticalDrop :
    energyInJoules setup.impactEnergyJustBeforeCollision =
      massInKilograms setup.blockMass *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
        lengthInMeters setup.verticalDrop

/-- Each wave receives its stated fraction of the pre-impact block energy. -/
structure SatisfiesSeismicEnergyPartitionLaw
    (setup : YosemiteRockfallSetup) : Prop where
  waveEnergyIsFractionOfImpactEnergy :
    ∀ wave,
      energyInJoules (setup.waveEnergy wave) =
        setup.waveEnergyFraction wave *
          energyInJoules setup.impactEnergyJustBeforeCollision

/-- Average power is the assigned seismic energy divided by impact duration. -/
structure SatisfiesFiniteImpactPowerLaw
    (setup : YosemiteRockfallSetup) : Prop where
  powerIsEnergyPerImpactDuration :
    ∀ wave,
      powerInWatts (setup.wavePowerDuringImpact wave) =
        energyInJoules (setup.waveEnergy wave) /
          timeInSeconds setup.impactDuration

/-!
Wavefront geometry from the model and figure: the body wave occupies a
hemisphere of area `2πr²`, whereas the shallow surface-wave cylinder has
lateral area `2πrd`.  The latter is the area across which surface-wave power
is distributed.
-/
structure SatisfiesSeismicWavefrontGeometryLaw
    (setup : YosemiteRockfallSetup) : Prop where
  bodyWavefrontArea :
    ∀ radius,
      0 < lengthInMeters radius →
      areaInSquareMeters (setup.wavefrontAreaAtDistance .body radius) =
        2 * Real.pi * lengthInMeters radius ^ 2
  surfaceWavefrontArea :
    ∀ radius,
      0 < lengthInMeters radius →
      areaInSquareMeters (setup.wavefrontAreaAtDistance .surface radius) =
        2 * Real.pi * lengthInMeters radius *
          lengthInMeters setup.surfaceCylinderDepth

/-!
Lossless propagation preserves the power assigned at impact.  Intensity is
that transported power divided by the relevant wavefront area.  These are
general propagation laws at every positive radius, not the requested
numerical conclusion at `200 km`.
-/
structure SatisfiesLosslessSeismicIntensityLaw
    (setup : YosemiteRockfallSetup) : Prop where
  noMechanicalEnergyLoss :
    ∀ wave radius,
      0 < lengthInMeters radius →
      powerInWatts (setup.transportedPowerAtDistance wave radius) =
        powerInWatts (setup.wavePowerDuringImpact wave)
  intensityIsPowerPerWavefrontArea :
    ∀ wave radius,
      0 < areaInSquareMeters (setup.wavefrontAreaAtDistance wave radius) →
      intensityInWattsPerSquareMeter
          (setup.intensityAtDistance wave radius) =
        powerInWatts (setup.transportedPowerAtDistance wave radius) /
          areaInSquareMeters (setup.wavefrontAreaAtDistance wave radius)

/-! ## Derived surface-wave relation -/

/-!
Combining the energy, duration, cylindrical-area, and lossless-propagation
laws yields the general surface-wave intensity formula at the station.  No
displayed answer is mentioned in this intermediate statement.
-/
lemma surfaceWaveIntensityAtStation_formula
    (setup : YosemiteRockfallSetup)
    (hPhysical : HasPhysicalRockfallParameters setup)
    (hImpactEnergy : SatisfiesRockfallImpactEnergyLaw setup)
    (hPartition : SatisfiesSeismicEnergyPartitionLaw setup)
    (hPower : SatisfiesFiniteImpactPowerLaw setup)
    (hGeometry : SatisfiesSeismicWavefrontGeometryLaw setup)
    (hLossless : SatisfiesLosslessSeismicIntensityLaw setup) :
    intensityInWattsPerSquareMeter
        (setup.intensityAtDistance .surface setup.stationDistance) =
      setup.waveEnergyFraction .surface *
        (massInKilograms setup.blockMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters setup.verticalDrop) /
        (timeInSeconds setup.impactDuration *
          (2 * Real.pi * lengthInMeters setup.stationDistance *
            lengthInMeters setup.surfaceCylinderDepth)) := by
  have hRadius : 0 < lengthInMeters setup.stationDistance :=
    hPhysical.stationDistancePositive
  have hDepth : 0 < lengthInMeters setup.surfaceCylinderDepth :=
    hPhysical.surfaceCylinderDepthPositive
  have hArea :
      areaInSquareMeters
          (setup.wavefrontAreaAtDistance .surface setup.stationDistance) =
        2 * Real.pi * lengthInMeters setup.stationDistance *
          lengthInMeters setup.surfaceCylinderDepth :=
    hGeometry.surfaceWavefrontArea setup.stationDistance hRadius
  have hAreaPositive :
      0 <
        areaInSquareMeters
          (setup.wavefrontAreaAtDistance .surface setup.stationDistance) := by
    rw [hArea]
    positivity
  rw [hLossless.intensityIsPowerPerWavefrontArea
        .surface setup.stationDistance hAreaPositive,
      hLossless.noMechanicalEnergyLoss .surface setup.stationDistance hRadius,
      hPower.powerIsEnergyPerImpactDuration .surface,
      hPartition.waveEnergyIsFractionOfImpactEnergy .surface,
      hImpactEnergy.impactEnergyFromVerticalDrop,
      hArea]
  ring

/-! ## Multiple-choice data and blueprint target -/

/-- Labels of the four answers printed with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed surface-wave intensities, in kilowatts per square metre. -/
def displayedIntensityInKilowattsPerSquareMeter : AnswerChoice → ℝ
  | .A => 43
  | .B => 48
  | .C => 53
  | .D => 58

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswerChoice : AnswerChoice := .D

/-- Agreement with a displayed whole-number intensity to the nearest unit. -/
def RoundsToDisplayedWholeKilowattPerSquareMeter
    (intensity displayedValue : ℝ) : Prop :=
  |intensity - displayedValue| < 1 / 2

/-!
The source data do not specify one block mass, so they do not determine one
displayed multiple-choice value.  The physically supported conclusion is the
mass-dependent intensity formula together with the exact interval obtained
from the two measured mass endpoints.  That interval lies strictly below the
rounding window for the recorded answer D (`58 kW/m²`), so D is retained only
as dataset metadata and is explicitly rejected by the modeled result.

Blueprint: `thm:physics:phyx_mini_0326:target`.
-/
theorem problem_phyx_mini_0326
    (setup : YosemiteRockfallSetup)
    (hPhysical : HasPhysicalRockfallParameters setup)
    (hData : MatchesYosemiteRockfallStatementAndFigure setup)
    (hImpactEnergy : SatisfiesRockfallImpactEnergyLaw setup)
    (hPartition : SatisfiesSeismicEnergyPartitionLaw setup)
    (hPower : SatisfiesFiniteImpactPowerLaw setup)
    (hGeometry : SatisfiesSeismicWavefrontGeometryLaw setup)
    (hLossless : SatisfiesLosslessSeismicIntensityLaw setup) :
    intensityInKilowattsPerSquareMeter
          (setup.intensityAtDistance .surface setup.stationDistance) =
        (setup.waveEnergyFraction .surface *
            (massInKilograms setup.blockMass *
              accelerationInMetersPerSecondSquared
                setup.gravitationalAcceleration *
              lengthInMeters setup.verticalDrop) /
            (timeInSeconds setup.impactDuration *
              (2 * Real.pi * lengthInMeters setup.stationDistance *
                lengthInMeters setup.surfaceCylinderDepth))) /
          1000 ∧
      ((1 / 5 : ℝ) *
              ((73 * 10 ^ 6) * (98 / 10) * 500) /
            ((1 / 2) * (2 * Real.pi * (200 * 1000) * 5))) /
          1000 ≤
        intensityInKilowattsPerSquareMeter
          (setup.intensityAtDistance .surface setup.stationDistance) ∧
      intensityInKilowattsPerSquareMeter
          (setup.intensityAtDistance .surface setup.stationDistance) ≤
        ((1 / 5 : ℝ) *
              ((17 * 10 ^ 7) * (98 / 10) * 500) /
            ((1 / 2) * (2 * Real.pi * (200 * 1000) * 5))) /
          1000 ∧
      ¬ RoundsToDisplayedWholeKilowattPerSquareMeter
          (intensityInKilowattsPerSquareMeter
            (setup.intensityAtDistance .surface setup.stationDistance))
          (displayedIntensityInKilowattsPerSquareMeter
            recordedDatasetAnswerChoice) := by
  have hFormulaWatts :=
    surfaceWaveIntensityAtStation_formula setup hPhysical hImpactEnergy
      hPartition hPower hGeometry hLossless
  have hFormulaKilowatts :
      intensityInKilowattsPerSquareMeter
            (setup.intensityAtDistance .surface setup.stationDistance) =
          (setup.waveEnergyFraction .surface *
              (massInKilograms setup.blockMass *
                accelerationInMetersPerSecondSquared
                  setup.gravitationalAcceleration *
                lengthInMeters setup.verticalDrop) /
              (timeInSeconds setup.impactDuration *
                (2 * Real.pi * lengthInMeters setup.stationDistance *
                  lengthInMeters setup.surfaceCylinderDepth))) /
            1000 := by
    simpa [intensityInKilowattsPerSquareMeter] using
      congrArg (fun value : ℝ => value / 1000) hFormulaWatts
  have hLengthConversion :
      lengthInKilometers setup.stationDistance =
        lengthInMeters setup.stationDistance / 1000 := by
    have h := congrArg (fun x : NNReal => (x : ℝ)) <|
      congrArg WithDim.val <|
        setup.stationDistance.2
          ({UnitChoices.SI with length := LengthUnit.meters} : UnitChoices)
          ({UnitChoices.SI with length := LengthUnit.kilometers} : UnitChoices)
    change
      lengthInKilometers setup.stationDistance =
        _ * lengthInMeters setup.stationDistance at h
    norm_num [lengthInKilometers, lengthInMeters, lengthReadout,
      nonnegativeQuantityReadout, UnitChoices.dimScale,
      LengthUnit.kilometers, LengthUnit.meters, LengthUnit.scale,
      LengthUnit.div_eq_val, NNReal.smul_def, NNReal.coe_inv] at h ⊢
    convert h using 1
    change _ / 1000 = (1 / 1000 : ℝ) * _
    ring
  have hStationMeters :
      lengthInMeters setup.stationDistance = 200 * 1000 := by
    rw [hData.stationDistanceKilometers] at hLengthConversion
    norm_num at hLengthConversion ⊢
    linarith
  have hIntensityNumeric :
      intensityInKilowattsPerSquareMeter
            (setup.intensityAtDistance .surface setup.stationDistance) =
        ((1 / 5 : ℝ) *
                (massInKilograms setup.blockMass * (98 / 10) * 500) /
              ((1 / 2) * (2 * Real.pi * (200 * 1000) * 5))) /
            1000 := by
    rw [hFormulaKilowatts, hData.eachWaveReceivesTwentyPercent,
      hData.standardEarthGravityReadout, hData.verticalDropMeters,
      hData.impactDurationSeconds, hStationMeters,
      hData.surfaceCylinderDepthMeters]
  have hMassLower :
      (73 * 10 ^ 6 : ℝ) ≤ massInKilograms setup.blockMass := by
    rw [← hData.measuredMassLowerKilograms]
    exact hData.actualMassWithinMeasuredRange.1
  have hMassUpper :
      massInKilograms setup.blockMass ≤ (17 * 10 ^ 7 : ℝ) := by
    rw [← hData.measuredMassUpperKilograms]
    exact hData.actualMassWithinMeasuredRange.2
  refine ⟨hFormulaKilowatts, ?_, ?_, ?_⟩
  · rw [hIntensityNumeric]
    gcongr
  · rw [hIntensityNumeric]
    gcongr
  · intro hRounds
    have hUpper :
        intensityInKilowattsPerSquareMeter
              (setup.intensityAtDistance .surface setup.stationDistance) ≤
          ((1 / 5 : ℝ) *
                ((17 * 10 ^ 7) * (98 / 10) * 500) /
              ((1 / 2) * (2 * Real.pi * (200 * 1000) * 5))) /
            1000 := by
      rw [hIntensityNumeric]
      gcongr
    have hNumericalUpper :
        ((1 / 5 : ℝ) *
                ((17 * 10 ^ 7) * (98 / 10) * 500) /
              ((1 / 2) * (2 * Real.pi * (200 * 1000) * 5))) /
            1000 <
          58 - 1 / 2 := by
      have hPi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hPiPositive : 0 < Real.pi := Real.pi_pos
      field_simp
      nlinarith
    have hBelowWindow :
        intensityInKilowattsPerSquareMeter
              (setup.intensityAtDistance .surface setup.stationDistance) <
          58 - 1 / 2 :=
      lt_of_le_of_lt hUpper hNumericalUpper
    simp only [RoundsToDisplayedWholeKilowattPerSquareMeter,
      recordedDatasetAnswerChoice,
      displayedIntensityInKilowattsPerSquareMeter] at hRounds
    rw [abs_lt] at hRounds
    linarith

end PhyXMiniProblems.ProblemPhyXMini0326
