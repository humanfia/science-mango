import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0189

open Dimension
open NNReal

/-!
# Sound transmission from the eardrum to the inner-ear fluid

Physlib supplies dimensionful areas, speeds, and pressures.  The additional
quantity types below use the same unit-independent representation for the
length amplitude, frequency, mass density, and acoustic intensity needed by
the elementary linear-acoustics model.
-/

/-- A nonnegative physical length, used here for a displacement amplitude. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ≥0)

/-- A nonnegative physical frequency, with dimension inverse time. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ≥0)

/-- A nonnegative mass density, with dimension `M L⁻³`. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) ℝ≥0)

/-- A nonnegative acoustic intensity, with SI unit `W / m²` and dimension
`M T⁻³`. -/
abbrev AcousticIntensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) ℝ≥0)

/-- Unit choices whose length unit is the millimeter.  Areas evaluated in
these choices therefore have square-millimeter readouts. -/
def squareMillimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.millimeters }

/-- Meter readout of a physical displacement amplitude. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Hertz readout of a physical frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Square-meter readout of a physical area. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Square-millimeter readout of a physical area. -/
def areaInSquareMillimeters (area : DimArea) : ℝ :=
  ((area squareMillimeterUnitChoices).val : ℝ)

/-- Meter-per-second readout of a physical propagation speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Pascal readout of a bulk modulus.  Bulk modulus has the physical dimension
of pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Kilogram-per-cubic-meter readout of a mass density. -/
def densityInKilogramsPerCubicMeter (density : MassDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Watt-per-square-meter readout of an acoustic intensity. -/
def intensityInWattsPerSquareMeter (intensity : AcousticIntensityQuantity) : ℝ :=
  ((intensity UnitChoices.SI).val : ℝ)

/-- Anatomical labels visible in the supplied ear diagram.  The parenthetical
names deliberately reproduce the labels in that figure. -/
inductive EarPart where
  | auditoryCanal
  | eardrum
  | malleusAnvil
  | incusHammer
  | stapesStirrup
  | cochlea
  deriving DecidableEq, Repr

/-- The three anatomical regions distinguished by the diagram and prose. -/
inductive EarRegion where
  | outerEar
  | middleEar
  | innerEar
  deriving DecidableEq, Repr

/-- A labeled part is either within one anatomical region or forms the
boundary between two regions. -/
inductive EarDiagramLocation where
  | inRegion (region : EarRegion)
  | separates (first second : EarRegion)
  deriving DecidableEq, Repr

/-- Location of each labeled part in the problem's simplified figure.  The
eardrum is recorded as separating the outer and middle ear, as stated in the
caption, rather than being assigned arbitrarily to one side. -/
def EarPart.diagramLocation : EarPart → EarDiagramLocation
  | .auditoryCanal => .inRegion .outerEar
  | .eardrum => .separates .outerEar .middleEar
  | .malleusAnvil => .inRegion .middleEar
  | .incusHammer => .inRegion .middleEar
  | .stapesStirrup => .inRegion .middleEar
  | .cochlea => .inRegion .innerEar

/-- Successive oscillation-transmission links described by the figure and
scenario.  This records anatomy rather than a quantitative transfer law. -/
inductive DirectlyTransmitsOscillation : EarPart → EarPart → Prop where
  | canalToEardrum : DirectlyTransmitsOscillation .auditoryCanal .eardrum
  | eardrumToMalleus : DirectlyTransmitsOscillation .eardrum .malleusAnvil
  | malleusToIncus : DirectlyTransmitsOscillation .malleusAnvil .incusHammer
  | incusToStapes : DirectlyTransmitsOscillation .incusHammer .stapesStirrup
  | stapesToCochlea : DirectlyTransmitsOscillation .stapesStirrup .cochlea

/-- The two propagation media relevant to the numerical acoustics problem. -/
inductive EarMediumLabel where
  | outerEarAir
  | innerEarFluid
  deriving DecidableEq, Repr

/-- Physical material data for a homogeneous acoustic medium. -/
structure AcousticMedium where
  label : EarMediumLabel
  soundSpeed : DimSpeed
  bulkModulus : DimPressure
  massDensity : MassDensityQuantity

/-- Scalar observables of a monochromatic acoustic wave, retained as
dimensionful quantities independent of a choice of units. -/
structure AcousticWave where
  frequency : FrequencyQuantity
  displacementAmplitude : LengthQuantity
  intensity : AcousticIntensityQuantity

/-- All physical quantities in the idealized ear-transmission experiment. -/
structure EarTransmissionSetup where
  air : AcousticMedium
  innerEarFluid : AcousticMedium
  incidentAirWave : AcousticWave
  transmittedFluidWave : AcousticWave
  movingEardrumArea : DimArea
  stapesContactArea : DimArea

/-- Numerical data explicitly printed in the problem. -/
structure MatchesProblemReadouts (setup : EarTransmissionSetup) : Prop where
  air_label : setup.air.label = .outerEarAir
  innerEarFluid_label : setup.innerEarFluid.label = .innerEarFluid
  movingEardrumArea_mm2 :
    areaInSquareMillimeters setup.movingEardrumArea = 43
  stapesContactArea_mm2 :
    areaInSquareMillimeters setup.stapesContactArea = 16 / 5
  airSoundSpeed_mps :
    speedInMetersPerSecond setup.air.soundSpeed = 344
  airBulkModulus_pa :
    pressureInPascals setup.air.bulkModulus = 142000
  innerEarSoundSpeed_mps :
    speedInMetersPerSecond setup.innerEarFluid.soundSpeed = 1500

/-- Positivity and nondegeneracy conditions for the acoustic model. -/
structure HasPhysicalAcousticData (setup : EarTransmissionSetup) : Prop where
  movingEardrumArea_pos : 0 < areaInSquareMeters setup.movingEardrumArea
  stapesContactArea_pos : 0 < areaInSquareMeters setup.stapesContactArea
  airSpeed_pos : 0 < speedInMetersPerSecond setup.air.soundSpeed
  innerEarSpeed_pos : 0 < speedInMetersPerSecond setup.innerEarFluid.soundSpeed
  airBulkModulus_pos : 0 < pressureInPascals setup.air.bulkModulus
  innerEarBulkModulus_pos :
    0 < pressureInPascals setup.innerEarFluid.bulkModulus
  airDensity_pos :
    0 < densityInKilogramsPerCubicMeter setup.air.massDensity
  innerEarDensity_pos :
    0 < densityInKilogramsPerCubicMeter setup.innerEarFluid.massDensity
  incidentFrequency_pos : 0 < frequencyInHertz setup.incidentAirWave.frequency

/-- Angular-frequency readout corresponding to a wave's ordinary frequency. -/
def angularFrequencyInRadiansPerSecond (wave : AcousticWave) : ℝ :=
  2 * Real.pi * frequencyInHertz wave.frequency

/-- Governing linear-acoustics and ideal lossless-transmission laws.

The first two fields are `B = ρ c²`.  The intensity fields state
`I = B ω² s² / (2c)` for a plane sound wave.  The final field is
conservation of acoustic power through the eardrum and stapes areas.  None of
these fields fixes the requested inner-ear displacement to a numeric answer. -/
structure ObeysIdealEarTransmissionLaws (setup : EarTransmissionSetup) : Prop where
  air_wave_speed_law :
    pressureInPascals setup.air.bulkModulus =
      densityInKilogramsPerCubicMeter setup.air.massDensity *
        speedInMetersPerSecond setup.air.soundSpeed ^ 2
  innerEar_wave_speed_law :
    pressureInPascals setup.innerEarFluid.bulkModulus =
      densityInKilogramsPerCubicMeter setup.innerEarFluid.massDensity *
        speedInMetersPerSecond setup.innerEarFluid.soundSpeed ^ 2
  frequency_preserved :
    frequencyInHertz setup.transmittedFluidWave.frequency =
      frequencyInHertz setup.incidentAirWave.frequency
  air_intensity_law :
    intensityInWattsPerSquareMeter setup.incidentAirWave.intensity =
      pressureInPascals setup.air.bulkModulus *
          angularFrequencyInRadiansPerSecond setup.incidentAirWave ^ 2 *
          lengthInMeters setup.incidentAirWave.displacementAmplitude ^ 2 /
        (2 * speedInMetersPerSecond setup.air.soundSpeed)
  innerEar_intensity_law :
    intensityInWattsPerSquareMeter setup.transmittedFluidWave.intensity =
      pressureInPascals setup.innerEarFluid.bulkModulus *
          angularFrequencyInRadiansPerSecond setup.transmittedFluidWave ^ 2 *
          lengthInMeters setup.transmittedFluidWave.displacementAmplitude ^ 2 /
        (2 * speedInMetersPerSecond setup.innerEarFluid.soundSpeed)
  lossless_power_transfer :
    areaInSquareMeters setup.movingEardrumArea *
        intensityInWattsPerSquareMeter setup.incidentAirWave.intensity =
      areaInSquareMeters setup.stapesContactArea *
        intensityInWattsPerSquareMeter setup.transmittedFluidWave.intensity

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displacement-amplitude readouts in meters printed in the choices. -/
def answerDisplacementInMeters : AnswerChoice → ℝ
  | .A => 44 / 10 ^ 12
  | .B => 44 / 10 ^ 11
  | .C => 44 / 10 ^ 13
  | .D => 4 / 10 ^ 11

/-- Answer A is the answer recorded by the dataset.  It is retained as source
metadata and is not asserted as a consequence of the printed physical data. -/
def recordedAnswerChoice : AnswerChoice := .A

/-- The strongest squared-amplitude relation supported by the printed data and
the standard idealized acoustic-transfer laws.

Conservation of power and the plane-wave intensity law give
`s_f² = (A_e / A_s) (B_a / B_f) (c_f / c_a) s_a²`; frequency cancels because
it is preserved across the transmission.  Substitution of the printed
readouts gives the relation below.  The incident displacement `s_a` and the
inner-fluid bulk modulus `B_f` remain explicit because neither is supplied in
the text, source report, or ear diagram.  Consequently, the recorded numeric
answer A cannot honestly be concluded from the available data alone.

This is the formalization target `thm:physics:phyx_mini_0189:target`. -/
theorem problem_phyx_mini_0189
    (setup : EarTransmissionSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalAcousticData setup)
    (hLaws : ObeysIdealEarTransmissionLaws setup) :
    lengthInMeters setup.transmittedFluidWave.displacementAmplitude ^ 2 =
      (43 / (16 / 5 : ℝ)) *
        (142000 /
          pressureInPascals setup.innerEarFluid.bulkModulus) *
        (1500 / 344) *
        lengthInMeters setup.incidentAirWave.displacementAmplitude ^ 2 := by
  have hAreaScale (area : DimArea) :
      areaInSquareMillimeters area =
        (UnitChoices.SI.dimScale squareMillimeterUnitChoices (L𝓭 * L𝓭) : ℝ) *
          areaInSquareMeters area := by
    have h := congrArg
      (fun x : WithDim (L𝓭 * L𝓭) ℝ≥0 => (x.val : ℝ))
      (area.2 UnitChoices.SI squareMillimeterUnitChoices)
    simpa [areaInSquareMillimeters, areaInSquareMeters] using h
  have hEardrumScaled :
      (UnitChoices.SI.dimScale squareMillimeterUnitChoices (L𝓭 * L𝓭) : ℝ) *
          areaInSquareMeters setup.movingEardrumArea = 43 := by
    rw [← hAreaScale]
    exact hReadouts.movingEardrumArea_mm2
  have hStapesScaled :
      (UnitChoices.SI.dimScale squareMillimeterUnitChoices (L𝓭 * L𝓭) : ℝ) *
          areaInSquareMeters setup.stapesContactArea = 16 / 5 := by
    rw [← hAreaScale]
    exact hReadouts.stapesContactArea_mm2
  have hAreaCross :
      (16 / 5 : ℝ) * areaInSquareMeters setup.movingEardrumArea =
        43 * areaInSquareMeters setup.stapesContactArea := by
    calc
      (16 / 5 : ℝ) * areaInSquareMeters setup.movingEardrumArea =
          ((UnitChoices.SI.dimScale
                squareMillimeterUnitChoices (L𝓭 * L𝓭) : ℝ) *
            areaInSquareMeters setup.stapesContactArea) *
              areaInSquareMeters setup.movingEardrumArea := by
                rw [hStapesScaled]
      _ = ((UnitChoices.SI.dimScale
                squareMillimeterUnitChoices (L𝓭 * L𝓭) : ℝ) *
            areaInSquareMeters setup.movingEardrumArea) *
              areaInSquareMeters setup.stapesContactArea := by
                ring
      _ = 43 * areaInSquareMeters setup.stapesContactArea := by
        rw [hEardrumScaled]
  have hAreaRatio :
      areaInSquareMeters setup.movingEardrumArea =
        (43 / (16 / 5 : ℝ)) *
          areaInSquareMeters setup.stapesContactArea := by
    norm_num at hAreaCross ⊢
    linarith
  have hOmega :
      angularFrequencyInRadiansPerSecond setup.transmittedFluidWave =
        angularFrequencyInRadiansPerSecond setup.incidentAirWave := by
    unfold angularFrequencyInRadiansPerSecond
    rw [hLaws.frequency_preserved]
  have hOmega_pos :
      0 < angularFrequencyInRadiansPerSecond setup.incidentAirWave := by
    unfold angularFrequencyInRadiansPerSecond
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
      hPhysical.incidentFrequency_pos
  have hPower := hLaws.lossless_power_transfer
  rw [hLaws.air_intensity_law, hLaws.innerEar_intensity_law,
    hReadouts.airBulkModulus_pa, hReadouts.airSoundSpeed_mps,
    hReadouts.innerEarSoundSpeed_mps, hOmega] at hPower
  have hPowerWithoutArea :
      (43 / (16 / 5 : ℝ)) *
          (142000 *
            angularFrequencyInRadiansPerSecond setup.incidentAirWave ^ 2 *
            lengthInMeters setup.incidentAirWave.displacementAmplitude ^ 2 /
            (2 * 344)) =
        pressureInPascals setup.innerEarFluid.bulkModulus *
            angularFrequencyInRadiansPerSecond setup.incidentAirWave ^ 2 *
            lengthInMeters
              setup.transmittedFluidWave.displacementAmplitude ^ 2 /
            (2 * 1500) := by
    apply mul_left_cancel₀ (ne_of_gt hPhysical.stapesContactArea_pos)
    calc
      areaInSquareMeters setup.stapesContactArea *
          ((43 / (16 / 5 : ℝ)) *
            (142000 *
                angularFrequencyInRadiansPerSecond
                  setup.incidentAirWave ^ 2 *
                lengthInMeters
                  setup.incidentAirWave.displacementAmplitude ^ 2 /
              (2 * 344))) =
        areaInSquareMeters setup.movingEardrumArea *
          (142000 *
              angularFrequencyInRadiansPerSecond setup.incidentAirWave ^ 2 *
              lengthInMeters
                setup.incidentAirWave.displacementAmplitude ^ 2 /
            (2 * 344)) := by
              rw [hAreaRatio]
              ring
      _ = areaInSquareMeters setup.stapesContactArea *
        (pressureInPascals setup.innerEarFluid.bulkModulus *
          angularFrequencyInRadiansPerSecond setup.incidentAirWave ^ 2 *
          lengthInMeters
            setup.transmittedFluidWave.displacementAmplitude ^ 2 /
          (2 * 1500)) := hPower
  have hPowerWithoutOmega :
      (43 / (16 / 5 : ℝ)) *
          (142000 *
            lengthInMeters setup.incidentAirWave.displacementAmplitude ^ 2 /
            (2 * 344)) =
        pressureInPascals setup.innerEarFluid.bulkModulus *
            lengthInMeters
              setup.transmittedFluidWave.displacementAmplitude ^ 2 /
            (2 * 1500) := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hOmega_pos))
    calc
      angularFrequencyInRadiansPerSecond setup.incidentAirWave ^ 2 *
          ((43 / (16 / 5 : ℝ)) *
            (142000 *
              lengthInMeters
                setup.incidentAirWave.displacementAmplitude ^ 2 /
              (2 * 344))) =
        (43 / (16 / 5 : ℝ)) *
          (142000 *
              angularFrequencyInRadiansPerSecond setup.incidentAirWave ^ 2 *
              lengthInMeters
                setup.incidentAirWave.displacementAmplitude ^ 2 /
            (2 * 344)) := by
              ring
      _ = pressureInPascals setup.innerEarFluid.bulkModulus *
          angularFrequencyInRadiansPerSecond setup.incidentAirWave ^ 2 *
          lengthInMeters
            setup.transmittedFluidWave.displacementAmplitude ^ 2 /
          (2 * 1500) := hPowerWithoutArea
      _ = angularFrequencyInRadiansPerSecond setup.incidentAirWave ^ 2 *
        (pressureInPascals setup.innerEarFluid.bulkModulus *
          lengthInMeters
            setup.transmittedFluidWave.displacementAmplitude ^ 2 /
          (2 * 1500)) := by
            ring
  have hInnerBulkModulus_ne :=
    ne_of_gt hPhysical.innerEarBulkModulus_pos
  field_simp [hInnerBulkModulus_ne] at hPowerWithoutOmega ⊢
  nlinarith

end PhyXMiniProblems.ProblemPhyXMini0189
