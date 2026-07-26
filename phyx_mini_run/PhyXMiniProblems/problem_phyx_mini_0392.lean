import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0392

open Dimension

/-!
# Horizontal hydrostatic force on a dam port

A lake is `6 m` deep beside a vertical rectangular port.  The port is `5 m`
wide and spans the full `6 m` water depth.  Water acts on its lake-side face
and atmospheric air acts on its other face.  The net horizontal force is the
integral of the water--air pressure difference over the port.

Lengths, pressure, density, acceleration, and force are represented by
unit-independent Physlib quantities.  Real numbers below occur only as
explicit SI readouts, as the downward depth coordinate measured in metres,
or as the numerical values printed in the multiple-choice answers.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- The physical dimension of mass density, `M L⁻³`. -/
def massDensityDimension : Dimension :=
  M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of force, `M L T⁻²`. -/
def forceDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length independent of the chosen readout unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical mass density. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim massDensityDimension NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative physical force magnitude. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A physical absolute pressure, using Physlib's pressure dimension. -/
abbrev PressureQuantity : Type := DimPressure

/-- Read a physical length in SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical mass density in SI kilograms per cubic metre. -/
def massDensityInKilogramsPerCubicMeter
    (density : MassDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Read a physical acceleration in SI metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a physical absolute pressure in SI pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical force magnitude in SI newtons. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Read a physical force magnitude in kilonewtons. -/
def forceInKilonewtons (force : ForceQuantity) : ℝ :=
  forceInNewtons force / 1000

/-! ## Scenario roles and primary-figure labels -/

/-- The two faces of the port distinguished by the scenario. -/
inductive PortSide where
  | lakeSide
  | drySide
  deriving DecidableEq, Fintype, Repr

/-- Fluids acting on the two faces of the port. -/
inductive Fluid where
  | water
  | air
  deriving DecidableEq, Repr

/-- Orientation of the rectangular port relative to the lake surface. -/
inductive PortOrientation where
  | vertical
  | horizontal
  | other
  deriving DecidableEq, Repr

/-- The two explicitly named views in the supplied raster. -/
inductive FigurePanel where
  | sideView
  | topView
  deriving DecidableEq, Fintype, Repr

/-- Literal text labels visible in the supplied raster. -/
inductive FigureTextLabel where
  | lake
  | sideView
  | topView
  | sixMeters
  | fiveMeters
  deriving DecidableEq, Fintype, Repr

/-- The two dimensionful arrows shown in the supplied raster. -/
inductive FigureLengthMark where
  | lakeDepth
  | portWidth
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative and dimensionful evidence transcribed from the primary image.  Its
`6 m` arrow measures the lake depth in the side view, while its `5 m` arrow
measures the port opening in the top view.  No force value is stored here.
-/
structure DamPortFigure where
  panelShown : FigurePanel → Bool
  textLabelShown : FigureTextLabel → Bool
  markedLength : FigureLengthMark → LengthQuantity
  sideViewLakeSurfaceHorizontal : Bool
  sideViewDamFaceVertical : Bool
  topViewPortSpansDamOpening : Bool
  topViewLakeTouchesPort : Bool

/-!
Independent quantities in the dam-port experiment.  The pressure field takes
a scalar argument because that argument is explicitly a metre readout of the
depth measured downward from the lake surface; each field value is still a
dimensionful physical pressure.  The requested force is an independent
observable constrained only by the governing law below.
-/
structure DamPortSetup where
  figure : DamPortFigure
  lakeDepth : LengthQuantity
  portWidth : LengthQuantity
  portHeight : LengthQuantity
  fluidAt : PortSide → Fluid
  portOrientation : PortOrientation
  lakeRetainedByDam : Bool
  portReplacesDamSection : Bool
  ambientAirPressure : PressureQuantity
  waterMassDensity : MassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity
  absolutePressureAtDepthMeters : PortSide → ℝ → PressureQuantity
  netHorizontalForceMagnitude : ForceQuantity

/-! ## Figure/data readouts and physical assumptions -/

/-- Numerical and qualitative data stated in the prose problem. -/
structure MatchesStatedProblemData (setup : DamPortSetup) : Prop where
  retainedLake : setup.lakeRetainedByDam = true
  replacementPort : setup.portReplacesDamSection = true
  waterOnLakeSide : setup.fluidAt .lakeSide = .water
  airOnDrySide : setup.fluidAt .drySide = .air
  portIsVertical : setup.portOrientation = .vertical
  lakeDepthMeters : lengthInMeters setup.lakeDepth = 6
  portWidthMeters : lengthInMeters setup.portWidth = 5
  portHeightMeters : lengthInMeters setup.portHeight = 6

/-!
Primary-image evidence: both named views and all printed labels are visible;
the side-view arrow is the lake depth and the top-view arrow is the port
width.  These observations contain no pressure or force answer.
-/
structure MatchesPrimaryDamPortFigure (setup : DamPortSetup) : Prop where
  everyPanelShown : ∀ panel, setup.figure.panelShown panel = true
  everyTextLabelShown : ∀ label, setup.figure.textLabelShown label = true
  depthMarkMatchesLakeDepth :
    setup.figure.markedLength .lakeDepth = setup.lakeDepth
  widthMarkMatchesPortWidth :
    setup.figure.markedLength .portWidth = setup.portWidth
  horizontalLakeSurface : setup.figure.sideViewLakeSurfaceHorizontal = true
  verticalDamFace : setup.figure.sideViewDamFaceVertical = true
  portSpansOpening : setup.figure.topViewPortSpansDamOpening = true
  lakeTouchesPort : setup.figure.topViewLakeTouchesPort = true

/-!
The standard textbook calibration implicit in the recorded answer: water is
read as `1000 kg/m³` and gravitational acceleration as `9.8 m/s²`.  Ambient
pressure is positive but need not be assigned a numerical value because it
cancels between the two faces.
-/
structure HasStandardWaterGravityCalibration (setup : DamPortSetup) : Prop where
  waterDensitySI :
    massDensityInKilogramsPerCubicMeter setup.waterMassDensity = 1000
  gravitationalAccelerationSI :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5
  ambientPressurePositive : 0 < pressureInPascals setup.ambientAirPressure

/-!
Hydrostatic equilibrium measured downward from the lake surface.  On the wet
face, absolute pressure is ambient pressure plus `ρ g y`; on the dry face,
the air pressure is spatially uniform and equal to ambient pressure.  This is
a general governing law and contains no resultant-force value or answer
choice.
-/
structure SatisfiesHydrostaticPressureLaw (setup : DamPortSetup) : Prop where
  waterPressureAtDepth :
    ∀ depthMeters ∈
        Set.Icc (0 : ℝ) (lengthInMeters setup.lakeDepth),
      pressureInPascals
          (setup.absolutePressureAtDepthMeters .lakeSide depthMeters) =
        pressureInPascals setup.ambientAirPressure +
          massDensityInKilogramsPerCubicMeter setup.waterMassDensity *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            depthMeters
  airPressureAtDepth :
    ∀ depthMeters ∈
        Set.Icc (0 : ℝ) (lengthInMeters setup.portHeight),
      pressureInPascals
          (setup.absolutePressureAtDepthMeters .drySide depthMeters) =
        pressureInPascals setup.ambientAirPressure

/-- Net water-minus-air pressure readout at a downward depth in metres. -/
def netPressureInPascalsAtDepthMeters
    (setup : DamPortSetup) (depthMeters : ℝ) : ℝ :=
  pressureInPascals
      (setup.absolutePressureAtDepthMeters .lakeSide depthMeters) -
    pressureInPascals
      (setup.absolutePressureAtDepthMeters .drySide depthMeters)

/-!
The resultant of a pressure traction on the vertical rectangular port.  A
horizontal strip of height `dy` has area `portWidth * dy`, so integrating the
net pressure over the full height gives the horizontal force.  This generic
law contains no supplied numerical values or answer choices.
-/
structure SatisfiesPressureResultantLaw (setup : DamPortSetup) : Prop where
  netPressureIntervalIntegrable :
    IntervalIntegrable (netPressureInPascalsAtDepthMeters setup)
      MeasureTheory.volume 0 (lengthInMeters setup.portHeight)
  forceIsPressureTractionIntegral :
    forceInNewtons setup.netHorizontalForceMagnitude =
      lengthInMeters setup.portWidth *
        ∫ depthMeters in (0 : ℝ)..lengthInMeters setup.portHeight,
          netPressureInPascalsAtDepthMeters setup depthMeters

/-! ## Multiple-choice display and target -/

/-- Labels printed beside the four proposed force magnitudes. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Force in kilonewtons printed beside each answer label. -/
def displayedForceInKilonewtons : AnswerChoice → ℝ
  | .A => 490
  | .B => 880
  | .C => 154
  | .D => 51 / 5

/-- A choice is strictly nearer to the ideal force than every alternative. -/
def IsUniqueClosestAnswer
    (forceKilonewtons : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice,
    otherChoice ≠ choice →
      |forceKilonewtons - displayedForceInKilonewtons choice| <
        |forceKilonewtons - displayedForceInKilonewtons otherChoice|

/-!
The hydrostatic pressure triangle gives
`F = ρ g w h² / 2 = 882 kN` under the conventional calibration.  Thus the
recorded `880 kN` value, answer B, is the unique closest displayed choice.

This declaration formalizes blueprint label
`thm:physics:phyx_mini_0392:target`.
-/
theorem problem_phyx_mini_0392
    (setup : DamPortSetup)
    (hData : MatchesStatedProblemData setup)
    (hFigure : MatchesPrimaryDamPortFigure setup)
    (hCalibration : HasStandardWaterGravityCalibration setup)
    (hHydrostatic : SatisfiesHydrostaticPressureLaw setup)
    (hResultant : SatisfiesPressureResultantLaw setup) :
    forceInKilonewtons setup.netHorizontalForceMagnitude = 882 ∧
      IsUniqueClosestAnswer
        (forceInKilonewtons setup.netHorizontalForceMagnitude) .B := by
  have hNetPressure :
      ∀ depthMeters ∈ Set.Icc (0 : ℝ) 6,
        netPressureInPascalsAtDepthMeters setup depthMeters =
          9800 * depthMeters := by
    intro depthMeters hDepth
    unfold netPressureInPascalsAtDepthMeters
    rw [
      hHydrostatic.waterPressureAtDepth depthMeters (by
        simpa only [hData.lakeDepthMeters] using hDepth),
      hHydrostatic.airPressureAtDepth depthMeters (by
        simpa only [hData.portHeightMeters] using hDepth),
      hCalibration.waterDensitySI,
      hCalibration.gravitationalAccelerationSI]
    ring
  have hIntegralId : (∫ depthMeters in (0 : ℝ)..6, depthMeters) = 18 := by
    have hReflection :
        (∫ depthMeters in (0 : ℝ)..6, (6 : ℝ) - depthMeters) =
          ∫ depthMeters in (0 : ℝ)..6, depthMeters := by
      simpa using
        (intervalIntegral.integral_comp_sub_left
          (fun depthMeters : ℝ => depthMeters) (6 : ℝ)
          (a := (0 : ℝ)) (b := 6))
    have hIdIntegrable :
        IntervalIntegrable (fun depthMeters : ℝ => depthMeters)
          MeasureTheory.volume 0 6 :=
      continuous_id.intervalIntegrable 0 6
    rw [intervalIntegral.integral_sub intervalIntegrable_const hIdIntegrable]
      at hReflection
    norm_num at hReflection ⊢
    linarith
  have hPressureIntegral :
      (∫ depthMeters in (0 : ℝ)..6,
        netPressureInPascalsAtDepthMeters setup depthMeters) = 176400 := by
    calc
      (∫ depthMeters in (0 : ℝ)..6,
        netPressureInPascalsAtDepthMeters setup depthMeters) =
          ∫ depthMeters in (0 : ℝ)..6, 9800 * depthMeters := by
        apply intervalIntegral.integral_congr
        intro depthMeters hDepth
        apply hNetPressure depthMeters
        simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 6)] using hDepth
      _ = 9800 * (∫ depthMeters in (0 : ℝ)..6, depthMeters) := by
        rw [intervalIntegral.integral_const_mul]
      _ = 176400 := by rw [hIntegralId]; norm_num
  have hForceNewtons :
      forceInNewtons setup.netHorizontalForceMagnitude = 882000 := by
    calc
      forceInNewtons setup.netHorizontalForceMagnitude =
          lengthInMeters setup.portWidth *
            ∫ depthMeters in (0 : ℝ)..lengthInMeters setup.portHeight,
              netPressureInPascalsAtDepthMeters setup depthMeters :=
        hResultant.forceIsPressureTractionIntegral
      _ = 882000 := by
        rw [hData.portWidthMeters, hData.portHeightMeters, hPressureIntegral]
        norm_num
  have hForceKilonewtons :
      forceInKilonewtons setup.netHorizontalForceMagnitude = 882 := by
    unfold forceInKilonewtons
    rw [hForceNewtons]
    norm_num
  constructor
  · exact hForceKilonewtons
  · rw [hForceKilonewtons]
    intro otherChoice hOtherChoice
    fin_cases otherChoice
    · norm_num [displayedForceInKilonewtons]
    · exact (hOtherChoice rfl).elim
    · norm_num [displayedForceInKilonewtons]
    · norm_num [displayedForceInKilonewtons]

end PhyXMiniProblems.ProblemPhyXMini0392
