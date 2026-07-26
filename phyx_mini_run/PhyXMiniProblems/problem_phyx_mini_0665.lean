import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0665

open Dimension

/-!
# Air pressure beneath a piston supporting a spilling water column

A thin horizontal piston of cross-sectional area `A` is at elevation `h` in
an open vertical cylinder of total height `H`.  Water above the piston spills
over the rim, so its free surface stays at elevation `H`; air supplied below
the piston supports the resulting water column.

All basic physical quantities are unit-independent and dimension-tagged.
Real numbers below occur only as explicitly named coherent-unit readouts and
as the symbolic formulas printed in the answer choices.

Assumption/target split:

* `MatchesSuppliedPistonCylinderFigure` records only labels and geometry seen
  in image `665.png`;
* `MatchesSpillingWaterScenario` records the named substances and qualitative
  idealizations from the prose;
* `SatisfiesSpillingColumnGeometry` states that the water depth is `H - h`;
* `SatisfiesHydrostaticPressureLaw` relates the water pressure at the piston
  to the ambient free-surface pressure and the water-column depth;
* `SatisfiesThinPistonForceBalance` balances the two pressure forces over area
  `A`; and
* the requested formula for the air pressure occurs only in theorem
  conclusions.  There are no previous-part results.
-/

/-! ## Dimensionful quantities and coherent-unit readouts -/

/-- The physical dimension of mass density, `M L^-3`. -/
def massDensityDimension : Dimension :=
  M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The physical dimension of acceleration, `L T^-2`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length, independent of the readout unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, spatially uniform mass density. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim massDensityDimension NNReal)

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A physical pressure, using Physlib's dimension `M L^-1 T^-2`. -/
abbrev PressureQuantity : Type := DimPressure

/-- Read a physical length in the length unit selected by `units`. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  ((length units).val : ℝ)

/-- Read an area in the squared length unit selected by `units`. -/
def areaReadout (units : UnitChoices) (area : DimArea) : ℝ :=
  ((area units).val : ℝ)

/-- Read a mass density in the coherent units selected by `units`. -/
def densityReadout
    (units : UnitChoices) (density : MassDensityQuantity) : ℝ :=
  ((density units).val : ℝ)

/-- Read an acceleration magnitude in the coherent units selected by `units`. -/
def accelerationReadout
    (units : UnitChoices) (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration units).val : ℝ)

/-- Read a pressure in the coherent pressure unit induced by `units`. -/
def pressureReadout (units : UnitChoices) (pressure : PressureQuantity) : ℝ :=
  (pressure units).val

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout UnitChoices.SI length

/-- Square-metre readout of a physical area. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  areaReadout UnitChoices.SI area

/-- Kilogram-per-cubic-metre readout of a physical mass density. -/
def densityInKilogramsPerCubicMeter (density : MassDensityQuantity) : ℝ :=
  densityReadout UnitChoices.SI density

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout UnitChoices.SI acceleration

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  pressureReadout UnitChoices.SI pressure

/-! ## Primary-figure vocabulary -/

/-- Literal labels visible in the primary raster. -/
inductive FigureLabel where
  | H
  | h
  | g
  | air
  deriving DecidableEq, Fintype, Repr

/-- The two vertical dimension marks drawn to the left of the cylinder. -/
inductive HeightMark where
  | totalHeightH
  | pistonElevationh
  deriving DecidableEq, Fintype, Repr

/-- Distinguished vertical locations in the cross-sectional diagram. -/
inductive FigureLocation where
  | cylinderBottomDatum
  | pistonPlane
  | openTopRim
  deriving DecidableEq, Fintype, Repr

/-- Vertical directions used to interpret the arrow labelled `g`. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Working liquid named by the problem. -/
inductive CylinderLiquid where
  | water
  | other
  deriving DecidableEq, Repr

/-- Gas supplied through the valve below the piston. -/
inductive SuppliedGas where
  | air
  | other
  deriving DecidableEq, Repr

/-!
Structured transcription of the physical information visible in image
`665.png`.  The label `h` denotes a variable piston elevation rather than a
fixed numerical readout.
-/
structure PistonCylinderFigure where
  labelShown : FigureLabel → Bool
  heightMarkEndpoints : HeightMark → FigureLocation × FigureLocation
  markedTotalHeightH : LengthQuantity
  gravityArrowDirection : VerticalDirection
  cylinderShownVertical : Bool
  topIsOpen : Bool
  horizontalPistonShown : Bool
  waterShownAbovePiston : Bool
  airLineEntersBelowPiston : Bool
  valveShownOnAirLine : Bool
  spillingRimIsAtTop : Bool

/-! ## Independent physical setup -/

/-!
The cylinder and its independent physical observables.  In particular,
`airPressureUnderPiston`, `waterPressureOnPiston`, and
`waterColumnDepthAbovePiston` are fields rather than definitions of the
requested formula.
-/
structure SpillingWaterPistonSetup where
  figure : PistonCylinderFigure
  liquid : CylinderLiquid
  suppliedGas : SuppliedGas
  cylinderTotalHeight : LengthQuantity
  pistonCrossSectionalArea : DimArea
  waterMassDensity : MassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity
  ambientPressureAtOpenSurface : PressureQuantity
  waterColumnDepthAbovePiston : LengthQuantity → LengthQuantity
  waterPressureOnPiston : LengthQuantity → PressureQuantity
  airPressureUnderPiston : LengthQuantity → PressureQuantity
  pistonIsThin : Bool
  pistonWeightIsNegligible : Bool
  pistonMovesWithoutFriction : Bool
  waterSpillsOverRim : Bool

/-! ## Scenario, figure evidence, and admissible elevations -/

/-- Qualitative information supplied by the problem prose. -/
structure MatchesSpillingWaterScenario
    (setup : SpillingWaterPistonSetup) : Prop where
  liquidIsWater : setup.liquid = .water
  suppliedGasIsAir : setup.suppliedGas = .air
  thinPiston : setup.pistonIsThin = true
  negligiblePistonWeight : setup.pistonWeightIsNegligible = true
  frictionlessPiston : setup.pistonMovesWithoutFriction = true
  waterContinuallySpillsAtRim : setup.waterSpillsOverRim = true

/-!
Literal evidence from the supplied raster.  It contains no pressure formula
and no answer-choice selection.
-/
structure MatchesSuppliedPistonCylinderFigure
    (setup : SpillingWaterPistonSetup) : Prop where
  everyLabelShown : ∀ label, setup.figure.labelShown label = true
  totalHeightRunsFromBottomToRim :
    setup.figure.heightMarkEndpoints .totalHeightH =
      (.cylinderBottomDatum, .openTopRim)
  pistonElevationRunsFromBottomToPiston :
    setup.figure.heightMarkEndpoints .pistonElevationh =
      (.cylinderBottomDatum, .pistonPlane)
  markedHMatchesCylinderHeight :
    setup.figure.markedTotalHeightH = setup.cylinderTotalHeight
  gravityPointsDown : setup.figure.gravityArrowDirection = .downward
  verticalCylinder : setup.figure.cylinderShownVertical = true
  openTop : setup.figure.topIsOpen = true
  horizontalPiston : setup.figure.horizontalPistonShown = true
  waterAbovePiston : setup.figure.waterShownAbovePiston = true
  airConnectionBelowPiston :
    setup.figure.airLineEntersBelowPiston = true
  valveOnAirConnection : setup.figure.valveShownOnAirLine = true
  rimAtCylinderTop : setup.figure.spillingRimIsAtTop = true

/-- A piston elevation lies between the bottom datum and the top rim. -/
def IsAdmissiblePistonElevation
    (setup : SpillingWaterPistonSetup) (h : LengthQuantity) : Prop :=
  0 ≤ lengthInMeters h ∧
    lengthInMeters h ≤ lengthInMeters setup.cylinderTotalHeight

/-- Positivity conditions needed for a physically meaningful force balance. -/
structure HasPhysicalSpillingWaterParameters
    (setup : SpillingWaterPistonSetup) : Prop where
  totalHeightPositive : 0 < lengthInMeters setup.cylinderTotalHeight
  pistonAreaPositive : 0 < areaInSquareMeters setup.pistonCrossSectionalArea
  waterDensityPositive :
    0 < densityInKilogramsPerCubicMeter setup.waterMassDensity
  gravityMagnitudePositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  ambientPressurePositive :
    0 < pressureInPascals setup.ambientPressureAtOpenSurface

/-! ## Geometry and governing physical laws -/

/-!
Because water spills over the open rim, the free-surface elevation remains
`H`; hence the water depth above a piston at elevation `h` is `H - h`.
-/
structure SatisfiesSpillingColumnGeometry
    (setup : SpillingWaterPistonSetup) : Prop where
  depthIsTopRimMinusPistonElevation :
    ∀ (h : LengthQuantity), IsAdmissiblePistonElevation setup h →
      ∀ units : UnitChoices,
        lengthReadout units (setup.waterColumnDepthAbovePiston h) =
          lengthReadout units setup.cylinderTotalHeight -
            lengthReadout units h

/-!
Hydrostatic equilibrium between the ambient open free surface and the water
face of the piston.  This law uses the independent water-column depth; it does
not state the requested air-pressure formula.
-/
structure SatisfiesHydrostaticPressureLaw
    (setup : SpillingWaterPistonSetup) : Prop where
  waterPressureAtPiston :
    ∀ (h : LengthQuantity), IsAdmissiblePistonElevation setup h →
      ∀ units : UnitChoices,
        pressureReadout units (setup.waterPressureOnPiston h) =
          pressureReadout units setup.ambientPressureAtOpenSurface +
            densityReadout units setup.waterMassDensity *
              accelerationReadout units setup.gravitationalAcceleration *
              lengthReadout units
                (setup.waterColumnDepthAbovePiston h)

/-!
For the thin, weightless, frictionless piston in quasistatic balance, the air
force upward equals the water-pressure force downward.  The common area `A`
is retained explicitly rather than cancelled inside the assumption.
-/
structure SatisfiesThinPistonForceBalance
    (setup : SpillingWaterPistonSetup) : Prop where
  verticalPressureForcesBalance :
    ∀ (h : LengthQuantity), IsAdmissiblePistonElevation setup h →
      ∀ units : UnitChoices,
        pressureReadout units (setup.airPressureUnderPiston h) *
            areaReadout units setup.pistonCrossSectionalArea =
          pressureReadout units (setup.waterPressureOnPiston h) *
            areaReadout units setup.pistonCrossSectionalArea

/-! ## Printed answer choices -/

/-- Labels of the four formulas printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
The pressure formula printed beside each answer label, evaluated in one
coherent unit system.  This is presentation data only; the main theorem below
states the physical target explicitly and does not unfold this table.
-/
def displayedPressureFormula
    (setup : SpillingWaterPistonSetup) (h : LengthQuantity)
    (units : UnitChoices) : AnswerChoice → ℝ
  | .A =>
      pressureReadout units setup.ambientPressureAtOpenSurface +
        (lengthReadout units setup.cylinderTotalHeight +
            lengthReadout units h) *
          densityReadout units setup.waterMassDensity *
          accelerationReadout units setup.gravitationalAcceleration
  | .B =>
      pressureReadout units setup.ambientPressureAtOpenSurface -
        (lengthReadout units setup.cylinderTotalHeight -
            lengthReadout units h) *
          densityReadout units setup.waterMassDensity *
          accelerationReadout units setup.gravitationalAcceleration
  | .C =>
      pressureReadout units setup.ambientPressureAtOpenSurface +
        (1 / 2 : ℝ) *
          (lengthReadout units setup.cylinderTotalHeight -
            lengthReadout units h) *
          densityReadout units setup.waterMassDensity *
          accelerationReadout units setup.gravitationalAcceleration
  | .D =>
      pressureReadout units setup.ambientPressureAtOpenSurface +
        (lengthReadout units setup.cylinderTotalHeight -
            lengthReadout units h) *
          densityReadout units setup.waterMassDensity *
          accelerationReadout units setup.gravitationalAcceleration

/-- A printed choice agrees with the physical air pressure in every coherent unit system. -/
def IsCorrectAnswer
    (setup : SpillingWaterPistonSetup) (h : LengthQuantity)
    (choice : AnswerChoice) : Prop :=
  ∀ units : UnitChoices,
    pressureReadout units (setup.airPressureUnderPiston h) =
      displayedPressureFormula setup h units choice

/-! ## Target conclusions -/

/-!
The air pressure below a piston at elevation `h` is

`P_air(h) = P₀ + (H - h) rho g`.

This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0665:target`.  The conclusion is stated for every
coherent choice of base units and is answer choice D.  It is derived from the
column geometry, hydrostatics, and force balance; it is not a premise field.
-/
theorem problem_phyx_mini_0665
    (setup : SpillingWaterPistonSetup)
    (_scenario : MatchesSpillingWaterScenario setup)
    (_figure : MatchesSuppliedPistonCylinderFigure setup)
    (h_physical : HasPhysicalSpillingWaterParameters setup)
    (h_geometry : SatisfiesSpillingColumnGeometry setup)
    (h_hydrostatic : SatisfiesHydrostaticPressureLaw setup)
    (h_forceBalance : SatisfiesThinPistonForceBalance setup)
    (h : LengthQuantity)
    (h_admissible : IsAdmissiblePistonElevation setup h) :
    ∀ units : UnitChoices,
      pressureReadout units (setup.airPressureUnderPiston h) =
        pressureReadout units setup.ambientPressureAtOpenSurface +
          (lengthReadout units setup.cylinderTotalHeight -
              lengthReadout units h) *
            densityReadout units setup.waterMassDensity *
            accelerationReadout units setup.gravitationalAcceleration := by
  intro units
  have h_area_units :
      0 < areaReadout units setup.pistonCrossSectionalArea := by
    have h_scale :=
      setup.pistonCrossSectionalArea.property UnitChoices.SI units
    rw [areaReadout, h_scale]
    change
      0 <
        (UnitChoices.dimScale UnitChoices.SI units (L𝓭 * L𝓭) : ℝ) *
          ((setup.pistonCrossSectionalArea UnitChoices.SI).val : ℝ)
    have h_area_si := h_physical.pistonAreaPositive
    change
      0 < ((setup.pistonCrossSectionalArea UnitChoices.SI).val : ℝ)
      at h_area_si
    exact mul_pos
      (by
        exact_mod_cast
          UnitChoices.dimScale_pos UnitChoices.SI units (L𝓭 * L𝓭))
      h_area_si
  have h_force :=
    h_forceBalance.verticalPressureForcesBalance h h_admissible units
  calc
    pressureReadout units (setup.airPressureUnderPiston h) =
        pressureReadout units (setup.waterPressureOnPiston h) := by
      nlinarith
    _ =
        pressureReadout units setup.ambientPressureAtOpenSurface +
          densityReadout units setup.waterMassDensity *
            accelerationReadout units setup.gravitationalAcceleration *
            lengthReadout units (setup.waterColumnDepthAbovePiston h) :=
      h_hydrostatic.waterPressureAtPiston h h_admissible units
    _ =
        pressureReadout units setup.ambientPressureAtOpenSurface +
          (lengthReadout units setup.cylinderTotalHeight -
              lengthReadout units h) *
            densityReadout units setup.waterMassDensity *
            accelerationReadout units setup.gravitationalAcceleration := by
      rw [
        h_geometry.depthIsTopRimMinusPistonElevation
          h h_admissible units
      ]
      ring

/-- The explicit pressure formula selects answer choice D. -/
lemma answerChoiceD_isCorrect
    (setup : SpillingWaterPistonSetup)
    (h_scenario : MatchesSpillingWaterScenario setup)
    (h_figure : MatchesSuppliedPistonCylinderFigure setup)
    (h_physical : HasPhysicalSpillingWaterParameters setup)
    (h_geometry : SatisfiesSpillingColumnGeometry setup)
    (h_hydrostatic : SatisfiesHydrostaticPressureLaw setup)
    (h_forceBalance : SatisfiesThinPistonForceBalance setup)
    (h : LengthQuantity)
    (h_admissible : IsAdmissiblePistonElevation setup h) :
    IsCorrectAnswer setup h .D := by
  intro units
  simpa [displayedPressureFormula] using
    problem_phyx_mini_0665 setup h_scenario h_figure h_physical h_geometry
      h_hydrostatic h_forceBalance h h_admissible units

end PhyXMiniProblems.ProblemPhyXMini0665
