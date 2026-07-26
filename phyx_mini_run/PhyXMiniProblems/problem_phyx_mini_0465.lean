import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0465

open Dimension

/-!
# Force from a constrained, thermally expanding aluminum spacer

An aluminum cylinder initially just fits between two rigid steel walls.  Its
free thermal expansion is prevented when its temperature rises from
`17.2 °C` to `22.3 °C`, so the cylinder develops a compressive axial stress.

Length, area, absolute temperature, thermal-expansion coefficient, stress,
Young's modulus, and force retain their physical dimensions through Physlib's
unit-independent `Dimensionful` representation.  Real numbers are used only
for explicitly named-unit readouts and the dimensionless axial strains.  The
source does not supply numerical aluminum properties or specify which force
unit its word "tons" denotes, so the target keeps the material properties
symbolic and records the printed answers only as metadata.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- An absolute physical temperature with dimension `Θ`. -/
abbrev AbsoluteTemperatureQuantity : Type :=
  Dimensionful (WithDim Θ𝓭 NNReal)

/-- A nonnegative linear-expansion coefficient with dimension `Θ⁻¹`. -/
abbrev ThermalExpansionCoefficientQuantity : Type :=
  Dimensionful (WithDim Θ𝓭⁻¹ NNReal)

/-- A signed axial force with dimension `M L T⁻²`. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ)

/-- Read a physical area in square centimetres. -/
def areaInSquareCentimeters (area : DimArea) : ℝ :=
  ((area {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ)

/-- Read a physical area in coherent SI square metres. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read an absolute temperature in kelvin. -/
def temperatureInKelvin (temperature : AbsoluteTemperatureQuantity) : ℝ :=
  ((temperature UnitChoices.SI).val : ℝ)

/--
Read an absolute temperature in degrees Celsius.  The affine offset
`273.15 K` is represented exactly as `5463 / 20`.
-/
def temperatureInDegreesCelsius
    (temperature : AbsoluteTemperatureQuantity) : ℝ :=
  temperatureInKelvin temperature - 5463 / 20

/-- Read a linear thermal-expansion coefficient in inverse kelvin. -/
def thermalExpansionCoefficientPerKelvin
    (coefficient : ThermalExpansionCoefficientQuantity) : ℝ :=
  ((coefficient UnitChoices.SI).val : ℝ)

/-- Read a stress or elastic modulus in coherent SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a signed physical force in coherent SI newtons. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  (force UnitChoices.SI).val

/-! ## Apparatus roles and primary-figure vocabulary -/

/-- The cylinder and wall materials appearing in the scenario. -/
inductive Material where
  | aluminum
  | steel
  | other
  deriving DecidableEq, Repr

/-- The two walls on which the spacer exerts equal compressive loads. -/
inductive WallLabel where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Sign convention used by the displayed negative answer choices. -/
inductive AxialLoadSignConvention where
  | compressionNegative
  | tensionNegative
  deriving DecidableEq, Repr

/-- Literal and qualitative evidence visible in image `465.png`. -/
structure SpacerFigure where
  wallIsShown : WallLabel → Bool
  wallHatchingIsShown : WallLabel → Bool
  wallsAreDrawnParallel : Bool
  cylinderIsDrawnBetweenWalls : Bool
  dashedEllipticalCrossSectionIsShown : Bool
  areaLeaderPointsToCrossSection : Bool
  lengthDimensionSpansWalls : Bool
  areaLabel : String
  lengthLabel : String

/-!
Independent quantities describing the heated-spacer experiment.  The forces
on the walls and the intermediate strain and stress are fields to be related
by governing laws; none is defined using a displayed answer value.
-/
structure HeatedSpacerSetup where
  spacerMaterial : Material
  wallMaterial : WallLabel → Material
  wallsPerfectlyRigid : Bool
  wallSeparationIsConstant : Bool
  spacerInitiallyJustSlips : Bool
  signConvention : AxialLoadSignConvention
  referenceLength : LengthQuantity
  constrainedLengthAfterHeating : LengthQuantity
  wallSeparation : LengthQuantity
  crossSectionalArea : DimArea
  initialTemperature : AbsoluteTemperatureQuantity
  finalTemperature : AbsoluteTemperatureQuantity
  linearThermalExpansionCoefficient : ThermalExpansionCoefficientQuantity
  youngModulus : DimPressure
  thermalStrain : ℝ
  mechanicalStrain : ℝ
  totalAxialStrain : ℝ
  axialStress : DimPressure
  totalForceExertedOnWall : WallLabel → ForceQuantity
  figure : SpacerFigure

/-! ## Scenario, figure/data readouts, and governing laws -/

/-- Qualitative apparatus assumptions stated in the prose. -/
structure MatchesHeatedSpacerScenario (setup : HeatedSpacerSetup) : Prop where
  spacerIsAluminum : setup.spacerMaterial = .aluminum
  bothWallsAreSteel : ∀ wall, setup.wallMaterial wall = .steel
  wallsArePerfectlyRigid : setup.wallsPerfectlyRigid = true
  wallDistanceRemainsConstant : setup.wallSeparationIsConstant = true
  cylinderInitiallyJustSlips : setup.spacerInitiallyJustSlips = true
  compressionUsesNegativeSign : setup.signConvention = .compressionNegative

/-!
Exact transcription of the primary bitmap, including its `A = 20 cm²` and
`10 cm` labels.  These are input geometry readouts, not force conclusions.
-/
structure MatchesPrimarySpacerFigure (setup : HeatedSpacerSetup) : Prop where
  bothWallsShown : ∀ wall, setup.figure.wallIsShown wall = true
  bothWallsHatchedAsFixed :
    ∀ wall, setup.figure.wallHatchingIsShown wall = true
  wallsParallel : setup.figure.wallsAreDrawnParallel = true
  cylinderBetweenWalls : setup.figure.cylinderIsDrawnBetweenWalls = true
  dashedCrossSection :
    setup.figure.dashedEllipticalCrossSectionIsShown = true
  areaLeader : setup.figure.areaLeaderPointsToCrossSection = true
  lengthArrowSpansWalls : setup.figure.lengthDimensionSpansWalls = true
  literalAreaLabel : setup.figure.areaLabel = "A = 20 cm²"
  literalLengthLabel : setup.figure.lengthLabel = "10 cm"
  referenceLengthCentimeters :
    lengthInCentimeters setup.referenceLength = 10
  crossSectionalAreaSquareCentimeters :
    areaInSquareCentimeters setup.crossSectionalArea = 20

/-- The two temperatures explicitly supplied in the problem text. -/
structure MatchesTemperatureReadouts (setup : HeatedSpacerSetup) : Prop where
  initialTemperatureCelsius :
    temperatureInDegreesCelsius setup.initialTemperature = 86 / 5
  finalTemperatureCelsius :
    temperatureInDegreesCelsius setup.finalTemperature = 223 / 10

/-- Positivity and heating assumptions selecting the physical branch. -/
structure HasPhysicalSpacerParameters (setup : HeatedSpacerSetup) : Prop where
  referenceLengthPositive :
    0 < ((setup.referenceLength UnitChoices.SI).val : ℝ)
  crossSectionalAreaPositive :
    0 < areaInSquareMeters setup.crossSectionalArea
  youngModulusPositive : 0 < pressureInPascals setup.youngModulus
  expansionCoefficientPositive :
    0 < thermalExpansionCoefficientPerKelvin
      setup.linearThermalExpansionCoefficient
  finalTemperatureAboveInitial :
    temperatureInKelvin setup.initialTemperature <
      temperatureInKelvin setup.finalTemperature

/-!
The one-dimensional constrained-thermoelastic model, stated in every coherent
choice of units:

* initial slip fit and rigid walls fix the heated cylinder length;
* axial strain is relative length change;
* total strain is mechanical strain plus free thermal strain;
* free thermal strain is `α ΔT`;
* Hooke's law gives `σ = E ε_mechanical`;
* uniform axial stress gives `F = σ A` on each wall.

No field of this structure assigns a numerical force, a ton-force value, or
an answer label.
-/
structure SatisfiesConstrainedThermoelasticLaws
    (setup : HeatedSpacerSetup) : Prop where
  initialSlipFit : setup.wallSeparation = setup.referenceLength
  heatedLengthFixedByWalls :
    setup.constrainedLengthAfterHeating = setup.wallSeparation
  axialStrainFromLengths :
    ∀ units : UnitChoices,
      setup.totalAxialStrain =
        (((setup.constrainedLengthAfterHeating units).val : ℝ) -
            ((setup.referenceLength units).val : ℝ)) /
          ((setup.referenceLength units).val : ℝ)
  strainDecomposition :
    setup.totalAxialStrain = setup.mechanicalStrain + setup.thermalStrain
  freeThermalStrainLaw :
    ∀ units : UnitChoices,
      setup.thermalStrain =
        ((setup.linearThermalExpansionCoefficient units).val : ℝ) *
          (((setup.finalTemperature units).val : ℝ) -
            ((setup.initialTemperature units).val : ℝ))
  linearElasticHookeLaw :
    ∀ units : UnitChoices,
      (setup.axialStress units).val =
        (setup.youngModulus units).val * setup.mechanicalStrain
  uniformStressForceLaw :
    ∀ (units : UnitChoices) (wall : WallLabel),
      (setup.totalForceExertedOnWall wall units).val =
        (setup.axialStress units).val *
          ((setup.crossSectionalArea units).val : ℝ)

/-! ## Displayed choices and current target -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/--
The signed numerical magnitudes printed beside the choices.  The suffix
`tons` is intentionally left uninterpreted because the source does not say
whether it means short-, long-, or metric-ton force.
-/
def displayedForceInUnspecifiedTons : AnswerChoice → ℝ
  | .A => -8 / 5
  | .B => -19 / 10
  | .C => -23 / 10
  | .D => -18 / 5

/-- Literal answer strings, preserving the source's ambiguous unit spelling. -/
def displayedAnswerText : AnswerChoice → String
  | .A => "A: -1.6tons"
  | .B => "B: -1.9tons"
  | .C => "C: -2.3tons"
  | .D => "D: -3.6tons"

/-- Dataset answer-label metadata; it is not a premise or theorem conclusion. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
The rigid-wall boundary condition makes the mechanical strain the negative of
the `α ΔT` thermal strain.  The source-supplied data give
`A = 20 cm² = 1/500 m²` and `ΔT = 5.1 K`, hence the strongest numerical
specialization supported by the source is

`F = -(51/5000) E α` newtons

for SI readouts `E` in pascals and `α` in inverse kelvin.  Young's modulus and
the expansion coefficient remain symbolic because the source supplies neither
value.  No interpretation of the ambiguous answer unit `tons` is asserted.

This formalizes `thm:physics:phyx_mini_0465:target`.
-/
theorem problem_phyx_mini_0465
    (setup : HeatedSpacerSetup)
    (_scenario : MatchesHeatedSpacerScenario setup)
    (_figure : MatchesPrimarySpacerFigure setup)
    (_temperatures : MatchesTemperatureReadouts setup)
    (_physical : HasPhysicalSpacerParameters setup)
    (_laws : SatisfiesConstrainedThermoelasticLaws setup) :
    ∀ wall : WallLabel,
      forceInNewtons (setup.totalForceExertedOnWall wall) =
        -(51 / 5000) * pressureInPascals setup.youngModulus *
          thermalExpansionCoefficientPerKelvin
            setup.linearThermalExpansionCoefficient := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0465
