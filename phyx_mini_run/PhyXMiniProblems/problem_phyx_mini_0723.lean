import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/-!
# Density of an unknown liquid from two floating depths

The same constant-cross-section block floats first in an unknown liquid and
then in water.  The primary figure gives a common top-face area `A` and the
submerged-depth labels `h_u` and `h_w`.  Archimedes' law and static equilibrium
allow the unknown density to be found by comparing the two placements.

Physical magnitudes are represented by Physlib's unit-independent
`Dimensionful` quantities.  Real numbers occur only as named unit readouts and
as the displayed answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0723

open Dimension

/-! ## Dimensionful quantities and unit readouts -/

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical area, with dimension `L²`. -/
abbrev AreaQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭) NNReal)

/-- A nonnegative physical volume, with dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative mass density, with dimension `M L⁻³`. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) NNReal)

/-- A nonnegative acceleration magnitude, with dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative force magnitude, with dimension `M L T⁻²`. -/
abbrev ForceQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Numerical readout of a physical length in meters. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Numerical readout of a physical length in centimeters. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ)

/-- Numerical readout of a physical area in square meters. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  nonnegativeSIReadout area

/-- Numerical readout of a physical volume in cubic meters. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  nonnegativeSIReadout volume

/-- Numerical readout of a mass density in kilograms per cubic meter. -/
def densityInKilogramsPerCubicMeter
    (density : MassDensityQuantity) : ℝ :=
  nonnegativeSIReadout density

/-- Numerical readout of an acceleration in meters per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeSIReadout acceleration

/-- Numerical readout of a force in newtons. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  nonnegativeSIReadout force

/-! ## Apparatus and primary-figure labels -/

/-- The two placements of the same block shown in the figure. -/
inductive Placement where
  | inUnknownLiquid
  | inWater
  deriving DecidableEq, Repr

/-- Liquid names printed on the two panels of the primary figure. -/
inductive FigureLiquidLabel where
  | unknownLiquid
  | water
  deriving DecidableEq, Repr

/-- Symbols attached to the submerged-length arrows in the figure. -/
inductive FigureDepthSymbol where
  | hUnknown
  | hWater
  deriving DecidableEq, Repr

/-- The common top-face-area symbol printed over both block drawings. -/
inductive FigureAreaSymbol where
  | areaA
  deriving DecidableEq, Repr

/-- Quantitative and categorical information read from the supplied image. -/
structure SuppliedFigureReadout where
  liquidLabel : Placement → FigureLiquidLabel
  submergedDepthSymbol : Placement → FigureDepthSymbol
  submergedDepth : Placement → LengthQuantity
  submergedLengthAnnotationShown : Placement → Bool
  topFaceAreaSymbol : Placement → FigureAreaSymbol
  topFaceArea : Placement → AreaQuantity
  horizontalLiquidSurfaceShown : Placement → Bool

/--
The physical state used for both placements of the same block.

The single fields `crossSectionalArea`, `gravitationalAcceleration`, and
`blockWeight` encode that the same prismatic block and the same gravitational
environment are used in both liquids.  The requested unknown density remains
an independent component of `fluidDensity`; it is not defined from the answer.
-/
structure FloatingBlockSetup where
  crossSectionalArea : AreaQuantity
  submergedDepth : Placement → LengthQuantity
  displacedVolume : Placement → VolumeQuantity
  fluidDensity : Placement → MassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity
  blockWeight : ForceQuantity
  buoyantForce : Placement → ForceQuantity
  suppliedFigure : SuppliedFigureReadout

/-! ## Problem data and governing laws -/

/--
Data stated in the prose or read from the primary figure.  The decimal depth
readouts are written as exact rational centimeter values.
-/
structure MatchesProblemAndFigureData (setup : FloatingBlockSetup) : Prop where
  unknownLiquidLabel :
    setup.suppliedFigure.liquidLabel .inUnknownLiquid = .unknownLiquid
  waterLabel : setup.suppliedFigure.liquidLabel .inWater = .water
  unknownDepthLabel :
    setup.suppliedFigure.submergedDepthSymbol .inUnknownLiquid = .hUnknown
  waterDepthLabel :
    setup.suppliedFigure.submergedDepthSymbol .inWater = .hWater
  unknownSubmergedLengthAnnotationShown :
    setup.suppliedFigure.submergedLengthAnnotationShown .inUnknownLiquid = true
  waterSubmergedLengthAnnotationShown :
    setup.suppliedFigure.submergedLengthAnnotationShown .inWater = true
  unknownPanelUsesAreaA :
    setup.suppliedFigure.topFaceAreaSymbol .inUnknownLiquid = .areaA
  waterPanelUsesAreaA :
    setup.suppliedFigure.topFaceAreaSymbol .inWater = .areaA
  unknownSurfaceShown :
    setup.suppliedFigure.horizontalLiquidSurfaceShown .inUnknownLiquid = true
  waterSurfaceShown :
    setup.suppliedFigure.horizontalLiquidSurfaceShown .inWater = true
  unknownFigureDepthMatchesSetup :
    setup.suppliedFigure.submergedDepth .inUnknownLiquid =
      setup.submergedDepth .inUnknownLiquid
  waterFigureDepthMatchesSetup :
    setup.suppliedFigure.submergedDepth .inWater =
      setup.submergedDepth .inWater
  unknownFigureAreaMatchesSetup :
    setup.suppliedFigure.topFaceArea .inUnknownLiquid =
      setup.crossSectionalArea
  waterFigureAreaMatchesSetup :
    setup.suppliedFigure.topFaceArea .inWater = setup.crossSectionalArea
  unknownDepthInCentimeters :
    lengthInCentimeters (setup.submergedDepth .inUnknownLiquid) = 46 / 10
  waterDepthInCentimeters :
    lengthInCentimeters (setup.submergedDepth .inWater) = 58 / 10

/-- The conventional fresh-water density used by the recorded answer. -/
def UsesFreshWaterDensity (setup : FloatingBlockSetup) : Prop :=
  densityInKilogramsPerCubicMeter (setup.fluidDensity .inWater) = 1000

/-- Nondegeneracy assumptions needed to compare the two force balances. -/
structure HasPhysicalParameters (setup : FloatingBlockSetup) : Prop where
  areaPositive : 0 < areaInSquareMeters setup.crossSectionalArea
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration

/--
For the constant-cross-section block, displaced volume is top-face area times
submerged depth in either placement.
-/
def SatisfiesPrismaticDisplacementLaw
    (setup : FloatingBlockSetup) : Prop :=
  ∀ placement : Placement,
    volumeInCubicMeters (setup.displacedVolume placement) =
      areaInSquareMeters setup.crossSectionalArea *
        lengthInMeters (setup.submergedDepth placement)

/-- Archimedes' law: buoyancy is `fluid density × displaced volume × g`. -/
def SatisfiesArchimedesPrinciple
    (setup : FloatingBlockSetup) : Prop :=
  ∀ placement : Placement,
    forceInNewtons (setup.buoyantForce placement) =
      densityInKilogramsPerCubicMeter (setup.fluidDensity placement) *
        volumeInCubicMeters (setup.displacedVolume placement) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration

/-- Static flotation: in each liquid, buoyancy balances the same block weight. -/
def FloatsInStaticEquilibrium (setup : FloatingBlockSetup) : Prop :=
  ∀ placement : Placement,
    forceInNewtons (setup.buoyantForce placement) =
      forceInNewtons setup.blockWeight

/-! ## Derived relation and displayed answer -/

/-- Labels of the four density choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Density readout in kilograms per cubic meter printed for each choice. -/
def AnswerChoice.densityInKilogramsPerCubicMeter : AnswerChoice → ℝ
  | .A => 1360
  | .B => 1160
  | .C => 1260
  | .D => 1200

/-- The answer key supplied with the dataset, retained only as metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- A displayed density choice is at least as close as every alternative. -/
def IsClosestDisplayedDensity
    (setup : FloatingBlockSetup) (choice : AnswerChoice) : Prop :=
  ∀ alternative : AnswerChoice,
    |densityInKilogramsPerCubicMeter
          (setup.fluidDensity .inUnknownLiquid) -
        choice.densityInKilogramsPerCubicMeter| ≤
      |densityInKilogramsPerCubicMeter
          (setup.fluidDensity .inUnknownLiquid) -
        alternative.densityInKilogramsPerCubicMeter|

/--
Comparing the two equilibria cancels the common area, gravity, and block
weight, leaving the standard density-depth relation.
-/
lemma density_times_depth_eq_water_density_times_depth
    (setup : FloatingBlockSetup)
    (hPhysical : HasPhysicalParameters setup)
    (hDisplacement : SatisfiesPrismaticDisplacementLaw setup)
    (hArchimedes : SatisfiesArchimedesPrinciple setup)
    (hEquilibrium : FloatsInStaticEquilibrium setup) :
    densityInKilogramsPerCubicMeter
          (setup.fluidDensity .inUnknownLiquid) *
        lengthInMeters (setup.submergedDepth .inUnknownLiquid) =
      densityInKilogramsPerCubicMeter (setup.fluidDensity .inWater) *
        lengthInMeters (setup.submergedDepth .inWater) := by
  unfold SatisfiesPrismaticDisplacementLaw at hDisplacement
  unfold SatisfiesArchimedesPrinciple at hArchimedes
  unfold FloatsInStaticEquilibrium at hEquilibrium
  have hForces := (hEquilibrium .inUnknownLiquid).trans
    (hEquilibrium .inWater).symm
  rw [hArchimedes .inUnknownLiquid, hDisplacement .inUnknownLiquid,
    hArchimedes .inWater, hDisplacement .inWater] at hForces
  have hCommon_ne :
      areaInSquareMeters setup.crossSectionalArea *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration ≠ 0 :=
    mul_ne_zero (ne_of_gt hPhysical.areaPositive)
      (ne_of_gt hPhysical.gravityPositive)
  apply mul_left_cancel₀ hCommon_ne
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hForces

/--
The exact ideal-model density is `1000 * 5.8 / 4.6 = 29000 / 23 kg/m³`.
-/
lemma unknown_liquid_density_exact
    (setup : FloatingBlockSetup)
    (hData : MatchesProblemAndFigureData setup)
    (hWater : UsesFreshWaterDensity setup)
    (hPhysical : HasPhysicalParameters setup)
    (hDisplacement : SatisfiesPrismaticDisplacementLaw setup)
    (hArchimedes : SatisfiesArchimedesPrinciple setup)
    (hEquilibrium : FloatsInStaticEquilibrium setup) :
    densityInKilogramsPerCubicMeter
        (setup.fluidDensity .inUnknownLiquid) = 29000 / 23 := by
  have hCentimeters (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h := length.property UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.centimeters}
    unfold lengthInCentimeters lengthInMeters nonnegativeSIReadout
    rw [h]
    simp only [UnitChoices.SI_time, UnitChoices.SI_mass,
      UnitChoices.SI_charge, UnitChoices.SI_temperature, WithDim.dim_apply,
      WithDim.smul_val, smul_eq_mul, NNReal.coe_mul, mul_eq_mul_right_iff,
      NNReal.coe_eq_zero]
    left
    norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
    rfl
  have hUnknownMeters :
      lengthInMeters (setup.submergedDepth .inUnknownLiquid) = 23 / 500 := by
    have hConversion :=
      hCentimeters (setup.submergedDepth .inUnknownLiquid)
    rw [hData.unknownDepthInCentimeters] at hConversion
    norm_num at hConversion ⊢
    linarith
  have hWaterMeters :
      lengthInMeters (setup.submergedDepth .inWater) = 29 / 500 := by
    have hConversion := hCentimeters (setup.submergedDepth .inWater)
    rw [hData.waterDepthInCentimeters] at hConversion
    norm_num at hConversion ⊢
    linarith
  have hBalance :=
    density_times_depth_eq_water_density_times_depth setup hPhysical
      hDisplacement hArchimedes hEquilibrium
  unfold UsesFreshWaterDensity at hWater
  rw [hUnknownMeters, hWaterMeters, hWater] at hBalance
  norm_num at hBalance ⊢
  linarith

/--
The unknown liquid has ideal-model density `29000 / 23 kg/m³`, approximately
`1260.87 kg/m³`.  Thus the printed value `1260 kg/m³` is within `1 kg/m³` and
is the closest supplied answer, choice C.

This declaration formalizes `thm:physics:phyx_mini_0723:target`.
-/
theorem problem_phyx_mini_0723
    (setup : FloatingBlockSetup)
    (hData : MatchesProblemAndFigureData setup)
    (hWater : UsesFreshWaterDensity setup)
    (hPhysical : HasPhysicalParameters setup)
    (hDisplacement : SatisfiesPrismaticDisplacementLaw setup)
    (hArchimedes : SatisfiesArchimedesPrinciple setup)
    (hEquilibrium : FloatsInStaticEquilibrium setup) :
    densityInKilogramsPerCubicMeter
          (setup.fluidDensity .inUnknownLiquid) = 29000 / 23 ∧
      |densityInKilogramsPerCubicMeter
            (setup.fluidDensity .inUnknownLiquid) -
          AnswerChoice.C.densityInKilogramsPerCubicMeter| < 1 ∧
      IsClosestDisplayedDensity setup .C := by
  have hDensity :=
    unknown_liquid_density_exact setup hData hWater hPhysical
      hDisplacement hArchimedes hEquilibrium
  refine ⟨hDensity, ?_, ?_⟩
  · rw [hDensity]
    norm_num [AnswerChoice.densityInKilogramsPerCubicMeter, abs_of_nonneg,
      abs_of_nonpos]
  · unfold IsClosestDisplayedDensity
    intro alternative
    rw [hDensity]
    cases alternative <;>
      norm_num [AnswerChoice.densityInKilogramsPerCubicMeter, abs_of_nonneg,
        abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0723
