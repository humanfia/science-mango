import Mathlib
import Physlib.Units.WithDim.Basic

/-!
# Concrete ballast for an open steel tank

A vertical steel tank is open at the top and floats without flooding.  The
supplied figure labels the upper interior as air, the lower interior as
concrete, and the exterior as ocean.  Its `10 m` arrow runs from the tank
bottom to the ocean surface, so it represents the draft rather than the
concrete fill height.

Physical quantities use Physlib's unit-independent `Dimensionful` type with
dimensions carried by `WithDim`.  Real numbers occur only as coherent SI
readouts and as the numerical values printed in the problem.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0664

open Dimension

/-! ## Dimensionful quantities and SI readouts -/

/-- A physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical cross-sectional area. -/
abbrev AreaQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭) ℝ)

/-- A physical volume. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- A physical mass density, with dimension `M L⁻³`. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) ℝ)

/-- A physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A physical force magnitude. -/
abbrev ForceQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a dimensionful quantity in the coherent SI unit system. -/
def siReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  siReadout length

/-- Square-metre readout of a physical area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  siReadout area

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  siReadout volume

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  siReadout mass

/-- Kilogram-per-cubic-metre readout of a mass density. -/
def densityInKilogramsPerCubicMeter
    (density : MassDensityQuantity) : ℝ :=
  siReadout density

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  siReadout acceleration

/-- Newton readout of a force magnitude. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  siReadout force

/-! ## Apparatus and primary-figure labels -/

/-- Whether the tank's top boundary is open or sealed. -/
inductive TankTopBoundary where
  | open
  | sealed
  deriving DecidableEq, Repr

/-- Orientation of the long axis of the tank. -/
inductive TankAxisOrientation where
  | vertical
  | nonvertical
  deriving DecidableEq, Repr

/-- Material of the tank shell. -/
inductive TankShellMaterial where
  | steel
  | other
  deriving DecidableEq, Repr

/-- Location of the concrete ballast inside the tank. -/
inductive BallastLocation where
  | atTankBottom
  | elsewhere
  deriving DecidableEq, Repr

/-- Text labels visible in the supplied cross-sectional figure. -/
inductive FigureRegionLabel where
  | air
  | concrete
  | ocean
  | other
  deriving DecidableEq, Repr

/--
Primary-image readout.  No numerical concrete height is introduced because
the figure does not label one.
-/
structure SuppliedFigureReadout where
  upperInteriorLabel : FigureRegionLabel
  lowerInteriorLabel : FigureRegionLabel
  exteriorLabel : FigureRegionLabel
  bottomToOceanSurfaceArrow : LengthQuantity
  oceanSurfaceShown : Bool

/--
Physical state of the floating tank.  In particular, `concreteMass` is an
independent unknown and is not defined using the requested answer.
-/
structure BallastedTankSetup where
  topBoundary : TankTopBoundary
  axisOrientation : TankAxisOrientation
  shellMaterial : TankShellMaterial
  ballastLocation : BallastLocation
  interiorFlooded : Bool
  tankCrossSectionalArea : AreaQuantity
  tankHeight : LengthQuantity
  emptyTankMass : MassQuantity
  concreteMass : MassQuantity
  oceanMassDensity : MassDensityQuantity
  displacedOceanVolume : VolumeQuantity
  gravitationalAcceleration : AccelerationQuantity
  totalWeight : ForceQuantity
  buoyantForce : ForceQuantity
  suppliedFigure : SuppliedFigureReadout

/-- The draft indicated by the figure's vertical `10 m` arrow. -/
def draftInMeters (setup : BallastedTankSetup) : ℝ :=
  lengthInMeters setup.suppliedFigure.bottomToOceanSurfaceArrow

/-- Total tank-plus-ballast mass readout, neglecting the contained air mass. -/
def totalSupportedMassInKilograms (setup : BallastedTankSetup) : ℝ :=
  massInKilograms setup.emptyTankMass +
    massInKilograms setup.concreteMass

/-! ## Problem data, environmental calibration, and governing laws -/

/--
Data stated in the prose or read from the primary figure.  The tank is dry
inside, has air over concrete, and extends `16 m` from bottom to its open top;
the ocean surface is `10 m` above its bottom.
-/
structure MatchesProblemAndFigureData (setup : BallastedTankSetup) : Prop where
  topIsOpen : setup.topBoundary = .open
  axisIsVertical : setup.axisOrientation = .vertical
  shellIsSteel : setup.shellMaterial = .steel
  concreteIsAtBottom : setup.ballastLocation = .atTankBottom
  interiorIsUnflooded : setup.interiorFlooded = false
  airLabelAbove : setup.suppliedFigure.upperInteriorLabel = .air
  concreteLabelBelow : setup.suppliedFigure.lowerInteriorLabel = .concrete
  oceanLabelOutside : setup.suppliedFigure.exteriorLabel = .ocean
  oceanSurfaceIsShown : setup.suppliedFigure.oceanSurfaceShown = true
  crossSectionalAreaReadout :
    areaInSquareMeters setup.tankCrossSectionalArea = 3
  tankHeightReadout : lengthInMeters setup.tankHeight = 16
  emptyTankMassReadout : massInKilograms setup.emptyTankMass = 10000
  bottomToSurfaceArrowReadout : draftInMeters setup = 10

/--
Environmental calibration implicit in the recorded exact answer.  The source
calls the fluid ocean water but supplies no density; `997 kg/m³` is therefore
kept as an explicit extra datum rather than hidden in Archimedes' law.
-/
structure UsesRecordedOceanDensityCalibration
    (setup : BallastedTankSetup) : Prop where
  oceanDensityReadout :
    densityInKilogramsPerCubicMeter setup.oceanMassDensity = 997

/-- Positivity needed to cancel gravity in the later static-equilibrium proof. -/
structure HasPhysicalGravity (setup : BallastedTankSetup) : Prop where
  gravityIsPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration

/--
Prismatic displacement law: for the upright unflooded tank, displaced ocean
volume is the horizontal cross-sectional area times the draft.
-/
def SatisfiesPrismaticDisplacementLaw
    (setup : BallastedTankSetup) : Prop :=
  volumeInCubicMeters setup.displacedOceanVolume =
    areaInSquareMeters setup.tankCrossSectionalArea * draftInMeters setup

/-- The downward weight magnitude is `(tank mass + concrete mass) g`. -/
def SatisfiesTotalWeightLaw (setup : BallastedTankSetup) : Prop :=
  forceInNewtons setup.totalWeight =
    totalSupportedMassInKilograms setup *
      accelerationInMetersPerSecondSquared setup.gravitationalAcceleration

/-- Archimedes' law: buoyancy is `ocean density × displaced volume × g`. -/
def SatisfiesArchimedesPrinciple
    (setup : BallastedTankSetup) : Prop :=
  forceInNewtons setup.buoyantForce =
    densityInKilogramsPerCubicMeter setup.oceanMassDensity *
      volumeInCubicMeters setup.displacedOceanVolume *
      accelerationInMetersPerSecondSquared setup.gravitationalAcceleration

/-- Static vertical flotation: upward buoyancy balances downward weight. -/
def FloatsInVerticalStaticEquilibrium
    (setup : BallastedTankSetup) : Prop :=
  forceInNewtons setup.buoyantForce = forceInNewtons setup.totalWeight

/-! ## Derived quantities and requested answer -/

/-- The supplied answer-choice labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Concrete-mass readout printed beside each answer choice. -/
def AnswerChoice.massInKilograms : AnswerChoice → ℝ
  | .A => 10000
  | .B => 29910
  | .C => 9970
  | .D => 19910

/-- A modeled concrete mass agrees with a displayed answer choice. -/
def MatchesAnswerChoice
    (setup : BallastedTankSetup) (choice : AnswerChoice) : Prop :=
  massInKilograms setup.concreteMass = choice.massInKilograms

/-- The `3 m²` area and `10 m` draft displace `30 m³` of ocean. -/
lemma displaced_ocean_volume_at_requested_draft
    (setup : BallastedTankSetup)
    (hData : MatchesProblemAndFigureData setup)
    (hDisplacement : SatisfiesPrismaticDisplacementLaw setup) :
    volumeInCubicMeters setup.displacedOceanVolume = 30 := by
  calc
    volumeInCubicMeters setup.displacedOceanVolume =
        areaInSquareMeters setup.tankCrossSectionalArea *
          draftInMeters setup := hDisplacement
    _ = 3 * 10 := by
      rw [hData.crossSectionalAreaReadout,
        hData.bottomToSurfaceArrowReadout]
    _ = 30 := by norm_num

/-- At the requested draft, buoyancy supports `997 × 30 = 29910 kg`. -/
lemma total_supported_mass_at_requested_draft
    (setup : BallastedTankSetup)
    (hData : MatchesProblemAndFigureData setup)
    (hDensity : UsesRecordedOceanDensityCalibration setup)
    (hGravity : HasPhysicalGravity setup)
    (hDisplacement : SatisfiesPrismaticDisplacementLaw setup)
    (hWeight : SatisfiesTotalWeightLaw setup)
    (hArchimedes : SatisfiesArchimedesPrinciple setup)
    (hEquilibrium : FloatsInVerticalStaticEquilibrium setup) :
    totalSupportedMassInKilograms setup = 29910 := by
  have hVolume :
      volumeInCubicMeters setup.displacedOceanVolume = 30 :=
    displaced_ocean_volume_at_requested_draft setup hData hDisplacement
  have hGravityPositive :
      0 < accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration :=
    hGravity.gravityIsPositive
  have hWeight' := hWeight
  have hArchimedes' := hArchimedes
  have hEquilibrium' := hEquilibrium
  simp only [SatisfiesTotalWeightLaw] at hWeight'
  simp only [SatisfiesArchimedesPrinciple] at hArchimedes'
  simp only [FloatsInVerticalStaticEquilibrium] at hEquilibrium'
  rw [hDensity.oceanDensityReadout, hVolume] at hArchimedes'
  norm_num at hArchimedes'
  nlinarith

/-!
The required concrete ballast is
`997 kg/m³ × (3 m² × 10 m) - 10000 kg = 19910 kg`, answer choice D.

This is the declaration corresponding to
`thm:physics:phyx_mini_0664:target`.
-/
theorem problem_phyx_mini_0664
    (setup : BallastedTankSetup)
    (hData : MatchesProblemAndFigureData setup)
    (hDensity : UsesRecordedOceanDensityCalibration setup)
    (hGravity : HasPhysicalGravity setup)
    (hDisplacement : SatisfiesPrismaticDisplacementLaw setup)
    (hWeight : SatisfiesTotalWeightLaw setup)
    (hArchimedes : SatisfiesArchimedesPrinciple setup)
    (hEquilibrium : FloatsInVerticalStaticEquilibrium setup) :
    massInKilograms setup.concreteMass = 19910 ∧
      MatchesAnswerChoice setup .D := by
  have hTotal : totalSupportedMassInKilograms setup = 29910 :=
    total_supported_mass_at_requested_draft setup hData hDensity hGravity
      hDisplacement hWeight hArchimedes hEquilibrium
  have hConcrete : massInKilograms setup.concreteMass = 19910 := by
    simp only [totalSupportedMassInKilograms,
      hData.emptyTankMassReadout] at hTotal
    linarith
  constructor
  · exact hConcrete
  · simpa [MatchesAnswerChoice, AnswerChoice.massInKilograms] using hConcrete

end PhyXMiniProblems.ProblemPhyXMini0664
