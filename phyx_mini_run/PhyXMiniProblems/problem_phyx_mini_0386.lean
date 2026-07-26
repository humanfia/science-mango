import Mathlib
import Physlib.Units.WithDim.Basic

namespace PhyXMiniProblems.ProblemPhyXMini0386

open Dimension

noncomputable section

/-!
# Concrete ballast for an open steel tank

The tank is modeled as a vertical prism floating without flooding. The
supplied figure places its bottom `10 m` below the ocean surface, with concrete
at the bottom and air above it. Dimensional quantities are tagged by Physlib's
`WithDim`; real numbers occur only as numerical readouts in the stated SI
units.
-/

/-- The physical dimension of an area. -/
def areaDimension : Dimension := L𝓭 * L𝓭

/-- The physical dimension of a volume. -/
def volumeDimension : Dimension := L𝓭 * L𝓭 * L𝓭

/-- The physical dimension of mass density, `M L⁻³`. -/
def massDensityDimension : Dimension :=
  M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The physical dimension of acceleration. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of force. -/
def forceDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- An area readout in square metres in the SI unit system. -/
def squareMeters (value : ℝ) : WithDim areaDimension ℝ := ⟨value⟩

/-- A length readout in metres in the SI unit system. -/
def meters (value : ℝ) : WithDim L𝓭 ℝ := ⟨value⟩

/-- A volume readout in cubic metres in the SI unit system. -/
def cubicMeters (value : ℝ) : WithDim volumeDimension ℝ := ⟨value⟩

/-- A mass readout in kilograms in the SI unit system. -/
def kilograms (value : ℝ) : WithDim M𝓭 ℝ := ⟨value⟩

/-- A mass-density readout in kilograms per cubic metre. -/
def kilogramsPerCubicMeter (value : ℝ) :
    WithDim massDensityDimension ℝ := ⟨value⟩

/-- An acceleration readout in metres per second squared. -/
def metersPerSecondSquared (value : ℝ) :
    WithDim accelerationDimension ℝ := ⟨value⟩

/-- A force readout in newtons. -/
def newtons (value : ℝ) : WithDim forceDimension ℝ := ⟨value⟩

/-- Whether the tank's upper boundary is open or sealed. -/
inductive TankTopBoundary where
  | open
  | sealed
  deriving DecidableEq, Repr

/-- Orientation of the tank's long axis relative to the ocean surface. -/
inductive TankAxisOrientation where
  | vertical
  | nonvertical
  deriving DecidableEq, Repr

/-- Material names stated in the scenario or printed in the figure. -/
inductive FigureMaterial where
  | steel
  | air
  | concrete
  | ocean
  deriving DecidableEq, Repr

/-- The location of the concrete ballast inside the tank. -/
inductive BallastLocation where
  | atTankBottom
  | elsewhere
  deriving DecidableEq, Repr

/--
Physical quantities and categorical figure data for the ballasted tank.

The concrete mass and the force magnitudes are independent observables. Their
relations are supplied only by the governing-law predicates below, so the
requested mass is not built into the setup.
-/
structure BallastedTankSetup where
  unitSystem : UnitChoices
  topBoundary : TankTopBoundary
  axisOrientation : TankAxisOrientation
  shellMaterial : FigureMaterial
  upperInteriorMaterial : FigureMaterial
  lowerInteriorMaterial : FigureMaterial
  exteriorFluid : FigureMaterial
  ballastLocation : BallastLocation
  tankCrossSectionArea : WithDim areaDimension ℝ
  tankHeight : WithDim L𝓭 ℝ
  tankBottomDepthBelowSurface : WithDim L𝓭 ℝ
  emptyTankMass : WithDim M𝓭 ℝ
  concreteMass : WithDim M𝓭 ℝ
  oceanMassDensity : WithDim massDensityDimension ℝ
  displacedOceanVolume : WithDim volumeDimension ℝ
  gravitationalAcceleration : WithDim accelerationDimension ℝ
  totalWeight : WithDim forceDimension ℝ
  buoyantForce : WithDim forceDimension ℝ

/-- The total supported mass is the steel tank mass plus its concrete ballast.
The mass of the contained air is neglected in this elementary model. -/
def totalSupportedMass (setup : BallastedTankSetup) : WithDim M𝓭 ℝ :=
  setup.emptyTankMass + setup.concreteMass

/--
Numerical and diagrammatic data explicitly supplied by the problem and its
figure. In particular, the `10 m` arrow is read as the depth of the tank bottom
below the ocean surface, not as the concrete fill height.
-/
structure HasTankAndFigureData (setup : BallastedTankSetup) : Prop where
  usesSIUnits : setup.unitSystem = UnitChoices.SI
  openAtTop : setup.topBoundary = .open
  tankIsVertical : setup.axisOrientation = .vertical
  steelShell : setup.shellMaterial = .steel
  airAboveConcrete : setup.upperInteriorMaterial = .air
  concreteAtBottom : setup.lowerInteriorMaterial = .concrete
  oceanOutside : setup.exteriorFluid = .ocean
  ballastAtTankBottom : setup.ballastLocation = .atTankBottom
  crossSectionAreaReadout : setup.tankCrossSectionArea = squareMeters 3
  tankHeightReadout : setup.tankHeight = meters 16
  requestedBottomDepthReadout :
    setup.tankBottomDepthBelowSurface = meters 10
  emptyTankMassReadout : setup.emptyTankMass = kilograms 10000

/--
Reference-density calibration implicit in the recorded exact answer.

The problem does not state an ocean density. The choice `19910 kg` is obtained
from the textbook readout `997 kg/m³`; keeping this as a separate hypothesis
makes that otherwise hidden modeling choice explicit.
-/
structure HasRecordedOceanDensityCalibration
    (setup : BallastedTankSetup) : Prop where
  oceanDensityReadout :
    setup.oceanMassDensity = kilogramsPerCubicMeter 997

/-- Nondegeneracy needed to cancel gravity from the force balance. -/
structure HasPhysicalGravity (setup : BallastedTankSetup) : Prop where
  gravityIsPositive : 0 < setup.gravitationalAcceleration

/--
Prismatic displacement law for the upright, unflooded tank: the displaced
ocean volume is the effective horizontal cross-sectional area times the draft.
Steel-wall thickness is neglected at the resolution of the supplied area.
-/
def SatisfiesPrismaticDisplacementLaw (setup : BallastedTankSetup) : Prop :=
  setup.displacedOceanVolume = WithDim.cast
    (setup.tankCrossSectionArea * setup.tankBottomDepthBelowSurface)
    (by
      ext <;> simp [areaDimension, volumeDimension])

/-- The tank's downward weight magnitude is `(tank mass + ballast mass) g`. -/
def SatisfiesTotalWeightLaw (setup : BallastedTankSetup) : Prop :=
  setup.totalWeight = WithDim.cast
    (totalSupportedMass setup * setup.gravitationalAcceleration)
    (by
      ext <;> simp [accelerationDimension, forceDimension]
      all_goals ring)

/-- Archimedes' law: buoyancy is `ocean density × displaced volume × g`. -/
def SatisfiesArchimedesLaw (setup : BallastedTankSetup) : Prop :=
  setup.buoyantForce = WithDim.cast
    (setup.oceanMassDensity * setup.displacedOceanVolume *
      setup.gravitationalAcceleration)
    (by
      ext <;>
        simp [massDensityDimension, volumeDimension, accelerationDimension,
          forceDimension]
      all_goals ring)

/-- Static vertical flotation: the upward buoyant force balances the weight. -/
def FloatsInVerticalStaticEquilibrium (setup : BallastedTankSetup) : Prop :=
  setup.buoyantForce = setup.totalWeight

/-- The four concrete-mass answers printed beside the multiple-choice labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The concrete mass, in kilograms, displayed for an answer choice. -/
def answerMassInKilograms : AnswerChoice → ℝ
  | .A => 490
  | .B => 19910
  | .C => 154
  | .D => 10.2

/-- The area and requested `10 m` draft displace exactly `30 m³` of ocean. -/
lemma displacedOceanVolume_at_requestedDraft
    (setup : BallastedTankSetup)
    (hData : HasTankAndFigureData setup)
    (hDisplacement : SatisfiesPrismaticDisplacementLaw setup) :
    setup.displacedOceanVolume = cubicMeters 30 := by
  rw [SatisfiesPrismaticDisplacementLaw] at hDisplacement
  calc
    setup.displacedOceanVolume = WithDim.cast
        (setup.tankCrossSectionArea * setup.tankBottomDepthBelowSurface) _ :=
      hDisplacement
    _ = cubicMeters 30 := by
      rw [hData.crossSectionAreaReadout,
        hData.requestedBottomDepthReadout]
      ext
      change (3 : ℝ) * 10 = 30
      norm_num

/-- At the requested draft, buoyancy supports `997 × 30 = 29910 kg`. -/
lemma totalSupportedMass_at_requestedDraft
    (setup : BallastedTankSetup)
    (hData : HasTankAndFigureData setup)
    (hDensity : HasRecordedOceanDensityCalibration setup)
    (hGravity : HasPhysicalGravity setup)
    (hDisplacement : SatisfiesPrismaticDisplacementLaw setup)
    (hWeight : SatisfiesTotalWeightLaw setup)
    (hArchimedes : SatisfiesArchimedesLaw setup)
    (hEquilibrium : FloatsInVerticalStaticEquilibrium setup) :
    totalSupportedMass setup = kilograms 29910 := by
  have hVolume :=
    displacedOceanVolume_at_requestedDraft setup hData hDisplacement
  unfold SatisfiesTotalWeightLaw at hWeight
  unfold SatisfiesArchimedesLaw at hArchimedes
  unfold FloatsInVerticalStaticEquilibrium at hEquilibrium
  have hBalance :=
    hArchimedes.symm.trans (hEquilibrium.trans hWeight)
  rw [hDensity.oceanDensityReadout, hVolume] at hBalance
  have hBalanceVal := congrArg WithDim.val hBalance
  apply WithDim.ext
  simp only [WithDim.cast, WithDim.withDim_hMul_val,
    kilogramsPerCubicMeter, cubicMeters, kilograms] at hBalanceVal ⊢
  have hg : 0 < setup.gravitationalAcceleration.val :=
    hGravity.gravityIsPositive
  nlinarith

/--
The concrete ballast must have mass
`997 kg/m³ × (3 m² × 10 m) - 10000 kg = 19910 kg`, which is answer B.

This is the declaration corresponding to
`thm:physics:phyx_mini_0386:target`.
-/
theorem requiredConcreteMass_eq_answerB
    (setup : BallastedTankSetup)
    (hData : HasTankAndFigureData setup)
    (hDensity : HasRecordedOceanDensityCalibration setup)
    (hGravity : HasPhysicalGravity setup)
    (hDisplacement : SatisfiesPrismaticDisplacementLaw setup)
    (hWeight : SatisfiesTotalWeightLaw setup)
    (hArchimedes : SatisfiesArchimedesLaw setup)
    (hEquilibrium : FloatsInVerticalStaticEquilibrium setup) :
    setup.concreteMass = kilograms (answerMassInKilograms .B) := by
  have hTotal :=
    totalSupportedMass_at_requestedDraft setup hData hDensity hGravity
      hDisplacement hWeight hArchimedes hEquilibrium
  rw [totalSupportedMass, hData.emptyTankMassReadout] at hTotal
  have hTotalVal := congrArg WithDim.val hTotal
  apply WithDim.ext
  norm_num [kilograms, answerMassInKilograms] at hTotalVal ⊢
  linarith

end

end PhyXMiniProblems.ProblemPhyXMini0386
