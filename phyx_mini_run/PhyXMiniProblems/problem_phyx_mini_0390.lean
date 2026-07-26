import Mathlib
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0390

open Dimension

/-!
# Two freely supported pistons over a connected gas chamber

The apparatus has two piston/cylinder branches, labelled `A` and `B`, whose
gas chambers are joined by a pipe. Atmospheric pressure `P₀` acts above both
pistons and the connected gas acts below them. The requested quantity is the
mass of piston B for which both pistons can remain freely supported instead of
resting on the cylinder bottoms.

Areas, masses, acceleration, and pressures are represented by unit-independent
dimensionful quantities. Real numbers occur only at explicitly named unit
readout boundaries and in the multiple-choice data.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- A nonnegative physical mass, independent of a choice of units. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative acceleration magnitude with physical dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- The numerical value of an area in square metres. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- The numerical value of an area in square centimetres. -/
def areaInSquareCentimeters (area : DimArea) : ℝ :=
  10000 * areaInSquareMeters area

/-- The numerical value of a mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- The numerical value of an acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- The numerical value of an absolute pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- The numerical value of an absolute pressure in kilopascals. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-! ## Apparatus and primary-image information -/

/-- The two piston/cylinder branches labelled in the figure. -/
inductive Cylinder where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- Whether a piston is freely supported or is supported by the cylinder base. -/
inductive PistonSupportRegime where
  | freelySupportedInStaticEquilibrium
  | restingOnCylinderBottom
  deriving DecidableEq, Repr

/-- Whether the regions below the two pistons form one connected chamber. -/
inductive ChamberConnectionModel where
  | oneContinuousGasChamber
  | disconnectedChambers
  deriving DecidableEq, Repr

/-- Literal symbolic labels visible in the supplied figure. -/
inductive FigureLabel where
  | A
  | B
  | P0
  | g
  deriving DecidableEq, Fintype, Repr

/-- Qualitative geometry and annotations read from the primary image. -/
structure ConnectedPistonFigure where
  showsLabel : FigureLabel → Bool
  showsCylinder : Cylinder → Bool
  showsPiston : Cylinder → Bool
  showsBlueGasBelowPiston : Cylinder → Bool
  showsOutsidePressureAbovePiston : Cylinder → Bool
  showsBottomConnectingPipe : Bool
  blueRegionIsContinuousThroughPipe : Bool
  pistonBIsDrawnHigherThanPistonA : Bool
  showsDownwardGravityArrow : Bool

/-!
The physical parameters and observables of the apparatus. Pressures below the
two pistons are kept separate so that equality of connected-chamber pressure
is a governing law rather than a definitional shortcut. In particular,
`pistonMass .B` is an independent physical quantity.
-/
structure ConnectedPistonSetup where
  crossSectionalArea : Cylinder → DimArea
  pistonMass : Cylinder → MassQuantity
  gravitationalAcceleration : AccelerationQuantity
  outsidePressureAbovePistons : DimPressure
  gasPressureBelowPiston : Cylinder → DimPressure
  pistonSupportRegime : Cylinder → PistonSupportRegime
  chamberConnectionModel : ChamberConnectionModel
  figure : ConnectedPistonFigure

/-! ## Scenario, measurements, and physical conditions -/

/-- The chambers below A and B are connected by the pipe described in the prose. -/
structure MatchesConnectedPistonScenario
    (setup : ConnectedPistonSetup) : Prop where
  gasChambersConnectedByPipe :
    setup.chamberConnectionModel = .oneContinuousGasChamber

/-!
Numerical data supplied by the problem. The unknown mass of piston B is not a
field of this structure.
-/
structure MatchesProblemReadouts (setup : ConnectedPistonSetup) : Prop where
  areaAInSquareCentimeters :
    areaInSquareCentimeters (setup.crossSectionalArea .A) = 75
  areaBInSquareCentimeters :
    areaInSquareCentimeters (setup.crossSectionalArea .B) = 25
  massAInKilograms : massInKilograms (setup.pistonMass .A) = 25
  outsidePressureInKilopascals :
    pressureInKilopascals setup.outsidePressureAbovePistons = 100

/-- The exact conventional calibration `g₀ = 9.80665 m/s²`. -/
structure UsesStandardGravity (setup : ConnectedPistonSetup) : Prop where
  standardGravitySI :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration = 196133 / 20000

/-!
Primary-image evidence. The image supplies geometry and labels but no value
for the mass of piston B.
-/
structure MatchesSuppliedConnectedPistonFigure
    (setup : ConnectedPistonSetup) : Prop where
  everyPrintedLabelShown : ∀ label, setup.figure.showsLabel label = true
  bothCylindersShown : ∀ cylinder, setup.figure.showsCylinder cylinder = true
  bothPistonsShown : ∀ cylinder, setup.figure.showsPiston cylinder = true
  blueGasBelowBothPistons :
    ∀ cylinder, setup.figure.showsBlueGasBelowPiston cylinder = true
  outsidePressureShownAboveBothPistons :
    ∀ cylinder,
      setup.figure.showsOutsidePressureAbovePiston cylinder = true
  bottomConnectingPipeShown : setup.figure.showsBottomConnectingPipe = true
  connectedBlueRegionShown :
    setup.figure.blueRegionIsContinuousThroughPipe = true
  pistonBShownHigher : setup.figure.pistonBIsDrawnHigherThanPistonA = true
  downwardGravityArrowShown :
    setup.figure.showsDownwardGravityArrow = true

/-- Positivity and nondegeneracy conditions for the physical apparatus. -/
structure HasPhysicalConnectedPistonParameters
    (setup : ConnectedPistonSetup) : Prop where
  areaPositive :
    ∀ cylinder, 0 < areaInSquareMeters (setup.crossSectionalArea cylinder)
  massPositive :
    ∀ cylinder, 0 < massInKilograms (setup.pistonMass cylinder)
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  outsidePressurePositive :
    0 < pressureInPascals setup.outsidePressureAbovePistons
  gasPressurePositive :
    ∀ cylinder,
      0 < pressureInPascals (setup.gasPressureBelowPiston cylinder)

/-!
The operating condition in the question: neither piston receives a support
reaction from the bottom of its cylinder.
-/
def NeitherPistonRestsOnBottom (setup : ConnectedPistonSetup) : Prop :=
  ∀ cylinder,
    setup.pistonSupportRegime cylinder =
      .freelySupportedInStaticEquilibrium

/-! ## Governing mechanics -/

/-!
The connected-pressure law and vertical force balance for each freely
supported piston. In coherent SI readouts, force balance is

`P_gas A = P₀ A + m g`.

It is conditional on free support because a piston resting on the base would
also have a bottom reaction force. Neither field states the desired mass ratio
or the numerical mass of piston B.
-/
structure SatisfiesConnectedPistonLaws
    (setup : ConnectedPistonSetup) : Prop where
  uniformConnectedGasPressure :
    setup.chamberConnectionModel = .oneContinuousGasChamber →
      setup.gasPressureBelowPiston .A =
        setup.gasPressureBelowPiston .B
  freelySupportedPistonForceBalance : ∀ cylinder,
    setup.pistonSupportRegime cylinder =
        .freelySupportedInStaticEquilibrium →
      pressureInPascals (setup.gasPressureBelowPiston cylinder) *
          areaInSquareMeters (setup.crossSectionalArea cylinder) =
        pressureInPascals setup.outsidePressureAbovePistons *
            areaInSquareMeters (setup.crossSectionalArea cylinder) +
          massInKilograms (setup.pistonMass cylinder) *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration

/-! ## Derived mass relation and answer -/

/-- Equal pressure and force balance make piston mass proportional to area. -/
theorem freelySupportedPistonMassRatio
    (setup : ConnectedPistonSetup)
    (hScenario : MatchesConnectedPistonScenario setup)
    (hNoBottomContact : NeitherPistonRestsOnBottom setup)
    (hPhysical : HasPhysicalConnectedPistonParameters setup)
    (hLaws : SatisfiesConnectedPistonLaws setup) :
    massInKilograms (setup.pistonMass .B) *
        areaInSquareMeters (setup.crossSectionalArea .A) =
      massInKilograms (setup.pistonMass .A) *
        areaInSquareMeters (setup.crossSectionalArea .B) := by
  have hPressure := congrArg pressureInPascals
    (hLaws.uniformConnectedGasPressure
      hScenario.gasChambersConnectedByPipe)
  have hBalanceA := hLaws.freelySupportedPistonForceBalance .A
    (hNoBottomContact .A)
  have hBalanceB := hLaws.freelySupportedPistonForceBalance .B
    (hNoBottomContact .B)
  rw [hPressure] at hBalanceA
  have hCross :
      (massInKilograms (setup.pistonMass .B) *
          areaInSquareMeters (setup.crossSectionalArea .A) -
        massInKilograms (setup.pistonMass .A) *
          areaInSquareMeters (setup.crossSectionalArea .B)) *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration = 0 := by
    linear_combination
      areaInSquareMeters (setup.crossSectionalArea .B) * hBalanceA -
      areaInSquareMeters (setup.crossSectionalArea .A) * hBalanceB
  rcases mul_eq_zero.mp hCross with hMass | hGravity
  · linarith
  · exact (ne_of_gt hPhysical.gravityPositive hGravity).elim

/-!
Substitution of the two areas and mass A gives the exact mass of piston B.
The outside pressure and gravitational acceleration cancel from the relation.
-/
theorem pistonBMassIsTwentyFiveThirdsKilograms
    (setup : ConnectedPistonSetup)
    (hScenario : MatchesConnectedPistonScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hNoBottomContact : NeitherPistonRestsOnBottom setup)
    (hPhysical : HasPhysicalConnectedPistonParameters setup)
    (hLaws : SatisfiesConnectedPistonLaws setup) :
    massInKilograms (setup.pistonMass .B) = 25 / 3 := by
  have hAreaA :
      areaInSquareMeters (setup.crossSectionalArea .A) = 3 / 400 := by
    have h := hReadouts.areaAInSquareCentimeters
    unfold areaInSquareCentimeters at h
    norm_num at h ⊢
    linarith
  have hAreaB :
      areaInSquareMeters (setup.crossSectionalArea .B) = 1 / 400 := by
    have h := hReadouts.areaBInSquareCentimeters
    unfold areaInSquareCentimeters at h
    norm_num at h ⊢
    linarith
  have hRatio := freelySupportedPistonMassRatio setup hScenario
    hNoBottomContact hPhysical hLaws
  rw [hReadouts.massAInKilograms, hAreaA, hAreaB] at hRatio
  norm_num at hRatio ⊢
  linarith

/-- Labels of the four answer choices in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Piston-B mass in kilograms displayed beside each answer label. -/
def displayedMassKilograms : AnswerChoice → ℝ
  | .A => 490
  | .B => 833 / 100
  | .C => 154
  | .D => 51 / 5

/-- Dataset metadata records answer label B. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
An exact mass rounds to a displayed value to the nearest hundredth of a
kilogram when the error is less than half of `0.01 kg`.
-/
def RoundsToNearestHundredthKilogram
    (exactKilograms displayedKilograms : ℝ) : Prop :=
  |exactKilograms - displayedKilograms| < 1 / 200

/-- A chosen answer is strictly closer to the exact mass than every rival. -/
def IsUniqueClosestChoice
    (exactKilograms : ℝ) (chosen : AnswerChoice) : Prop :=
  ∀ other, other ≠ chosen →
    |exactKilograms - displayedMassKilograms chosen| <
      |exactKilograms - displayedMassKilograms other|

/-!
With the stated measurements and no bottom contact, piston B has exact mass
`25/3 kg`; this rounds to `8.33 kg`, and choice B is uniquely closest.
-/
theorem problem_phyx_mini_0390
    (setup : ConnectedPistonSetup)
    (hScenario : MatchesConnectedPistonScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedConnectedPistonFigure setup)
    (hGravity : UsesStandardGravity setup)
    (hNoBottomContact : NeitherPistonRestsOnBottom setup)
    (hPhysical : HasPhysicalConnectedPistonParameters setup)
    (hLaws : SatisfiesConnectedPistonLaws setup) :
    massInKilograms (setup.pistonMass .B) = 25 / 3 ∧
      RoundsToNearestHundredthKilogram
        (massInKilograms (setup.pistonMass .B))
        (displayedMassKilograms .B) ∧
      IsUniqueClosestChoice
        (massInKilograms (setup.pistonMass .B)) .B := by
  have hMass := pistonBMassIsTwentyFiveThirdsKilograms setup hScenario
    hReadouts hNoBottomContact hPhysical hLaws
  refine ⟨hMass, ?_, ?_⟩
  · rw [hMass]
    norm_num [RoundsToNearestHundredthKilogram,
      displayedMassKilograms, abs_of_nonneg]
  · rw [hMass]
    unfold IsUniqueClosestChoice
    intro other hOther
    fin_cases other <;>
      norm_num [displayedMassKilograms, abs_of_nonneg, abs_of_nonpos]
        at *

end PhyXMiniProblems.ProblemPhyXMini0390
