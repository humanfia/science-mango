import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0939

open Dimension

/-!
# Mutual inductance of the pictured Tesla-coil winding pair

The primary raster `939.png` shows a long, closely wound yellow solenoid of
length `l`, cross-sectional area `A`, and `N₁` turns.  A gray `N₂`-turn coil
surrounds the primary near its center.  No numerical values of `l`, `A`, `N₁`,
or `N₂` are present in either the prose or the raster.

Physical magnitudes below use Physlib's unit-covariant
`Dimensionful (WithDim ...)` representation.  Scalar equations are stated only
after an explicitly named coherent-SI readout.

Assumption/target split:

* governing laws: the ideal long-solenoid field law `B = μ₀ (N₁/l) I`, the
  uniform-flux law `Φ = BA`, the secondary linkage law `λ₂ = N₂ Φ`, and the
  defining law `λ₂ = MI`;
* previous-part results: none;
* figure/data readouts: the winding placement, colors, and the four symbolic
  labels `l`, `A`, `N₁`, and `N₂`; the dataset also records choice `B`, whose
  displayed value is `25 μH`;
* current target conclusion: the physically supported symbolic relation
  `M = μ₀ N₁ N₂ A / l` in coherent SI units.

The recorded `25 μH` is retained as source metadata, but is not a physical
conclusion: the source omits the numerical parameters needed to derive it.
-/

/-! ## Dimensionful physical quantities and their SI readout -/

/-- Electric current has dimension charge per time. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Cross-sectional area has dimension length squared. -/
def areaDimension : Dimension :=
  L𝓭 * L𝓭

/-- Magnetic flux density has dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux and flux linkage have dimension `B L²`. -/
def magneticFluxDimension : Dimension :=
  magneticFluxDensityDimension * areaDimension

/-- Inductance has the dimension of magnetic flux divided by current. -/
def inductanceDimension : Dimension :=
  magneticFluxDimension * electricCurrentDimension⁻¹

/-- Magnetic permeability has the dimension of inductance per length. -/
def magneticPermeabilityDimension : Dimension :=
  inductanceDimension * L𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaQuantity : Type :=
  Dimensionful (WithDim areaDimension NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative magnetic flux or flux linkage. -/
abbrev MagneticFluxQuantity : Type :=
  Dimensionful (WithDim magneticFluxDimension NNReal)

/-- A nonnegative, unit-independent magnetic permeability. -/
abbrev MagneticPermeabilityQuantity : Type :=
  Dimensionful (WithDim magneticPermeabilityDimension NNReal)

/-- A nonnegative, unit-independent mutual inductance. -/
abbrev MutualInductanceQuantity : Type :=
  Dimensionful (WithDim inductanceDimension NNReal)

/-- Read a nonnegative dimensionful quantity in Physlib's coherent SI units. -/
def coherentSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-! ## Winding roles and literal figure evidence -/

/-- The two windings distinguished by the prose and primary raster. -/
inductive WindingRole where
  | primarySolenoid
  | surroundingSecondary
  deriving DecidableEq, Fintype, Repr

/-- The four symbolic annotations visible in `939.png`. -/
inductive FigureLabel where
  | solenoidLengthL
  | crossSectionalAreaA
  | primaryTurnsN1
  | secondaryTurnsN2
  deriving DecidableEq, Fintype, Repr

/-- The winding colors used in the primary raster. -/
inductive WindingColor where
  | yellow
  | gray
  | other
  deriving DecidableEq, Repr

/-- Physical idealizations available for the primary winding. -/
inductive PrimaryWindingModel where
  | longCloselyWoundSolenoid
  | other
  deriving DecidableEq, Repr

/-- Placements available for the secondary relative to the primary. -/
inductive SecondaryPlacement where
  | surroundsPrimaryAtCenter
  | other
  deriving DecidableEq, Repr

/-- Literal presentation data from the supplied raster, with no numeric data. -/
structure TeslaCoilFigure where
  windingShown : WindingRole → Bool
  windingColor : WindingRole → WindingColor
  labelShown : FigureLabel → Bool
  primaryDrawnAsLongCylinder : Bool
  primaryDrawnCloselyWound : Bool
  secondaryDrawnAroundPrimary : Bool
  secondaryDrawnAtPrimaryCenter : Bool
  lengthArrowRunsAlongPrimaryAxis : Bool
  areaLeaderPointsToEndCrossSection : Bool

/-!
Independent physical data for the idealized experiment.  In particular,
`mutualInductance` is not defined from the requested closed form; it is related
to the other observables only by the governing-law premise below.
-/
structure TeslaCoilSetup where
  primaryWindingModel : PrimaryWindingModel
  secondaryPlacement : SecondaryPlacement
  solenoidLength : LengthQuantity
  crossSectionalArea : AreaQuantity
  primaryTurnCount : ℕ
  secondaryTurnCount : ℕ
  nonzeroTestCurrent : ElectricCurrentQuantity
  primaryInteriorField : MagneticFluxDensityQuantity
  fluxThroughOneSecondaryTurn : MagneticFluxQuantity
  secondaryFluxLinkage : MagneticFluxQuantity
  freeSpacePermeability : MagneticPermeabilityQuantity
  mutualInductance : MutualInductanceQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  figure : TeslaCoilFigure

/-! ## Scenario, data, and governing-law assumptions -/

/-- The qualitative winding arrangement stated in the problem prose. -/
structure MatchesWrittenTeslaCoilScenario (setup : TeslaCoilSetup) : Prop where
  primaryIsLongCloselyWoundSolenoid :
    setup.primaryWindingModel = .longCloselyWoundSolenoid
  secondarySurroundsPrimaryAtCenter :
    setup.secondaryPlacement = .surroundsPrimaryAtCenter

/-- Literal label, color, and placement evidence from the primary raster. -/
structure MatchesSuppliedTeslaCoilFigure (setup : TeslaCoilSetup) : Prop where
  bothWindingsShown : ∀ winding, setup.figure.windingShown winding = true
  allFourSymbolicLabelsShown : ∀ label, setup.figure.labelShown label = true
  primaryIsYellow :
    setup.figure.windingColor .primarySolenoid = .yellow
  secondaryIsGray :
    setup.figure.windingColor .surroundingSecondary = .gray
  primaryHasLongCylindricalPresentation :
    setup.figure.primaryDrawnAsLongCylinder = true
  primaryHasCloselySpacedTurns :
    setup.figure.primaryDrawnCloselyWound = true
  secondarySurroundsPrimary :
    setup.figure.secondaryDrawnAroundPrimary = true
  secondaryIsCentered :
    setup.figure.secondaryDrawnAtPrimaryCenter = true
  lengthArrowFollowsPrimaryAxis :
    setup.figure.lengthArrowRunsAlongPrimaryAxis = true
  areaLeaderEndsAtCrossSection :
    setup.figure.areaLeaderPointsToEndCrossSection = true

/-- Positivity and nondegeneracy of the physical parameters. -/
structure HasPhysicalTeslaCoilParameters (setup : TeslaCoilSetup) : Prop where
  lengthPositive : 0 < coherentSIReadout setup.solenoidLength
  areaPositive : 0 < coherentSIReadout setup.crossSectionalArea
  primaryTurnCountPositive : 0 < setup.primaryTurnCount
  secondaryTurnCountPositive : 0 < setup.secondaryTurnCount
  testCurrentPositive : 0 < coherentSIReadout setup.nonzeroTestCurrent
  permeabilityPositive : 0 < coherentSIReadout setup.freeSpacePermeability

/-!
The hollow air-core idealization identifies the dimensionful permeability's
coherent-SI readout with Physlib's free-space system parameter `μ₀`.  This
premise contains no mutual-inductance formula or answer value.
-/
structure UsesFreeSpacePermeability (setup : TeslaCoilSetup) : Prop where
  permeabilityReadoutAgreesWithSystem :
    coherentSIReadout setup.freeSpacePermeability =
      setup.electromagneticSystem.μ₀

/-!
The four independent textbook laws used in the derivation.  They are stated
at the coherent-SI readout boundary and do not contain the requested closed
form `M = μ₀ N₁ N₂ A / l`.
-/
structure SatisfiesIdealTeslaCoilLaws (setup : TeslaCoilSetup) : Prop where
  longSolenoidFieldLaw :
    coherentSIReadout setup.primaryInteriorField =
      coherentSIReadout setup.freeSpacePermeability *
        ((setup.primaryTurnCount : ℝ) /
          coherentSIReadout setup.solenoidLength) *
        coherentSIReadout setup.nonzeroTestCurrent
  fluxThroughSecondaryTurnLaw :
    coherentSIReadout setup.fluxThroughOneSecondaryTurn =
      coherentSIReadout setup.primaryInteriorField *
        coherentSIReadout setup.crossSectionalArea
  secondaryFluxLinkageLaw :
    coherentSIReadout setup.secondaryFluxLinkage =
      (setup.secondaryTurnCount : ℝ) *
        coherentSIReadout setup.fluxThroughOneSecondaryTurn
  mutualInductanceDefinition :
    coherentSIReadout setup.secondaryFluxLinkage =
      coherentSIReadout setup.mutualInductance *
        coherentSIReadout setup.nonzeroTestCurrent

/-! ## Displayed source choices and physical target -/

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Each answer choice's displayed mutual-inductance value, in microhenries. -/
def AnswerChoice.displayedMicrohenries : AnswerChoice → ℝ
  | .A => 22
  | .B => 25
  | .C => 75
  | .D => 28

/-- The source dataset records answer label `B`; this is metadata, not a law. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
The field, flux, linkage, and defining mutual-inductance laws yield the
symbolic free-space relation

`M = μ₀ N₁ N₂ A / l`.

The theorem deliberately does not claim `M = 25 μH`, because neither the text
nor the primary raster supplies the numerical values required for that claim.
This declaration formalizes `thm:physics:phyx_mini_0939:target`.
-/
theorem problem_phyx_mini_0939
    (setup : TeslaCoilSetup)
    (hScenario : MatchesWrittenTeslaCoilScenario setup)
    (hFigure : MatchesSuppliedTeslaCoilFigure setup)
    (hPhysical : HasPhysicalTeslaCoilParameters setup)
    (hFreeSpace : UsesFreeSpacePermeability setup)
    (hLaws : SatisfiesIdealTeslaCoilLaws setup) :
    coherentSIReadout setup.mutualInductance =
      setup.electromagneticSystem.μ₀ *
        (setup.primaryTurnCount : ℝ) *
        (setup.secondaryTurnCount : ℝ) *
        coherentSIReadout setup.crossSectionalArea /
        coherentSIReadout setup.solenoidLength := by
  have hCurrentNe : coherentSIReadout setup.nonzeroTestCurrent ≠ 0 :=
    ne_of_gt hPhysical.testCurrentPositive
  have hLengthNe : coherentSIReadout setup.solenoidLength ≠ 0 :=
    ne_of_gt hPhysical.lengthPositive
  calc
    coherentSIReadout setup.mutualInductance =
        coherentSIReadout setup.secondaryFluxLinkage /
          coherentSIReadout setup.nonzeroTestCurrent := by
      apply (eq_div_iff hCurrentNe).2
      exact hLaws.mutualInductanceDefinition.symm
    _ = (setup.secondaryTurnCount : ℝ) *
          coherentSIReadout setup.fluxThroughOneSecondaryTurn /
          coherentSIReadout setup.nonzeroTestCurrent := by
      rw [hLaws.secondaryFluxLinkageLaw]
    _ = (setup.secondaryTurnCount : ℝ) *
          (coherentSIReadout setup.primaryInteriorField *
            coherentSIReadout setup.crossSectionalArea) /
          coherentSIReadout setup.nonzeroTestCurrent := by
      rw [hLaws.fluxThroughSecondaryTurnLaw]
    _ = (setup.secondaryTurnCount : ℝ) *
          ((coherentSIReadout setup.freeSpacePermeability *
              ((setup.primaryTurnCount : ℝ) /
                coherentSIReadout setup.solenoidLength) *
              coherentSIReadout setup.nonzeroTestCurrent) *
            coherentSIReadout setup.crossSectionalArea) /
          coherentSIReadout setup.nonzeroTestCurrent := by
      rw [hLaws.longSolenoidFieldLaw]
    _ = setup.electromagneticSystem.μ₀ *
          (setup.primaryTurnCount : ℝ) *
          (setup.secondaryTurnCount : ℝ) *
          coherentSIReadout setup.crossSectionalArea /
          coherentSIReadout setup.solenoidLength := by
      rw [hFreeSpace.permeabilityReadoutAgreesWithSystem]
      field_simp [hCurrentNe, hLengthNe]

end PhyXMiniProblems.ProblemPhyXMini0939
