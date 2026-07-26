import Mathlib
import Physlib.Units.WithDim.Basic

/-!
# Self-inductance of a uniformly magnetized toroidal solenoid

The source describes a closely wound toroidal solenoid with cross-sectional
area `A`, mean radius `r`, `N` turns, winding current `i`, and a nonmagnetic
core.  The magnetic-flux density `B` is assumed uniform across the cross
section.  Physical scalar magnitudes are represented by Physlib dimensionful
quantities; real numbers occur only at coherent-SI readout boundaries and in
the printed multiple-choice data.

Assumption/target split:

* `MatchesPrimaryFigure` records the toroidal core, winding, cutaway area `A`,
  mean-radius arrow `r`, turn-count label `N`, and current arrows `i` visible in
  the primary bitmap.
* `MatchesProblemScenario` records the closely wound, nonmagnetic-core setup.
* `HasPhysicalParameters` supplies the positive geometry, turn count, test
  current, and vacuum permeability needed for the algebraic derivation.
* `SatisfiesToroidalSolenoidLaws` records uniformity of `B`, Ampere's law on
  the mean circular path, `Phi = B A`, flux linkage `lambda = N Phi`, and the
  defining relation `lambda = L i`.
* There are no previous-part results.
* Only the conclusion of `selfInductance_of_uniform_toroidal_solenoid` states
  the requested relation `L = mu_0 N^2 A / (2 pi r)`.

The source provides no numerical values for `A`, `r`, or `N`.  Consequently,
the recorded choice `C = 40 microhenries` is retained below as dataset
metadata, but is not asserted as a consequence of unavailable numerical data.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0922

open Dimension

/-! ## Physical dimensions and coherent-SI readouts -/

/-- Electric-current dimension `Q T⁻¹`. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Cross-sectional-area dimension `L²`. -/
def areaDimension : Dimension :=
  L𝓭 * L𝓭

/-- Magnetic-flux-density dimension `M T⁻¹ Q⁻¹` (tesla). -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic-flux dimension `M L² T⁻¹ Q⁻¹` (weber). -/
def magneticFluxDimension : Dimension :=
  magneticFluxDensityDimension * areaDimension

/-- Magnetic-permeability dimension `M L Q⁻²` (henry per metre). -/
def magneticPermeabilityDimension : Dimension :=
  M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- Inductance dimension `M L² Q⁻²` (henry). -/
def inductanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaQuantity : Type :=
  Dimensionful (WithDim areaDimension NNReal)

/-- A nonnegative winding-current magnitude. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative tangential magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative magnetic flux or flux-linkage magnitude. -/
abbrev MagneticFluxQuantity : Type :=
  Dimensionful (WithDim magneticFluxDimension NNReal)

/-- A nonnegative magnetic permeability. -/
abbrev MagneticPermeabilityQuantity : Type :=
  Dimensionful (WithDim magneticPermeabilityDimension NNReal)

/-- A nonnegative self-inductance. -/
abbrev InductanceQuantity : Type :=
  Dimensionful (WithDim inductanceDimension NNReal)

/-- Read any nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Square-metre readout of a physical area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  nonnegativeSIReadout area

/-- Ampere readout of a winding-current magnitude. -/
def currentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  nonnegativeSIReadout current

/-- Tesla readout of a tangential magnetic-flux-density magnitude. -/
def magneticFluxDensityInTeslas
    (field : MagneticFluxDensityQuantity) : ℝ :=
  nonnegativeSIReadout field

/-- Weber readout of magnetic flux or flux linkage. -/
def magneticFluxInWebers (flux : MagneticFluxQuantity) : ℝ :=
  nonnegativeSIReadout flux

/-- Henry-per-metre readout of magnetic permeability. -/
def permeabilityInHenriesPerMeter
    (permeability : MagneticPermeabilityQuantity) : ℝ :=
  nonnegativeSIReadout permeability

/-- Henry readout of self-inductance. -/
def inductanceInHenries (inductance : InductanceQuantity) : ℝ :=
  nonnegativeSIReadout inductance

/-! ## Figure vocabulary and physical setup -/

/-- Physical features explicitly visible in image `922.png`. -/
inductive FigureFeature where
  | toroidalCore
  | windingTurns
  | cutawayCrossSectionFace
  | dashedMeanRadiusArrow
  | currentDirectionArrows
  deriving DecidableEq, Fintype, Repr

/-- Mathematical labels printed in the primary figure. -/
inductive FigureLabel where
  | A
  | r
  | N
  | i
  deriving DecidableEq, Fintype, Repr

/-- Physical roles of the labels printed in the primary figure. -/
inductive FigureLabelRole where
  | crossSectionArea
  | meanRadius
  | totalTurnCount
  | windingCurrent
  deriving DecidableEq, Repr

/-- Literal and qualitative evidence transcribed from image `922.png`. -/
structure ToroidalSolenoidFigure where
  featureShown : FigureFeature → Bool
  labelShown : FigureLabel → Bool
  labelRole : FigureLabel → FigureLabelRole
  onlyAFewTurnsDrawn : Bool

/-- Magnetic behavior of the toroidal core material. -/
inductive CoreMaterial where
  | nonmagnetic
  | magnetic
  deriving DecidableEq, Repr

/-- Whether adjacent turns realize the closely wound idealization. -/
inductive WindingStyle where
  | closelyWound
  | separatedTurns
  deriving DecidableEq, Repr

/-- Sign convention for current relative to the purple arrows in the figure. -/
inductive CurrentOrientation where
  | alongDepictedArrows
  | oppositeDepictedArrows
  deriving DecidableEq, Repr

/-!
Independent physical quantities of the toroidal solenoid.  The abstract
`CrossSectionPoint` type lets field uniformity be stated without replacing the
cross section by a single scalar sample.  In particular, `selfInductance` is
not defined from either the requested formula or an answer choice.
-/
structure ToroidalSolenoidSetup (CrossSectionPoint : Type) where
  figure : ToroidalSolenoidFigure
  crossSectionAreaA : AreaQuantity
  meanRadiusR : LengthQuantity
  turnCountN : ℕ
  windingCurrentI : ElectricCurrentQuantity
  currentOrientation : CurrentOrientation
  coreMaterial : CoreMaterial
  coreRelativePermeability : ℝ
  windingStyle : WindingStyle
  vacuumPermeability : MagneticPermeabilityQuantity
  magneticFluxDensityB :
    CrossSectionPoint → MagneticFluxDensityQuantity
  referenceCrossSectionPoint : CrossSectionPoint
  magneticFluxPerTurn : MagneticFluxQuantity
  totalFluxLinkage : MagneticFluxQuantity
  selfInductance : InductanceQuantity

/-! ## Figure/data readouts and physical assumptions -/

/-- All labels and qualitative features read from the primary bitmap. -/
structure MatchesPrimaryFigure {CrossSectionPoint : Type}
    (setup : ToroidalSolenoidSetup CrossSectionPoint) : Prop where
  everyFeatureIsShown :
    ∀ feature : FigureFeature, setup.figure.featureShown feature = true
  everyLabelIsShown :
    ∀ label : FigureLabel, setup.figure.labelShown label = true
  labelAIsCrossSectionArea :
    setup.figure.labelRole .A = .crossSectionArea
  labelRIsMeanRadius :
    setup.figure.labelRole .r = .meanRadius
  labelNIsTotalTurnCount :
    setup.figure.labelRole .N = .totalTurnCount
  labelIIsWindingCurrent :
    setup.figure.labelRole .i = .windingCurrent
  fewTurnsAreRepresentative :
    setup.figure.onlyAFewTurnsDrawn = true
  positiveCurrentSenseFollowsArrows :
    setup.currentOrientation = .alongDepictedArrows

/-- Qualitative conditions stated in the problem text. -/
structure MatchesProblemScenario {CrossSectionPoint : Type}
    (setup : ToroidalSolenoidSetup CrossSectionPoint) : Prop where
  windingIsClose :
    setup.windingStyle = .closelyWound
  coreIsNonmagnetic :
    setup.coreMaterial = .nonmagnetic
  nonmagneticRelativePermeability :
    setup.coreRelativePermeability = 1

/-!
Physical nondegeneracy assumptions.  The positive test current is used only
to identify the inductance through `lambda = L i`; it does not prescribe the
requested value of `L`.
-/
structure HasPhysicalParameters {CrossSectionPoint : Type}
    (setup : ToroidalSolenoidSetup CrossSectionPoint) : Prop where
  crossSectionAreaPositive :
    0 < areaInSquareMeters setup.crossSectionAreaA
  meanRadiusPositive :
    0 < lengthInMeters setup.meanRadiusR
  turnCountPositive :
    0 < setup.turnCountN
  currentPositiveAlongFigureArrows :
    0 < currentInAmperes setup.windingCurrentI
  vacuumPermeabilityPositive :
    0 < permeabilityInHenriesPerMeter setup.vacuumPermeability

/-! ## Governing laws -/

/-!
The modeling relations used for a thin, closely wound toroid.  These are
governing laws and intermediate physical relations; none states the requested
closed form for self-inductance.
-/
structure SatisfiesToroidalSolenoidLaws {CrossSectionPoint : Type}
    (setup : ToroidalSolenoidSetup CrossSectionPoint) : Prop where
  magneticFieldUniformAcrossCrossSection :
    ∀ p q : CrossSectionPoint,
      setup.magneticFluxDensityB p = setup.magneticFluxDensityB q
  ampereLawOnMeanCircularPath :
    magneticFluxDensityInTeslas
          (setup.magneticFluxDensityB setup.referenceCrossSectionPoint) *
        (2 * Real.pi * lengthInMeters setup.meanRadiusR) =
      permeabilityInHenriesPerMeter setup.vacuumPermeability *
        setup.coreRelativePermeability * (setup.turnCountN : ℝ) *
        currentInAmperes setup.windingCurrentI
  fluxPerTurnFromUniformField :
    magneticFluxInWebers setup.magneticFluxPerTurn =
      magneticFluxDensityInTeslas
          (setup.magneticFluxDensityB setup.referenceCrossSectionPoint) *
        areaInSquareMeters setup.crossSectionAreaA
  fluxLinkageFromTurns :
    magneticFluxInWebers setup.totalFluxLinkage =
      (setup.turnCountN : ℝ) *
        magneticFluxInWebers setup.magneticFluxPerTurn
  selfInductanceDefinition :
    magneticFluxInWebers setup.totalFluxLinkage =
      inductanceInHenries setup.selfInductance *
        currentInAmperes setup.windingCurrentI

/-! ## Printed choices and recorded dataset answer -/

/-- Labels of the four printed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Printed answer magnitude in microhenries. -/
def answerInMicrohenries : AnswerChoice → ℝ
  | .A => 20
  | .B => 80
  | .C => 40
  | .D => 45

/-- Convert a printed microhenry magnitude to henries. -/
def answerInHenries (choice : AnswerChoice) : ℝ :=
  answerInMicrohenries choice * 10 ^ (-6 : ℤ)

/-- Dataset metadata records answer choice C; it is not a governing law. -/
def recordedAnswerChoice : AnswerChoice :=
  .C

/-! ## Requested self-inductance relation -/

/--
For a thin nonmagnetic toroid with field uniform across its cross section,
the self-inductance is `mu_0 N^2 A / (2 pi r)`.

This is the declaration corresponding to
`thm:physics:phyx_mini_0922:target`.
-/
theorem selfInductance_of_uniform_toroidal_solenoid
    {CrossSectionPoint : Type}
    (setup : ToroidalSolenoidSetup CrossSectionPoint)
    (hFigure : MatchesPrimaryFigure setup)
    (hScenario : MatchesProblemScenario setup)
    (hParameters : HasPhysicalParameters setup)
    (hLaws : SatisfiesToroidalSolenoidLaws setup) :
    inductanceInHenries setup.selfInductance =
      permeabilityInHenriesPerMeter setup.vacuumPermeability *
        (setup.turnCountN : ℝ) ^ 2 *
        areaInSquareMeters setup.crossSectionAreaA /
        (2 * Real.pi * lengthInMeters setup.meanRadiusR) := by
  have hAmpere :
      magneticFluxDensityInTeslas
            (setup.magneticFluxDensityB setup.referenceCrossSectionPoint) *
          (2 * Real.pi * lengthInMeters setup.meanRadiusR) =
        permeabilityInHenriesPerMeter setup.vacuumPermeability *
          (setup.turnCountN : ℝ) *
          currentInAmperes setup.windingCurrentI := by
    simpa [hScenario.nonmagneticRelativePermeability] using
      hLaws.ampereLawOnMeanCircularPath
  have hInductanceTimesCurrent :
      inductanceInHenries setup.selfInductance *
          currentInAmperes setup.windingCurrentI =
        (setup.turnCountN : ℝ) *
          (magneticFluxDensityInTeslas
              (setup.magneticFluxDensityB setup.referenceCrossSectionPoint) *
            areaInSquareMeters setup.crossSectionAreaA) := by
    calc
      inductanceInHenries setup.selfInductance *
            currentInAmperes setup.windingCurrentI =
          magneticFluxInWebers setup.totalFluxLinkage :=
        hLaws.selfInductanceDefinition.symm
      _ =
          (setup.turnCountN : ℝ) *
            magneticFluxInWebers setup.magneticFluxPerTurn :=
        hLaws.fluxLinkageFromTurns
      _ =
          (setup.turnCountN : ℝ) *
            (magneticFluxDensityInTeslas
                (setup.magneticFluxDensityB setup.referenceCrossSectionPoint) *
              areaInSquareMeters setup.crossSectionAreaA) := by
        rw [hLaws.fluxPerTurnFromUniformField]
  have hCurrentNonzero :
      currentInAmperes setup.windingCurrentI ≠ 0 :=
    ne_of_gt hParameters.currentPositiveAlongFigureArrows
  have hMeanPathNonzero :
      2 * Real.pi * lengthInMeters setup.meanRadiusR ≠ 0 := by
    exact
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (ne_of_gt hParameters.meanRadiusPositive)
  apply (eq_div_iff hMeanPathNonzero).2
  apply mul_right_cancel₀ hCurrentNonzero
  calc
    (inductanceInHenries setup.selfInductance *
          (2 * Real.pi * lengthInMeters setup.meanRadiusR)) *
        currentInAmperes setup.windingCurrentI =
      (inductanceInHenries setup.selfInductance *
          currentInAmperes setup.windingCurrentI) *
        (2 * Real.pi * lengthInMeters setup.meanRadiusR) := by
      ring
    _ =
      ((setup.turnCountN : ℝ) *
          (magneticFluxDensityInTeslas
              (setup.magneticFluxDensityB setup.referenceCrossSectionPoint) *
            areaInSquareMeters setup.crossSectionAreaA)) *
        (2 * Real.pi * lengthInMeters setup.meanRadiusR) := by
      rw [hInductanceTimesCurrent]
    _ =
      (setup.turnCountN : ℝ) *
        areaInSquareMeters setup.crossSectionAreaA *
        (magneticFluxDensityInTeslas
            (setup.magneticFluxDensityB setup.referenceCrossSectionPoint) *
          (2 * Real.pi * lengthInMeters setup.meanRadiusR)) := by
      ring
    _ =
      (setup.turnCountN : ℝ) *
        areaInSquareMeters setup.crossSectionAreaA *
        (permeabilityInHenriesPerMeter setup.vacuumPermeability *
          (setup.turnCountN : ℝ) *
          currentInAmperes setup.windingCurrentI) := by
      rw [hAmpere]
    _ =
      (permeabilityInHenriesPerMeter setup.vacuumPermeability *
          (setup.turnCountN : ℝ) ^ 2 *
          areaInSquareMeters setup.crossSectionAreaA) *
        currentInAmperes setup.windingCurrentI := by
      ring

end PhyXMiniProblems.ProblemPhyXMini0922
