import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.Electromagnetism.Dynamics.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0849

open Dimension

/-!
# Electric field at three points of a negatively charged conducting box

The supplied image shows point 1 immediately outside the center of the top
surface, point 2 in the conducting material, and point 3 in the empty cavity.
The source reports an excess-electron surface number density of
`5.0 * 10^10 m^-2` at the top center.

Physical field vectors, charge densities, and constants are kept separate
from their coherent-SI real-number readouts.  The field is also connected to
Physlib's `Electromagnetism.ElectricField`.

Assumption/target split:

* governing laws: excess-electron number density determines signed surface
  charge density, the exterior conductor boundary condition is
  `E = (sigma / epsilon_0) n`, and the field vanishes in equilibrated
  conducting material and in an enclosed charge-free cavity;
* previous-part results: none;
* figure/data readouts: the hollow negatively charged conductor, charge-free
  cavity, locations of points 1--3, top-center density `5.0 * 10^10 m^-2`,
  elementary charge, and vacuum permittivity;
* current target: point 1 rounds to `900 N/C`, points 2 and 3 have zero field
  strength, and the recorded answer D is the unique displayed match.
-/

/-! ## Dimensions, physical quantities, and SI readouts -/

/-- The dimension `L^-2` of a surface number density. -/
def surfaceNumberDensityDimension : Dimension :=
  L𝓭⁻¹ * L𝓭⁻¹

/-- The dimension `C L^-2` of a signed surface charge density. -/
def surfaceChargeDensityDimension : Dimension :=
  C𝓭 * L𝓭⁻¹ * L𝓭⁻¹

/-- The dimension `C^2 T^2 M^-1 L^-3` of vacuum permittivity. -/
def vacuumPermittivityDimension : Dimension :=
  C𝓭 * C𝓭 * T𝓭 * T𝓭 * M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The dimension `M L T^-2 C^-1` of an electric field. -/
def electricFieldDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative physical count of electrons per unit area. -/
abbrev SurfaceElectronNumberDensityQuantity : Type :=
  Dimensionful (WithDim surfaceNumberDensityDimension NNReal)

/-- A nonnegative physical magnitude of electric charge. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A signed physical surface charge density. -/
abbrev SignedSurfaceChargeDensityQuantity : Type :=
  Dimensionful (WithDim surfaceChargeDensityDimension ℝ)

/-- A nonnegative physical vacuum permittivity. -/
abbrev VacuumPermittivityQuantity : Type :=
  Dimensionful (WithDim vacuumPermittivityDimension NNReal)

/-- A physical electric-field vector in three-dimensional space. -/
abbrev ElectricFieldVectorQuantity : Type :=
  Dimensionful
    (WithDim electricFieldDimension (EuclideanSpace ℝ (Fin 3)))

/-- Coherent-SI readout in electrons per square metre. -/
def surfaceElectronNumberDensityPerSquareMeter
    (density : SurfaceElectronNumberDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a charge magnitude in coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of signed surface charge in coulombs per square metre. -/
def signedSurfaceChargeDensityInCoulombsPerSquareMeter
    (density : SignedSurfaceChargeDensityQuantity) : ℝ :=
  (density UnitChoices.SI).val

/-- Coherent-SI readout of vacuum permittivity in farads per metre. -/
def vacuumPermittivityInFaradsPerMeter
    (permittivity : VacuumPermittivityQuantity) : ℝ :=
  ((permittivity UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of an electric-field vector in newtons per coulomb. -/
def electricFieldVectorInNewtonsPerCoulomb
    (field : ElectricFieldVectorQuantity) : EuclideanSpace ℝ (Fin 3) :=
  (field UnitChoices.SI).val

/-!
Physlib provides the elementary charge as a `ChargeUnit`, rather than as a
dimensionful charge quantity.  Its ratio to the coulomb calibrates the
independent physical magnitude in the setup.
-/
def physlibElementaryChargeMagnitudeInCoulombs : ℝ :=
  ((ChargeUnit.elementaryCharge / ChargeUnit.coulombs : NNReal) : ℝ)

/-! ## Figure labels and physical setup -/

/-- The three numbered black dots in image 849. -/
inductive FigurePoint where
  | point1
  | point2
  | point3
  deriving DecidableEq, Fintype, Repr

/-- The qualitative region occupied by a labelled dot in the image. -/
inductive FigureRegion where
  | exteriorAdjacentToTopCenter
  | conductingMaterial
  | emptyInnerCavity
  deriving DecidableEq, Repr

/-- The surface location at which the electron density is reported. -/
inductive SurfaceSampleLocation where
  | topSurfaceCenter
  | other
  deriving DecidableEq, Repr

/-- The sign of the box's excess charge. -/
inductive ExcessChargeSign where
  | negative
  | zero
  | positive
  deriving DecidableEq, Repr

/-- The electrostatic idealization used for the conducting box. -/
inductive ElectrostaticModel where
  | hollowConductorInVacuum
  | other
  deriving DecidableEq, Repr

/-!
Literal qualitative information carried by image 849.  Gray material is the
conductor and the centered white rectangle is its cavity.
-/
structure ConductingBoxFigure where
  showsOuterConductingRectangle : Bool
  showsCenteredInnerCavityRectangle : Bool
  innerRectangleContainedInOuter : Bool
  showsPoint : FigurePoint → Bool
  regionOf : FigurePoint → FigureRegion

/-!
Independent physical data for the box.  No requested field strength, answer
choice, or rounding interval is stored in this setup.
-/
structure ConductingBoxSetup where
  model : ElectrostaticModel
  atElectrostaticEquilibrium : Bool
  cavityContainsCharge : Bool
  excessChargeSign : ExcessChargeSign
  surfaceSampleLocation : SurfaceSampleLocation
  surfaceElectronNumberDensity : SurfaceElectronNumberDensityQuantity
  elementaryChargeMagnitude : ChargeMagnitudeQuantity
  topSurfaceChargeDensity : SignedSurfaceChargeDensityQuantity
  vacuumPermittivity : VacuumPermittivityQuantity
  freeSpace : Electromagnetism.FreeSpace
  fieldVectorAt : FigurePoint → ElectricFieldVectorQuantity
  electricField : Electromagnetism.ElectricField 3
  observationTime : Time
  pointPosition : FigurePoint → Space 3
  topOutwardUnitNormal : EuclideanSpace ℝ (Fin 3)
  figure : ConductingBoxFigure

/-! ## Assumptions: scenario, reported data, figure, constants, and laws -/

/-- Qualitative physical assumptions stated or implied by the problem. -/
structure MatchesConductingBoxScenario (setup : ConductingBoxSetup) : Prop where
  hollowConductorInVacuum : setup.model = .hollowConductorInVacuum
  electrostaticEquilibrium : setup.atElectrostaticEquilibrium = true
  chargeFreeCavity : setup.cavityContainsCharge = false
  negativeExcessCharge : setup.excessChargeSign = .negative
  densitySampledAtTopCenter :
    setup.surfaceSampleLocation = .topSurfaceCenter

/-!
The sole numerical datum in the question: the top-center density is
`5.0 * 10^10` excess electrons per square metre.
-/
structure MatchesReportedSurfaceDensityData
    (setup : ConductingBoxSetup) : Prop where
  topCenterElectronDensity :
    surfaceElectronNumberDensityPerSquareMeter
        setup.surfaceElectronNumberDensity =
      (5 : ℝ) * 10 ^ 10

/-- Primary-image readout of the outer box, inner cavity, and three dots. -/
structure MatchesSuppliedConductingBoxFigure
    (setup : ConductingBoxSetup) : Prop where
  outerConductorShown :
    setup.figure.showsOuterConductingRectangle = true
  centeredCavityShown :
    setup.figure.showsCenteredInnerCavityRectangle = true
  cavityInsideConductor :
    setup.figure.innerRectangleContainedInOuter = true
  everyNumberedPointShown :
    ∀ point, setup.figure.showsPoint point = true
  point1OutsideAboveTopCenter :
    setup.figure.regionOf .point1 = .exteriorAdjacentToTopCenter
  point2InsideConductingMaterial :
    setup.figure.regionOf .point2 = .conductingMaterial
  point3InsideEmptyCavity :
    setup.figure.regionOf .point3 = .emptyInnerCavity

/-!
Calibration of the independent dimensionful constants.  The elementary
charge is tied to Physlib's unit-scale declaration.  Vacuum permittivity is
tied to Physlib's positive `FreeSpace.ε₀` and its standard SI value.  None of
these fields contains a requested electric-field answer.
-/
structure UsesStandardElectrostaticConstants
    (setup : ConductingBoxSetup) : Prop where
  elementaryChargeCalibration :
    chargeMagnitudeInCoulombs setup.elementaryChargeMagnitude =
      physlibElementaryChargeMagnitudeInCoulombs
  permittivityAgreesWithPhyslib :
    vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity =
      setup.freeSpace.ε₀
  standardVacuumPermittivity :
    setup.freeSpace.ε₀ = (88541878128 : ℝ) / 10 ^ 22

/-- Nondegeneracy conditions needed by the boundary calculation. -/
structure HasPhysicalConductingBoxParameters
    (setup : ConductingBoxSetup) : Prop where
  electronDensityPositive :
    0 < surfaceElectronNumberDensityPerSquareMeter
      setup.surfaceElectronNumberDensity
  elementaryChargePositive :
    0 < chargeMagnitudeInCoulombs setup.elementaryChargeMagnitude
  vacuumPermittivityPositive :
    0 < vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity
  topNormalHasUnitLength : ‖setup.topOutwardUnitNormal‖ = 1

/-!
The governing electrostatic laws used by the solution:

* excess electrons give the signed density `sigma = -n e`;
* immediately outside an equilibrated conductor, `E = (sigma/epsilon_0) n`;
* the field vanishes in conducting material at equilibrium;
* an enclosed charge-free cavity is electrostatically shielded.

The laws are generic over points having the relevant region role.  They do
not state the requested numerical field strengths at points 1--3.
-/
structure SatisfiesConductingBoxElectrostatics
    (setup : ConductingBoxSetup) : Prop where
  dimensionfulFieldAgreesWithPhyslib : ∀ point,
    electricFieldVectorInNewtonsPerCoulomb (setup.fieldVectorAt point) =
      setup.electricField setup.observationTime (setup.pointPosition point)
  surfaceChargeFromExcessElectrons :
    setup.excessChargeSign = .negative →
      signedSurfaceChargeDensityInCoulombsPerSquareMeter
          setup.topSurfaceChargeDensity =
        -(surfaceElectronNumberDensityPerSquareMeter
            setup.surfaceElectronNumberDensity *
          chargeMagnitudeInCoulombs setup.elementaryChargeMagnitude)
  exteriorSurfaceBoundaryCondition : ∀ point,
    setup.model = .hollowConductorInVacuum →
    setup.atElectrostaticEquilibrium = true →
    setup.figure.regionOf point = .exteriorAdjacentToTopCenter →
      electricFieldVectorInNewtonsPerCoulomb (setup.fieldVectorAt point) =
        (signedSurfaceChargeDensityInCoulombsPerSquareMeter
            setup.topSurfaceChargeDensity /
          vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity) •
            setup.topOutwardUnitNormal
  fieldVanishesInConductingMaterial : ∀ point,
    setup.model = .hollowConductorInVacuum →
    setup.atElectrostaticEquilibrium = true →
    setup.figure.regionOf point = .conductingMaterial →
      electricFieldVectorInNewtonsPerCoulomb (setup.fieldVectorAt point) = 0
  fieldVanishesInChargeFreeCavity : ∀ point,
    setup.model = .hollowConductorInVacuum →
    setup.atElectrostaticEquilibrium = true →
    setup.cavityContainsCharge = false →
    setup.figure.regionOf point = .emptyInnerCavity →
      electricFieldVectorInNewtonsPerCoulomb (setup.fieldVectorAt point) = 0

/-! ## Requested strengths and answer choices -/

/-- Field strength at a labelled dot, in newtons per coulomb. -/
def electricFieldStrengthInNewtonsPerCoulomb
    (setup : ConductingBoxSetup) (point : FigurePoint) : ℝ :=
  ‖electricFieldVectorInNewtonsPerCoulomb (setup.fieldVectorAt point)‖

/-- The four answer labels printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
The answer strings contain the dimensionally inconsistent text `N m^2/C`.
Because the question asks for electric-field strength, their numeric values
are modeled with the physically compatible unit `N/C`.
-/
def displayedExteriorFieldStrengthInNewtonsPerCoulomb : AnswerChoice → ℝ
  | .A => 800
  | .B => 1000
  | .C => 200
  | .D => 900

/-- Resolution implied by choices spaced in hundreds of newtons per coulomb. -/
def displayedResolutionInNewtonsPerCoulomb (_ : AnswerChoice) : ℝ := 100

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A physical readout rounds to a display at a stated positive resolution. -/
def RoundsToNearestResolution
    (value displayed resolution : ℝ) : Prop :=
  0 < resolution ∧ |value - displayed| ≤ resolution / 2

/-- A choice matches the rounded strength immediately outside the box. -/
def AnswerMatchesExteriorField
    (setup : ConductingBoxSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestResolution
    (electricFieldStrengthInNewtonsPerCoulomb setup .point1)
    (displayedExteriorFieldStrengthInNewtonsPerCoulomb choice)
    (displayedResolutionInNewtonsPerCoulomb choice)

/-- A choice is the unique displayed match for the exterior field strength. -/
def IsUniqueMatchingAnswer
    (setup : ConductingBoxSetup) (choice : AnswerChoice) : Prop :=
  AnswerMatchesExteriorField setup choice ∧
    ∀ other, AnswerMatchesExteriorField setup other → other = choice

/-!
The exterior field obtained from `n e / epsilon_0` lies within the rounding
interval for `900 N/C`.  This is an intermediate derived result rather than
an assumption.
-/
lemma point1_field_strength_rounding_bounds
    (setup : ConductingBoxSetup)
    (_hScenario : MatchesConductingBoxScenario setup)
    (_hData : MatchesReportedSurfaceDensityData setup)
    (_hFigure : MatchesSuppliedConductingBoxFigure setup)
    (_hConstants : UsesStandardElectrostaticConstants setup)
    (_hPhysical : HasPhysicalConductingBoxParameters setup)
    (_hLaws : SatisfiesConductingBoxElectrostatics setup) :
    850 ≤ electricFieldStrengthInNewtonsPerCoulomb setup .point1 ∧
      electricFieldStrengthInNewtonsPerCoulomb setup .point1 ≤ 950 := by
  have hElementaryCharge :
      physlibElementaryChargeMagnitudeInCoulombs =
        (1602176634 : ℝ) / 10 ^ 28 := by
    norm_num [physlibElementaryChargeMagnitudeInCoulombs,
      ChargeUnit.elementaryCharge, ChargeUnit.scale, ChargeUnit.coulombs,
      ChargeUnit.div_eq_val]
    rfl
  have hCharge :
      chargeMagnitudeInCoulombs setup.elementaryChargeMagnitude =
        (1602176634 : ℝ) / 10 ^ 28 :=
    _hConstants.elementaryChargeCalibration.trans hElementaryCharge
  have hPermittivity :
      vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity =
        (88541878128 : ℝ) / 10 ^ 22 :=
    _hConstants.permittivityAgreesWithPhyslib.trans
      _hConstants.standardVacuumPermittivity
  have hSurfaceCharge :=
    _hLaws.surfaceChargeFromExcessElectrons
      _hScenario.negativeExcessCharge
  have hFieldVector :=
    _hLaws.exteriorSurfaceBoundaryCondition .point1
      _hScenario.hollowConductorInVacuum
      _hScenario.electrostaticEquilibrium
      _hFigure.point1OutsideAboveTopCenter
  have hFieldStrength :
      electricFieldStrengthInNewtonsPerCoulomb setup .point1 =
        |(-((5 : ℝ) * 10 ^ 10 *
            ((1602176634 : ℝ) / 10 ^ 28))) /
          ((88541878128 : ℝ) / 10 ^ 22)| := by
    rw [electricFieldStrengthInNewtonsPerCoulomb, hFieldVector, norm_smul,
      Real.norm_eq_abs, _hPhysical.topNormalHasUnitLength, mul_one,
      hSurfaceCharge, _hData.topCenterElectronDensity, hCharge,
      hPermittivity]
  rw [hFieldStrength]
  norm_num [abs_of_neg]

/-!
**Blueprint target** `thm:physics:phyx_mini_0849:target`.

Point 1 has strength `900 N/C` to the precision of the displayed choices.
Point 2 lies in the conductor and point 3 in its charge-free cavity, so both
have zero field strength.  The nonzero value uniquely selects recorded
answer D.  None of these conclusions occurs in a hypothesis.
-/
theorem problem_phyx_mini_0849
    (setup : ConductingBoxSetup)
    (_hScenario : MatchesConductingBoxScenario setup)
    (_hData : MatchesReportedSurfaceDensityData setup)
    (_hFigure : MatchesSuppliedConductingBoxFigure setup)
    (_hConstants : UsesStandardElectrostaticConstants setup)
    (_hPhysical : HasPhysicalConductingBoxParameters setup)
    (_hLaws : SatisfiesConductingBoxElectrostatics setup) :
    RoundsToNearestResolution
        (electricFieldStrengthInNewtonsPerCoulomb setup .point1)
        900 100 ∧
      electricFieldStrengthInNewtonsPerCoulomb setup .point2 = 0 ∧
      electricFieldStrengthInNewtonsPerCoulomb setup .point3 = 0 ∧
      IsUniqueMatchingAnswer setup recordedDatasetAnswer := by
  have hBounds :=
    point1_field_strength_rounding_bounds setup _hScenario _hData _hFigure
      _hConstants _hPhysical _hLaws
  have hRounded :
      RoundsToNearestResolution
        (electricFieldStrengthInNewtonsPerCoulomb setup .point1)
        900 100 := by
    rw [RoundsToNearestResolution]
    constructor
    · norm_num
    · rw [abs_le]
      constructor <;> linarith [hBounds.1, hBounds.2]
  have hElementaryCharge :
      physlibElementaryChargeMagnitudeInCoulombs =
        (1602176634 : ℝ) / 10 ^ 28 := by
    norm_num [physlibElementaryChargeMagnitudeInCoulombs,
      ChargeUnit.elementaryCharge, ChargeUnit.scale, ChargeUnit.coulombs,
      ChargeUnit.div_eq_val]
    rfl
  have hCharge :
      chargeMagnitudeInCoulombs setup.elementaryChargeMagnitude =
        (1602176634 : ℝ) / 10 ^ 28 :=
    _hConstants.elementaryChargeCalibration.trans hElementaryCharge
  have hPermittivity :
      vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity =
        (88541878128 : ℝ) / 10 ^ 22 :=
    _hConstants.permittivityAgreesWithPhyslib.trans
      _hConstants.standardVacuumPermittivity
  have hSurfaceCharge :=
    _hLaws.surfaceChargeFromExcessElectrons
      _hScenario.negativeExcessCharge
  have hFieldVector1 :=
    _hLaws.exteriorSurfaceBoundaryCondition .point1
      _hScenario.hollowConductorInVacuum
      _hScenario.electrostaticEquilibrium
      _hFigure.point1OutsideAboveTopCenter
  have hFieldStrength :
      electricFieldStrengthInNewtonsPerCoulomb setup .point1 =
        |(-((5 : ℝ) * 10 ^ 10 *
            ((1602176634 : ℝ) / 10 ^ 28))) /
          ((88541878128 : ℝ) / 10 ^ 22)| := by
    rw [electricFieldStrengthInNewtonsPerCoulomb, hFieldVector1, norm_smul,
      Real.norm_eq_abs, _hPhysical.topNormalHasUnitLength, mul_one,
      hSurfaceCharge, _hData.topCenterElectronDensity, hCharge,
      hPermittivity]
  have hStrictBounds :
      850 < electricFieldStrengthInNewtonsPerCoulomb setup .point1 ∧
        electricFieldStrengthInNewtonsPerCoulomb setup .point1 < 950 := by
    rw [hFieldStrength]
    norm_num [abs_of_neg]
  have hFieldVector2 :=
    _hLaws.fieldVanishesInConductingMaterial .point2
      _hScenario.hollowConductorInVacuum
      _hScenario.electrostaticEquilibrium
      _hFigure.point2InsideConductingMaterial
  have hPoint2 :
      electricFieldStrengthInNewtonsPerCoulomb setup .point2 = 0 := by
    simp [electricFieldStrengthInNewtonsPerCoulomb, hFieldVector2]
  have hFieldVector3 :=
    _hLaws.fieldVanishesInChargeFreeCavity .point3
      _hScenario.hollowConductorInVacuum
      _hScenario.electrostaticEquilibrium
      _hScenario.chargeFreeCavity
      _hFigure.point3InsideEmptyCavity
  have hPoint3 :
      electricFieldStrengthInNewtonsPerCoulomb setup .point3 = 0 := by
    simp [electricFieldStrengthInNewtonsPerCoulomb, hFieldVector3]
  have hUnique :
      IsUniqueMatchingAnswer setup recordedDatasetAnswer := by
    constructor
    · simpa [AnswerMatchesExteriorField, recordedDatasetAnswer,
        displayedExteriorFieldStrengthInNewtonsPerCoulomb,
        displayedResolutionInNewtonsPerCoulomb] using hRounded
    · intro other hOther
      cases other with
      | A =>
          have hOther' :
              |electricFieldStrengthInNewtonsPerCoulomb setup .point1 -
                800| ≤ (100 : ℝ) / 2 := by
            simpa [AnswerMatchesExteriorField, RoundsToNearestResolution,
              displayedExteriorFieldStrengthInNewtonsPerCoulomb,
              displayedResolutionInNewtonsPerCoulomb] using hOther
          norm_num at hOther'
          rw [abs_le] at hOther'
          linarith [hStrictBounds.1, hOther'.2]
      | B =>
          have hOther' :
              |electricFieldStrengthInNewtonsPerCoulomb setup .point1 -
                1000| ≤ (100 : ℝ) / 2 := by
            simpa [AnswerMatchesExteriorField, RoundsToNearestResolution,
              displayedExteriorFieldStrengthInNewtonsPerCoulomb,
              displayedResolutionInNewtonsPerCoulomb] using hOther
          norm_num at hOther'
          rw [abs_le] at hOther'
          linarith [hStrictBounds.2, hOther'.1]
      | C =>
          have hOther' :
              |electricFieldStrengthInNewtonsPerCoulomb setup .point1 -
                200| ≤ (100 : ℝ) / 2 := by
            simpa [AnswerMatchesExteriorField, RoundsToNearestResolution,
              displayedExteriorFieldStrengthInNewtonsPerCoulomb,
              displayedResolutionInNewtonsPerCoulomb] using hOther
          norm_num at hOther'
          rw [abs_le] at hOther'
          linarith [hStrictBounds.1, hOther'.2]
      | D => rfl
  exact ⟨hRounded, hPoint2, hPoint3, hUnique⟩

end PhyXMiniProblems.ProblemPhyXMini0849
