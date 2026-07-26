import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0630

open Dimension

/-!
# Depletion depth in a silicon p-n junction

The primary figure places p-type silicon on the left and n-type silicon on
the right.  Its depletion-region landmarks are labelled `-a_p`, `0`, and
`a_n`, and the total depletion width is labelled `W`.  Ionized acceptors on
the depleted p side are shown with minus signs, while ionized donors on the
depleted n side are shown with plus signs.

The problem asks for the p-side depletion depth when the acceptor density is
`1.00 * 10^16 cm^-3`, the donor density is `5.00 * 10^16 cm^-3`, and the
n-side depletion depth is `55.0 nm`.  The governing equilibrium law is charge
neutrality per unit junction area, not a supplied value of `a_p`.

Assumption/target split:

* governing laws: the depletion approximation, fixed-ion charge densities,
  vanishing charge outside the depleted region, the leftward electric-field
  direction, and equilibrium charge neutrality;
* previous-part results: none;
* figure/data readouts: material and dopant identities, the three boundary
  labels, charge signs, `N_A`, `N_D`, and `a_n`;
* current target: `a_p = 275 nm` and hence answer choice A.

Dimensionful physical quantities use Physlib's unit-independent `WithDim`
infrastructure.  Real numbers occur only as explicitly named unit readouts,
schematic image coordinates, and dimensionless answer-choice data.
-/

/-! ## Dimensionful physical quantities and calibrated readouts -/

/-- The inverse-volume dimension carried by a number density. -/
def inverseVolumeDimension : Dimension :=
  L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The dimension of electric charge per unit volume. -/
def chargeDensityDimension : Dimension :=
  C𝓭 * inverseVolumeDimension

/-- The dimension of energy. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The dimension of one Cartesian component of an electric field. -/
def electricFieldDimension : Dimension :=
  energyDimension * C𝓭⁻¹ * L𝓭⁻¹

/-- A nonnegative physical length, used for depletion depths and widths. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical coordinate on the junction axis. -/
abbrev SignedAxialPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative atom or mobile-carrier number density. -/
abbrev NumberDensityQuantity : Type :=
  Dimensionful (WithDim inverseVolumeDimension NNReal)

/-- A nonnegative magnitude of electric charge. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A signed volume charge density. -/
abbrev ChargeDensityQuantity : Type :=
  Dimensionful (WithDim chargeDensityDimension ℝ)

/-- A signed x-component of the electric field. -/
abbrev AxialElectricFieldQuantity : Type :=
  Dimensionful (WithDim electricFieldDimension ℝ)

/-- Read a nonnegative physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed axial coordinate in the selected length unit. -/
def signedPositionReadout
    (unit : LengthUnit) (position : SignedAxialPositionQuantity) : ℝ :=
  (position {UnitChoices.SI with length := unit}).val

/-- Read a physical number density in inverse cubes of the selected unit. -/
def numberDensityReadout
    (unit : LengthUnit) (density : NumberDensityQuantity) : ℝ :=
  ((density {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a charge density in coulombs per cube of the selected length unit. -/
def chargeDensityReadout
    (unit : LengthUnit) (density : ChargeDensityQuantity) : ℝ :=
  (density {UnitChoices.SI with length := unit}).val

/-- Coulomb readout of a nonnegative physical charge magnitude. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a signed electric-field component. -/
def axialElectricFieldInVoltsPerMeter
    (field : AxialElectricFieldQuantity) : ℝ :=
  (field UnitChoices.SI).val

/-- Nanometre readout used for the supplied depth and answer choices. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Nanometre readout of a signed axial coordinate. -/
def signedPositionInNanometers
    (position : SignedAxialPositionQuantity) : ℝ :=
  signedPositionReadout LengthUnit.nanometers position

/-- Centimetre readout used in the areal charge-neutrality law. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Atom-density readout in the `cm^-3` units stated in the problem. -/
def numberDensityPerCubicCentimeter
    (density : NumberDensityQuantity) : ℝ :=
  numberDensityReadout LengthUnit.centimeters density

/-- Charge-density readout in coulombs per cubic centimetre. -/
def chargeDensityInCoulombsPerCubicCentimeter
    (density : ChargeDensityQuantity) : ℝ :=
  chargeDensityReadout LengthUnit.centimeters density

/-! ## Physical, geometric, and primary-figure labels -/

/-- The two sides of the junction. -/
inductive SemiconductorSide where
  | pSide
  | nSide
  deriving DecidableEq, Fintype, Repr

/-- Conductivity types named in the source. -/
inductive ConductivityType where
  | pType
  | nType
  deriving DecidableEq, Fintype, Repr

/-- Semiconductor material used on both sides. -/
inductive SemiconductorMaterial where
  | silicon
  deriving DecidableEq, Fintype, Repr

/-- Dopant species supplied in the numerical question. -/
inductive DopantSpecies where
  | boron
  | arsenic
  deriving DecidableEq, Fintype, Repr

/-- Mobile charge carriers excluded from the depletion region. -/
inductive MobileCarrier where
  | electron
  | hole
  deriving DecidableEq, Fintype, Repr

/-- Signs of the fixed ions drawn in the two depleted regions. -/
inductive FixedChargeSign where
  | negative
  | positive
  deriving DecidableEq, Fintype, Repr

/-- The positive x-axis points from the p side toward the n side. -/
inductive AxialDirection where
  | fromPToN
  | fromNToP
  deriving DecidableEq, Fintype, Repr

/-- The three physical landmarks labelled along the bottom of the figure. -/
inductive JunctionLandmark where
  | pDepletionBoundary
  | metallurgicalJunction
  | nDepletionBoundary
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative evidence in image `630.png`.  The horizontal coordinates record
only visual ordering; the image does not provide a quantitative spatial scale.
-/
structure PNJunctionFigure where
  sideText : SemiconductorSide → String
  landmarkText : JunctionLandmark → String
  horizontalCoordinate : JunctionLandmark → ℝ
  fixedIonSign : SemiconductorSide → FixedChargeSign
  depletionWidthText : String
  terminalLeadShown : SemiconductorSide → Bool
  hasQuantitativeSpatialScale : Bool

/-!
Independent physical quantities for the junction.  In particular,
`pSideDepletionDepth` is not defined using an answer value.  The charge and
field profiles are physical fields over dimensionful axial positions.
-/
structure PNJunctionSetup where
  material : SemiconductorSide → SemiconductorMaterial
  conductivityType : SemiconductorSide → ConductivityType
  dopant : SemiconductorSide → DopantSpecies
  acceptorAtomDensity : NumberDensityQuantity
  donorAtomDensity : NumberDensityQuantity
  pSideDepletionDepth : LengthQuantity
  nSideDepletionDepth : LengthQuantity
  totalDepletionWidth : LengthQuantity
  boundaryPosition : JunctionLandmark → SignedAxialPositionQuantity
  freeCarrierNumberDensity :
    MobileCarrier → SignedAxialPositionQuantity → NumberDensityQuantity
  fixedChargeDensity :
    SignedAxialPositionQuantity → ChargeDensityQuantity
  axialElectricField :
    SignedAxialPositionQuantity → AxialElectricFieldQuantity
  elementaryChargeMagnitude : ChargeMagnitudeQuantity
  positiveXAxisDirection : AxialDirection
  figure : PNJunctionFigure

/-! ## Regions on the one-dimensional junction axis -/

/-- A position is in the depleted p side, from `-a_p` up to the junction. -/
def InPSideDepletion
    (setup : PNJunctionSetup) (position : SignedAxialPositionQuantity) : Prop :=
  -lengthInNanometers setup.pSideDepletionDepth ≤
      signedPositionInNanometers position ∧
    signedPositionInNanometers position < 0

/-- A position is in the depleted n side, from the junction through `a_n`. -/
def InNSideDepletion
    (setup : PNJunctionSetup) (position : SignedAxialPositionQuantity) : Prop :=
  0 ≤ signedPositionInNanometers position ∧
    signedPositionInNanometers position ≤
      lengthInNanometers setup.nSideDepletionDepth

/-- The complete depletion region is the union of its p and n parts. -/
def InDepletionRegion
    (setup : PNJunctionSetup) (position : SignedAxialPositionQuantity) : Prop :=
  InPSideDepletion setup position ∨ InNSideDepletion setup position

/-- A position lies strictly outside the two depleted slabs. -/
def OutsideDepletionRegion
    (setup : PNJunctionSetup) (position : SignedAxialPositionQuantity) : Prop :=
  signedPositionInNanometers position <
      -lengthInNanometers setup.pSideDepletionDepth ∨
    lengthInNanometers setup.nSideDepletionDepth <
      signedPositionInNanometers position

/-! ## Stated problem data and primary-image evidence -/

/-!
Material identities, dopants, orientation, numerical inputs, and the geometry
encoded by the labels `-a_p`, `0`, `a_n`, and `W`.  No numerical p-side depth
occurs in this interface.
-/
structure MatchesProblemData (setup : PNJunctionSetup) : Prop where
  pSideIsSilicon : setup.material .pSide = .silicon
  nSideIsSilicon : setup.material .nSide = .silicon
  pSideConductivity : setup.conductivityType .pSide = .pType
  nSideConductivity : setup.conductivityType .nSide = .nType
  pSideDopedWithBoron : setup.dopant .pSide = .boron
  nSideDopedWithArsenic : setup.dopant .nSide = .arsenic
  xAxisPointsFromPToN : setup.positiveXAxisDirection = .fromPToN
  acceptorDensityPerCubicCentimeter :
    numberDensityPerCubicCentimeter setup.acceptorAtomDensity =
      (10 : ℝ) ^ 16
  donorDensityPerCubicCentimeter :
    numberDensityPerCubicCentimeter setup.donorAtomDensity =
      5 * (10 : ℝ) ^ 16
  nSideDepthNanometers :
    lengthInNanometers setup.nSideDepletionDepth = 55
  pBoundaryCoordinate :
    signedPositionInNanometers
        (setup.boundaryPosition .pDepletionBoundary) =
      -lengthInNanometers setup.pSideDepletionDepth
  junctionAtOrigin :
    signedPositionInNanometers
        (setup.boundaryPosition .metallurgicalJunction) = 0
  nBoundaryCoordinate :
    signedPositionInNanometers
        (setup.boundaryPosition .nDepletionBoundary) =
      lengthInNanometers setup.nSideDepletionDepth
  depletionWidthGeometry :
    lengthInNanometers setup.totalDepletionWidth =
      lengthInNanometers setup.pSideDepletionDepth +
        lengthInNanometers setup.nSideDepletionDepth

/-- Exact labels, signs, and left-to-right ordering visible in `630.png`. -/
structure MatchesPrimaryFigure (setup : PNJunctionSetup) : Prop where
  pSideText : setup.figure.sideText .pSide = "p"
  nSideText : setup.figure.sideText .nSide = "n"
  pBoundaryText :
    setup.figure.landmarkText .pDepletionBoundary = "-a_p"
  junctionText :
    setup.figure.landmarkText .metallurgicalJunction = "0"
  nBoundaryText :
    setup.figure.landmarkText .nDepletionBoundary = "a_n"
  widthText : setup.figure.depletionWidthText = "W"
  pSideFixedIonsAreNegative :
    setup.figure.fixedIonSign .pSide = .negative
  nSideFixedIonsArePositive :
    setup.figure.fixedIonSign .nSide = .positive
  pBoundaryLeftOfJunction :
    setup.figure.horizontalCoordinate .pDepletionBoundary <
      setup.figure.horizontalCoordinate .metallurgicalJunction
  junctionLeftOfNBoundary :
    setup.figure.horizontalCoordinate .metallurgicalJunction <
      setup.figure.horizontalCoordinate .nDepletionBoundary
  pTerminalLeadShown : setup.figure.terminalLeadShown .pSide = true
  nTerminalLeadShown : setup.figure.terminalLeadShown .nSide = true
  schematicNotToScale : setup.figure.hasQuantitativeSpatialScale = false

/-- Positivity conditions selecting a nondegenerate physical junction. -/
structure HasPhysicalParameters (setup : PNJunctionSetup) : Prop where
  acceptorDensityPositive :
    0 < numberDensityPerCubicCentimeter setup.acceptorAtomDensity
  donorDensityPositive :
    0 < numberDensityPerCubicCentimeter setup.donorAtomDensity
  pSideDepthPositive : 0 < lengthInNanometers setup.pSideDepletionDepth
  nSideDepthPositive : 0 < lengthInNanometers setup.nSideDepletionDepth
  elementaryChargePositive :
    0 < chargeMagnitudeInCoulombs setup.elementaryChargeMagnitude

/-! ## Governing depletion-region physics -/

/-!
The depletion approximation and equilibrium neutrality law.  The two fixed
charge-density formulas express `rho_p = -e N_A` and `rho_n = e N_D` in
consistent centimetre-based units.  The areal-neutrality relation
`N_A a_p = N_D a_n` is a governing equilibrium law relating independent
physical inputs; it does not supply the requested numerical value of `a_p`.
-/
structure SatisfiesDepletionRegionPhysics (setup : PNJunctionSetup) : Prop where
  noMobileCarriersInDepletion :
    ∀ carrier position,
      InDepletionRegion setup position →
        numberDensityPerCubicCentimeter
            (setup.freeCarrierNumberDensity carrier position) = 0
  constantNegativeChargeOnPDepletion :
    ∀ position,
      InPSideDepletion setup position →
        chargeDensityInCoulombsPerCubicCentimeter
            (setup.fixedChargeDensity position) =
          -(chargeMagnitudeInCoulombs setup.elementaryChargeMagnitude *
            numberDensityPerCubicCentimeter setup.acceptorAtomDensity)
  constantPositiveChargeOnNDepletion :
    ∀ position,
      InNSideDepletion setup position →
        chargeDensityInCoulombsPerCubicCentimeter
            (setup.fixedChargeDensity position) =
          chargeMagnitudeInCoulombs setup.elementaryChargeMagnitude *
            numberDensityPerCubicCentimeter setup.donorAtomDensity
  noNetChargeOutsideDepletion :
    ∀ position,
      OutsideDepletionRegion setup position →
        chargeDensityInCoulombsPerCubicCentimeter
            (setup.fixedChargeDensity position) = 0
  electricFieldPointsTowardPSide :
    ∀ position,
      InDepletionRegion setup position →
        axialElectricFieldInVoltsPerMeter
            (setup.axialElectricField position) ≤ 0
  stabilizingElectricFieldDeveloped :
    ∃ position,
      InDepletionRegion setup position ∧
        axialElectricFieldInVoltsPerMeter
            (setup.axialElectricField position) < 0
  equilibriumChargeNeutralityPerUnitArea :
    numberDensityPerCubicCentimeter setup.acceptorAtomDensity *
        lengthInCentimeters setup.pSideDepletionDepth =
      numberDensityPerCubicCentimeter setup.donorAtomDensity *
        lengthInCentimeters setup.nSideDepletionDepth

/-! ## Displayed choices and current target -/

/-- Labels of the four depletion-depth choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Nanometre value printed beside each answer label. -/
def AnswerChoice.depthInNanometers : AnswerChoice → ℝ
  | .A => 275
  | .B => 399
  | .C => 250
  | .D => 7 / 20

/-- A displayed choice matches the independently modeled p-side depth. -/
def MatchesAnswerChoice
    (setup : PNJunctionSetup) (choice : AnswerChoice) : Prop :=
  lengthInNanometers setup.pSideDepletionDepth = choice.depthInNanometers

/-!
Charge neutrality with the supplied densities and n-side depth determines
`a_p = (N_D / N_A) a_n = 275 nm`.  The second and third conjuncts identify
the matching displayed option without putting that answer into any premise.
-/
theorem p_side_depletion_depth_is_275_nanometers
    (setup : PNJunctionSetup)
    (hData : MatchesProblemData setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hPhysical : HasPhysicalParameters setup)
    (hLaws : SatisfiesDepletionRegionPhysics setup) :
    lengthInNanometers setup.pSideDepletionDepth = 275 ∧
      MatchesAnswerChoice setup .A ∧
      ∀ choice, MatchesAnswerChoice setup choice ↔ choice = .A := by
  let centimeterUnits : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.centimeters}
  let nanometerUnits : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.nanometers}
  let lengthScale : ℝ :=
    UnitChoices.dimScale nanometerUnits centimeterUnits L𝓭
  have pDepthConversion :
      lengthInCentimeters setup.pSideDepletionDepth =
        lengthScale * lengthInNanometers setup.pSideDepletionDepth := by
    change
      ((setup.pSideDepletionDepth centimeterUnits).val : ℝ) =
        lengthScale *
          ((setup.pSideDepletionDepth nanometerUnits).val : ℝ)
    rw [setup.pSideDepletionDepth.2 nanometerUnits centimeterUnits]
    simp [lengthScale]
  have nDepthConversion :
      lengthInCentimeters setup.nSideDepletionDepth =
        lengthScale * lengthInNanometers setup.nSideDepletionDepth := by
    change
      ((setup.nSideDepletionDepth centimeterUnits).val : ℝ) =
        lengthScale *
          ((setup.nSideDepletionDepth nanometerUnits).val : ℝ)
    rw [setup.nSideDepletionDepth.2 nanometerUnits centimeterUnits]
    simp [lengthScale]
  have lengthScalePositive : 0 < lengthScale := by
    exact_mod_cast
      UnitChoices.dimScale_pos nanometerUnits centimeterUnits L𝓭
  have neutrality := hLaws.equilibriumChargeNeutralityPerUnitArea
  rw [hData.acceptorDensityPerCubicCentimeter,
    hData.donorDensityPerCubicCentimeter, pDepthConversion,
    nDepthConversion, hData.nSideDepthNanometers] at neutrality
  have scaledDepth :
      lengthScale * lengthInNanometers setup.pSideDepletionDepth =
        lengthScale * 275 := by
    nlinarith [neutrality]
  have hDepth : lengthInNanometers setup.pSideDepletionDepth = 275 :=
    mul_left_cancel₀ (ne_of_gt lengthScalePositive) scaledDepth
  refine ⟨hDepth, ?_, ?_⟩
  · simpa [MatchesAnswerChoice, AnswerChoice.depthInNanometers] using hDepth
  · intro choice
    cases choice with
    | A =>
      simp [MatchesAnswerChoice, AnswerChoice.depthInNanometers, hDepth]
    | B =>
      simp [MatchesAnswerChoice, AnswerChoice.depthInNanometers, hDepth]
    | C =>
      simp [MatchesAnswerChoice, AnswerChoice.depthInNanometers, hDepth]
    | D =>
      simp [MatchesAnswerChoice, AnswerChoice.depthInNanometers, hDepth]
      norm_num

end PhyXMiniProblems.ProblemPhyXMini0630
