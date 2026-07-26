import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0897

open Dimension

/-!
# Net electrostatic force on the bottom-left charge

The primary figure shows three point charges at occupied corners of a dashed
`3.0 cm` by `4.0 cm` rectangle.  The `+5.0 nC` charge at the bottom-left is the
target; the other charges are `-5.0 nC` at the bottom-right and `+10 nC` at the
top-right.  The unoccupied top-left corner has no charge marker.

Charges, lengths, positions, and force components are represented by
unit-independent Physlib quantities.  Real numbers below are only coherent-SI
or explicitly selected-unit readouts.  Coulomb's law determines each pairwise
force, and vector superposition determines the net force.  The requested
numeric magnitude and answer choice occur only in the theorem conclusion.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A signed, unit-independent Cartesian length coordinate. -/
abbrev LengthCoordinateQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed, unit-independent Cartesian force component. -/
abbrev ForceComponentQuantity : Type :=
  Dimensionful (WithDim forceDimension ℝ)

/-- Read a signed physical charge in coherent-SI coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read a signed physical charge in nanocoulombs. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  10 ^ 9 * chargeInCoulombs charge

/-- Read a length coordinate in a selected physical length unit. -/
def lengthReadout
    (unit : LengthUnit) (length : LengthCoordinateQuantity) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

/-- Read a length coordinate in coherent-SI metres. -/
def lengthInMeters (length : LengthCoordinateQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a signed Cartesian force component in coherent-SI newtons. -/
def forceComponentInNewtons (force : ForceComponentQuantity) : ℝ :=
  (force UnitChoices.SI).val

/-! ## Physical vector roles and figure labels -/

/-- A physical point in the plane, represented by two dimensionful coordinates. -/
structure Position2D where
  x : LengthCoordinateQuantity
  y : LengthCoordinateQuantity

/-- A physical planar force vector, represented by two dimensionful components. -/
structure ForceVector2D where
  x : ForceComponentQuantity
  y : ForceComponentQuantity

/-- The three occupied corners visible in the supplied figure. -/
inductive ChargeSite where
  | bottomLeft
  | bottomRight
  | topRight
  deriving DecidableEq, Fintype, Repr

/-- The two source sites which exert force on the bottom-left target charge. -/
inductive SourceSite where
  | bottomRight
  | topRight
  deriving DecidableEq, Fintype, Repr

/-- Regard a source-site label as its corresponding occupied-corner label. -/
def SourceSite.chargeSite : SourceSite → ChargeSite
  | .bottomRight => .bottomRight
  | .topRight => .topRight

/-- Polarity signs drawn inside the three charge markers. -/
inductive ChargePolarity where
  | positive
  | negative
  deriving DecidableEq, Repr

/-!
Literal typed content of image `897.png`.  The label fields contain physical
quantities rather than untyped scalar stand-ins; their numerical readouts are
specified separately in `MatchesSuppliedChargeRectangleFigure`.
-/
structure ChargeRectangleFigure where
  dashedRectangleShown : Bool
  horizontalDimensionLabel : LengthCoordinateQuantity
  verticalDimensionLabel : LengthCoordinateQuantity
  chargeLabel : ChargeSite → SignedChargeQuantity
  polarityMarker : ChargeSite → ChargePolarity
  topLeftChargeMarkerShown : Bool
  forceQuestionTarget : ChargeSite

/-!
The physical three-charge setup.  The pairwise and net forces are independent
physical vector fields of the structure, not definitions in terms of the
recorded multiple-choice answer.
-/
structure ThreeChargeRectangleSetup where
  electromagneticSystem : Electromagnetism.EMSystem
  rectangleWidth : LengthCoordinateQuantity
  rectangleHeight : LengthCoordinateQuantity
  charge : ChargeSite → SignedChargeQuantity
  position : ChargeSite → Position2D
  forceOnBottomLeftFrom : SourceSite → ForceVector2D
  netForceOnBottomLeft : ForceVector2D
  figure : ChargeRectangleFigure

/-! ## Geometry helpers -/

/-- Horizontal displacement from a source charge to the target charge. -/
def sourceToTargetDXInMeters
    (setup : ThreeChargeRectangleSetup) (source : SourceSite) : ℝ :=
  lengthInMeters (setup.position .bottomLeft).x -
    lengthInMeters (setup.position source.chargeSite).x

/-- Vertical displacement from a source charge to the target charge. -/
def sourceToTargetDYInMeters
    (setup : ThreeChargeRectangleSetup) (source : SourceSite) : ℝ :=
  lengthInMeters (setup.position .bottomLeft).y -
    lengthInMeters (setup.position source.chargeSite).y

/-- Euclidean separation between a source charge and the target charge. -/
def sourceTargetDistanceInMeters
    (setup : ThreeChargeRectangleSetup) (source : SourceSite) : ℝ :=
  Real.sqrt
    (sourceToTargetDXInMeters setup source ^ 2 +
      sourceToTargetDYInMeters setup source ^ 2)

/-- Coherent-SI magnitude of a planar physical force vector, in newtons. -/
def forceMagnitudeInNewtons (force : ForceVector2D) : ℝ :=
  Real.sqrt
    (forceComponentInNewtons force.x ^ 2 +
      forceComponentInNewtons force.y ^ 2)

/-! ## Figure/data readouts and physical assumptions -/

/-!
Primary-image evidence and the intrinsic rectangle geometry.  The coordinate
relations use the bottom-left site only as a reference point; they do not fix
an arbitrary absolute origin.  No force magnitude or answer choice is stated
in these fields.
-/
structure MatchesSuppliedChargeRectangleFigure
    (setup : ThreeChargeRectangleSetup) : Prop where
  dashedRectangleIsShown : setup.figure.dashedRectangleShown = true
  horizontalLabelMatchesWidth :
    setup.figure.horizontalDimensionLabel = setup.rectangleWidth
  verticalLabelMatchesHeight :
    setup.figure.verticalDimensionLabel = setup.rectangleHeight
  chargeLabelsMatchPhysicalCharges :
    ∀ site, setup.figure.chargeLabel site = setup.charge site
  targetIsBottomLeft : setup.figure.forceQuestionTarget = .bottomLeft
  topLeftCornerIsUnoccupied :
    setup.figure.topLeftChargeMarkerShown = false
  bottomLeftPolarity :
    setup.figure.polarityMarker .bottomLeft = .positive
  bottomRightPolarity :
    setup.figure.polarityMarker .bottomRight = .negative
  topRightPolarity :
    setup.figure.polarityMarker .topRight = .positive
  widthInCentimeters :
    lengthReadout LengthUnit.centimeters setup.rectangleWidth = 3
  heightInCentimeters :
    lengthReadout LengthUnit.centimeters setup.rectangleHeight = 4
  bottomLeftChargeInNanocoulombs :
    chargeInNanocoulombs (setup.charge .bottomLeft) = 5
  bottomRightChargeInNanocoulombs :
    chargeInNanocoulombs (setup.charge .bottomRight) = -5
  topRightChargeInNanocoulombs :
    chargeInNanocoulombs (setup.charge .topRight) = 10
  bottomRowHorizontalSeparation :
    lengthInMeters (setup.position .bottomRight).x -
        lengthInMeters (setup.position .bottomLeft).x =
      lengthInMeters setup.rectangleWidth
  bottomRowSameHeight :
    lengthInMeters (setup.position .bottomRight).y =
      lengthInMeters (setup.position .bottomLeft).y
  rightColumnSameHorizontalCoordinate :
    lengthInMeters (setup.position .topRight).x =
      lengthInMeters (setup.position .bottomRight).x
  rightColumnVerticalSeparation :
    lengthInMeters (setup.position .topRight).y -
        lengthInMeters (setup.position .bottomRight).y =
      lengthInMeters setup.rectangleHeight

/-! A physically nondegenerate rectangle and positive Coulomb constant. -/
structure HasPhysicalChargeRectangleParameters
    (setup : ThreeChargeRectangleSetup) : Prop where
  widthPositive : 0 < lengthInMeters setup.rectangleWidth
  heightPositive : 0 < lengthInMeters setup.rectangleHeight
  sourceDistancesPositive :
    ∀ source, 0 < sourceTargetDistanceInMeters setup source
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-!
The standard school-physics calibration of Coulomb's constant, in coherent SI
units `N m² C⁻²`.  This supplies reference data, not the requested force.
-/
structure UsesStandardCoulombConstant
    (setup : ThreeChargeRectangleSetup) : Prop where
  coulombConstantReadout :
    setup.electromagneticSystem.coulombConstant = 8.99e9

/-!
Vector Coulomb law for each source acting on the bottom-left target:

`F = k q_target q_source (r_target - r_source) / |r_target-r_source|³`.

The signed charge product handles attraction and repulsion.  The two equations
state the general governing law componentwise and contain no net-force answer.
-/
structure SatisfiesPairwiseCoulombForceLaw
    (setup : ThreeChargeRectangleSetup) : Prop where
  forceXFromEachSource : ∀ source,
    forceComponentInNewtons (setup.forceOnBottomLeftFrom source).x =
      setup.electromagneticSystem.coulombConstant *
        chargeInCoulombs (setup.charge .bottomLeft) *
        chargeInCoulombs (setup.charge source.chargeSite) *
        sourceToTargetDXInMeters setup source /
        sourceTargetDistanceInMeters setup source ^ 3
  forceYFromEachSource : ∀ source,
    forceComponentInNewtons (setup.forceOnBottomLeftFrom source).y =
      setup.electromagneticSystem.coulombConstant *
        chargeInCoulombs (setup.charge .bottomLeft) *
        chargeInCoulombs (setup.charge source.chargeSite) *
        sourceToTargetDYInMeters setup source /
        sourceTargetDistanceInMeters setup source ^ 3

/-- The net force is the vector sum of the two pairwise forces. -/
structure SatisfiesElectrostaticForceSuperposition
    (setup : ThreeChargeRectangleSetup) : Prop where
  netXIsSourceSum :
    forceComponentInNewtons setup.netForceOnBottomLeft.x =
      forceComponentInNewtons
          (setup.forceOnBottomLeftFrom .bottomRight).x +
        forceComponentInNewtons
          (setup.forceOnBottomLeftFrom .topRight).x
  netYIsSourceSum :
    forceComponentInNewtons setup.netForceOnBottomLeft.y =
      forceComponentInNewtons
          (setup.forceOnBottomLeftFrom .bottomRight).y +
        forceComponentInNewtons
          (setup.forceOnBottomLeftFrom .topRight).y

/-! ## Displayed choices and current target -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Force magnitude in newtons printed beside each answer label. -/
def displayedForceMagnitudeInNewtons : AnswerChoice → ℝ
  | .A => 7.25e-4
  | .B => 6.35e-4
  | .C => 2.0e-4
  | .D => 1.33e-4

/-!
A displayed choice is closest when its printed value is at least as close to
the physical net-force magnitude as every alternative.
-/
def IsClosestDisplayedForceMagnitude
    (force : ForceVector2D) (choice : AnswerChoice) : Prop :=
  ∀ alternative,
    |forceMagnitudeInNewtons force -
        displayedForceMagnitudeInNewtons choice| ≤
      |forceMagnitudeInNewtons force -
        displayedForceMagnitudeInNewtons alternative|

/-- A physical force magnitude agrees with a displayed SI value to a tolerance. -/
def IsWithinNewtonTolerance
    (force : ForceVector2D) (displayed tolerance : ℝ) : Prop :=
  0 ≤ tolerance ∧
    |forceMagnitudeInNewtons force - displayed| ≤ tolerance

/-!
The Coulomb forces from the two source corners combine to approximately
`2.0 * 10⁻⁴ N` on the `+5.0 nC` bottom-left charge.  The `5 * 10⁻⁶ N`
tolerance is half the last displayed digit of `2.0 * 10⁻⁴ N`; the same
calculation makes choice C the closest displayed answer.
-/
theorem problem_phyx_mini_0897
    (setup : ThreeChargeRectangleSetup)
    (hFigure : MatchesSuppliedChargeRectangleFigure setup)
    (hPhysical : HasPhysicalChargeRectangleParameters setup)
    (hReference : UsesStandardCoulombConstant setup)
    (hCoulomb : SatisfiesPairwiseCoulombForceLaw setup)
    (hSuperposition : SatisfiesElectrostaticForceSuperposition setup) :
    IsWithinNewtonTolerance setup.netForceOnBottomLeft 2.0e-4 5e-6 ∧
      IsClosestDisplayedForceMagnitude setup.netForceOnBottomLeft .C := by
  have hCentimetersToMeters (length : LengthCoordinateQuantity) :
      lengthReadout LengthUnit.centimeters length =
        100 * lengthInMeters length := by
    have hscale := congrArg WithDim.val (length.2
      UnitChoices.SI
      ({UnitChoices.SI with length := LengthUnit.centimeters} : UnitChoices))
    norm_num [lengthInMeters, lengthReadout,
      UnitChoices.SI, UnitChoices.dimScale, LengthUnit.centimeters,
      LengthUnit.scale, LengthUnit.meters, LengthUnit.div_eq_val] at hscale ⊢
    exact hscale
  have hWidth :
      lengthInMeters setup.rectangleWidth = (3 : ℝ) / 100 := by
    have h := hFigure.widthInCentimeters
    rw [hCentimetersToMeters] at h
    linarith only [h]
  have hHeight :
      lengthInMeters setup.rectangleHeight = (4 : ℝ) / 100 := by
    have h := hFigure.heightInCentimeters
    rw [hCentimetersToMeters] at h
    linarith only [h]
  have hTargetCharge :
      chargeInCoulombs (setup.charge .bottomLeft) =
        (1 : ℝ) / 200000000 := by
    have h := hFigure.bottomLeftChargeInNanocoulombs
    norm_num [chargeInNanocoulombs] at h ⊢
    linarith only [h]
  have hBottomRightCharge :
      chargeInCoulombs (setup.charge .bottomRight) =
        -(1 : ℝ) / 200000000 := by
    have h := hFigure.bottomRightChargeInNanocoulombs
    norm_num [chargeInNanocoulombs] at h ⊢
    linarith only [h]
  have hTopRightCharge :
      chargeInCoulombs (setup.charge .topRight) =
        (1 : ℝ) / 100000000 := by
    have h := hFigure.topRightChargeInNanocoulombs
    norm_num [chargeInNanocoulombs] at h ⊢
    linarith only [h]
  have hBottomRightDX :
      sourceToTargetDXInMeters setup .bottomRight =
        -(3 : ℝ) / 100 := by
    simp only [sourceToTargetDXInMeters, SourceSite.chargeSite]
    linarith only [hFigure.bottomRowHorizontalSeparation, hWidth]
  have hBottomRightDY :
      sourceToTargetDYInMeters setup .bottomRight = 0 := by
    simp only [sourceToTargetDYInMeters, SourceSite.chargeSite]
    linarith only [hFigure.bottomRowSameHeight]
  have hTopRightDX :
      sourceToTargetDXInMeters setup .topRight =
        -(3 : ℝ) / 100 := by
    simp only [sourceToTargetDXInMeters, SourceSite.chargeSite]
    linarith only [hFigure.bottomRowHorizontalSeparation,
      hFigure.rightColumnSameHorizontalCoordinate, hWidth]
  have hTopRightDY :
      sourceToTargetDYInMeters setup .topRight =
        -(4 : ℝ) / 100 := by
    simp only [sourceToTargetDYInMeters, SourceSite.chargeSite]
    linarith only [hFigure.bottomRowSameHeight,
      hFigure.rightColumnVerticalSeparation, hHeight]
  have hBottomRightDistance :
      sourceTargetDistanceInMeters setup .bottomRight =
        (3 : ℝ) / 100 := by
    rw [sourceTargetDistanceInMeters, hBottomRightDX, hBottomRightDY]
    norm_num
  have hTopRightDistance :
      sourceTargetDistanceInMeters setup .topRight =
        (1 : ℝ) / 20 := by
    rw [sourceTargetDistanceInMeters, hTopRightDX, hTopRightDY]
    norm_num
  have hBottomRightForceX :
      forceComponentInNewtons
          (setup.forceOnBottomLeftFrom .bottomRight).x =
        (899 : ℝ) / 3600000 := by
    rw [hCoulomb.forceXFromEachSource,
      hReference.coulombConstantReadout,
      hTargetCharge, SourceSite.chargeSite, hBottomRightCharge,
      hBottomRightDX, hBottomRightDistance]
    norm_num
  have hBottomRightForceY :
      forceComponentInNewtons
          (setup.forceOnBottomLeftFrom .bottomRight).y = 0 := by
    rw [hCoulomb.forceYFromEachSource,
      hReference.coulombConstantReadout,
      hTargetCharge, SourceSite.chargeSite, hBottomRightCharge,
      hBottomRightDY, hBottomRightDistance]
    norm_num
  have hTopRightForceX :
      forceComponentInNewtons
          (setup.forceOnBottomLeftFrom .topRight).x =
        -(2697 : ℝ) / 25000000 := by
    rw [hCoulomb.forceXFromEachSource,
      hReference.coulombConstantReadout,
      hTargetCharge, SourceSite.chargeSite, hTopRightCharge,
      hTopRightDX, hTopRightDistance]
    norm_num
  have hTopRightForceY :
      forceComponentInNewtons
          (setup.forceOnBottomLeftFrom .topRight).y =
        -(899 : ℝ) / 6250000 := by
    rw [hCoulomb.forceYFromEachSource,
      hReference.coulombConstantReadout,
      hTargetCharge, SourceSite.chargeSite, hTopRightCharge,
      hTopRightDY, hTopRightDistance]
    norm_num
  have hNetForceX :
      forceComponentInNewtons setup.netForceOnBottomLeft.x =
        (63829 : ℝ) / 450000000 := by
    rw [hSuperposition.netXIsSourceSum,
      hBottomRightForceX, hTopRightForceX]
    norm_num
  have hNetForceY :
      forceComponentInNewtons setup.netForceOnBottomLeft.y =
        -(899 : ℝ) / 6250000 := by
    rw [hSuperposition.netYIsSourceSum,
      hBottomRightForceY, hTopRightForceY]
    norm_num
  have hMagnitudeNonnegative :
      0 ≤ forceMagnitudeInNewtons setup.netForceOnBottomLeft := by
    exact Real.sqrt_nonneg _
  have hMagnitudeSquared :
      forceMagnitudeInNewtons setup.netForceOnBottomLeft ^ 2 =
        (330554209 : ℝ) / 8100000000000000 := by
    rw [forceMagnitudeInNewtons, hNetForceX, hNetForceY,
      Real.sq_sqrt (by positivity)]
    norm_num
  have hMagnitudeLower :
      (1 : ℝ) / 5000 ≤
        forceMagnitudeInNewtons setup.netForceOnBottomLeft := by
    nlinarith only [hMagnitudeNonnegative, hMagnitudeSquared]
  have hMagnitudeUpper :
      forceMagnitudeInNewtons setup.netForceOnBottomLeft ≤
        (41 : ℝ) / 200000 := by
    nlinarith only [hMagnitudeNonnegative, hMagnitudeSquared]
  constructor
  · refine ⟨by norm_num, ?_⟩
    rw [abs_of_nonneg (by
      norm_num
      linarith only [hMagnitudeLower])]
    norm_num
    linarith only [hMagnitudeUpper]
  · intro alternative
    fin_cases alternative
    · simp only [displayedForceMagnitudeInNewtons]
      rw [abs_of_nonneg (by
          norm_num
          linarith only [hMagnitudeLower]),
        abs_of_nonpos (by
          norm_num
          linarith only [hMagnitudeUpper])]
      norm_num
      linarith only [hMagnitudeUpper]
    · simp only [displayedForceMagnitudeInNewtons]
      rw [abs_of_nonneg (by
          norm_num
          linarith only [hMagnitudeLower]),
        abs_of_nonpos (by
          norm_num
          linarith only [hMagnitudeUpper])]
      norm_num
      linarith only [hMagnitudeUpper]
    · rfl
    · simp only [displayedForceMagnitudeInNewtons]
      rw [abs_of_nonneg (by
          norm_num
          linarith only [hMagnitudeLower]),
        abs_of_nonneg (by
          norm_num
          linarith only [hMagnitudeLower])]
      norm_num
      linarith

end PhyXMiniProblems.ProblemPhyXMini0897
