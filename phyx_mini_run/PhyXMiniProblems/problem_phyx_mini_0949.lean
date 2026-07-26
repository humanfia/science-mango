import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0949

open Dimension

/-!
# Magnetic torque on a straight current-carrying bar

A uniform straight conducting bar of length `L` carries conventional current
`I` from endpoint `a` to endpoint `b`.  It lies in a spatially uniform magnetic
field of flux-density magnitude `B` directed into the page.  The magnetic
force on the element labelled `dx` is perpendicular to the bar.  Its moment
arm about the axis through `a` is the along-bar coordinate `x`.

The physical magnitudes below are unit-independent Physlib `Dimensionful`
quantities.  Real numbers occur only as coherent-SI readouts, as the metre
coordinate used to parameterize the bar, and in the displayed answer
expressions.

Assumption/target split:

* governing laws: the applied Physlib magnetic field is uniform and directed
  into the page, the perpendicular magnetic-force density obeys
  `dF/dx = I B`, and torque about `a` is the line integral
  `tau = integral_0^L x (dF/dx) dx`;
* previous-part results: none;
* figure/data readouts: the endpoint labels `a` and `b`, current arrow `I`
  from `a` to `b`, field label `B` and uniform crosses, along-bar coordinate
  `x`, highlighted differential element `dx`, and perpendicular force arrow;
* current target: the torque magnitude is `(1 / 2) I B L^2`, answer B.

No setup, scenario, figure, geometry, field-law, or force-law field states the
evaluated target formula.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Magnetic flux density has dimension `M T⁻¹ C⁻¹` (tesla). -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Electric current has dimension `C T⁻¹` (ampere). -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Magnetic force per unit length has dimension `M T⁻²` (newton/metre). -/
def forcePerLengthDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Torque has dimension `M L² T⁻²` (newton metre). -/
def torqueDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative, unit-independent conventional-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent magnetic force per unit bar length. -/
abbrev ForcePerLengthMagnitude : Type :=
  Dimensionful (WithDim forcePerLengthDimension NNReal)

/-- A nonnegative, unit-independent torque magnitude. -/
abbrev TorqueMagnitude : Type :=
  Dimensionful (WithDim torqueDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Read magnetic flux density in teslas. -/
def magneticFluxDensityInTeslas
    (fieldMagnitude : MagneticFluxDensityMagnitude) : ℝ :=
  nonnegativeSIReadout fieldMagnitude

/-- Read conventional current in amperes. -/
def currentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  nonnegativeSIReadout current

/-- Read magnetic force per unit length in newtons per metre. -/
def forcePerLengthInNewtonsPerMeter
    (forceDensity : ForcePerLengthMagnitude) : ℝ :=
  nonnegativeSIReadout forceDensity

/-- Read torque magnitude in newton metres. -/
def torqueInNewtonMeters (torque : TorqueMagnitude) : ℝ :=
  nonnegativeSIReadout torque

/-! ## Bar geometry, spatial roles, and figure vocabulary -/

/-- The two endpoints explicitly labelled in the supplied figure. -/
inductive BarEndpoint where
  | a
  | b
  deriving DecidableEq, Fintype, Repr

/-- Conventional-current direction along the bar. -/
inductive BarCurrentDirection where
  | fromAToB
  | fromBToA
  deriving DecidableEq, Repr

/-- Qualitative directions in the plane of, or normal to, the page. -/
inductive PageDirection where
  | northeastAlongBar
  | southwestAlongBar
  | northwestPerpendicularToBar
  | southeastPerpendicularToBar
  | intoPage
  | outOfPage
  deriving DecidableEq, Repr

/-- Relative placement of an endpoint in the supplied diagonal-bar drawing. -/
inductive PagePlacement where
  | southwest
  | northeast
  deriving DecidableEq, Repr

/-- Relation of the requested rotation axis to the straight bar. -/
inductive AxisRelationToBar where
  | perpendicular
  | parallel
  deriving DecidableEq, Repr

/-- Material and shape idealization stated for the bar. -/
inductive BarModel where
  | uniformStraightConductor
  | other
  deriving DecidableEq, Repr

/-- Symbolic labels visible in image `949.png`. -/
inductive FigureQuantityLabel where
  | endpointA
  | endpointB
  | current
  | magneticField
  | alongBarCoordinate
  | differentialElement
  deriving DecidableEq, Fintype, Repr

/-- Printed symbol expected for each labelled figure quantity. -/
def expectedPrintedSymbol : FigureQuantityLabel → String
  | .endpointA => "a"
  | .endpointB => "b"
  | .current => "I"
  | .magneticField => "B"
  | .alongBarCoordinate => "x"
  | .differentialElement => "dx"

/-- Literal qualitative content of the supplied raster. -/
structure CurrentBarFigure where
  barShown : Bool
  endpointMarked : BarEndpoint → Bool
  endpointPlacement : BarEndpoint → PagePlacement
  quantityLabelShown : FigureQuantityLabel → Bool
  printedSymbol : FigureQuantityLabel → String
  uniformFieldCrossesShown : Bool
  currentArrowShown : Bool
  currentArrowDirection : PageDirection
  highlightedDifferentialElementShown : Bool
  differentialElementDirection : PageDirection
  coordinateXMarkedOnBar : Bool
  magneticForceArrowShown : Bool
  magneticForceArrowDirection : PageDirection
  magneticFieldDirection : PageDirection

/-!
Independent physical quantities and spatial data for the bar.  The argument
of `barPointAtMeterCoordinate` and of `magneticForcePerLengthAtMeter` is the
coherent-SI coordinate `x` measured from endpoint `a`.  The requested torque
is stored as an independent observable, not defined from an answer choice.
-/
structure CurrentCarryingBarSetup where
  barModel : BarModel
  barLength : LengthQuantity
  endpointPosition : BarEndpoint → Space 3
  barPointAtMeterCoordinate : ℝ → Space 3
  currentMagnitude : ElectricCurrentMagnitude
  currentDirection : BarCurrentDirection
  magneticField : Electromagnetism.MagneticField 3
  magneticFluxDensityMagnitude : MagneticFluxDensityMagnitude
  uniformFieldRegion : Set (Time × Space 3)
  observationTime : Time
  magneticForcePerLengthAtMeter : ℝ → ForcePerLengthMagnitude
  torqueMagnitudeAboutA : TorqueMagnitude
  torqueAxisEndpoint : BarEndpoint
  torqueAxisRelationToBar : AxisRelationToBar
  figure : CurrentBarFigure

/-- The page-normal component of a three-dimensional Physlib field vector. -/
def pageNormalIndex : Fin 3 := 2

/-! ## Scenario, primary-image evidence, and physical parameter conditions -/

/-- Qualitative assumptions stated in the problem prose. -/
structure MatchesCurrentCarryingBarDescription
    (setup : CurrentCarryingBarSetup) : Prop where
  uniformStraightBar : setup.barModel = .uniformStraightConductor
  currentRunsFromAToB : setup.currentDirection = .fromAToB
  fieldPointsIntoPage : setup.figure.magneticFieldDirection = .intoPage
  torqueAxisPassesThroughA : setup.torqueAxisEndpoint = .a
  torqueAxisIsPerpendicularToBar :
    setup.torqueAxisRelationToBar = .perpendicular

/-!
Primary-raster evidence: all printed labels, endpoint placements, uniform
crosses, and the current, differential-element, and magnetic-force arrows.
No torque value or answer expression occurs here.
-/
structure MatchesPrimaryCurrentBarFigure
    (setup : CurrentCarryingBarSetup) : Prop where
  barIsShown : setup.figure.barShown = true
  bothEndpointsAreMarked :
    ∀ endpoint, setup.figure.endpointMarked endpoint = true
  endpointAIsSouthwest :
    setup.figure.endpointPlacement .a = .southwest
  endpointBIsNortheast :
    setup.figure.endpointPlacement .b = .northeast
  allQuantityLabelsAreShown :
    ∀ label, setup.figure.quantityLabelShown label = true
  printedQuantitySymbols :
    ∀ label, setup.figure.printedSymbol label = expectedPrintedSymbol label
  uniformFieldCrossesAreShown :
    setup.figure.uniformFieldCrossesShown = true
  currentArrowIsShown : setup.figure.currentArrowShown = true
  currentArrowPointsFromAToB :
    setup.figure.currentArrowDirection = .northeastAlongBar
  differentialElementIsHighlighted :
    setup.figure.highlightedDifferentialElementShown = true
  differentialElementPointsAlongBar :
    setup.figure.differentialElementDirection = .northeastAlongBar
  coordinateXIsMarkedOnBar : setup.figure.coordinateXMarkedOnBar = true
  forceArrowIsShown : setup.figure.magneticForceArrowShown = true
  forceArrowIsPerpendicularToBar :
    setup.figure.magneticForceArrowDirection =
      .northwestPerpendicularToBar
  fieldDirectionIsIntoPage :
    setup.figure.magneticFieldDirection = .intoPage

/-- Positivity and non-vacuity conditions for the depicted apparatus. -/
structure HasPhysicalCurrentBarParameters
    (setup : CurrentCarryingBarSetup) : Prop where
  barLengthPositive : 0 < lengthInMeters setup.barLength
  currentMagnitudePositive : 0 < currentInAmperes setup.currentMagnitude
  magneticFluxDensityPositive :
    0 < magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  uniformFieldRegionNonempty : setup.uniformFieldRegion.Nonempty

/-!
The metre parameter starts at endpoint `a`, ends at endpoint `b`, and measures
distance along the straight bar.  Every bar element at the observation time
lies in the region occupied by the uniform field.
-/
structure SatisfiesStraightBarGeometry
    (setup : CurrentCarryingBarSetup) : Prop where
  zeroCoordinateIsA :
    setup.barPointAtMeterCoordinate 0 = setup.endpointPosition .a
  lengthCoordinateIsB :
    setup.barPointAtMeterCoordinate (lengthInMeters setup.barLength) =
      setup.endpointPosition .b
  coordinateMeasuresAlongBarDistance : ∀ xMeters yMeters : ℝ,
    0 ≤ xMeters →
    xMeters ≤ lengthInMeters setup.barLength →
    0 ≤ yMeters →
    yMeters ≤ lengthInMeters setup.barLength →
      dist (setup.barPointAtMeterCoordinate xMeters)
          (setup.barPointAtMeterCoordinate yMeters) =
        |xMeters - yMeters|
  barLiesInUniformFieldRegion : ∀ xMeters : ℝ,
    0 ≤ xMeters →
    xMeters ≤ lengthInMeters setup.barLength →
      (setup.observationTime, setup.barPointAtMeterCoordinate xMeters) ∈
        setup.uniformFieldRegion

/-! ## Uniform-field, magnetic-force, and torque laws -/

/-!
The Physlib magnetic field is uniform on the stated region and has only its
negative page-normal component, matching the crosses that denote a field into
the page.  The scalar component is calibrated by the independent dimensionful
flux-density magnitude `B`.
-/
structure SatisfiesUniformIntoPageMagneticField
    (setup : CurrentCarryingBarSetup) : Prop where
  uniformIntoPageField : ∀ time position component,
    (time, position) ∈ setup.uniformFieldRegion →
      setup.magneticField time position component =
        if component = pageNormalIndex then
          -magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
        else 0

/-!
Governing laws for a current element perpendicular to a uniform magnetic
field:

* the Lorentz-force magnitude per unit length is `dF/dx = I B` everywhere on
  the bar; and
* torque about endpoint `a` is the first moment of that distributed force,
  `integral_0^L x (dF/dx) dx`.

The second law deliberately retains the unevaluated interval integral, so it
does not assume the requested factor `L^2 / 2`.
-/
structure SatisfiesDistributedMagneticForceAndTorqueLaws
    (setup : CurrentCarryingBarSetup) : Prop where
  perpendicularMagneticForceDensity : ∀ xMeters : ℝ,
    0 ≤ xMeters →
    xMeters ≤ lengthInMeters setup.barLength →
      forcePerLengthInNewtonsPerMeter
          (setup.magneticForcePerLengthAtMeter xMeters) =
        currentInAmperes setup.currentMagnitude *
          magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  torqueIsFirstMomentAboutA :
    torqueInNewtonMeters setup.torqueMagnitudeAboutA =
      ∫ xMeters in (0 : ℝ)..lengthInMeters setup.barLength,
        xMeters * forcePerLengthInNewtonsPerMeter
          (setup.magneticForcePerLengthAtMeter xMeters)

/-! ## Displayed answer choices and target conclusion -/

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
Literal transcription of the scalar expressions displayed beside the four
answer labels.  This metadata does not define the independent torque field.
-/
def AnswerChoice.displayedExpressionInSI
    (choice : AnswerChoice) (setup : CurrentCarryingBarSetup) : ℝ :=
  let current := currentInAmperes setup.currentMagnitude
  let field :=
    magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  let length := lengthInMeters setup.barLength
  match choice with
  | .A => current * field * length ^ 2
  | .B => (1 / 2) * current * field * length ^ 2
  | .C => (1 / 4) * current * field * length ^ 2
  | .D => (1 / 3) * current * field * length ^ 2

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
Evaluating the first moment of the uniform force density gives

`tau_a = (1 / 2) I B L^2`,

which is displayed answer B.  This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0949:target`.
-/
theorem problem_phyx_mini_0949
    (setup : CurrentCarryingBarSetup)
    (_scenario : MatchesCurrentCarryingBarDescription setup)
    (_figure : MatchesPrimaryCurrentBarFigure setup)
    (_physical : HasPhysicalCurrentBarParameters setup)
    (_geometry : SatisfiesStraightBarGeometry setup)
    (_fieldLaw : SatisfiesUniformIntoPageMagneticField setup)
    (_forceAndTorqueLaws :
      SatisfiesDistributedMagneticForceAndTorqueLaws setup) :
    torqueInNewtonMeters setup.torqueMagnitudeAboutA =
      (1 / 2) * currentInAmperes setup.currentMagnitude *
        magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
        lengthInMeters setup.barLength ^ 2 := by
  rw [_forceAndTorqueLaws.torqueIsFirstMomentAboutA]
  calc
    (∫ xMeters in (0 : ℝ)..lengthInMeters setup.barLength,
        xMeters * forcePerLengthInNewtonsPerMeter
          (setup.magneticForcePerLengthAtMeter xMeters)) =
        ∫ xMeters in (0 : ℝ)..lengthInMeters setup.barLength,
          xMeters *
            (currentInAmperes setup.currentMagnitude *
              magneticFluxDensityInTeslas
                setup.magneticFluxDensityMagnitude) := by
      apply intervalIntegral.integral_congr
      intro xMeters xMetersInInterval
      have xMetersOnBar :
          xMeters ∈
            Set.Icc (0 : ℝ) (lengthInMeters setup.barLength) := by
        simpa [Set.uIcc_of_le
          (le_of_lt _physical.barLengthPositive)] using xMetersInInterval
      dsimp only
      rw [_forceAndTorqueLaws.perpendicularMagneticForceDensity
        xMeters xMetersOnBar.1 xMetersOnBar.2]
    _ = (1 / 2) * currentInAmperes setup.currentMagnitude *
          magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
          lengthInMeters setup.barLength ^ 2 := by
      rw [show (fun xMeters : ℝ =>
          xMeters *
            (currentInAmperes setup.currentMagnitude *
              magneticFluxDensityInTeslas
                setup.magneticFluxDensityMagnitude)) =
          fun xMeters =>
            (currentInAmperes setup.currentMagnitude *
              magneticFluxDensityInTeslas
                setup.magneticFluxDensityMagnitude) *
              xMeters ^ 1 by
        funext xMeters
        simp only [pow_one]
        ring]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      ring

end PhyXMiniProblems.ProblemPhyXMini0949
