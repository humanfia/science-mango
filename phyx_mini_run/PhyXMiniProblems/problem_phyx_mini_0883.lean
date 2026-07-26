import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0883

open Dimension

/-!
# Motional potential difference across a bar beside a straight current

An ideal long vertical wire carries an upward current of magnitude `I`.  A
horizontal metal bar starts a distance `d` to the right of the wire, has length
`l`, and moves upward with speed `v`.  Thus the current and velocity are
parallel, while the bar is radial and perpendicular to both.  The requested
quantity is the potential at the end nearer the long wire minus the potential
at the farther end.

The source's answer choices write the speed as `v₀`, although the prose and
figure label it `v`; `barSpeed` represents this one physical magnitude.

Physical quantities use Physlib's unit-covariant
`Dimensionful (WithDim ...)` representation.  Real numbers occur only as
coherent-SI readouts, radial metre coordinates, and dimensionless expressions
such as `(d + l) / d`.

Assumption/target split:

* `MatchesStraightWireMovingBarScenario` states the component models and
  positivity of the physical magnitudes;
* `MatchesSuppliedStraightWireMovingBarFigure` records the `I`, `v`, `d`, and
  `l` labels, arrow directions, orientations, and endpoint distances read from
  image 883;
* `SatisfiesStraightWireMotionalEmfLaws` states the long-wire magnetic-field
  law, the local `v B` motional-emf density, and the line-integral law for the
  endpoint potential difference; and
* `nearEndMinusFarEndPotential_eq_answer_C` alone concludes the logarithmic
  expression requested in the question.  No premise contains that expression.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Speed has dimension `L T⁻¹`. -/
def speedDimension : Dimension :=
  L𝓭 * T𝓭⁻¹

/-- Electric current has dimension charge per time, `C T⁻¹`. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Magnetic permeability has SI dimension `M L C⁻²`. -/
def magneticPermeabilityDimension : Dimension :=
  M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux density has SI dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Motional-emf density has the electric-field dimension `M L T⁻² C⁻¹`. -/
def electricFieldDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electric potential difference has dimension `M L² T⁻² C⁻¹`. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical speed. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim speedDimension NNReal)

/-- A nonnegative electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative magnetic permeability. -/
abbrev MagneticPermeabilityQuantity : Type :=
  Dimensionful (WithDim magneticPermeabilityDimension NNReal)

/-- A nonnegative magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative local motional-emf density, measured in volts per metre. -/
abbrev MotionalEmfDensityMagnitude : Type :=
  Dimensionful (WithDim electricFieldDimension NNReal)

/-- A nonnegative endpoint potential difference. -/
abbrev ElectricPotentialDifference : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Read a speed in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  nonnegativeSIReadout speed

/-- Read an electric-current magnitude in amperes. -/
def currentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  nonnegativeSIReadout current

/-- Read magnetic permeability in henries per metre. -/
def permeabilityInHenriesPerMeter
    (permeability : MagneticPermeabilityQuantity) : ℝ :=
  nonnegativeSIReadout permeability

/-- Read a magnetic-flux-density magnitude in teslas. -/
def magneticFluxDensityInTeslas
    (field : MagneticFluxDensityMagnitude) : ℝ :=
  nonnegativeSIReadout field

/-- Read local motional-emf density in volts per metre. -/
def motionalEmfDensityInVoltsPerMeter
    (density : MotionalEmfDensityMagnitude) : ℝ :=
  nonnegativeSIReadout density

/-- Read an electric potential difference in volts. -/
def potentialDifferenceInVolts
    (potential : ElectricPotentialDifference) : ℝ :=
  nonnegativeSIReadout potential

/-! ## Component roles, figure vocabulary, and physical setup -/

/-- Idealization assigned to the current-carrying source wire. -/
inductive SourceWireModel where
  | idealInfiniteStraightWire
  | other
  deriving DecidableEq, Repr

/-- Idealization assigned to the moving metal object. -/
inductive MovingBarModel where
  | straightMetalConductor
  | other
  deriving DecidableEq, Repr

/-- The two ends of the moving bar, distinguished by distance from the wire. -/
inductive BarEndpoint where
  | nearWire
  | farFromWire
  deriving DecidableEq, Fintype, Repr

/-- The four physical quantities explicitly labelled in the raster. -/
inductive FigureQuantityLabel where
  | sourceCurrent
  | barSpeed
  | wireBarGap
  | barLength
  deriving DecidableEq, Fintype, Repr

/-- The printed symbol expected for each labelled quantity. -/
def expectedPrintedSymbol : FigureQuantityLabel → String
  | .sourceCurrent => "I"
  | .barSpeed => "v"
  | .wireBarGap => "d"
  | .barLength => "l"

/-- The two axes needed to describe the idealized planar figure. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Directions of the two single-headed arrows visible in the figure. -/
inductive FigureArrowDirection where
  | upward
  | downward
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-!
Literal and idealized readouts of image `883.png`.  Quantitative distances are
kept in the physical setup; this structure records only presentation and
orientation facts from the raster.
-/
structure StraightWireMovingBarFigure where
  quantityLabelShown : FigureQuantityLabel → Bool
  printedSymbol : FigureQuantityLabel → String
  sourceWireAxis : FigureAxis
  movingBarAxis : FigureAxis
  currentArrowDirection : FigureArrowDirection
  velocityArrowDirection : FigureArrowDirection
  currentArrowShown : Bool
  velocityArrowShown : Bool
  gapDoubleArrowShown : Bool
  barLengthDoubleArrowShown : Bool
  barDrawnToRightOfSourceWire : Bool

/-!
Independent physical quantities in the apparatus.  The field profiles and the
potential difference are not defined from the answer; the governing laws that
relate them are separate assumptions below.
-/
structure StraightWireMovingBarSetup where
  sourceWireModel : SourceWireModel
  movingBarModel : MovingBarModel
  mediumPermeability : MagneticPermeabilityQuantity
  sourceCurrentMagnitude : ElectricCurrentMagnitude
  barSpeed : SpeedQuantity
  wireBarGap : LengthQuantity
  barLength : LengthQuantity
  barEndpointRadialDistance : BarEndpoint → LengthQuantity
  magneticFieldMagnitudeAtRadiusMeter : ℝ → MagneticFluxDensityMagnitude
  motionalEmfDensityAtRadiusMeter : ℝ → MotionalEmfDensityMagnitude
  nearEndMinusFarEndPotential : ElectricPotentialDifference
  figure : StraightWireMovingBarFigure

/-! ## Scenario, primary-figure evidence, and governing laws -/

/-- The component idealizations and nondegenerate physical magnitudes. -/
structure MatchesStraightWireMovingBarScenario
    (setup : StraightWireMovingBarSetup) : Prop where
  sourceIsIdealInfiniteStraightWire :
    setup.sourceWireModel = .idealInfiniteStraightWire
  movingObjectIsStraightMetalConductor :
    setup.movingBarModel = .straightMetalConductor
  permeabilityPositive :
    0 < permeabilityInHenriesPerMeter setup.mediumPermeability
  currentMagnitudePositive :
    0 < currentInAmperes setup.sourceCurrentMagnitude
  speedPositive :
    0 < speedInMetersPerSecond setup.barSpeed
  gapPositive :
    0 < lengthInMeters setup.wireBarGap
  barLengthPositive :
    0 < lengthInMeters setup.barLength

/-!
The labels, orientations, arrow directions, and distance assignments supplied
by the primary raster.  In particular, the current and velocity arrows are
both upward (parallel), while the bar is horizontal.  The far-end radius is
`d + l`; no potential-difference value is asserted here.
-/
structure MatchesSuppliedStraightWireMovingBarFigure
    (setup : StraightWireMovingBarSetup) : Prop where
  allFourQuantityLabelsShown :
    ∀ label, setup.figure.quantityLabelShown label = true
  printedQuantitySymbols :
    ∀ label, setup.figure.printedSymbol label = expectedPrintedSymbol label
  sourceWireIsVertical :
    setup.figure.sourceWireAxis = .vertical
  movingBarIsHorizontal :
    setup.figure.movingBarAxis = .horizontal
  currentArrowPointsUpward :
    setup.figure.currentArrowDirection = .upward
  velocityArrowPointsUpward :
    setup.figure.velocityArrowDirection = .upward
  currentArrowIsShown :
    setup.figure.currentArrowShown = true
  velocityArrowIsShown :
    setup.figure.velocityArrowShown = true
  gapDoubleArrowIsShown :
    setup.figure.gapDoubleArrowShown = true
  barLengthDoubleArrowIsShown :
    setup.figure.barLengthDoubleArrowShown = true
  barIsDrawnToRightOfWire :
    setup.figure.barDrawnToRightOfSourceWire = true
  nearEndDistanceIsGap :
    lengthInMeters (setup.barEndpointRadialDistance .nearWire) =
      lengthInMeters setup.wireBarGap
  farEndDistanceIsGapPlusLength :
    lengthInMeters (setup.barEndpointRadialDistance .farFromWire) =
      lengthInMeters setup.wireBarGap + lengthInMeters setup.barLength

/-!
The governing electromagnetic laws used in the intended derivation.

* The first field is the magnitude `B(r) = μ I / (2 π r)` around an ideal
  infinite straight wire.
* For the upward velocity and current shown in the figure, the magnitude of
  the radially oriented motional-emf density along the bar is `v B(r)`.
* The near-end-minus-far-end potential is the line integral of that density
  from the near radius to the far radius.

These are general local and integral laws.  They do not assume the logarithmic
closed form requested by the current question.
-/
structure SatisfiesStraightWireMotionalEmfLaws
    (setup : StraightWireMovingBarSetup) : Prop where
  infiniteStraightWireMagneticField :
    ∀ radiusMeters : ℝ, 0 < radiusMeters →
      magneticFluxDensityInTeslas
          (setup.magneticFieldMagnitudeAtRadiusMeter radiusMeters) =
        permeabilityInHenriesPerMeter setup.mediumPermeability *
            currentInAmperes setup.sourceCurrentMagnitude /
          (2 * Real.pi * radiusMeters)
  localMotionalEmfDensity :
    ∀ radiusMeters : ℝ,
      lengthInMeters (setup.barEndpointRadialDistance .nearWire) ≤
          radiusMeters →
      radiusMeters ≤
          lengthInMeters (setup.barEndpointRadialDistance .farFromWire) →
      motionalEmfDensityInVoltsPerMeter
          (setup.motionalEmfDensityAtRadiusMeter radiusMeters) =
        speedInMetersPerSecond setup.barSpeed *
          magneticFluxDensityInTeslas
            (setup.magneticFieldMagnitudeAtRadiusMeter radiusMeters)
  potentialDifferenceIsMotionalLineIntegral :
    potentialDifferenceInVolts setup.nearEndMinusFarEndPotential =
      ∫ radiusMeters in
          lengthInMeters (setup.barEndpointRadialDistance .nearWire)..
          lengthInMeters (setup.barEndpointRadialDistance .farFromWire),
        motionalEmfDensityInVoltsPerMeter
          (setup.motionalEmfDensityAtRadiusMeter radiusMeters)

/-!
For the geometry and electromagnetic laws above, the potential at the end of
the moving bar nearer the source wire minus that at the farther end is answer
choice C:

`(μ v I / (2 π)) log ((d + l) / d)`.
-/
theorem nearEndMinusFarEndPotential_eq_answer_C
    (setup : StraightWireMovingBarSetup)
    (scenario : MatchesStraightWireMovingBarScenario setup)
    (figure : MatchesSuppliedStraightWireMovingBarFigure setup)
    (laws : SatisfiesStraightWireMotionalEmfLaws setup) :
    potentialDifferenceInVolts setup.nearEndMinusFarEndPotential =
      (permeabilityInHenriesPerMeter setup.mediumPermeability *
          speedInMetersPerSecond setup.barSpeed *
          currentInAmperes setup.sourceCurrentMagnitude /
        (2 * Real.pi)) *
        Real.log
          ((lengthInMeters setup.wireBarGap +
              lengthInMeters setup.barLength) /
            lengthInMeters setup.wireBarGap) := by
  rw [laws.potentialDifferenceIsMotionalLineIntegral,
    figure.nearEndDistanceIsGap,
    figure.farEndDistanceIsGapPlusLength]
  have hfarPos :
      0 < lengthInMeters setup.wireBarGap + lengthInMeters setup.barLength :=
    add_pos scenario.gapPositive scenario.barLengthPositive
  have hbounds :
      lengthInMeters setup.wireBarGap ≤
        lengthInMeters setup.wireBarGap + lengthInMeters setup.barLength :=
    le_of_lt (lt_add_of_pos_right _ scenario.barLengthPositive)
  calc
    (∫ radiusMeters in lengthInMeters setup.wireBarGap..
        lengthInMeters setup.wireBarGap + lengthInMeters setup.barLength,
        motionalEmfDensityInVoltsPerMeter
          (setup.motionalEmfDensityAtRadiusMeter radiusMeters)) =
        ∫ radiusMeters in lengthInMeters setup.wireBarGap..
          lengthInMeters setup.wireBarGap + lengthInMeters setup.barLength,
          (permeabilityInHenriesPerMeter setup.mediumPermeability *
              speedInMetersPerSecond setup.barSpeed *
              currentInAmperes setup.sourceCurrentMagnitude /
            (2 * Real.pi)) * (1 / radiusMeters) := by
      apply intervalIntegral.integral_congr
      intro radiusMeters hradius
      rw [Set.uIcc_of_le hbounds] at hradius
      have hnear :
          lengthInMeters (setup.barEndpointRadialDistance .nearWire) ≤
            radiusMeters := by
        rw [figure.nearEndDistanceIsGap]
        exact hradius.1
      have hfar :
          radiusMeters ≤
            lengthInMeters (setup.barEndpointRadialDistance .farFromWire) := by
        rw [figure.farEndDistanceIsGapPlusLength]
        exact hradius.2
      change motionalEmfDensityInVoltsPerMeter
          (setup.motionalEmfDensityAtRadiusMeter radiusMeters) = _
      rw [laws.localMotionalEmfDensity radiusMeters hnear hfar,
        laws.infiniteStraightWireMagneticField radiusMeters
          (scenario.gapPositive.trans_le hradius.1)]
      ring
    _ = (permeabilityInHenriesPerMeter setup.mediumPermeability *
            speedInMetersPerSecond setup.barSpeed *
            currentInAmperes setup.sourceCurrentMagnitude /
          (2 * Real.pi)) *
        (∫ radiusMeters in lengthInMeters setup.wireBarGap..
          lengthInMeters setup.wireBarGap + lengthInMeters setup.barLength,
          1 / radiusMeters) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (permeabilityInHenriesPerMeter setup.mediumPermeability *
            speedInMetersPerSecond setup.barSpeed *
            currentInAmperes setup.sourceCurrentMagnitude /
          (2 * Real.pi)) *
        Real.log
          ((lengthInMeters setup.wireBarGap +
              lengthInMeters setup.barLength) /
            lengthInMeters setup.wireBarGap) := by
      rw [integral_one_div_of_pos scenario.gapPositive hfarPos]

end PhyXMiniProblems.ProblemPhyXMini0883
