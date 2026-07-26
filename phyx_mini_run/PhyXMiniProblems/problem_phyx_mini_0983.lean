import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Electromagnetism.Dynamics.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0983

open Dimension

/-!
# Maxwell displacement-current induction in a radial--axial circuit

The primary image shows a cylindrical region with an upward axial electric
field, a dashed cylinder axis, a circular Ampere path of radius `r`, and a
conducting rectangular circuit.  The circuit has its inner axial side on the
cylinder axis, radial width `a`, axial height `b`, and a resistor `R` on its
upper branch.  The electric field starts at zero and has axial component
`E(t) = eta * t^2`.

The physical route is Ampere--Maxwell induction of an azimuthal magnetic
field, magnetic flux through the radial--axial rectangle, Faraday--Lenz
induction, and Ohm's law.  Physical magnitudes use Physlib's unit-independent
`Dimensionful` quantities.  Real numbers below are coherent-SI readouts,
measured coordinates, scalar field components, or literal source-choice
expressions.

Assumption/target split:

* governing laws: the quadratic electric-field profile and derivative,
  cylindrical Ampere--Maxwell circulation, the radial magnetic-flux integral,
  Faraday--Lenz, Ohm's law, and a generic sign-to-current-direction rule;
* previous-part results: none;
* figure/data readouts: the cylinder and dashed axis, upward electric-field
  arrows, circular path and radius `r`, rectangular circuit, labels `a`, `b`,
  and `R`, inner circuit side on the axis, and observation time `5.00 s`;
* current target conclusions: the current on the upper radial branch points
  outward when viewed from above, and the physically supported current
  magnitude is `mu_0 * epsilon_0 * eta * b * a^2 / (2 * R)`.

The dataset's recorded choice B has an extra factor of `b`.  It is retained
below only as literal source metadata, not as a physical target or premise.

Neither current conclusion occurs in a setup, scenario predicate, physical
parameter predicate, or governing-law field.
-/

/-! ## Physical dimensions and coherent-SI readouts -/

/-- Electric-field dimension `M L T^-2 C^-1` (volt per metre). -/
def electricFieldDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Dimension of `eta` in `E(t) = eta * t^2`, namely electric field per time squared. -/
def electricFieldQuadraticCoefficientDimension : Dimension :=
  electricFieldDimension * T𝓭⁻¹ * T𝓭⁻¹

/-- Dimension of the time derivative of an electric-field component. -/
def electricFieldRateDimension : Dimension :=
  electricFieldDimension * T𝓭⁻¹

/-- Magnetic-flux-density dimension `M T^-1 C^-1` (tesla). -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic-flux dimension `M L^2 T^-1 C^-1` (weber). -/
def magneticFluxDimension : Dimension :=
  magneticFluxDensityDimension * L𝓭 * L𝓭

/-- Magnetic-flux-rate and electromotive-force dimension (volt). -/
def electromotiveForceDimension : Dimension :=
  magneticFluxDimension * T𝓭⁻¹

/-- Electric-current dimension `C T^-1` (ampere). -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Electrical-resistance dimension `M L^2 T^-1 C^-2` (ohm). -/
def electricalResistanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- Vacuum-permittivity dimension `C^2 T^2 M^-1 L^-3`. -/
def vacuumPermittivityDimension : Dimension :=
  C𝓭 * C𝓭 * T𝓭 * T𝓭 * M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- Vacuum-permeability dimension `M L C^-2`. -/
def vacuumPermeabilityDimension : Dimension :=
  M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical time. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- The nonnegative physical coefficient `eta` in `E(t) = eta * t^2`. -/
abbrev ElectricFieldQuadraticCoefficientMagnitude : Type :=
  Dimensionful
    (WithDim electricFieldQuadraticCoefficientDimension NNReal)

/-- A signed axial electric-field component. -/
abbrev SignedElectricFieldComponent : Type :=
  Dimensionful (WithDim electricFieldDimension ℝ)

/-- A signed time derivative of an axial electric-field component. -/
abbrev SignedElectricFieldRate : Type :=
  Dimensionful (WithDim electricFieldRateDimension ℝ)

/-- A signed azimuthal magnetic-flux-density component. -/
abbrev SignedMagneticFluxDensityComponent : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension ℝ)

/-- Signed magnetic flux through the oriented rectangular circuit. -/
abbrev SignedMagneticFlux : Type :=
  Dimensionful (WithDim magneticFluxDimension ℝ)

/-- Signed magnetic-flux rate at the observation time. -/
abbrev SignedMagneticFluxRate : Type :=
  Dimensionful (WithDim electromotiveForceDimension ℝ)

/-- Signed electromotive force relative to the chosen circuit traversal. -/
abbrev ElectromotiveForce : Type :=
  Dimensionful (WithDim electromotiveForceDimension ℝ)

/-- Signed electric current relative to the chosen circuit traversal. -/
abbrev ElectricCurrent : Type :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- A nonnegative total circuit resistance. -/
abbrev ElectricalResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative physical vacuum permittivity. -/
abbrev VacuumPermittivityMagnitude : Type :=
  Dimensionful (WithDim vacuumPermittivityDimension NNReal)

/-- A nonnegative physical vacuum permeability. -/
abbrev VacuumPermeabilityMagnitude : Type :=
  Dimensionful (WithDim vacuumPermeabilityDimension NNReal)

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a signed dimensionful quantity. -/
def signedSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Read physical time in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  nonnegativeSIReadout time

/-- Read physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Read `eta` in volts per metre per second squared. -/
def coefficientInVoltsPerMeterSecondSquared
    (coefficient : ElectricFieldQuadraticCoefficientMagnitude) : ℝ :=
  nonnegativeSIReadout coefficient

/-- Read a signed electric-field component in volts per metre. -/
def electricFieldComponentInVoltsPerMeter
    (field : SignedElectricFieldComponent) : ℝ :=
  signedSIReadout field

/-- Read a signed electric-field rate in volts per metre per second. -/
def electricFieldRateInVoltsPerMeterSecond
    (rate : SignedElectricFieldRate) : ℝ :=
  signedSIReadout rate

/-- Read a signed magnetic-flux-density component in teslas. -/
def magneticFluxDensityComponentInTeslas
    (field : SignedMagneticFluxDensityComponent) : ℝ :=
  signedSIReadout field

/-- Read signed magnetic flux in webers. -/
def magneticFluxInWebers (flux : SignedMagneticFlux) : ℝ :=
  signedSIReadout flux

/-- Read signed magnetic-flux rate in webers per second. -/
def magneticFluxRateInWebersPerSecond
    (rate : SignedMagneticFluxRate) : ℝ :=
  signedSIReadout rate

/-- Read signed electromotive force in volts. -/
def electromotiveForceInVolts (emf : ElectromotiveForce) : ℝ :=
  signedSIReadout emf

/-- Read signed electric current in amperes. -/
def electricCurrentInAmperes (current : ElectricCurrent) : ℝ :=
  signedSIReadout current

/-- Read the magnitude of a signed electric current in amperes. -/
def electricCurrentMagnitudeInAmperes (current : ElectricCurrent) : ℝ :=
  |electricCurrentInAmperes current|

/-- Read total circuit resistance in ohms. -/
def resistanceInOhms (resistance : ElectricalResistanceMagnitude) : ℝ :=
  nonnegativeSIReadout resistance

/-- Read vacuum permittivity in farads per metre. -/
def permittivityInFaradsPerMeter
    (permittivity : VacuumPermittivityMagnitude) : ℝ :=
  nonnegativeSIReadout permittivity

/-- Read vacuum permeability in henries per metre. -/
def permeabilityInHenriesPerMeter
    (permeability : VacuumPermeabilityMagnitude) : ℝ :=
  nonnegativeSIReadout permeability

/-! ## Primary-image vocabulary and circuit geometry -/

/-- Named physical features visible in image `983.png`. -/
inductive FigureFeature where
  | cylindricalElectricFieldRegion
  | upwardElectricFieldArrows
  | dashedCylinderAxis
  | circularAmperePath
  | radialAxialRectangularCircuit
  | resistorOnUpperBranch
  deriving DecidableEq, Fintype, Repr

/-- Symbols printed in the primary image. -/
inductive FigureLabel where
  | electricFieldE
  | resistanceR
  | ampereRadiusr
  | radialWidtha
  | axialLengthb
  deriving DecidableEq, Fintype, Repr

/-- Physical role of each printed label. -/
inductive FigureLabelRole where
  | axialElectricField
  | totalCircuitResistance
  | circularAmperePathRadius
  | circuitRadialWidth
  | circuitAxialLength
  deriving DecidableEq, Repr

/-- Direction along the vertical cylinder axis. -/
inductive AxialDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Orientation of the radial--axial rectangle's unit normal. -/
inductive AzimuthalNormalOrientation where
  | rightHandedAboutUpwardAxis
  | oppositeRightHandedAboutUpwardAxis
  deriving DecidableEq, Repr

/-- Current direction resolvable in a view from above the cylinder. -/
inductive CurrentDirectionFromAbove where
  | radiallyOutwardAlongUpperBranch
  | radiallyInwardAlongUpperBranch
  deriving DecidableEq, Repr

/-- View used by the qualitative direction question. -/
inductive DiagramViewpoint where
  | aboveCylinder
  | sideOfCylinder
  deriving DecidableEq, Repr

/-- Literal and qualitative evidence transcribed from the primary raster. -/
structure MaxwellInductionFigure where
  featureShown : FigureFeature → Bool
  labelShown : FigureLabel → Bool
  labelRole : FigureLabel → FigureLabelRole
  electricFieldArrowDirection : AxialDirection
  circuitInnerAxialSideCoincidesWithAxis : Bool
  circularPathCenteredOnAxis : Bool
  circularPathCrossesCircuitSurface : Bool
  resistorLiesOnUpperRadialBranch : Bool
  viewpointRequestedByQuestion : DiagramViewpoint
  containsNumericalLengthOrResistanceReadout : Bool

/-!
The conducting circuit and its spanning radial--axial rectangle.  The first
coordinate of `pointAtMeters` is radial distance from the cylinder axis and
the second is axial distance along the side of length `b`.
-/
structure RadialAxialCircuitGeometry where
  spanningSurface : Set (Space 3)
  cylinderAxis : Set (Space 3)
  pointAtMeters : ℝ → ℝ → Space 3
  radialWidtha : LengthQuantity
  axialLengthb : LengthQuantity
  displayedAmpereRadiusr : LengthQuantity
  radialDirection : EuclideanSpace ℝ (Fin 3)
  upwardAxialDirection : EuclideanSpace ℝ (Fin 3)
  orientedAzimuthalNormal : EuclideanSpace ℝ (Fin 3)
  normalOrientation : AzimuthalNormalOrientation

/-!
Independent physical objects, profiles, and observables.  The field profiles
are dimensionful scalar components used to calibrate Physlib's spacetime
vector fields.  The induced current and its direction are independent fields,
not definitions made from an answer choice.
-/
structure DisplacementCurrentInductionSetup where
  figure : MaxwellInductionFigure
  geometry : RadialAxialCircuitGeometry
  cylindricalFieldRegion : Set (Time × Space 3)
  electricField : Electromagnetism.ElectricField 3
  inducedMagneticField : Electromagnetism.MagneticField 3
  electricFieldCoefficientEta : ElectricFieldQuadraticCoefficientMagnitude
  axialElectricFieldComponent : ℝ → SignedElectricFieldComponent
  axialElectricFieldRate : ℝ → SignedElectricFieldRate
  azimuthalMagneticFieldComponentAtMeters :
    ℝ → ℝ → SignedMagneticFluxDensityComponent
  rectangularMagneticFlux : ℝ → SignedMagneticFlux
  fluxRateAtObservation : SignedMagneticFluxRate
  inducedEmfAtObservation : ElectromotiveForce
  inducedCurrentAtObservation : ElectricCurrent
  inducedCurrentDirectionFromAbove : CurrentDirectionFromAbove
  observationTime : TimeQuantity
  totalCircuitResistanceR : ElectricalResistanceMagnitude
  vacuumPermittivityEpsilon0 : VacuumPermittivityMagnitude
  vacuumPermeabilityMu0 : VacuumPermeabilityMagnitude
  freeSpace : Electromagnetism.FreeSpace

/-! ## Scenario, figure, geometry, and physical-parameter assumptions -/

/-- Prose and primary-raster data, containing no induced-current answer. -/
structure MatchesProblemAndPrimaryFigure
    (setup : DisplacementCurrentInductionSetup) : Prop where
  everyNamedFeatureShown :
    ∀ feature : FigureFeature, setup.figure.featureShown feature = true
  everyPrintedLabelShown :
    ∀ label : FigureLabel, setup.figure.labelShown label = true
  electricFieldLabelRole :
    setup.figure.labelRole .electricFieldE = .axialElectricField
  resistanceLabelRole :
    setup.figure.labelRole .resistanceR = .totalCircuitResistance
  radiusLabelRole :
    setup.figure.labelRole .ampereRadiusr = .circularAmperePathRadius
  widthLabelRole :
    setup.figure.labelRole .radialWidtha = .circuitRadialWidth
  lengthLabelRole :
    setup.figure.labelRole .axialLengthb = .circuitAxialLength
  fieldArrowsPointUpward :
    setup.figure.electricFieldArrowDirection = .upward
  innerCircuitSideOnAxis :
    setup.figure.circuitInnerAxialSideCoincidesWithAxis = true
  amperePathCenteredOnAxis :
    setup.figure.circularPathCenteredOnAxis = true
  amperePathCrossesCircuitSurface :
    setup.figure.circularPathCrossesCircuitSurface = true
  resistorOnUpperBranch :
    setup.figure.resistorLiesOnUpperRadialBranch = true
  requestedViewIsFromAbove :
    setup.figure.viewpointRequestedByQuestion = .aboveCylinder
  noNumericalGeometryDataInRaster :
    setup.figure.containsNumericalLengthOrResistanceReadout = false
  observationAtFiveSeconds :
    timeInSeconds setup.observationTime = 5

/-- Geometric meaning of the rectangle drawn tight against the axis. -/
structure SatisfiesRadialAxialCircuitGeometry
    (setup : DisplacementCurrentInductionSetup) : Prop where
  allParameterPointsOnSurface : ∀ radialMeters axialMeters,
    radialMeters ∈ Set.Icc 0 (lengthInMeters setup.geometry.radialWidtha) →
    axialMeters ∈ Set.Icc 0 (lengthInMeters setup.geometry.axialLengthb) →
    setup.geometry.pointAtMeters radialMeters axialMeters ∈
      setup.geometry.spanningSurface
  innerSideLiesOnAxis : ∀ axialMeters,
    axialMeters ∈ Set.Icc 0 (lengthInMeters setup.geometry.axialLengthb) →
    setup.geometry.pointAtMeters 0 axialMeters ∈ setup.geometry.cylinderAxis
  radiusMarkerWithinCircuitWidth :
    lengthInMeters setup.geometry.displayedAmpereRadiusr ≤
      lengthInMeters setup.geometry.radialWidtha
  radialDirectionIsUnit : ‖setup.geometry.radialDirection‖ = 1
  axialDirectionIsUnit : ‖setup.geometry.upwardAxialDirection‖ = 1
  normalIsUnit : ‖setup.geometry.orientedAzimuthalNormal‖ = 1
  radialAndAxialDirectionsPerpendicular :
    inner ℝ setup.geometry.radialDirection
      setup.geometry.upwardAxialDirection = 0
  normalPerpendicularToRadialDirection :
    inner ℝ setup.geometry.orientedAzimuthalNormal
      setup.geometry.radialDirection = 0
  normalPerpendicularToAxialDirection :
    inner ℝ setup.geometry.orientedAzimuthalNormal
      setup.geometry.upwardAxialDirection = 0
  normalUsesRightHandRule :
    setup.geometry.normalOrientation = .rightHandedAboutUpwardAxis

/-- Positivity, nondegeneracy, and Physlib calibration assumptions. -/
structure HasPhysicalInductionParameters
    (setup : DisplacementCurrentInductionSetup) : Prop where
  coefficientPositive :
    0 < coefficientInVoltsPerMeterSecondSquared
      setup.electricFieldCoefficientEta
  radialWidthPositive : 0 < lengthInMeters setup.geometry.radialWidtha
  axialLengthPositive : 0 < lengthInMeters setup.geometry.axialLengthb
  ampereRadiusPositive :
    0 < lengthInMeters setup.geometry.displayedAmpereRadiusr
  observationTimePositive : 0 < timeInSeconds setup.observationTime
  resistancePositive : 0 < resistanceInOhms setup.totalCircuitResistanceR
  permittivityPositive :
    0 < permittivityInFaradsPerMeter setup.vacuumPermittivityEpsilon0
  permeabilityPositive :
    0 < permeabilityInHenriesPerMeter setup.vacuumPermeabilityMu0
  permittivityAgreesWithPhyslib :
    permittivityInFaradsPerMeter setup.vacuumPermittivityEpsilon0 =
      setup.freeSpace.ε₀
  permeabilityAgreesWithPhyslib :
    permeabilityInHenriesPerMeter setup.vacuumPermeabilityMu0 =
      setup.freeSpace.μ₀
  fieldRegionNonempty : setup.cylindricalFieldRegion.Nonempty
  circuitSurfaceNonempty : setup.geometry.spanningSurface.Nonempty

/-! ## Governing electromagnetic and circuit laws -/

/-!
The uniform axial field is calibrated to the Physlib electric field and has
the stated quadratic time dependence.  Its rate is introduced by a genuine
derivative relation rather than by differentiating inside a target formula.
-/
structure SatisfiesQuadraticAxialElectricFieldModel
    (setup : DisplacementCurrentInductionSetup) : Prop where
  fieldSpatiallyUniform : ∀ time p q,
    (time, p) ∈ setup.cylindricalFieldRegion →
    (time, q) ∈ setup.cylindricalFieldRegion →
    setup.electricField time p = setup.electricField time q
  dimensionfulComponentAgreesWithVectorField : ∀ time p,
    (time, p) ∈ setup.cylindricalFieldRegion →
    setup.electricField time p =
      electricFieldComponentInVoltsPerMeter
          (setup.axialElectricFieldComponent time) •
        setup.geometry.upwardAxialDirection
  quadraticTimeProfile : ∀ timeSeconds : ℝ,
    electricFieldComponentInVoltsPerMeter
        (setup.axialElectricFieldComponent timeSeconds) =
      coefficientInVoltsPerMeterSecondSquared
          setup.electricFieldCoefficientEta * timeSeconds ^ 2
  fieldInitiallyZero :
    electricFieldComponentInVoltsPerMeter
      (setup.axialElectricFieldComponent 0) = 0
  fieldRateIsDerivative : ∀ timeSeconds : ℝ,
    HasDerivAt
      (fun t => electricFieldComponentInVoltsPerMeter
        (setup.axialElectricFieldComponent t))
      (electricFieldRateInVoltsPerMeterSecond
        (setup.axialElectricFieldRate timeSeconds))
      timeSeconds

/-!
Cylindrical Ampere--Maxwell law for circular paths centered on the axis.
The right side is vacuum displacement current through the disk of radius
`r`; no requested current in the conducting rectangle appears here.
-/
structure SatisfiesCylindricalAmpereMaxwellLaw
    (setup : DisplacementCurrentInductionSetup) : Prop where
  magneticFieldOnCircuitSurfaceIsAzimuthal : ∀ timeSeconds radialMeters axialMeters,
    radialMeters ∈ Set.Icc 0 (lengthInMeters setup.geometry.radialWidtha) →
    axialMeters ∈ Set.Icc 0 (lengthInMeters setup.geometry.axialLengthb) →
    setup.inducedMagneticField timeSeconds
        (setup.geometry.pointAtMeters radialMeters axialMeters) =
      magneticFluxDensityComponentInTeslas
          (setup.azimuthalMagneticFieldComponentAtMeters
            timeSeconds radialMeters) •
        setup.geometry.orientedAzimuthalNormal
  fieldComponentAtAxisIsZero : ∀ timeSeconds,
    magneticFluxDensityComponentInTeslas
      (setup.azimuthalMagneticFieldComponentAtMeters timeSeconds 0) = 0
  ampereMaxwellCirculation : ∀ timeSeconds radialMeters : ℝ,
    0 < radialMeters →
    radialMeters ≤ lengthInMeters setup.geometry.radialWidtha →
    magneticFluxDensityComponentInTeslas
          (setup.azimuthalMagneticFieldComponentAtMeters
            timeSeconds radialMeters) *
        (2 * Real.pi * radialMeters) =
      permeabilityInHenriesPerMeter setup.vacuumPermeabilityMu0 *
        permittivityInFaradsPerMeter setup.vacuumPermittivityEpsilon0 *
        (Real.pi * radialMeters ^ 2) *
        electricFieldRateInVoltsPerMeterSecond
          (setup.axialElectricFieldRate timeSeconds)
  radialProfileIntervalIntegrable : ∀ timeSeconds,
    IntervalIntegrable
      (fun radialMeters =>
        magneticFluxDensityComponentInTeslas
          (setup.azimuthalMagneticFieldComponentAtMeters
            timeSeconds radialMeters))
      MeasureTheory.volume 0 (lengthInMeters setup.geometry.radialWidtha)

/-!
The aligned field flux is the axial length `b` times the radial integral from
the axis to width `a`.  Faraday--Lenz and passive-sign Ohm law determine the
signed emf and current.  The direction clauses are generic implications from
current sign; they do not assume which sign occurs in this problem.
-/
structure SatisfiesFluxFaradayOhmAndDirectionLaws
    (setup : DisplacementCurrentInductionSetup) : Prop where
  fluxIsRadialSurfaceIntegral : ∀ timeSeconds,
    magneticFluxInWebers (setup.rectangularMagneticFlux timeSeconds) =
      lengthInMeters setup.geometry.axialLengthb *
        (∫ radialMeters in
          (0 : ℝ)..lengthInMeters setup.geometry.radialWidtha,
          magneticFluxDensityComponentInTeslas
            (setup.azimuthalMagneticFieldComponentAtMeters
              timeSeconds radialMeters))
  fluxRateAtObservationIsDerivative :
    HasDerivAt
      (fun timeSeconds =>
        magneticFluxInWebers (setup.rectangularMagneticFlux timeSeconds))
      (magneticFluxRateInWebersPerSecond setup.fluxRateAtObservation)
      (timeInSeconds setup.observationTime)
  faradayLenzLaw :
    electromotiveForceInVolts setup.inducedEmfAtObservation =
      -magneticFluxRateInWebersPerSecond setup.fluxRateAtObservation
  passiveSeriesCircuitOhmLaw :
    electromotiveForceInVolts setup.inducedEmfAtObservation =
      resistanceInOhms setup.totalCircuitResistanceR *
        electricCurrentInAmperes setup.inducedCurrentAtObservation
  positiveTraversalRunsInwardOnUpperBranch :
    0 < electricCurrentInAmperes setup.inducedCurrentAtObservation →
      setup.inducedCurrentDirectionFromAbove =
        .radiallyInwardAlongUpperBranch
  negativeTraversalRunsOutwardOnUpperBranch :
    electricCurrentInAmperes setup.inducedCurrentAtObservation < 0 →
      setup.inducedCurrentDirectionFromAbove =
        .radiallyOutwardAlongUpperBranch

/-! ## Source answer metadata and formalization target -/

/-- Labels of the four source expressions. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
Literal scalar transcription of the source choices.  These are deliberately
not typed as electric currents: as printed, several are dimensionally
inconsistent, including choice B's extra factor of the axial length `b`.
-/
def displayedSourceExpression
    (setup : DisplacementCurrentInductionSetup) : AnswerChoice → ℝ
  | .A =>
      permeabilityInHenriesPerMeter setup.vacuumPermeabilityMu0 *
        coefficientInVoltsPerMeterSecondSquared
          setup.electricFieldCoefficientEta *
        lengthInMeters setup.geometry.axialLengthb ^ 2 /
        (2 * resistanceInOhms setup.totalCircuitResistanceR)
  | .B =>
      permeabilityInHenriesPerMeter setup.vacuumPermeabilityMu0 *
        permittivityInFaradsPerMeter setup.vacuumPermittivityEpsilon0 *
        coefficientInVoltsPerMeterSecondSquared
          setup.electricFieldCoefficientEta *
        lengthInMeters setup.geometry.axialLengthb ^ 2 *
        lengthInMeters setup.geometry.radialWidtha ^ 2 /
        (2 * resistanceInOhms setup.totalCircuitResistanceR)
  | .C =>
      permeabilityInHenriesPerMeter setup.vacuumPermeabilityMu0 *
        permittivityInFaradsPerMeter setup.vacuumPermittivityEpsilon0 *
        coefficientInVoltsPerMeterSecondSquared
          setup.electricFieldCoefficientEta *
        lengthInMeters setup.geometry.radialWidtha ^ 2 /
        (2 * resistanceInOhms setup.totalCircuitResistanceR)
  | .D =>
      permeabilityInHenriesPerMeter setup.vacuumPermeabilityMu0 *
        permittivityInFaradsPerMeter setup.vacuumPermittivityEpsilon0 *
        coefficientInVoltsPerMeterSecondSquared
          setup.electricFieldCoefficientEta *
        lengthInMeters setup.geometry.axialLengthb *
        lengthInMeters setup.geometry.radialWidtha

/-- The dataset metadata records source choice B. -/
def recordedDatasetAnswer : AnswerChoice :=
  .B

/-!
At `5.00 s`, the direction conclusion states the unambiguous top-view
component for the vertical radial--axial rectangle: current on its upper
radial branch travels away from the cylinder axis.  The magnitude is the
dimensionally coherent Maxwell--Faraday--Ohm result.  Since the magnetic flux
is linear in time, its derivative and hence the induced-current magnitude do
not depend on the positive observation time.

The source's recorded choice B remains available through
`recordedDatasetAnswer` and `displayedSourceExpression`; it is not used in
this theorem because its extra factor of `b` gives the dimension of current
times length.

This declaration corresponds to blueprint label
`thm:physics:phyx_mini_0983:target`.
-/
theorem problem_phyx_mini_0983
    (setup : DisplacementCurrentInductionSetup)
    (_hFigure : MatchesProblemAndPrimaryFigure setup)
    (_hGeometry : SatisfiesRadialAxialCircuitGeometry setup)
    (_hPhysical : HasPhysicalInductionParameters setup)
    (_hElectric : SatisfiesQuadraticAxialElectricFieldModel setup)
    (_hAmpereMaxwell : SatisfiesCylindricalAmpereMaxwellLaw setup)
    (_hCircuit : SatisfiesFluxFaradayOhmAndDirectionLaws setup) :
    electricCurrentMagnitudeInAmperes setup.inducedCurrentAtObservation =
        permeabilityInHenriesPerMeter setup.vacuumPermeabilityMu0 *
          permittivityInFaradsPerMeter setup.vacuumPermittivityEpsilon0 *
          coefficientInVoltsPerMeterSecondSquared
            setup.electricFieldCoefficientEta *
          lengthInMeters setup.geometry.axialLengthb *
          lengthInMeters setup.geometry.radialWidtha ^ 2 /
          (2 * resistanceInOhms setup.totalCircuitResistanceR) ∧
      setup.inducedCurrentDirectionFromAbove =
        .radiallyOutwardAlongUpperBranch := by
  let η : ℝ :=
    coefficientInVoltsPerMeterSecondSquared
      setup.electricFieldCoefficientEta
  let a : ℝ := lengthInMeters setup.geometry.radialWidtha
  let b : ℝ := lengthInMeters setup.geometry.axialLengthb
  let μ : ℝ :=
    permeabilityInHenriesPerMeter setup.vacuumPermeabilityMu0
  let ε : ℝ :=
    permittivityInFaradsPerMeter setup.vacuumPermittivityEpsilon0
  let R : ℝ := resistanceInOhms setup.totalCircuitResistanceR
  let I : ℝ :=
    electricCurrentInAmperes setup.inducedCurrentAtObservation
  have hη : 0 < η := _hPhysical.coefficientPositive
  have ha : 0 < a := _hPhysical.radialWidthPositive
  have hb : 0 < b := _hPhysical.axialLengthPositive
  have hμ : 0 < μ := _hPhysical.permeabilityPositive
  have hε : 0 < ε := _hPhysical.permittivityPositive
  have hR : 0 < R := _hPhysical.resistancePositive
  have hElectricFieldRate (timeSeconds : ℝ) :
      electricFieldRateInVoltsPerMeterSecond
          (setup.axialElectricFieldRate timeSeconds) =
        2 * η * timeSeconds := by
    have hActual := _hElectric.fieldRateIsDerivative timeSeconds
    have hModel :
        HasDerivAt (fun t : ℝ => η * (t * t))
          (2 * η * timeSeconds) timeSeconds := by
      exact
        (HasDerivAt.const_mul η
          ((hasDerivAt_id timeSeconds).mul
            (hasDerivAt_id timeSeconds))).congr_deriv (by
              simp only [id_eq]
              ring)
    have hFunctionsAgree :
        (fun t : ℝ =>
            electricFieldComponentInVoltsPerMeter
              (setup.axialElectricFieldComponent t)) =ᶠ[nhds timeSeconds]
          (fun t : ℝ => η * (t * t)) := by
      filter_upwards [] with t
      simpa [η, pow_two] using _hElectric.quadraticTimeProfile t
    exact hActual.unique (hModel.congr_of_eventuallyEq hFunctionsAgree)
  have hMagneticField
      (timeSeconds radialMeters : ℝ)
      (hradialNonnegative : 0 ≤ radialMeters)
      (hradialAtMostWidth : radialMeters ≤ a) :
      magneticFluxDensityComponentInTeslas
          (setup.azimuthalMagneticFieldComponentAtMeters
            timeSeconds radialMeters) =
        μ * ε * η * timeSeconds * radialMeters := by
    rcases hradialNonnegative.eq_or_lt with hzero | hpositive
    · subst radialMeters
      simpa using
        _hAmpereMaxwell.fieldComponentAtAxisIsZero timeSeconds
    · have hCirculation :=
        _hAmpereMaxwell.ampereMaxwellCirculation
          timeSeconds radialMeters hpositive hradialAtMostWidth
      rw [hElectricFieldRate timeSeconds] at hCirculation
      apply mul_right_cancel₀
        (show 2 * Real.pi * radialMeters ≠ 0 by positivity)
      calc
        magneticFluxDensityComponentInTeslas
              (setup.azimuthalMagneticFieldComponentAtMeters
                timeSeconds radialMeters) *
            (2 * Real.pi * radialMeters) =
            μ * ε * (Real.pi * radialMeters ^ 2) *
              (2 * η * timeSeconds) := by
                simpa [μ, ε] using hCirculation
        _ = (μ * ε * η * timeSeconds * radialMeters) *
              (2 * Real.pi * radialMeters) := by ring
  have hFlux (timeSeconds : ℝ) :
      magneticFluxInWebers
          (setup.rectangularMagneticFlux timeSeconds) =
        (μ * ε * η * b * a ^ 2 / 2) * timeSeconds := by
    rw [_hCircuit.fluxIsRadialSurfaceIntegral]
    change
      b *
          (∫ radialMeters in (0 : ℝ)..a,
            magneticFluxDensityComponentInTeslas
              (setup.azimuthalMagneticFieldComponentAtMeters
                timeSeconds radialMeters)) =
        (μ * ε * η * b * a ^ 2 / 2) * timeSeconds
    calc
      b *
          (∫ radialMeters in (0 : ℝ)..a,
            magneticFluxDensityComponentInTeslas
              (setup.azimuthalMagneticFieldComponentAtMeters
                timeSeconds radialMeters)) =
          b * ∫ radialMeters in (0 : ℝ)..a,
            (μ * ε * η * timeSeconds) * radialMeters := by
              congr 1
              apply intervalIntegral.integral_congr
              intro radialMeters radialMetersInInterval
              have radialMetersInCircuit :
                  radialMeters ∈ Set.Icc (0 : ℝ) a := by
                simpa [Set.uIcc_of_le ha.le] using
                  radialMetersInInterval
              exact hMagneticField timeSeconds radialMeters
                radialMetersInCircuit.1 radialMetersInCircuit.2
      _ = (μ * ε * η * b * a ^ 2 / 2) * timeSeconds := by
        rw [intervalIntegral.integral_const_mul, integral_id]
        ring
  let fluxSlope : ℝ := μ * ε * η * b * a ^ 2 / 2
  have hFluxRate :
      magneticFluxRateInWebersPerSecond setup.fluxRateAtObservation =
        fluxSlope := by
    have hActual := _hCircuit.fluxRateAtObservationIsDerivative
    have hModel :
        HasDerivAt (fun t : ℝ => fluxSlope * t) fluxSlope
          (timeInSeconds setup.observationTime) := by
      simpa using
        HasDerivAt.const_mul fluxSlope
          (hasDerivAt_id (timeInSeconds setup.observationTime))
    have hFunctionsAgree :
        (fun t : ℝ =>
            magneticFluxInWebers (setup.rectangularMagneticFlux t)) =ᶠ[
              nhds (timeInSeconds setup.observationTime)]
          (fun t : ℝ => fluxSlope * t) := by
      filter_upwards [] with t
      simpa [fluxSlope] using hFlux t
    exact hActual.unique (hModel.congr_of_eventuallyEq hFunctionsAgree)
  have hFluxSlopePositive : 0 < fluxSlope := by
    dsimp only [fluxSlope]
    positivity
  have hResistanceNonzero : R ≠ 0 := ne_of_gt hR
  have hResistanceTimesCurrent : R * I = -fluxSlope := by
    calc
      R * I =
          electromotiveForceInVolts setup.inducedEmfAtObservation := by
            simpa [R, I] using
              _hCircuit.passiveSeriesCircuitOhmLaw.symm
      _ = -fluxSlope := by
        rw [_hCircuit.faradayLenzLaw, hFluxRate]
  have hCurrent : I = -fluxSlope / R := by
    apply (eq_div_iff hResistanceNonzero).2
    calc
      I * R = R * I := by ring
      _ = -fluxSlope := hResistanceTimesCurrent
  have hCurrentNegative : I < 0 := by
    rw [hCurrent]
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hFluxSlopePositive) hR
  constructor
  · change
      |I| =
        μ * ε * η * b * a ^ 2 / (2 * R)
    rw [abs_of_neg hCurrentNegative, hCurrent]
    dsimp only [fluxSlope]
    field_simp
  · exact
      _hCircuit.negativeTraversalRunsOutwardOnUpperBranch
        hCurrentNegative

end PhyXMiniProblems.ProblemPhyXMini0983
