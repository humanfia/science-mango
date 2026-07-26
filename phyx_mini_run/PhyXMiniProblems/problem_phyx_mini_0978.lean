import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Time.Derivatives
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0978

open Dimension

/-!
# Current induced in a smaller coil by a capacitor discharge

The prose describes a `5000`-turn outer circular coil of radius `40.0 cm`
connected to a `10.00 μF` capacitor whose upper plate initially carries
`+100 μC`.  A concentric, parallel `100`-turn inner coil of radius `4.00 cm`
is made from the same wire, whose resistance per unit length is `0.0100 Ω/m`.
The switch closes at `t = 0`, and the requested observable is the magnitude of
the inner-coil current at `1.26 ms`.

The primary raster uses the labels differently from the prose: it prints
`N₁ turns` beside the inner gray winding and `N₂ turns` beside the outer
capacitor-connected winding.  The formalization preserves that literal label
mapping separately from the prose's numerical assignments, rather than using
the potentially ambiguous subscripts as physical identifiers.

Physlib `Dimensionful` quantities represent all physical magnitudes.  Real
numbers appear only at coherent-SI readout boundaries, in unit conversions,
and in literal displayed data.

Assumption/target split:

* governing laws: circular-wire length and resistance, capacitor and resistor
  laws for the outer `RC` discharge, the magnetic field at the center of a
  circular multi-turn coil, exact flux linkage, a center-field leading term
  with an explicit finite-radius remainder and quadratic remainder-rate bound,
  Faraday's law, and Ohm's law for the inner coil;
* previous-part results: none;
* figure/data readouts: the two concentric parallel winding roles, literal
  `N₁`, `N₂`, `2b`, `a`, `C`, and `S` labels, the prose's turn counts and
  radii, wire resistance per metre, capacitance, initial charge, switching
  time, observation time, and four displayed current choices;
* current target conclusions: a controlled error bound between the physical
  induced-current magnitude and the center-field estimate, and the fact that
  recorded choice B, `365 mA`, is the unique nearest displayed value.

The inner current waveform is an independent setup field.  No premise assigns
its value at `1.26 ms` or mentions a correct answer choice.
-/

/-! ## Dimensions and dimensionful electrical quantities -/

/-- Electric current has dimension charge per time. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Energy has dimension `M L² T⁻²`. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Electric potential difference has dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  energyDimension * C𝓭⁻¹

/-- Electrical resistance has dimension voltage per current. -/
def electricalResistanceDimension : Dimension :=
  electricPotentialDimension * electricCurrentDimension⁻¹

/-- Resistance per unit wire length has dimension resistance per length. -/
def resistancePerLengthDimension : Dimension :=
  electricalResistanceDimension * L𝓭⁻¹

/-- Capacitance has dimension charge per voltage. -/
def capacitanceDimension : Dimension :=
  C𝓭 * electricPotentialDimension⁻¹

/-- Magnetic flux density has dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux has dimension flux density times area. -/
def magneticFluxDimension : Dimension :=
  magneticFluxDensityDimension * L𝓭 * L𝓭

/-- Electromotive force has the same dimension as electric potential. -/
def electromotiveForceDimension : Dimension :=
  electricPotentialDimension

/-- Inductance has dimension voltage times time per current. -/
def inductanceDimension : Dimension :=
  electricPotentialDimension * T𝓭 * electricCurrentDimension⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent resistance per unit length. -/
abbrev ResistancePerLengthMagnitude : Type :=
  Dimensionful (WithDim resistancePerLengthDimension NNReal)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent capacitance. -/
abbrev CapacitanceMagnitude : Type :=
  Dimensionful (WithDim capacitanceDimension NNReal)

/-- A nonnegative, unit-independent charge magnitude. -/
abbrev ChargeMagnitude : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A signed, unit-independent capacitor charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A signed, unit-independent electric potential difference. -/
abbrev SignedPotentialDifference : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A signed, unit-independent electric current. -/
abbrev SignedCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- A signed, unit-independent magnetic flux density. -/
abbrev SignedMagneticFluxDensity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension ℝ)

/-- A signed, unit-independent magnetic flux or flux linkage. -/
abbrev SignedMagneticFlux : Type :=
  Dimensionful (WithDim magneticFluxDimension ℝ)

/-- A signed, unit-independent induced electromotive force. -/
abbrev SignedElectromotiveForce : Type :=
  Dimensionful (WithDim electromotiveForceDimension ℝ)

/-- A nonnegative, unit-independent mutual inductance. -/
abbrev MutualInductanceMagnitude : Type :=
  Dimensionful (WithDim inductanceDimension NNReal)

/-! ## Coherent-SI and displayed-unit readouts -/

/-- Read a signed dimensionful quantity in coherent SI units. -/
def signedSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a length in metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  nonnegativeSIReadout length

/-- Read a length in centimetres. -/
def lengthInCentimeters (length : LengthMagnitude) : ℝ :=
  100 * lengthInMeters length

/-- Read a wire's resistance per unit length in ohms per metre. -/
def resistancePerLengthInOhmsPerMeter
    (resistancePerLength : ResistancePerLengthMagnitude) : ℝ :=
  nonnegativeSIReadout resistancePerLength

/-- Read an electrical resistance in ohms. -/
def resistanceInOhms (resistance : ResistanceMagnitude) : ℝ :=
  nonnegativeSIReadout resistance

/-- Read a capacitance in farads. -/
def capacitanceInFarads (capacitance : CapacitanceMagnitude) : ℝ :=
  nonnegativeSIReadout capacitance

/-- Read a capacitance in microfarads. -/
def capacitanceInMicrofarads (capacitance : CapacitanceMagnitude) : ℝ :=
  (10 : ℝ) ^ 6 * capacitanceInFarads capacitance

/-- Read a nonnegative charge magnitude in coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitude) : ℝ :=
  nonnegativeSIReadout charge

/-- Read a nonnegative charge magnitude in microcoulombs. -/
def chargeMagnitudeInMicrocoulombs (charge : ChargeMagnitude) : ℝ :=
  (10 : ℝ) ^ 6 * chargeMagnitudeInCoulombs charge

/-- Read a signed capacitor charge in coulombs. -/
def signedChargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  signedSIReadout charge

/-- Read a signed potential difference in volts. -/
def potentialDifferenceInVolts
    (voltage : SignedPotentialDifference) : ℝ :=
  signedSIReadout voltage

/-- Read a signed current in amperes. -/
def currentInAmperes (current : SignedCurrentQuantity) : ℝ :=
  signedSIReadout current

/-- Read a signed magnetic flux density in teslas. -/
def magneticFluxDensityInTeslas
    (field : SignedMagneticFluxDensity) : ℝ :=
  signedSIReadout field

/-- Read a signed magnetic flux or linkage in webers. -/
def magneticFluxInWebers (flux : SignedMagneticFlux) : ℝ :=
  signedSIReadout flux

/-- Read a signed electromotive force in volts. -/
def electromotiveForceInVolts
    (emf : SignedElectromotiveForce) : ℝ :=
  signedSIReadout emf

/-- Read a mutual inductance in henries. -/
def mutualInductanceInHenries
    (inductance : MutualInductanceMagnitude) : ℝ :=
  nonnegativeSIReadout inductance

/-- Read a point of Physlib `Time` in the chosen seconds coordinate. -/
def timeInSeconds (time : Time) : ℝ :=
  time.val

/-- Read a point of Physlib `Time` in milliseconds after switching. -/
def timeInMilliseconds (time : Time) : ℝ :=
  1000 * timeInSeconds time

/-! ## Coil roles, circuit roles, and primary-raster vocabulary -/

/-- Physical identifiers that do not depend on the conflicting `N₁`/`N₂` labels. -/
inductive CoilRole where
  | outerCapacitorConnected
  | innerInduced
  deriving DecidableEq, Fintype, Repr

/-- Literal turn-count labels printed in image `978.png`. -/
inductive FigureTurnLabel where
  | N1
  | N2
  deriving DecidableEq, Fintype, Repr

/-- Literal geometric labels printed in image `978.png`. -/
inductive FigureLengthLabel where
  | a
  | twoB
  deriving DecidableEq, Fintype, Repr

/-- The geometric meaning of a printed length marker. -/
inductive FigureLengthMeaning where
  | radius
  | diameter
  deriving DecidableEq, Repr

/-- Electrical role assigned to a winding in the prose model. -/
inductive CoilCircuitRole where
  | capacitorDischargeLoop
  | closedPassiveInductionLoop
  deriving DecidableEq, Repr

/-- State of the single switch shown in the circuit. -/
inductive SwitchState where
  | open
  | closed
  deriving DecidableEq, Repr

/-- Idealized dynamical model used for each winding. -/
inductive CoilDynamicalModel where
  | resistiveRCDriveNeglectingSelfInductance
  | quasistaticResistiveInductionNeglectingSelfInductance
  deriving DecidableEq, Repr

/-- Explicit finite-radius approximation contract used to couple the coils. -/
inductive CouplingFieldModel where
  | centerFieldLeadingTermWithQuadraticRemainder
  deriving DecidableEq, Repr

/-!
Literal visual information in the primary raster.  The maps state which
physical winding each printed label denotes; they do not assign numerical
turn counts or a current.
-/
structure CoupledCircularCoilFigure where
  coilShown : CoilRole → Bool
  turnLabelShown : FigureTurnLabel → Bool
  coilAtTurnLabel : FigureTurnLabel → CoilRole
  lengthLabelShown : FigureLengthLabel → Bool
  coilAtLengthLabel : FigureLengthLabel → CoilRole
  lengthLabelMeaning : FigureLengthLabel → FigureLengthMeaning
  capacitorLabelCShown : Bool
  switchLabelSShown : Bool
  switchDrawnOpen : Bool
  outerCoilConnectedToCapacitorAndSwitch : Bool
  innerCoilDrawnInsideOuterCoil : Bool
  coilsDrawnConcentric : Bool
  coilPlanesDrawnParallel : Bool

/-!
Independent physical quantities and waveforms for the switching experiment.
In particular, `current .innerInduced` is not defined from a displayed answer.
-/
structure CoupledCircularCoilDischargeSetup where
  turnCount : CoilRole → ℕ
  radius : CoilRole → LengthMagnitude
  wireLength : CoilRole → LengthMagnitude
  wireResistancePerLength : CoilRole → ResistancePerLengthMagnitude
  resistance : CoilRole → ResistanceMagnitude
  circuitRole : CoilRole → CoilCircuitRole
  dynamicalModel : CoilRole → CoilDynamicalModel
  couplingFieldModel : CouplingFieldModel
  capacitance : CapacitanceMagnitude
  initialUpperPlateCharge : ChargeMagnitude
  capacitorUpperPlateCharge : Time → SignedChargeQuantity
  capacitorVoltage : Time → SignedPotentialDifference
  current : CoilRole → Time → SignedCurrentQuantity
  magneticFieldAtInnerCoil : Time → SignedMagneticFluxDensity
  magneticFluxThroughOneInnerTurn : Time → SignedMagneticFlux
  innerFluxLinkage : Time → SignedMagneticFlux
  innerFluxLinkageSpatialRemainder : Time → SignedMagneticFlux
  inducedEmfInInnerCoil : Time → SignedElectromotiveForce
  centerFieldMutualInductance : MutualInductanceMagnitude
  switchState : Time → SwitchState
  observationTime : Time
  electromagneticSystem : Electromagnetism.EMSystem
  figure : CoupledCircularCoilFigure

/-! ## Scalar waveforms and their time derivatives -/

/-- Upper-plate charge waveform in coulombs. -/
def upperPlateChargeWaveformInCoulombs
    (setup : CoupledCircularCoilDischargeSetup) : Time → ℝ :=
  fun time => signedChargeInCoulombs (setup.capacitorUpperPlateCharge time)

/-- Oriented current waveform of one physical winding in amperes. -/
def currentWaveformInAmperes
    (setup : CoupledCircularCoilDischargeSetup)
    (coil : CoilRole) : Time → ℝ :=
  fun time => currentInAmperes (setup.current coil time)

/-- Inner-coil flux-linkage waveform in webers. -/
def innerFluxLinkageWaveformInWebers
    (setup : CoupledCircularCoilDischargeSetup) : Time → ℝ :=
  fun time => magneticFluxInWebers (setup.innerFluxLinkage time)

/-- Finite-radius correction to the center-field linkage, in webers. -/
def innerFluxLinkageSpatialRemainderInWebers
    (setup : CoupledCircularCoilDischargeSetup) : Time → ℝ :=
  fun time =>
    magneticFluxInWebers (setup.innerFluxLinkageSpatialRemainder time)

/-- Time derivative of the upper-plate charge readout, in amperes. -/
def upperPlateChargeDerivativeInAmperes
    (setup : CoupledCircularCoilDischargeSetup) : Time → ℝ :=
  Time.deriv (upperPlateChargeWaveformInCoulombs setup)

/-- Time derivative of the outer-coil current, in amperes per second. -/
def outerCurrentDerivativeInAmperesPerSecond
    (setup : CoupledCircularCoilDischargeSetup) : Time → ℝ :=
  Time.deriv (currentWaveformInAmperes setup .outerCapacitorConnected)

/-- Time derivative of inner-coil flux linkage, in webers per second. -/
def innerFluxLinkageRateInWebersPerSecond
    (setup : CoupledCircularCoilDischargeSetup) : Time → ℝ :=
  Time.deriv (innerFluxLinkageWaveformInWebers setup)

/-- Time derivative of the finite-radius linkage remainder, in volts. -/
def innerFluxLinkageSpatialRemainderRateInVolts
    (setup : CoupledCircularCoilDischargeSetup) : Time → ℝ :=
  Time.deriv (innerFluxLinkageSpatialRemainderInWebers setup)

/-- Dimensionless ratio of the inner radius to the outer radius. -/
def innerToOuterRadiusRatio
    (setup : CoupledCircularCoilDischargeSetup) : ℝ :=
  lengthInMeters (setup.radius .innerInduced) /
    lengthInMeters (setup.radius .outerCapacitorConnected)

/-! ## Scenario, figure, data, and governing-law assumptions -/

/-- The physical winding roles and relative geometry stated in the prose. -/
structure MatchesWrittenCoupledCoilScenario
    (setup : CoupledCircularCoilDischargeSetup) : Prop where
  outerCoilFormsCapacitorLoop :
    setup.circuitRole .outerCapacitorConnected = .capacitorDischargeLoop
  innerCoilIsClosedPassiveLoop :
    setup.circuitRole .innerInduced = .closedPassiveInductionLoop
  bothCoilsUseSameWireMaterial :
    setup.wireResistancePerLength .outerCapacitorConnected =
      setup.wireResistancePerLength .innerInduced
  outerModel :
    setup.dynamicalModel .outerCapacitorConnected =
      .resistiveRCDriveNeglectingSelfInductance
  innerModel :
    setup.dynamicalModel .innerInduced =
      .quasistaticResistiveInductionNeglectingSelfInductance
  finiteRadiusCouplingModel :
    setup.couplingFieldModel =
      .centerFieldLeadingTermWithQuadraticRemainder

/-!
Exact transcription of image `978.png`, including its literal assignment of
`N₁` to the inner winding and `N₂` to the outer winding.  This structure has
no numerical current field.
-/
structure MatchesPrimaryCoupledCoilFigure
    (setup : CoupledCircularCoilDischargeSetup) : Prop where
  bothCoilsShown : ∀ coil, setup.figure.coilShown coil = true
  bothTurnLabelsShown : ∀ label, setup.figure.turnLabelShown label = true
  figureN1LabelsInnerCoil :
    setup.figure.coilAtTurnLabel .N1 = .innerInduced
  figureN2LabelsOuterCoil :
    setup.figure.coilAtTurnLabel .N2 = .outerCapacitorConnected
  bothLengthLabelsShown : ∀ label, setup.figure.lengthLabelShown label = true
  figureTwoBLabelsInnerCoil :
    setup.figure.coilAtLengthLabel .twoB = .innerInduced
  figureTwoBIsDiameter :
    setup.figure.lengthLabelMeaning .twoB = .diameter
  figureALabelsOuterCoil :
    setup.figure.coilAtLengthLabel .a = .outerCapacitorConnected
  figureAIsRadius :
    setup.figure.lengthLabelMeaning .a = .radius
  capacitorLabelShown : setup.figure.capacitorLabelCShown = true
  switchLabelShown : setup.figure.switchLabelSShown = true
  switchInitiallyDrawnOpen : setup.figure.switchDrawnOpen = true
  outerCircuitConnectionShown :
    setup.figure.outerCoilConnectedToCapacitorAndSwitch = true
  innerCoilIsInside : setup.figure.innerCoilDrawnInsideOuterCoil = true
  coilsAreConcentric : setup.figure.coilsDrawnConcentric = true
  coilPlanesAreParallel : setup.figure.coilPlanesDrawnParallel = true

/-!
All numerical values from the prose, calibrated against physical quantities.
The turn counts use unambiguous physical coil roles, not the conflicting
subscripts printed in the raster.
-/
structure MatchesCoupledCoilNumericalData
    (setup : CoupledCircularCoilDischargeSetup) : Prop where
  outerTurnCount : setup.turnCount .outerCapacitorConnected = 5000
  innerTurnCount : setup.turnCount .innerInduced = 100
  outerRadiusCentimeters :
    lengthInCentimeters (setup.radius .outerCapacitorConnected) = 40
  innerRadiusCentimeters :
    lengthInCentimeters (setup.radius .innerInduced) = 4
  outerWireResistancePerMeter :
    resistancePerLengthInOhmsPerMeter
        (setup.wireResistancePerLength .outerCapacitorConnected) =
      1 / 100
  innerWireResistancePerMeter :
    resistancePerLengthInOhmsPerMeter
        (setup.wireResistancePerLength .innerInduced) =
      1 / 100
  tenMicrofaradCapacitor :
    capacitanceInMicrofarads setup.capacitance = 10
  oneHundredMicrocoulombInitialCharge :
    chargeMagnitudeInMicrocoulombs setup.initialUpperPlateCharge = 100
  observationAtOnePointTwoSixMilliseconds :
    timeInMilliseconds setup.observationTime = 126 / 100

/-- The switch is open before `t = 0` and closed from `t = 0` onward. -/
structure MatchesSwitchClosingProtocol
    (setup : CoupledCircularCoilDischargeSetup) : Prop where
  openBeforeZero : ∀ time : Time, time < 0 →
    setup.switchState time = .open
  closedFromZero : ∀ time : Time, 0 ≤ time →
    setup.switchState time = .closed

/-- Positivity and nondegeneracy conditions for the physical apparatus. -/
structure HasPhysicalCoupledCoilParameters
    (setup : CoupledCircularCoilDischargeSetup) : Prop where
  turnCountsPositive : ∀ coil, 0 < setup.turnCount coil
  radiiPositive : ∀ coil, 0 < lengthInMeters (setup.radius coil)
  wireLengthsPositive : ∀ coil, 0 < lengthInMeters (setup.wireLength coil)
  lineResistancesPositive : ∀ coil,
    0 < resistancePerLengthInOhmsPerMeter
      (setup.wireResistancePerLength coil)
  resistancesPositive : ∀ coil, 0 < resistanceInOhms (setup.resistance coil)
  capacitancePositive : 0 < capacitanceInFarads setup.capacitance
  initialChargePositive :
    0 < chargeMagnitudeInCoulombs setup.initialUpperPlateCharge
  observationTimePositive : 0 < setup.observationTime
  vacuumPermeabilityPositive : 0 < setup.electromagneticSystem.μ₀

/-!
Each circular winding uses `N · 2πr` of wire, and its resistance is its wire
length times the resistance per metre.  These laws apply uniformly to either
coil and contain no observation-time current.
-/
structure SatisfiesCircularWireResistanceLaws
    (setup : CoupledCircularCoilDischargeSetup) : Prop where
  circularWireLengthLaw : ∀ coil,
    lengthInMeters (setup.wireLength coil) =
      (setup.turnCount coil : ℝ) * 2 * Real.pi *
        lengthInMeters (setup.radius coil)
  resistanceFromWireLength : ∀ coil,
    resistanceInOhms (setup.resistance coil) =
      resistancePerLengthInOhmsPerMeter
          (setup.wireResistancePerLength coil) *
        lengthInMeters (setup.wireLength coil)

/-!
The upper-plate charge is continuous at switching and initially equals the
given positive charge magnitude.  This is initial data, not the requested
inner-coil current.
-/
structure HasChargedCapacitorInitialState
    (setup : CoupledCircularCoilDischargeSetup) : Prop where
  initialUpperPlateChargeCalibration :
    upperPlateChargeWaveformInCoulombs setup 0 =
      chargeMagnitudeInCoulombs setup.initialUpperPlateCharge

/-!
Ideal outer-loop `RC` laws after the switch closes.  Charge leaves the upper
plate at the outer-loop current, `q = C V`, and the capacitor voltage equals
the resistive drop.  These are the governing ODE laws, not its exponential
solution or the final induced-current value.
-/
structure SatisfiesIdealOuterRCDischargeLaws
    (setup : CoupledCircularCoilDischargeSetup) : Prop where
  chargeWaveformDifferentiable :
    Differentiable ℝ (upperPlateChargeWaveformInCoulombs setup)
  outerCurrentWaveformDifferentiable :
    Differentiable ℝ
      (currentWaveformInAmperes setup .outerCapacitorConnected)
  capacitorCurrentLaw : ∀ time : Time, 0 ≤ time →
    upperPlateChargeDerivativeInAmperes setup time =
      -currentWaveformInAmperes setup .outerCapacitorConnected time
  capacitorConstitutiveLaw : ∀ time : Time, 0 ≤ time →
    upperPlateChargeWaveformInCoulombs setup time =
      capacitanceInFarads setup.capacitance *
        potentialDifferenceInVolts (setup.capacitorVoltage time)
  outerLoopKirchhoffOhmLaw : ∀ time : Time, 0 ≤ time →
    potentialDifferenceInVolts (setup.capacitorVoltage time) =
      resistanceInOhms (setup.resistance .outerCapacitorConnected) *
        currentWaveformInAmperes setup .outerCapacitorConnected time

/-!
The coherent-SI value of Physlib's free-space permeability parameter is the
textbook `4π × 10⁻⁷`.  It is a universal calibration, not a current result.
-/
structure UsesTextbookVacuumPermeability
    (setup : CoupledCircularCoilDischargeSetup) : Prop where
  vacuumPermeabilityCalibration :
    setup.electromagneticSystem.μ₀ =
      4 * Real.pi / (10 : ℝ) ^ 7

/-!
Exact circular-coil center-field and flux-linkage laws, together with the
coefficient of the center-field leading term.  The actual flux through the
finite inner disk is retained as an independent waveform rather than equated
globally to center field times area.
-/
structure SatisfiesConcentricCircularCoilFluxLaws
    (setup : CoupledCircularCoilDischargeSetup) : Prop where
  innerFluxLinkageWaveformDifferentiable :
    Differentiable ℝ (innerFluxLinkageWaveformInWebers setup)
  outerCenterFieldLaw : ∀ time : Time, 0 ≤ time →
    magneticFluxDensityInTeslas (setup.magneticFieldAtInnerCoil time) =
      setup.electromagneticSystem.μ₀ *
        (setup.turnCount .outerCapacitorConnected : ℝ) *
        currentWaveformInAmperes setup .outerCapacitorConnected time /
          (2 * lengthInMeters (setup.radius .outerCapacitorConnected))
  innerFluxLinkageLaw : ∀ time : Time, 0 ≤ time →
    innerFluxLinkageWaveformInWebers setup time =
      (setup.turnCount .innerInduced : ℝ) *
        magneticFluxInWebers (setup.magneticFluxThroughOneInnerTurn time)
  centerFieldMutualInductanceCalibration :
    mutualInductanceInHenries setup.centerFieldMutualInductance =
      setup.electromagneticSystem.μ₀ *
        (setup.turnCount .outerCapacitorConnected : ℝ) *
        (setup.turnCount .innerInduced : ℝ) * Real.pi *
        lengthInMeters (setup.radius .innerInduced) ^ 2 /
          (2 * lengthInMeters (setup.radius .outerCapacitorConnected))

/-!
The small-disk approximation is an exact leading-term-plus-remainder
decomposition, not a global assertion that the outer field is uniform.  The
rate of the spatial remainder is bounded by the square of the radius ratio,
the expected first nonconstant radial order for concentric circular coils.
This contract applies at arbitrary post-switch times and contains neither the
observation-time current nor an answer choice.
-/
structure SatisfiesFiniteRadiusFluxApproximation
    (setup : CoupledCircularCoilDischargeSetup) : Prop where
  spatialRemainderWaveformDifferentiable :
    Differentiable ℝ (innerFluxLinkageSpatialRemainderInWebers setup)
  exactLinkageDecomposition : ∀ time : Time, 0 ≤ time →
    innerFluxLinkageWaveformInWebers setup time =
      mutualInductanceInHenries setup.centerFieldMutualInductance *
          currentWaveformInAmperes setup .outerCapacitorConnected time +
        innerFluxLinkageSpatialRemainderInWebers setup time
  quadraticRemainderRateBound : ∀ time : Time, 0 ≤ time →
    |innerFluxLinkageSpatialRemainderRateInVolts setup time| ≤
      innerToOuterRadiusRatio setup ^ 2 *
        |mutualInductanceInHenries setup.centerFieldMutualInductance *
          outerCurrentDerivativeInAmperesPerSecond setup time|

/-!
Faraday's law gives the inner emf from the derivative of flux linkage, and
Ohm's law gives the instantaneous response of the closed resistive inner
loop.  These laws hold at every post-switch time and do not mention `365 mA`.
-/
structure SatisfiesFaradayAndInnerOhmLaws
    (setup : CoupledCircularCoilDischargeSetup) : Prop where
  faradayLaw : ∀ time : Time, 0 ≤ time →
    electromotiveForceInVolts (setup.inducedEmfInInnerCoil time) =
      -innerFluxLinkageRateInWebersPerSecond setup time
  innerCoilOhmLaw : ∀ time : Time, 0 ≤ time →
    electromotiveForceInVolts (setup.inducedEmfInInnerCoil time) =
      resistanceInOhms (setup.resistance .innerInduced) *
        currentWaveformInAmperes setup .innerInduced time

/-! ## Displayed choices and formalization target -/

/-- Labels of the four current choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Current magnitude printed by each choice, in milliamperes. -/
def AnswerChoice.displayedCurrentInMilliamperes : AnswerChoice → ℝ
  | .A => 182
  | .B => 365
  | .C => 500
  | .D => 730

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Magnitude of the inner-coil current at the requested time, in milliamperes. -/
def observedInnerCurrentMagnitudeInMilliamperes
    (setup : CoupledCircularCoilDischargeSetup) : ℝ :=
  1000 *
    |currentWaveformInAmperes setup .innerInduced setup.observationTime|

/-!
The center-field estimate for the requested current magnitude, in amperes.
The physical current remains an independent setup field; this definition uses
only apparatus parameters and the ideal outer-loop solution's closed form.
-/
def centerFieldCurrentEstimateInAmperes
    (setup : CoupledCircularCoilDischargeSetup) : ℝ :=
  mutualInductanceInHenries setup.centerFieldMutualInductance *
      chargeMagnitudeInCoulombs setup.initialUpperPlateCharge /
      (resistanceInOhms
            (setup.resistance .outerCapacitorConnected) ^ 2 *
        capacitanceInFarads setup.capacitance ^ 2 *
        resistanceInOhms (setup.resistance .innerInduced)) *
    Real.exp
      (-timeInSeconds setup.observationTime /
        (resistanceInOhms
              (setup.resistance .outerCapacitorConnected) *
          capacitanceInFarads setup.capacitance))

/-!
A displayed choice is selected by the physical current when its absolute
rounding error is strictly smaller than that of every other listed choice.
-/
def IsUniqueNearestDisplayedCurrentChoice
    (computedMilliamperes : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |computedMilliamperes - choice.displayedCurrentInMilliamperes| <
      |computedMilliamperes - other.displayedCurrentInMilliamperes|

/-!
Solving the outer `RC` laws and applying the center-field leading term and
inner-loop Ohm's law gives the estimate

`M Q₀ / (R_outer² C² R_inner) · exp (-t/(R_outer C))`.

The explicit finite-radius contract bounds the difference between the actual
magnitude and this estimate by `(b/a)²` times the estimate.  At the supplied
parameter values and `t = 1.26 ms`, that controlled interval is uniquely
nearest to `365 mA`, recorded choice B.  Neither conclusion occurs in any
premise above.

This declaration formalizes blueprint label
`thm:physics:phyx_mini_0978:target`.
-/
theorem problem_phyx_mini_0978
    (setup : CoupledCircularCoilDischargeSetup)
    (_scenario : MatchesWrittenCoupledCoilScenario setup)
    (_figure : MatchesPrimaryCoupledCoilFigure setup)
    (_data : MatchesCoupledCoilNumericalData setup)
    (_switching : MatchesSwitchClosingProtocol setup)
    (_physical : HasPhysicalCoupledCoilParameters setup)
    (_wireLaws : SatisfiesCircularWireResistanceLaws setup)
    (_initial : HasChargedCapacitorInitialState setup)
    (_outerRC : SatisfiesIdealOuterRCDischargeLaws setup)
    (_vacuum : UsesTextbookVacuumPermeability setup)
    (_fluxLaws : SatisfiesConcentricCircularCoilFluxLaws setup)
    (_finiteRadius : SatisfiesFiniteRadiusFluxApproximation setup)
    (_inductionLaws : SatisfiesFaradayAndInnerOhmLaws setup) :
    |(|currentWaveformInAmperes setup .innerInduced setup.observationTime| -
          centerFieldCurrentEstimateInAmperes setup)| ≤
        innerToOuterRadiusRatio setup ^ 2 *
          centerFieldCurrentEstimateInAmperes setup ∧
      IsUniqueNearestDisplayedCurrentChoice
        (observedInnerCurrentMagnitudeInMilliamperes setup)
        recordedDatasetAnswer := by
  let R : ℝ :=
    resistanceInOhms (setup.resistance .outerCapacitorConnected)
  let Rᵢ : ℝ :=
    resistanceInOhms (setup.resistance .innerInduced)
  let C : ℝ := capacitanceInFarads setup.capacitance
  let Q : ℝ :=
    chargeMagnitudeInCoulombs setup.initialUpperPlateCharge
  let M : ℝ :=
    mutualInductanceInHenries setup.centerFieldMutualInductance
  let q : Time → ℝ := upperPlateChargeWaveformInCoulombs setup
  let iₒ : Time → ℝ :=
    currentWaveformInAmperes setup .outerCapacitorConnected
  let iᵢ : Time → ℝ :=
    currentWaveformInAmperes setup .innerInduced
  let Φ : Time → ℝ := innerFluxLinkageWaveformInWebers setup
  let ε : Time → ℝ :=
    innerFluxLinkageSpatialRemainderInWebers setup
  let t : Time := setup.observationTime
  have hR_pos : 0 < R := _physical.resistancesPositive _
  have hRi_pos : 0 < Rᵢ := _physical.resistancesPositive _
  have hC_pos : 0 < C := _physical.capacitancePositive
  have hQ_pos : 0 < Q := _physical.initialChargePositive
  have ht_pos : (0 : Time) < t := _physical.observationTimePositive
  have hR_ne : R ≠ 0 := ne_of_gt hR_pos
  have hRi_ne : Rᵢ ≠ 0 := ne_of_gt hRi_pos
  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  have hRC_ne : R * C ≠ 0 := mul_ne_zero hR_ne hC_ne
  have hCR_ne : C * R ≠ 0 := mul_ne_zero hC_ne hR_ne
  have h_outer_radius :
      lengthInMeters (setup.radius .outerCapacitorConnected) = 2 / 5 := by
    have h := _data.outerRadiusCentimeters
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have h_inner_radius :
      lengthInMeters (setup.radius .innerInduced) = 1 / 25 := by
    have h := _data.innerRadiusCentimeters
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have hC_value : C = 1 / 100000 := by
    have h := _data.tenMicrofaradCapacitor
    norm_num [C, capacitanceInMicrofarads] at h ⊢
    linarith
  have hQ_value : Q = 1 / 10000 := by
    have h := _data.oneHundredMicrocoulombInitialCharge
    norm_num [Q, chargeMagnitudeInMicrocoulombs] at h ⊢
    linarith
  have ht_value : t.val = 63 / 50000 := by
    have h := _data.observationAtOnePointTwoSixMilliseconds
    norm_num [t, timeInMilliseconds, timeInSeconds] at h ⊢
    linarith
  have h_outer_wire_length :
      lengthInMeters (setup.wireLength .outerCapacitorConnected) =
        4000 * Real.pi := by
    rw [_wireLaws.circularWireLengthLaw, _data.outerTurnCount,
      h_outer_radius]
    norm_num
    ring
  have h_inner_wire_length :
      lengthInMeters (setup.wireLength .innerInduced) =
        8 * Real.pi := by
    rw [_wireLaws.circularWireLengthLaw, _data.innerTurnCount,
      h_inner_radius]
    norm_num
    ring
  have hR_value : R = 40 * Real.pi := by
    rw [show R = resistanceInOhms
      (setup.resistance .outerCapacitorConnected) from rfl,
      _wireLaws.resistanceFromWireLength,
      _data.outerWireResistancePerMeter, h_outer_wire_length]
    norm_num
    ring
  have hRi_value : Rᵢ = 2 * Real.pi / 25 := by
    rw [show Rᵢ = resistanceInOhms
      (setup.resistance .innerInduced) from rfl,
      _wireLaws.resistanceFromWireLength,
      _data.innerWireResistancePerMeter, h_inner_wire_length]
    norm_num
    ring
  have hM_value : M = Real.pi ^ 2 / 2500 := by
    rw [show M = mutualInductanceInHenries
      setup.centerFieldMutualInductance from rfl,
      _fluxLaws.centerFieldMutualInductanceCalibration,
      _vacuum.vacuumPermeabilityCalibration,
      _data.outerTurnCount, _data.innerTurnCount,
      h_inner_radius, h_outer_radius]
    norm_num
    ring
  have h_ratio_value : innerToOuterRadiusRatio setup = 1 / 10 := by
    rw [innerToOuterRadiusRatio, h_inner_radius, h_outer_radius]
    norm_num
  have hq_diff : Differentiable ℝ q :=
    _outerRC.chargeWaveformDifferentiable
  have hio_diff : Differentiable ℝ iₒ :=
    _outerRC.outerCurrentWaveformDifferentiable
  have hPhi_diff : Differentiable ℝ Φ :=
    _fluxLaws.innerFluxLinkageWaveformDifferentiable
  have hepsilon_diff : Differentiable ℝ ε :=
    _finiteRadius.spatialRemainderWaveformDifferentiable
  have hq_initial : q 0 = Q :=
    _initial.initialUpperPlateChargeCalibration
  have hq_deriv (s : Time) (hs : 0 ≤ s) :
      Time.deriv q s = -(q s / (R * C)) := by
    rw [show Time.deriv q s =
      upperPlateChargeDerivativeInAmperes setup s from rfl,
      _outerRC.capacitorCurrentLaw s hs]
    have hcapacitor := _outerRC.capacitorConstitutiveLaw s hs
    have hloop := _outerRC.outerLoopKirchhoffOhmLaw s hs
    change q s = C *
      potentialDifferenceInVolts (setup.capacitorVoltage s) at hcapacitor
    change potentialDifferenceInVolts (setup.capacitorVoltage s) =
      R * iₒ s at hloop
    rw [hloop] at hcapacitor
    congr 1
    rw [eq_div_iff hRC_ne]
    rw [hcapacitor]
    ring
  have hintegratingFactorDeriv (s : Time) :
      Time.deriv
          (fun u => q u * Real.exp (u.val / (R * C))) s =
        Time.deriv q s * Real.exp (s.val / (R * C)) +
          q s * (Real.exp (s.val / (R * C)) / (R * C)) := by
    have hinner :
        fderiv ℝ (fun u : Time => u.val / (R * C)) s 1 =
          1 / (R * C) := by
      simp only [div_eq_mul_inv]
      rw [fderiv_mul_const (Time.val_differentiable s)]
      simp [Time.fderiv_val]
    rw [Time.deriv_eq, fderiv_fun_mul (hq_diff s) (by fun_prop)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [fderiv_exp (by fun_prop)]
    simp only [smul_apply, smul_eq_mul]
    rw [hinner]
    simp only [Time.deriv_eq]
    ring
  let integratingFactor : Time → ℝ :=
    fun u => q u * Real.exp (u.val / (R * C))
  let timeInterval : Set Time :=
    {s | s.val ∈ Set.Icc (0 : ℝ) t.val}
  have ht_value_pos : (0 : ℝ) < t.val := by
    simpa only [Time.zero_val] using (Time.lt_def 0 t).mp ht_pos
  have h_integrating_factor_fderiv_zero
      (s : Time) (hs : s ∈ timeInterval) :
      fderiv ℝ integratingFactor s = 0 := by
    change (0 : ℝ) ≤ s.val ∧ s.val ≤ t.val at hs
    have hs_nonnegative : (0 : Time) ≤ s := by
      apply (Time.le_def 0 s).mpr
      simpa only [Time.zero_val] using hs.1
    have hderiv :
        Time.deriv integratingFactor s = 0 := by
      rw [show Time.deriv integratingFactor s =
        Time.deriv
          (fun u => q u * Real.exp (u.val / (R * C))) s from rfl,
        hintegratingFactorDeriv, hq_deriv s hs_nonnegative]
      field_simp
      ring
    apply ContinuousLinearMap.ext
    intro v
    calc
      (fderiv ℝ integratingFactor s) v =
          (fderiv ℝ integratingFactor s) (v.val • (1 : Time)) :=
        congrArg (fun w => (fderiv ℝ integratingFactor s) w)
          (Time.eq_one_smul v)
      _ = v.val • (fderiv ℝ integratingFactor s) 1 := by
        rw [map_smul]
      _ = 0 := by
        rw [show (fderiv ℝ integratingFactor s) 1 = 0 by
          exact hderiv]
        simp
      _ = (0 : Time →L[ℝ] ℝ) v := by simp
  have h_unique_diff_interval :
      UniqueDiffOn ℝ timeInterval := by
    change UniqueDiffOn ℝ
      (Time.toRealCLE ⁻¹' Set.Icc (0 : ℝ) t.val)
    apply Time.toRealCLE.uniqueDiffOn_preimage_iff.mpr
    exact uniqueDiffOn_Icc ht_value_pos
  have h_convex_time_interval :
      Convex ℝ timeInterval := by
    change Convex ℝ (Time.toRealCLE ⁻¹' Set.Icc (0 : ℝ) t.val)
    exact (convex_Icc (0 : ℝ) t.val).linear_preimage
      Time.toRealCLE.toLinearMap
  have h_integrating_factor_differentiable :
      Differentiable ℝ integratingFactor := by
    dsimp only [integratingFactor]
    exact hq_diff.mul (by fun_prop)
  have h_integrating_factor_constant :
      q 0 * Real.exp ((0 : Time).val / (R * C)) =
        q t * Real.exp (t.val / (R * C)) := by
    change integratingFactor 0 = integratingFactor t
    apply h_convex_time_interval.is_const_of_fderivWithin_eq_zero
      h_integrating_factor_differentiable.differentiableOn
    · intro s hs
      rw [fderivWithin_eq_fderiv (h_unique_diff_interval s hs)
        (h_integrating_factor_differentiable s)]
      exact h_integrating_factor_fderiv_zero s hs
    · simp only [timeInterval, Set.mem_setOf_eq, Set.mem_Icc,
        Time.zero_val]
      exact ⟨le_rfl, ht_value_pos.le⟩
    · simp only [timeInterval, Set.mem_setOf_eq, Set.mem_Icc]
      exact ⟨ht_value_pos.le, le_rfl⟩
  have hq_solution :
      q t = Q * Real.exp (-t.val / (R * C)) := by
    have h := h_integrating_factor_constant
    rw [hq_initial] at h
    simp only [Time.zero_val, zero_div, Real.exp_zero, mul_one] at h
    rw [show -t.val / (R * C) = -(t.val / (R * C)) by ring,
      Real.exp_neg]
    rw [eq_mul_inv_iff_mul_eq₀ (Real.exp_ne_zero _)]
    exact h.symm
  have h_nonnegative_eventually :
      ∀ᶠ s in nhds t, (0 : Time) ≤ s := by
    have hopen : IsOpen {s : Time | (0 : ℝ) < s.val} :=
      isOpen_lt continuous_const Time.val_differentiable.continuous
    have hmem : {s : Time | (0 : ℝ) < s.val} ∈ nhds t :=
      hopen.mem_nhds ht_value_pos
    filter_upwards [hmem] with s hs
    apply (Time.le_def 0 s).mpr
    simpa only [Time.zero_val] using hs.le
  have hio_eq_q (s : Time) (hs : 0 ≤ s) :
      iₒ s = q s / (C * R) := by
    have hcapacitor := _outerRC.capacitorConstitutiveLaw s hs
    have hloop := _outerRC.outerLoopKirchhoffOhmLaw s hs
    change q s = C *
      potentialDifferenceInVolts (setup.capacitorVoltage s) at hcapacitor
    change potentialDifferenceInVolts (setup.capacitorVoltage s) =
      R * iₒ s at hloop
    rw [hloop] at hcapacitor
    rw [eq_div_iff hCR_ne]
    rw [hcapacitor]
    ring
  have hio_eventually :
      iₒ =ᶠ[nhds t] fun s => q s / (C * R) :=
    h_nonnegative_eventually.mono fun s hs => hio_eq_q s hs
  have hio_deriv :
      Time.deriv iₒ t = Time.deriv q t / (C * R) := by
    calc
      Time.deriv iₒ t =
          Time.deriv (fun s => q s / (C * R)) t := by
            simp only [Time.deriv]
            rw [hio_eventually.fderiv_eq]
      _ = Time.deriv q t / (C * R) := by
        simpa only [div_eq_mul_inv] using
          Time.deriv_mul_const q (C * R)⁻¹ (hq_diff t)
  have hio_deriv_solution :
      Time.deriv iₒ t =
        -(Q / (R ^ 2 * C ^ 2)) *
          Real.exp (-t.val / (R * C)) := by
    rw [hio_deriv, hq_deriv t ht_pos.le, hq_solution]
    field_simp
  have h_center_estimate :
      centerFieldCurrentEstimateInAmperes setup =
        -(M * Time.deriv iₒ t) / Rᵢ := by
    change
      M * Q / (R ^ 2 * C ^ 2 * Rᵢ) *
          Real.exp (-t.val / (R * C)) =
        -(M * Time.deriv iₒ t) / Rᵢ
    rw [hio_deriv_solution]
    field_simp
  have hM_pos : 0 < M := by
    rw [hM_value]
    positivity
  have hio_deriv_neg : Time.deriv iₒ t < 0 := by
    rw [hio_deriv_solution]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (by positivity))
      (Real.exp_pos _)
  have h_leading_deriv_neg :
      M * Time.deriv iₒ t < 0 :=
    mul_neg_of_pos_of_neg hM_pos hio_deriv_neg
  have h_center_pos :
      0 < centerFieldCurrentEstimateInAmperes setup := by
    rw [h_center_estimate]
    exact div_pos (neg_pos.mpr h_leading_deriv_neg) hRi_pos
  have hdecomposition_eventually :
      Φ =ᶠ[nhds t] fun s => M * iₒ s + ε s := by
    filter_upwards [h_nonnegative_eventually] with s hs
    have h := _finiteRadius.exactLinkageDecomposition s hs
    change Φ s = M * iₒ s + ε s at h
    exact h
  have hMio_deriv :
      Time.deriv (fun s => M * iₒ s) t =
        M * Time.deriv iₒ t := by
    rw [show (fun s => M * iₒ s) = fun s => iₒ s * M by
      funext s
      ring]
    rw [Time.deriv_mul_const iₒ M (hio_diff t)]
    ring
  have hPhi_deriv :
      Time.deriv Φ t =
        M * Time.deriv iₒ t + Time.deriv ε t := by
    calc
      Time.deriv Φ t =
          Time.deriv (fun s => M * iₒ s + ε s) t := by
            simp only [Time.deriv]
            rw [hdecomposition_eventually.fderiv_eq]
      _ = M * Time.deriv iₒ t + Time.deriv ε t := by
        rw [Time.deriv_add (fun s => M * iₒ s) ε
          (by fun_prop) (hepsilon_diff t), hMio_deriv]
  have h_inner_current_relation :
      Rᵢ * iᵢ t =
        -(M * Time.deriv iₒ t + Time.deriv ε t) := by
    calc
      Rᵢ * iᵢ t =
          electromotiveForceInVolts
            (setup.inducedEmfInInnerCoil t) := by
              symm
              exact _inductionLaws.innerCoilOhmLaw t ht_pos.le
      _ = -Time.deriv Φ t := by
        exact _inductionLaws.faradayLaw t ht_pos.le
      _ = -(M * Time.deriv iₒ t + Time.deriv ε t) := by
        rw [hPhi_deriv]
  have h_inner_current :
      iᵢ t =
        -(M * Time.deriv iₒ t + Time.deriv ε t) / Rᵢ := by
    rw [eq_div_iff hRi_ne]
    simpa only [mul_comm] using h_inner_current_relation
  have h_remainder_rate :
      |Time.deriv ε t| ≤
        innerToOuterRadiusRatio setup ^ 2 *
          |M * Time.deriv iₒ t| := by
    have h :=
      _finiteRadius.quadraticRemainderRateBound t ht_pos.le
    change
      |Time.deriv ε t| ≤
        innerToOuterRadiusRatio setup ^ 2 *
          |M * Time.deriv iₒ t| at h
    exact h
  have h_current_error :
      |(|iᵢ t| - centerFieldCurrentEstimateInAmperes setup)| ≤
        innerToOuterRadiusRatio setup ^ 2 *
          centerFieldCurrentEstimateInAmperes setup := by
    calc
      |(|iᵢ t| - centerFieldCurrentEstimateInAmperes setup)| =
          |(|iᵢ t| -
            |centerFieldCurrentEstimateInAmperes setup|)| := by
              rw [abs_of_pos h_center_pos]
      _ ≤ |iᵢ t - centerFieldCurrentEstimateInAmperes setup| :=
        abs_abs_sub_abs_le_abs_sub _ _
      _ = |Time.deriv ε t| / Rᵢ := by
        rw [h_inner_current, h_center_estimate]
        have hdiff :
            -(M * Time.deriv iₒ t + Time.deriv ε t) / Rᵢ -
                -(M * Time.deriv iₒ t) / Rᵢ =
              -Time.deriv ε t / Rᵢ := by
          field_simp
          ring
        rw [hdiff, abs_div, abs_neg, abs_of_pos hRi_pos]
      _ ≤
          (innerToOuterRadiusRatio setup ^ 2 *
            |M * Time.deriv iₒ t|) / Rᵢ :=
        div_le_div_of_nonneg_right h_remainder_rate hRi_pos.le
      _ =
          innerToOuterRadiusRatio setup ^ 2 *
            centerFieldCurrentEstimateInAmperes setup := by
        rw [h_center_estimate, abs_of_neg h_leading_deriv_neg]
        field_simp
  have h_center_value :
      centerFieldCurrentEstimateInAmperes setup =
        25 / (8 * Real.pi) *
          Real.exp (-63 / (20 * Real.pi)) := by
    change
      M * Q / (R ^ 2 * C ^ 2 * Rᵢ) *
          Real.exp (-t.val / (R * C)) =
        25 / (8 * Real.pi) *
          Real.exp (-63 / (20 * Real.pi))
    rw [hM_value, hQ_value, hR_value, hC_value, hRi_value,
      ht_value]
    field_simp [Real.pi_ne_zero]
    ring_nf
  have h_exponent_gt_one :
      1 < 63 / (20 * Real.pi) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith [Real.pi_lt_d2]
  have h_exponent_lt :
      63 / (20 * Real.pi) < 315 / 314 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith [Real.pi_gt_d2]
  have h_exp_lower_endpoint :
      (9 : ℝ) / 25 < Real.exp (-(315 / 314 : ℝ)) := by
    rw [show -(315 / 314 : ℝ) = (-1 : ℝ) + (-1 / 314) by
      norm_num, Real.exp_add]
    have hfirst :
        (9 : ℝ) / 25 <
          (0.36787944116 : ℝ) * (313 / 314) := by
      norm_num
    have hsecond :
        (0.36787944116 : ℝ) * (313 / 314) ≤
          Real.exp (-1) * Real.exp (-1 / 314) := by
      apply mul_le_mul Real.exp_neg_one_gt_d9.le
      · have h := Real.add_one_le_exp (-1 / 314 : ℝ)
        norm_num at h ⊢
        exact h
      · norm_num
      · positivity
    exact hfirst.trans_le hsecond
  have h_exp_lower :
      (9 : ℝ) / 25 <
        Real.exp (-63 / (20 * Real.pi)) := by
    refine h_exp_lower_endpoint.trans
      (Real.exp_lt_exp.mpr ?_)
    simpa only [neg_div] using neg_lt_neg h_exponent_lt
  have h_exp_upper :
      Real.exp (-63 / (20 * Real.pi)) < (3 : ℝ) / 8 := by
    calc
      Real.exp (-63 / (20 * Real.pi)) < Real.exp (-1) :=
        Real.exp_lt_exp.mpr (by
          simpa only [neg_div] using neg_lt_neg h_exponent_gt_one)
      _ < (3 : ℝ) / 8 :=
        Real.exp_neg_one_lt_d9.trans (by norm_num)
  have h_factor_lower :
      (49 : ℝ) / 50 < 25 / (8 * Real.pi) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith [Real.pi_lt_d2]
  have h_factor_upper :
      25 / (8 * Real.pi) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith [Real.pi_gt_d2]
  have h_center_lower :
      (7 : ℝ) / 20 <
        centerFieldCurrentEstimateInAmperes setup := by
    rw [h_center_value]
    calc
      (7 : ℝ) / 20 < (49 / 50 : ℝ) * (9 / 25 : ℝ) := by
        norm_num
      _ < 25 / (8 * Real.pi) *
          Real.exp (-63 / (20 * Real.pi)) := by
        calc
          (49 / 50 : ℝ) * (9 / 25 : ℝ) <
              25 / (8 * Real.pi) * (9 / 25 : ℝ) :=
            mul_lt_mul_of_pos_right h_factor_lower (by norm_num)
          _ < 25 / (8 * Real.pi) *
              Real.exp (-63 / (20 * Real.pi)) :=
            mul_lt_mul_of_pos_left h_exp_lower (by positivity)
  have h_center_upper :
      centerFieldCurrentEstimateInAmperes setup < (19 : ℝ) / 50 := by
    rw [h_center_value]
    calc
      25 / (8 * Real.pi) *
          Real.exp (-63 / (20 * Real.pi)) <
          (1 : ℝ) * (3 / 8 : ℝ) := by
        calc
          25 / (8 * Real.pi) *
              Real.exp (-63 / (20 * Real.pi)) <
              (1 : ℝ) * Real.exp (-63 / (20 * Real.pi)) :=
            mul_lt_mul_of_pos_right h_factor_upper (Real.exp_pos _)
          _ < (1 : ℝ) * (3 / 8 : ℝ) :=
            mul_lt_mul_of_pos_left h_exp_upper zero_lt_one
      _ < (19 : ℝ) / 50 := by
        norm_num
  have herror_numeric :
      |(|iᵢ t| - centerFieldCurrentEstimateInAmperes setup)| ≤
        (1 : ℝ) / 100 *
          centerFieldCurrentEstimateInAmperes setup := by
    rw [h_ratio_value] at h_current_error
    norm_num at h_current_error
    exact h_current_error
  have herror_sides :
      -(1 / 100 *
          centerFieldCurrentEstimateInAmperes setup) ≤
            |iᵢ t| - centerFieldCurrentEstimateInAmperes setup ∧
        |iᵢ t| - centerFieldCurrentEstimateInAmperes setup ≤
          1 / 100 *
            centerFieldCurrentEstimateInAmperes setup :=
    abs_le.mp herror_numeric
  have h_observed_lower :
      (1000 : ℝ) / 3 <
        observedInnerCurrentMagnitudeInMilliamperes setup := by
    change (1000 : ℝ) / 3 < 1000 * |iᵢ t|
    linarith only [herror_sides.1, h_center_lower]
  have h_observed_upper :
      observedInnerCurrentMagnitudeInMilliamperes setup < 400 := by
    change 1000 * |iᵢ t| < (400 : ℝ)
    linarith only [herror_sides.2, h_center_upper]
  have h_unique_choice :
      IsUniqueNearestDisplayedCurrentChoice
        (observedInnerCurrentMagnitudeInMilliamperes setup)
        recordedDatasetAnswer := by
    intro other hother
    rw [recordedDatasetAnswer] at hother ⊢
    fin_cases other
    · simp only [AnswerChoice.displayedCurrentInMilliamperes]
      have hA :
          0 <
            observedInnerCurrentMagnitudeInMilliamperes setup - 182 := by
        linarith only [h_observed_lower]
      rw [abs_of_pos hA, abs_lt]
      constructor <;>
        linarith only [h_observed_lower, h_observed_upper]
    · exact (hother rfl).elim
    · simp only [AnswerChoice.displayedCurrentInMilliamperes]
      have hC :
          observedInnerCurrentMagnitudeInMilliamperes setup - 500 < 0 := by
        linarith only [h_observed_upper]
      rw [abs_of_neg hC, abs_lt]
      constructor <;>
        linarith only [h_observed_lower, h_observed_upper]
    · simp only [AnswerChoice.displayedCurrentInMilliamperes]
      have hD :
          observedInnerCurrentMagnitudeInMilliamperes setup - 730 < 0 := by
        linarith only [h_observed_upper]
      rw [abs_of_neg hD, abs_lt]
      constructor <;>
        linarith only [h_observed_lower, h_observed_upper]
  exact ⟨h_current_error, h_unique_choice⟩

end PhyXMiniProblems.ProblemPhyXMini0978
