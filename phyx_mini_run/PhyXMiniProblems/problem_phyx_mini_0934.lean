import Mathlib
import Physlib.SpaceAndTime.Time.Derivatives
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0934

open Dimension

/-!
# First current maximum after switching a charged capacitor into an LC loop

The primary raster `934.png` shows a `12 V` battery and `2 Ω` resistor in the
position-1 charging branch of a two-position switch.  The switch common is the
upper plate of a `2.0 μF` capacitor.  Position 2 disconnects the charging
branch and connects that plate to a `50 mH` inductor; the capacitor and
inductor then share the lower return node and form an ideal LC loop.

We choose the coordinate carried by Physlib's `Time` to be measured in
seconds, with the switching event as its origin.  Electrical quantities are
unit-independent Physlib `Dimensionful` values.  Real numbers occur only at
coherent-SI readout boundaries and in literal figure or answer-choice data.

Assumption/target split:

* governing laws: `q = C V_C`, `dq/dt = -I`, `V_L = L dI/dt`, and Kirchhoff's
  voltage law `V_C = V_L` in the post-switch ideal LC loop;
* previous-state result: the long stay at position 1 leaves the capacitor at
  the source voltage and the inductor-loop current zero at `t = 0`;
* figure/data readouts: source `12 V`, resistance `2 Ω`, capacitance `2.0 μF`,
  inductance `50 mH`, the switch contacts and common return wire, and choices
  `0.20`, `0.50`, `0.40`, `0.60` interpreted in milliseconds;
* current target: the first post-switch global maximum of the oriented current
  occurs at the ideal-LC quarter-period, approximately `0.50 ms`, uniquely
  selecting recorded choice B.

Neither the first-maximum predicate nor the quarter-period conclusion occurs
in any premise structure.
-/

/-! ## Dimensionful electrical quantities and coherent-SI readouts -/

/-- Energy has physical dimension `M L² T⁻²`. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Electric current has physical dimension charge per time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Electric potential difference has physical dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  energyDimension * C𝓭⁻¹

/-- Electrical resistance has physical dimension voltage per current. -/
def electricalResistanceDimension : Dimension :=
  electricPotentialDimension * electricCurrentDimension⁻¹

/-- Capacitance has physical dimension charge per voltage. -/
def capacitanceDimension : Dimension :=
  C𝓭 * electricPotentialDimension⁻¹

/-- Inductance has physical dimension voltage times time per current. -/
def inductanceDimension : Dimension :=
  electricPotentialDimension * T𝓭 * electricCurrentDimension⁻¹

/-- A nonnegative, unit-independent voltage magnitude. -/
abbrev VoltageMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- A signed, unit-independent instantaneous potential difference. -/
abbrev PotentialDifferenceQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A nonnegative, unit-independent resistance. -/
abbrev ResistanceQuantity : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent capacitance. -/
abbrev CapacitanceQuantity : Type :=
  Dimensionful (WithDim capacitanceDimension NNReal)

/-- A nonnegative, unit-independent inductance. -/
abbrev InductanceQuantity : Type :=
  Dimensionful (WithDim inductanceDimension NNReal)

/-- A signed, unit-independent capacitor charge. -/
abbrev ElectricChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A signed, unit-independent current in the capacitor-to-inductor orientation. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- Coherent-SI readout of a signed physical quantity. -/
def signedSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Coherent-SI readout of a nonnegative physical quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a source-voltage magnitude in volts. -/
def voltageMagnitudeInVolts (voltage : VoltageMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout voltage

/-- Read a signed instantaneous potential difference in volts. -/
def potentialDifferenceInVolts
    (voltage : PotentialDifferenceQuantity) : ℝ :=
  signedSIReadout voltage

/-- Read resistance in ohms. -/
def resistanceInOhms (resistance : ResistanceQuantity) : ℝ :=
  nonnegativeSIReadout resistance

/-- Read capacitance in farads. -/
def capacitanceInFarads (capacitance : CapacitanceQuantity) : ℝ :=
  nonnegativeSIReadout capacitance

/-- Read capacitance in microfarads. -/
def capacitanceInMicrofarads (capacitance : CapacitanceQuantity) : ℝ :=
  (10 : ℝ) ^ 6 * capacitanceInFarads capacitance

/-- Read inductance in henries. -/
def inductanceInHenries (inductance : InductanceQuantity) : ℝ :=
  nonnegativeSIReadout inductance

/-- Read inductance in millihenries. -/
def inductanceInMillihenries (inductance : InductanceQuantity) : ℝ :=
  (10 : ℝ) ^ 3 * inductanceInHenries inductance

/-- Read signed capacitor charge in coulombs. -/
def chargeInCoulombs (charge : ElectricChargeQuantity) : ℝ :=
  signedSIReadout charge

/-- Read the signed loop current in amperes. -/
def currentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  signedSIReadout current

/-! ## Component roles, switch geometry, and primary-figure content -/

/-- The five component symbols visible in `934.png`. -/
inductive FigureComponent where
  | battery
  | resistor
  | switch
  | capacitor
  | inductor
  deriving DecidableEq, Fintype, Repr

/-- The four two-terminal electrical components in the figure. -/
inductive TwoTerminalComponent where
  | battery
  | resistor
  | capacitor
  | inductor
  deriving DecidableEq, Fintype, Repr

/-- The three terminals of the depicted single-pole double-throw switch. -/
inductive SwitchTerminal where
  | common
  | contactOne
  | contactTwo
  deriving DecidableEq, Fintype, Repr

/-- Named electrical nodes read from the circuit drawing. -/
inductive CircuitNode where
  | commonReturn
  | sourcePositive
  | positionOneContact
  | capacitorUpperPlate
  | positionTwoContact
  deriving DecidableEq, Fintype, Repr

/-- The two numbered switch positions shown in the raster. -/
inductive SwitchPosition where
  | positionOne
  | positionTwo
  deriving DecidableEq, Repr

/-- Standard idealized physical roles assigned to the component symbols. -/
inductive ComponentModel where
  | idealBattery
  | idealOhmicResistor
  | idealCapacitor
  | idealInductor
  deriving DecidableEq, Repr

/-!
Literal presentation information transcribed from the primary raster.  The
printed scalar values are kept separate from the physical quantities that
they calibrate.
-/
structure SwitchedLCFigure where
  componentShown : FigureComponent → Bool
  batteryPlusGlyphShown : Bool
  batteryMinusGlyphShown : Bool
  switchContactOneLabelShown : Bool
  switchContactTwoLabelShown : Bool
  switchDrawnAt : SwitchPosition
  printedSourceVoltageVolts : ℝ
  printedResistanceOhms : ℝ
  printedCapacitanceMicrofarads : ℝ
  printedInductanceMillihenries : ℝ
  capacitorLowerPlateOnCommonReturn : Bool
  inductorLowerTerminalOnCommonReturn : Bool

/-!
Independent physical data for the switching experiment.  The charge, voltage,
and current waveforms are observables; none is defined by the requested
first-maximum time or by a displayed answer.
-/
structure SwitchedLCCircuitSetup where
  componentModel : TwoTerminalComponent → ComponentModel
  sourceVoltage : VoltageMagnitudeQuantity
  chargingResistance : ResistanceQuantity
  capacitance : CapacitanceQuantity
  inductance : InductanceQuantity
  capacitorCharge : Time → ElectricChargeQuantity
  capacitorVoltage : Time → PotentialDifferenceQuantity
  inductorVoltage : Time → PotentialDifferenceQuantity
  loopCurrent : Time → ElectricCurrentQuantity
  switchPosition : Time → SwitchPosition
  componentTerminals : TwoTerminalComponent → CircuitNode × CircuitNode
  switchTerminalNode : SwitchTerminal → CircuitNode
  figure : SwitchedLCFigure

/-- The capacitor charge readout as a function of time in seconds. -/
def capacitorChargeWaveformInCoulombs
    (setup : SwitchedLCCircuitSetup) : Time → ℝ :=
  fun t => chargeInCoulombs (setup.capacitorCharge t)

/-- The oriented loop-current readout as a function of time in seconds. -/
def currentWaveformInAmperes
    (setup : SwitchedLCCircuitSetup) : Time → ℝ :=
  fun t => currentInAmperes (setup.loopCurrent t)

/-- Time derivative of the capacitor-charge readout, in amperes. -/
def capacitorChargeDerivativeInAmperes
    (setup : SwitchedLCCircuitSetup) : Time → ℝ :=
  Time.deriv (capacitorChargeWaveformInCoulombs setup)

/-- Time derivative of the current readout, in amperes per second. -/
def currentDerivativeInAmperesPerSecond
    (setup : SwitchedLCCircuitSetup) : Time → ℝ :=
  Time.deriv (currentWaveformInAmperes setup)

/-! ## Figure evidence, switching protocol, and governing laws -/

/-- The ideal lumped-component interpretation of the circuit symbols. -/
structure MatchesIdealSwitchedLCScenario
    (setup : SwitchedLCCircuitSetup) : Prop where
  batteryModel : setup.componentModel .battery = .idealBattery
  resistorModel : setup.componentModel .resistor = .idealOhmicResistor
  capacitorModel : setup.componentModel .capacitor = .idealCapacitor
  inductorModel : setup.componentModel .inductor = .idealInductor

/-!
The node incidences read from `934.png`.  In position 1 the switch common joins
the capacitor to the source/resistor branch; in position 2 it joins the
capacitor to the inductor, whose lower terminal shares the common return.
-/
structure MatchesSuppliedSwitchedLCTopology
    (setup : SwitchedLCCircuitSetup) : Prop where
  batteryTerminals :
    setup.componentTerminals .battery = (.commonReturn, .sourcePositive)
  resistorTerminals :
    setup.componentTerminals .resistor =
      (.sourcePositive, .positionOneContact)
  capacitorTerminals :
    setup.componentTerminals .capacitor =
      (.capacitorUpperPlate, .commonReturn)
  inductorTerminals :
    setup.componentTerminals .inductor =
      (.positionTwoContact, .commonReturn)
  switchCommonNode :
    setup.switchTerminalNode .common = .capacitorUpperPlate
  switchContactOneNode :
    setup.switchTerminalNode .contactOne = .positionOneContact
  switchContactTwoNode :
    setup.switchTerminalNode .contactTwo = .positionTwoContact

/-!
Primary-raster symbols, labels, and calibration of every printed component
value.  These fields contain no current-maximum time.
-/
structure MatchesSuppliedSwitchedLCFigure
    (setup : SwitchedLCCircuitSetup) : Prop where
  everyComponentShown : ∀ component,
    setup.figure.componentShown component = true
  positiveBatteryTerminalShown : setup.figure.batteryPlusGlyphShown = true
  negativeBatteryTerminalShown : setup.figure.batteryMinusGlyphShown = true
  contactOneLabelShown : setup.figure.switchContactOneLabelShown = true
  contactTwoLabelShown : setup.figure.switchContactTwoLabelShown = true
  switchInitiallyDrawnInPositionOne :
    setup.figure.switchDrawnAt = .positionOne
  capacitorReturnWireShown :
    setup.figure.capacitorLowerPlateOnCommonReturn = true
  inductorReturnWireShown :
    setup.figure.inductorLowerTerminalOnCommonReturn = true
  printedSourceVoltage : setup.figure.printedSourceVoltageVolts = 12
  printedResistance : setup.figure.printedResistanceOhms = 2
  printedCapacitance : setup.figure.printedCapacitanceMicrofarads = 2.0
  printedInductance : setup.figure.printedInductanceMillihenries = 50
  sourceVoltageCalibration :
    voltageMagnitudeInVolts setup.sourceVoltage =
      setup.figure.printedSourceVoltageVolts
  resistanceCalibration :
    resistanceInOhms setup.chargingResistance =
      setup.figure.printedResistanceOhms
  capacitanceCalibration :
    capacitanceInMicrofarads setup.capacitance =
      setup.figure.printedCapacitanceMicrofarads
  inductanceCalibration :
    inductanceInMillihenries setup.inductance =
      setup.figure.printedInductanceMillihenries

/-!
The switch has occupied position 1 throughout negative time and changes to
position 2 at `t = 0 s`, where it remains.  The position-2 topology disconnects
the source/resistor branch and closes the capacitor-inductor loop.
-/
structure MatchesSwitchingProtocol
    (setup : SwitchedLCCircuitSetup) : Prop where
  positionOneBeforeZero : ∀ t : Time, t < 0 →
    setup.switchPosition t = .positionOne
  positionTwoFromZero : ∀ t : Time, 0 ≤ t →
    setup.switchPosition t = .positionTwo

/-- Positivity and nondegeneracy of the passive component data. -/
structure HasPhysicalSwitchedLCParameters
    (setup : SwitchedLCCircuitSetup) : Prop where
  sourceVoltagePositive : 0 < voltageMagnitudeInVolts setup.sourceVoltage
  chargingResistancePositive : 0 < resistanceInOhms setup.chargingResistance
  capacitancePositive : 0 < capacitanceInFarads setup.capacitance
  inductancePositive : 0 < inductanceInHenries setup.inductance

/-!
The result of leaving position 1 selected for a long time: immediately after
switching, capacitor voltage is continuous and equals the battery voltage,
and the newly connected inductor-loop current is zero.  This is an initial
state, not the requested first-maximum time.
-/
structure HasLongTimePositionOneInitialState
    (setup : SwitchedLCCircuitSetup) : Prop where
  capacitorInitiallyAtSourceVoltage :
    potentialDifferenceInVolts (setup.capacitorVoltage 0) =
      voltageMagnitudeInVolts setup.sourceVoltage
  loopCurrentInitiallyZero : currentWaveformInAmperes setup 0 = 0

/-!
Ideal post-switch LC dynamics in the orientation from the capacitor's upper
plate through the inductor to the common return.  The charge and current
readouts are differentiable, `q = C V_C`, charge leaves the upper plate at
rate `I`, the inductor obeys `V_L = L dI/dt`, and KVL equates the two oriented
voltage drops.  These general laws contain no quarter-period or answer choice.
-/
structure SatisfiesIdealPostSwitchLCDynamics
    (setup : SwitchedLCCircuitSetup) : Prop where
  chargeWaveformDifferentiable :
    Differentiable ℝ (capacitorChargeWaveformInCoulombs setup)
  currentWaveformDifferentiable :
    Differentiable ℝ (currentWaveformInAmperes setup)
  capacitorConstitutiveLaw : ∀ t : Time, 0 ≤ t →
    capacitorChargeWaveformInCoulombs setup t =
      capacitanceInFarads setup.capacitance *
        potentialDifferenceInVolts (setup.capacitorVoltage t)
  capacitorCurrentLaw : ∀ t : Time, 0 ≤ t →
    capacitorChargeDerivativeInAmperes setup t =
      -currentWaveformInAmperes setup t
  inductorVoltageLaw : ∀ t : Time, 0 ≤ t →
    potentialDifferenceInVolts (setup.inductorVoltage t) =
      inductanceInHenries setup.inductance *
        currentDerivativeInAmperesPerSecond setup t
  kirchhoffVoltageLaw : ∀ t : Time, 0 ≤ t →
    potentialDifferenceInVolts (setup.capacitorVoltage t) =
      potentialDifferenceInVolts (setup.inductorVoltage t)

/-! ## First-maximum target and displayed answer choices -/

/-!
The event time is positive, its current is a global maximum over all
post-switch times, and every earlier nonnegative time has strictly smaller
current.  The last clause selects the first occurrence among the periodic
maxima of the ideal LC current.
-/
def IsFirstPostSwitchCurrentMaximum
    (setup : SwitchedLCCircuitSetup) (eventTime : Time) : Prop :=
  0 < eventTime ∧
    (∀ otherTime : Time, 0 ≤ otherTime →
      currentWaveformInAmperes setup otherTime ≤
        currentWaveformInAmperes setup eventTime) ∧
    (∀ earlierTime : Time,
      0 ≤ earlierTime → earlierTime < eventTime →
      currentWaveformInAmperes setup earlierTime <
        currentWaveformInAmperes setup eventTime)

/-- The ideal-LC quarter-period expressed in seconds. -/
def idealLCFirstPeakTimeInSeconds (setup : SwitchedLCCircuitSetup) : ℝ :=
  Real.pi / 2 *
    Real.sqrt
      (inductanceInHenries setup.inductance *
        capacitanceInFarads setup.capacitance)

/-- The corresponding point of Physlib `Time`, whose chosen unit is seconds. -/
def idealLCFirstPeakTime (setup : SwitchedLCCircuitSetup) : Time :=
  (idealLCFirstPeakTimeInSeconds setup : Time)

/-- Labels of the four time choices supplied with the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
The source text truncates the unit after each number.  Dimensional evaluation
of the pictured `50 mH` and `2.0 μF` components identifies these displayed
readouts as milliseconds.
-/
def AnswerChoice.displayedTimeInMilliseconds : AnswerChoice → ℝ
  | .A => 0.20
  | .B => 0.50
  | .C => 0.40
  | .D => 0.60

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
A displayed choice is correct when it is strictly closer to the exact
quarter-period than every other displayed time.  This treats `0.50 ms` as the
two-significant-figure answer to the approximately `0.4967 ms` physical time,
rather than asserting a false exact equality.
-/
def IsUniqueClosestFirstPeakTimeChoice
    (setup : SwitchedLCCircuitSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |1000 * idealLCFirstPeakTimeInSeconds setup -
        choice.displayedTimeInMilliseconds| <
      |1000 * idealLCFirstPeakTimeInSeconds setup -
        other.displayedTimeInMilliseconds|

/-!
For the charged `2.0 μF` capacitor switched across the `50 mH` inductor, the
oriented current first reaches its global maximum after one quarter of the LC
period, at `π/2 * sqrt (LC) ≈ 0.4967 ms`.  Thus the uniquely closest displayed
time is `0.50 ms`, recorded answer B.

This formalizes blueprint label `thm:physics:phyx_mini_0934:target`.
-/
theorem problem_phyx_mini_0934
    (setup : SwitchedLCCircuitSetup)
    (_scenario : MatchesIdealSwitchedLCScenario setup)
    (_topology : MatchesSuppliedSwitchedLCTopology setup)
    (_figure : MatchesSuppliedSwitchedLCFigure setup)
    (_switching : MatchesSwitchingProtocol setup)
    (_physical : HasPhysicalSwitchedLCParameters setup)
    (_initial : HasLongTimePositionOneInitialState setup)
    (_dynamics : SatisfiesIdealPostSwitchLCDynamics setup) :
    IsFirstPostSwitchCurrentMaximum setup (idealLCFirstPeakTime setup) ∧
      IsUniqueClosestFirstPeakTimeChoice setup recordedDatasetAnswer := by
  let V : ℝ := voltageMagnitudeInVolts setup.sourceVoltage
  let C : ℝ := capacitanceInFarads setup.capacitance
  let L : ℝ := inductanceInHenries setup.inductance
  let s : ℝ := Real.sqrt (L * C)
  let A : ℝ := V * C / s
  let q₀ : ℝ := Real.pi / 2 * s
  let Q : Time → ℝ := capacitorChargeWaveformInCoulombs setup
  let I : Time → ℝ := currentWaveformInAmperes setup
  let q : ℝ → ℝ := fun x => Q (Time.toRealCLE.symm x)
  let i : ℝ → ℝ := fun x => I (Time.toRealCLE.symm x)
  let qCandidate : ℝ → ℝ := fun x => C * V * Real.cos (x / s)
  let iCandidate : ℝ → ℝ := fun x => A * Real.sin (x / s)
  let chargeError : ℝ → ℝ := fun x => q x - qCandidate x
  let currentError : ℝ → ℝ := fun x => i x - iCandidate x
  let errorEnergy : ℝ → ℝ := fun x =>
    chargeError x ^ 2 + C * L * currentError x ^ 2

  have hV : 0 < V := by
    simpa [V] using _physical.sourceVoltagePositive
  have hC : 0 < C := by
    simpa [C] using _physical.capacitancePositive
  have hL : 0 < L := by
    simpa [L] using _physical.inductancePositive
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hs_sq : s ^ 2 = L * C := by
    dsimp [s]
    exact Real.sq_sqrt (mul_nonneg hL.le hC.le)
  have hA : 0 < A := by
    dsimp [A]
    positivity

  have hsymm_one : Time.toRealCLE.symm (1 : ℝ) = (1 : Time) := by
    rw [ContinuousLinearEquiv.symm_apply_eq]
    change (1 : ℝ) = (1 : Time).val
    rw [Time.one_val]
  have hbridge (w : Time → ℝ) (x : ℝ)
      (hw : DifferentiableAt ℝ w (Time.toRealCLE.symm x)) :
      HasDerivAt (fun y : ℝ => w (Time.toRealCLE.symm y))
        (Time.deriv w (Time.toRealCLE.symm x)) x := by
    simpa [Function.comp_def, Time.deriv_eq, hsymm_one] using
      hw.hasFDerivAt.comp_hasDerivAt_of_eq x
        ((Time.toRealCLE.symm : ℝ →L[ℝ] Time).hasDerivAt) rfl

  have hq (x : ℝ) (hx : 0 < x) : HasDerivAt q (-i x) x := by
    have htime : (0 : Time) ≤ Time.toRealCLE.symm x := by
      rw [Time.le_def]
      simpa [Time.toRealCLE] using hx.le
    have hlaw := _dynamics.capacitorCurrentLaw
      (Time.toRealCLE.symm x) htime
    have hderiv :
        Time.deriv Q (Time.toRealCLE.symm x) =
          -I (Time.toRealCLE.symm x) := by
      simpa [Q, I, capacitorChargeDerivativeInAmperes] using hlaw
    have hraw :=
      hbridge Q x
        (_dynamics.chargeWaveformDifferentiable.differentiableAt)
    exact (hraw.congr_deriv hderiv).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun y => by rfl))

  have hi (x : ℝ) (hx : 0 < x) :
      HasDerivAt i (q x / (C * L)) x := by
    have htime : (0 : Time) ≤ Time.toRealCLE.symm x := by
      rw [Time.le_def]
      simpa [Time.toRealCLE] using hx.le
    have hcap := _dynamics.capacitorConstitutiveLaw
      (Time.toRealCLE.symm x) htime
    have hind := _dynamics.inductorVoltageLaw
      (Time.toRealCLE.symm x) htime
    have hind' :
        potentialDifferenceInVolts
            (setup.inductorVoltage (Time.toRealCLE.symm x)) =
          L * Time.deriv I (Time.toRealCLE.symm x) := by
      simpa [I, L, currentDerivativeInAmperesPerSecond] using hind
    have hkvl := _dynamics.kirchhoffVoltageLaw
      (Time.toRealCLE.symm x) htime
    have hderiv :
        Time.deriv I (Time.toRealCLE.symm x) =
          Q (Time.toRealCLE.symm x) / (C * L) := by
      apply (eq_div_iff (mul_ne_zero hC.ne' hL.ne')).2
      calc
        Time.deriv I (Time.toRealCLE.symm x) * (C * L) =
            C * (L * Time.deriv I (Time.toRealCLE.symm x)) := by ring
        _ = C *
            potentialDifferenceInVolts
              (setup.inductorVoltage (Time.toRealCLE.symm x)) := by
              rw [← hind']
        _ = C *
            potentialDifferenceInVolts
              (setup.capacitorVoltage (Time.toRealCLE.symm x)) := by
              rw [← hkvl]
        _ = Q (Time.toRealCLE.symm x) := by
              simpa [Q, C] using hcap.symm
    have hraw :=
      hbridge I x
        (_dynamics.currentWaveformDifferentiable.differentiableAt)
    exact (hraw.congr_deriv hderiv).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun y => by rfl))

  have hqCandidate (x : ℝ) :
      HasDerivAt qCandidate (-iCandidate x) x := by
    change HasDerivAt (fun y => C * V * Real.cos (y / s))
      (-(A * Real.sin (x / s))) x
    have hscalar :
        -(A * Real.sin (x / s)) =
          C * V * (-Real.sin (x / s) * (1 / s)) := by
      dsimp [A]
      field_simp [hs.ne']
    rw [hscalar]
    simpa only [id_eq] using
      (((hasDerivAt_id x).div_const s).cos.const_mul (C * V))

  have hiCandidate (x : ℝ) :
      HasDerivAt iCandidate (qCandidate x / (C * L)) x := by
    change HasDerivAt (fun y => A * Real.sin (y / s))
      (C * V * Real.cos (x / s) / (C * L)) x
    have hscalar :
        C * V * Real.cos (x / s) / (C * L) =
          A * (Real.cos (x / s) * (1 / s)) := by
      dsimp [A]
      field_simp [hC.ne', hL.ne', hs.ne']
      rw [hs_sq]
      ring
    rw [hscalar]
    simpa only [id_eq] using
      (((hasDerivAt_id x).div_const s).sin.const_mul A)

  have hChargeError (x : ℝ) (hx : 0 < x) :
      HasDerivAt chargeError (-currentError x) x := by
    have hscalar :
        -i x - -iCandidate x = -(i x - iCandidate x) := by ring
    exact (((hq x hx).sub (hqCandidate x)).congr_deriv hscalar)
      |>.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun y => by rfl))

  have hCurrentError (x : ℝ) (hx : 0 < x) :
      HasDerivAt currentError (chargeError x / (C * L)) x := by
    have hscalar :
        q x / (C * L) - qCandidate x / (C * L) =
          (q x - qCandidate x) / (C * L) := by ring
    exact (((hi x hx).sub (hiCandidate x)).congr_deriv hscalar)
      |>.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun y => by rfl))

  have hErrorEnergy (x : ℝ) (hx : 0 < x) :
      HasDerivAt errorEnergy 0 x := by
    have hraw :=
      ((hChargeError x hx).pow 2).add
        (((hCurrentError x hx).pow 2).const_mul (C * L))
    have hscalar :
        (2 : ℝ) * chargeError x ^ (2 - 1) * (-currentError x) +
          C * L *
            ((2 : ℝ) * currentError x ^ (2 - 1) *
              (chargeError x / (C * L))) = 0 := by
      field_simp [hC.ne', hL.ne']
      ring
    exact (hraw.congr_deriv hscalar).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun y => by rfl))

  have hq_cont : Continuous q := by
    exact _dynamics.chargeWaveformDifferentiable.continuous.comp
      Time.toRealCLE.symm.continuous
  have hi_cont : Continuous i := by
    exact _dynamics.currentWaveformDifferentiable.continuous.comp
      Time.toRealCLE.symm.continuous
  have hqCandidate_cont : Continuous qCandidate := by
    dsimp [qCandidate]
    fun_prop
  have hiCandidate_cont : Continuous iCandidate := by
    dsimp [iCandidate]
    fun_prop
  have hChargeError_cont : Continuous chargeError :=
    hq_cont.sub hqCandidate_cont
  have hCurrentError_cont : Continuous currentError :=
    hi_cont.sub hiCandidate_cont
  have hErrorEnergy_cont : Continuous errorEnergy := by
    exact
      (hChargeError_cont.pow 2).add
        ((continuous_const.mul continuous_const).mul
          (hCurrentError_cont.pow 2))

  have hQ_zero : Q 0 = C * V := by
    have hcap := _dynamics.capacitorConstitutiveLaw (0 : Time) le_rfl
    rw [_initial.capacitorInitiallyAtSourceVoltage] at hcap
    simpa [Q, C, V] using hcap
  have hI_zero : I 0 = 0 := by
    simpa [I] using _initial.loopCurrentInitiallyZero
  have hsymm_zero : Time.toRealCLE.symm (0 : ℝ) = (0 : Time) :=
    map_zero Time.toRealCLE.symm
  have hErrorEnergy_zero : errorEnergy 0 = 0 := by
    dsimp [errorEnergy, chargeError, currentError, qCandidate, iCandidate,
      q, i]
    rw [hsymm_zero, hQ_zero, hI_zero]
    simp

  have hRealWaveform (x : ℝ) (hx : 0 ≤ x) :
      i x = iCandidate x := by
    rcases hx.eq_or_lt with rfl | hx_pos
    · dsimp [i, iCandidate]
      rw [hsymm_zero, hI_zero]
      simp
    · have hErrorEnergy_const (u v : ℝ) (hu : u ∈ Set.Ioi (0 : ℝ))
          (hv : v ∈ Set.Ioi (0 : ℝ)) :
          errorEnergy u = errorEnergy v := by
        exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
          (fun z hz =>
            (hErrorEnergy z hz).differentiableAt.differentiableWithinAt)
          (fun z hz => (hErrorEnergy z hz).deriv) hu hv
      have hErrorEnergy_tendsto :
          Filter.Tendsto errorEnergy
            (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
            (nhds (errorEnergy 0)) :=
        continuousWithinAt_Ioi_iff_Ici.mpr
          hErrorEnergy_cont.continuousWithinAt
      have hEventuallyConstant :
          Filter.EventuallyEq (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
            errorEnergy (fun _ => errorEnergy x) := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact hErrorEnergy_const u x hu hx_pos
      have hEnergyAtX : errorEnergy x = 0 := by
        have hlimit : errorEnergy 0 = errorEnergy x :=
          tendsto_nhds_unique
            (hErrorEnergy_tendsto.congr' hEventuallyConstant)
            tendsto_const_nhds
        exact hlimit.symm.trans hErrorEnergy_zero
      have hCurrentError_zero : currentError x = 0 := by
        dsimp [errorEnergy] at hEnergyAtX
        have hChargeTerm : 0 ≤ chargeError x ^ 2 :=
          sq_nonneg (chargeError x)
        have hCurrentTermNonpos :
            C * L * currentError x ^ 2 ≤ 0 := by
          linarith
        have hCurrentSquareNonpos : currentError x ^ 2 ≤ 0 :=
          nonpos_of_mul_nonpos_right hCurrentTermNonpos (mul_pos hC hL)
        nlinarith [sq_nonneg (currentError x)]
      exact sub_eq_zero.mp hCurrentError_zero

  have hWaveform (t : Time) (ht : 0 ≤ t) :
      I t = A * Real.sin (t.val / s) := by
    have htval : (0 : ℝ) ≤ t.val := by
      rw [Time.le_def] at ht
      simpa using ht
    have h := hRealWaveform t.val htval
    have hback : Time.toRealCLE.symm t.val = t := by
      simpa [Time.toRealCLE] using Time.toRealCLE.symm_apply_apply t
    change I (Time.toRealCLE.symm t.val) =
      A * Real.sin (t.val / s) at h
    rw [hback] at h
    exact h

  have hC_value : C = (1 : ℝ) / 500000 := by
    have h := _figure.capacitanceCalibration
    rw [_figure.printedCapacitance] at h
    norm_num [capacitanceInMicrofarads, C] at h ⊢
    linarith
  have hL_value : L = (1 : ℝ) / 20 := by
    have h := _figure.inductanceCalibration
    rw [_figure.printedInductance] at h
    norm_num [inductanceInMillihenries, L] at h ⊢
    linarith

  have hq₀_pos : 0 < q₀ := by
    dsimp [q₀]
    positivity
  have hq₀_argument : q₀ / s = Real.pi / 2 := by
    dsimp [q₀]
    field_simp [hs.ne']
  have hq₀_time_pos : (0 : Time) < (q₀ : Time) := by
    rw [Time.lt_def]
    simpa using hq₀_pos
  have hI_q₀ : I (q₀ : Time) = A := by
    rw [hWaveform (q₀ : Time) hq₀_time_pos.le]
    change A * Real.sin (q₀ / s) = A
    rw [hq₀_argument, Real.sin_pi_div_two, mul_one]

  have hfirstMaximum :
      IsFirstPostSwitchCurrentMaximum setup (q₀ : Time) := by
    refine ⟨hq₀_time_pos, ?_, ?_⟩
    · intro other hother
      change I other ≤ I (q₀ : Time)
      rw [hWaveform other hother, hI_q₀]
      exact mul_le_of_le_one_right hA.le (Real.sin_le_one _)
    · intro earlier hearlier hearlier_lt
      change I earlier < I (q₀ : Time)
      rw [hWaveform earlier hearlier, hI_q₀]
      have hearlier_val : (0 : ℝ) ≤ earlier.val := by
        rw [Time.le_def] at hearlier
        simpa using hearlier
      have harg_nonneg : 0 ≤ earlier.val / s :=
        div_nonneg hearlier_val hs.le
      have harg_lt : earlier.val / s < Real.pi / 2 := by
        have hval_lt : earlier.val < q₀ := by
          rw [Time.lt_def] at hearlier_lt
          simpa using hearlier_lt
        rw [div_lt_iff₀ hs]
        simpa [q₀, mul_comm] using hval_lt
      have hsin_lt : Real.sin (earlier.val / s) < 1 := by
        rw [← Real.sin_pi_div_two]
        exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
          (by linarith [Real.pi_pos]) le_rfl harg_lt
      nlinarith

  have hs_square_value : s ^ 2 = (1 : ℝ) / 10000000 := by
    rw [hs_sq, hL_value, hC_value]
    norm_num
  have hs_lower : (3152 : ℝ) / 10000000 < s := by
    apply (sq_lt_sq₀ (by positivity) hs.le).mp
    rw [hs_square_value]
    norm_num
  have hs_upper : s < (3163 : ℝ) / 10000000 := by
    apply (sq_lt_sq₀ hs.le (by positivity)).mp
    rw [hs_square_value]
    norm_num
  have hpi_s_lower :
      (3.1415 : ℝ) * ((3152 : ℝ) / 10000000) < Real.pi * s :=
    mul_lt_mul_of_pos' Real.pi_gt_d4 hs_lower (by positivity) Real.pi_pos
  have hpi_s_upper :
      Real.pi * s < (3.15 : ℝ) * ((3163 : ℝ) / 10000000) :=
    mul_lt_mul_of_pos' Real.pi_lt_d2 hs_upper hs (by positivity)
  have hq₀_milliseconds :
      1000 * q₀ = 500 * Real.pi * s := by
    dsimp [q₀]
    ring
  have hmilliseconds_lower : (0.495 : ℝ) < 1000 * q₀ := by
    rw [hq₀_milliseconds]
    norm_num at hpi_s_lower ⊢
    nlinarith
  have hmilliseconds_upper : 1000 * q₀ < (0.5 : ℝ) := by
    rw [hq₀_milliseconds]
    norm_num at hpi_s_upper ⊢
    nlinarith

  have hclosest :
      IsUniqueClosestFirstPeakTimeChoice setup recordedDatasetAnswer := by
    intro other hother
    change
      |1000 * q₀ - AnswerChoice.displayedTimeInMilliseconds .B| <
        |1000 * q₀ - other.displayedTimeInMilliseconds|
    fin_cases other
    · norm_num [AnswerChoice.displayedTimeInMilliseconds]
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · exact absurd rfl hother
    · norm_num [AnswerChoice.displayedTimeInMilliseconds]
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · norm_num [AnswerChoice.displayedTimeInMilliseconds]
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith

  change
    IsFirstPostSwitchCurrentMaximum setup (q₀ : Time) ∧
      IsUniqueClosestFirstPeakTimeChoice setup .B
  exact ⟨hfirstMaximum, hclosest⟩

end PhyXMiniProblems.ProblemPhyXMini0934
