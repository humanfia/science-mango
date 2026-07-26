import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Filter.AtTopBot.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0991

open Dimension Filter

/-!
# Transient current in a parallel `RL`--`RC` circuit

The primary raster `991.png` shows three branches sharing the same left and
right nodes.  The top branch contains the emf source `𝐸`, the middle branch
contains `R₁` in series with `L`, and the bottom branch contains `R₂` in
series with `C`.  A switch `S` on the common left lead closes at `t = 0`.

Physical component values and instantaneous observables are represented by
unit-independent Physlib `Dimensionful` quantities.  The real arguments of the
time traces and the real expressions in the laws are coherent-SI readouts:
seconds, volts, amperes, coulombs, ohms, henries, and farads as indicated.

Assumption/target split:

* governing laws: Kirchhoff's current law, the ideal series-`RL` KVL law,
  `i₂ = dq₂/dt`, the ideal series-`RC` KVL law, the long-time definition of
  final current, and the steady-DC current law;
* previous-part results: none;
* figure/data readouts: the switch, source, `R₁`, `R₂`, `L`, and `C` labels;
  the three-branch topology, series order, source polarity, and component
  colors visible in `991.png`; no numerical component values are printed;
* current target conclusions: the exact `RL` and `RC` branch-current formulas,
  the resulting battery-current formula, and an if-and-only-if characterization
  of whether the independently represented queried time `t₂` is a half-final-
  current time.

The source and raster supply no numerical values for `E`, `R₁`, `R₂`, `L`, or
`C`.  Consequently, the recorded `0.22 s` choice is retained below only as
dataset metadata; it is not asserted as a physical consequence.  Neither side
of the symbolic half-current characterization occurs in a premise or in the
definition of the queried time.
-/

/-! ## Dimensions, physical quantities, and coherent-SI readouts -/

/-- Electric potential has dimension `M L² T⁻² C⁻¹` (volt). -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electric current has dimension `C T⁻¹` (ampere). -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Electrical resistance has dimension `M L² T⁻¹ C⁻²` (ohm). -/
def electricalResistanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- Capacitance has dimension `M⁻¹ L⁻² T² C²` (farad). -/
def capacitanceDimension : Dimension :=
  M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * T𝓭 * T𝓭 * C𝓭 * C𝓭

/-- Inductance has dimension `M L² C⁻²` (henry). -/
def inductanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent emf magnitude. -/
abbrev ElectricPotentialMagnitude : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- A signed, unit-independent electric-current quantity. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- A signed, unit-independent electric-charge quantity. -/
abbrev ElectricChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, unit-independent resistance magnitude. -/
abbrev ResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent capacitance magnitude. -/
abbrev CapacitanceMagnitude : Type :=
  Dimensionful (WithDim capacitanceDimension NNReal)

/-- A nonnegative, unit-independent inductance magnitude. -/
abbrev InductanceMagnitude : Type :=
  Dimensionful (WithDim inductanceDimension NNReal)

/-- A nonnegative elapsed time after the switch-closing event. -/
abbrev ElapsedTimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a signed dimensionful quantity. -/
def signedSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Read an emf magnitude in volts. -/
def electricPotentialInVolts (potential : ElectricPotentialMagnitude) : ℝ :=
  nonnegativeSIReadout potential

/-- Read signed conventional current in amperes. -/
def electricCurrentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  signedSIReadout current

/-- Read signed electric charge in coulombs. -/
def electricChargeInCoulombs (charge : ElectricChargeQuantity) : ℝ :=
  signedSIReadout charge

/-- Read resistance in ohms. -/
def resistanceInOhms (resistance : ResistanceMagnitude) : ℝ :=
  nonnegativeSIReadout resistance

/-- Read capacitance in farads. -/
def capacitanceInFarads (capacitance : CapacitanceMagnitude) : ℝ :=
  nonnegativeSIReadout capacitance

/-- Read inductance in henries. -/
def inductanceInHenries (inductance : InductanceMagnitude) : ℝ :=
  nonnegativeSIReadout inductance

/-- Read an elapsed time in seconds. -/
def elapsedTimeInSeconds (time : ElapsedTimeQuantity) : ℝ :=
  nonnegativeSIReadout time

/-! ## Literal circuit objects and primary-figure evidence -/

/-- Electrical components explicitly drawn in `991.png`. -/
inductive CircuitComponent where
  | switchS
  | voltageSource
  | resistorR1
  | inductorL
  | resistorR2
  | capacitorC
  deriving DecidableEq, Fintype, Repr

/-- The three horizontal paths between the common left and right nodes. -/
inductive CircuitBranch where
  | sourceTop
  | inductiveMiddle
  | capacitiveBottom
  deriving DecidableEq, Fintype, Repr

/-- Symbolic labels printed in the primary raster. -/
inductive FigureLabel where
  | switchS
  | emfE
  | resistorR1
  | inductorL
  | resistorR2
  | capacitorC
  deriving DecidableEq, Fintype, Repr

/-- Horizontal sides used to record the source polarity. -/
inductive HorizontalSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Colors carrying literal component-identification information in the raster. -/
inductive FigureColor where
  | black
  | blue
  | magenta
  | green
  | gold
  deriving DecidableEq, Fintype, Repr

/-- Typed transcription of the topology and labels visible in `991.png`. -/
structure ParallelRLRCCircuitFigure where
  componentShown : CircuitComponent → Bool
  labelShown : FigureLabel → Bool
  componentColor : CircuitComponent → FigureColor
  branchComponentsLeftToRight : CircuitBranch → List CircuitComponent
  allBranchesShareLeftNode : Bool
  allBranchesShareRightNode : Bool
  switchOnCommonLeftLead : Bool
  switchDrawnOpen : Bool
  sourcePositiveTerminalSide : HorizontalSide

/-- Switch state as a function of coherent-SI time in seconds. -/
inductive SwitchState where
  | open
  | closed
  deriving DecidableEq, Repr

/-! ## Independent apparatus and time-dependent observables -/

/-!
The queried time is an independent physical field.  In particular, it is not
defined as a root of the half-current equation and is not fixed to an answer
choice by construction.
-/
structure ParallelRLRCCircuitSetup where
  sourceEmf : ElectricPotentialMagnitude
  resistorR1Resistance : ResistanceMagnitude
  resistorR2Resistance : ResistanceMagnitude
  inductorInductance : InductanceMagnitude
  capacitorCapacitance : CapacitanceMagnitude
  switchState : ℝ → SwitchState
  inductiveBranchCurrent : ℝ → ElectricCurrentQuantity
  capacitiveBranchCurrent : ℝ → ElectricCurrentQuantity
  batteryCurrent : ℝ → ElectricCurrentQuantity
  capacitorCharge : ℝ → ElectricChargeQuantity
  finalBatteryCurrent : ElectricCurrentQuantity
  queriedTimeT2 : ElapsedTimeQuantity
  figure : ParallelRLRCCircuitFigure

/-! ## Scenario, figure readouts, initial data, and governing laws -/

/-- The switch is open before `t = 0` and is closed from `t = 0` onward. -/
structure MatchesSwitchClosingScenario
    (setup : ParallelRLRCCircuitSetup) : Prop where
  openBeforeZero : ∀ t : ℝ, t < 0 → setup.switchState t = .open
  closedFromZero : ∀ t : ℝ, 0 ≤ t → setup.switchState t = .closed

/-!
Every qualitative datum read directly from the primary image.  None of these
fields contains a component value, a transient time, or a current formula.
-/
structure MatchesPrimaryParallelRLRCFigure
    (setup : ParallelRLRCCircuitSetup) : Prop where
  switchShown : setup.figure.componentShown .switchS = true
  sourceShown : setup.figure.componentShown .voltageSource = true
  resistorR1Shown : setup.figure.componentShown .resistorR1 = true
  inductorShown : setup.figure.componentShown .inductorL = true
  resistorR2Shown : setup.figure.componentShown .resistorR2 = true
  capacitorShown : setup.figure.componentShown .capacitorC = true
  switchLabelShown : setup.figure.labelShown .switchS = true
  emfLabelShown : setup.figure.labelShown .emfE = true
  resistorR1LabelShown : setup.figure.labelShown .resistorR1 = true
  inductorLabelShown : setup.figure.labelShown .inductorL = true
  resistorR2LabelShown : setup.figure.labelShown .resistorR2 = true
  capacitorLabelShown : setup.figure.labelShown .capacitorC = true
  sourceBranchOrder :
    setup.figure.branchComponentsLeftToRight .sourceTop = [.voltageSource]
  inductiveBranchOrder :
    setup.figure.branchComponentsLeftToRight .inductiveMiddle =
      [.resistorR1, .inductorL]
  capacitiveBranchOrder :
    setup.figure.branchComponentsLeftToRight .capacitiveBottom =
      [.resistorR2, .capacitorC]
  commonLeftNode : setup.figure.allBranchesShareLeftNode = true
  commonRightNode : setup.figure.allBranchesShareRightNode = true
  switchOnLeftLead : setup.figure.switchOnCommonLeftLead = true
  switchDrawnOpen : setup.figure.switchDrawnOpen = true
  sourcePositiveOnLeft : setup.figure.sourcePositiveTerminalSide = .left
  sourceColor : setup.figure.componentColor .voltageSource = .blue
  resistorR1Color : setup.figure.componentColor .resistorR1 = .magenta
  resistorR2Color : setup.figure.componentColor .resistorR2 = .magenta
  inductorColor : setup.figure.componentColor .inductorL = .green
  capacitorColor : setup.figure.componentColor .capacitorC = .gold

/-- Positive, nondegenerate ideal-component parameters. -/
structure HasPhysicalParallelRLRCParameters
    (setup : ParallelRLRCCircuitSetup) : Prop where
  sourceEmfPositive : 0 < electricPotentialInVolts setup.sourceEmf
  resistorR1Positive : 0 < resistanceInOhms setup.resistorR1Resistance
  resistorR2Positive : 0 < resistanceInOhms setup.resistorR2Resistance
  inductancePositive : 0 < inductanceInHenries setup.inductorInductance
  capacitancePositive : 0 < capacitanceInFarads setup.capacitorCapacitance

/-!
The capacitor is explicitly initially uncharged.  The zero initial inductor
current records the usual idealization that the branch was disconnected and
unenergized while the switch was open.
-/
structure HasUnenergizedInitialState
    (setup : ParallelRLRCCircuitSetup) : Prop where
  initialCapacitorChargeZero :
    electricChargeInCoulombs (setup.capacitorCharge 0) = 0
  initialInductorCurrentZero :
    electricCurrentInAmperes (setup.inductiveBranchCurrent 0) = 0

/-!
Ideal transient circuit laws after closure.  Derivatives are taken within the
closed half-line `t ≥ 0`, so the laws also have the physically relevant
right derivative at the switching instant.
-/
structure SatisfiesIdealParallelRLRCTransientLaws
    (setup : ParallelRLRCCircuitSetup) : Prop where
  kirchhoffCurrentLaw : ∀ t : ℝ, 0 ≤ t →
    electricCurrentInAmperes (setup.batteryCurrent t) =
      electricCurrentInAmperes (setup.inductiveBranchCurrent t) +
        electricCurrentInAmperes (setup.capacitiveBranchCurrent t)
  inductiveBranchLaw : ∀ t : ℝ, 0 ≤ t →
    ∃ currentRateAmperesPerSecond : ℝ,
      HasDerivWithinAt
          (fun s => electricCurrentInAmperes (setup.inductiveBranchCurrent s))
          currentRateAmperesPerSecond (Set.Ici 0) t ∧
        electricPotentialInVolts setup.sourceEmf =
          resistanceInOhms setup.resistorR1Resistance *
              electricCurrentInAmperes (setup.inductiveBranchCurrent t) +
            inductanceInHenries setup.inductorInductance *
              currentRateAmperesPerSecond
  capacitorCurrentIsChargeRate : ∀ t : ℝ, 0 ≤ t →
    ∃ chargeRateCoulombsPerSecond : ℝ,
      HasDerivWithinAt
          (fun s => electricChargeInCoulombs (setup.capacitorCharge s))
          chargeRateCoulombsPerSecond (Set.Ici 0) t ∧
        electricCurrentInAmperes (setup.capacitiveBranchCurrent t) =
          chargeRateCoulombsPerSecond
  capacitiveBranchLaw : ∀ t : ℝ, 0 ≤ t →
    electricPotentialInVolts setup.sourceEmf =
      resistanceInOhms setup.resistorR2Resistance *
          electricCurrentInAmperes (setup.capacitiveBranchCurrent t) +
        electricChargeInCoulombs (setup.capacitorCharge t) /
          capacitanceInFarads setup.capacitorCapacitance
  finalCurrentIsLongTimeLimit :
    Tendsto
      (fun t => electricCurrentInAmperes (setup.batteryCurrent t))
      atTop
      (nhds (electricCurrentInAmperes setup.finalBatteryCurrent))
  steadyStateCurrentLaw :
    electricCurrentInAmperes setup.finalBatteryCurrent =
      electricPotentialInVolts setup.sourceEmf /
        resistanceInOhms setup.resistorR1Resistance

/-! ## Displayed-answer metadata -/

/-- The four answer labels printed with the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Numerical time in seconds printed beside each answer label. -/
def displayedAnswerTimeInSeconds : AnswerChoice → ℝ
  | .A => 1 / 50
  | .B => 11 / 50
  | .C => 4 / 25
  | .D => 11 / 100

/-- The source dataset records choice B; this is metadata, not a circuit law. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-! ## Symbolic transient conclusions -/

/--
For nonnegative coherent-SI time, the ideal series-`RL` branch has its standard
switch-on transient.  The exponential argument is dimensionless: `R₁/L` has
units of inverse seconds.
-/
lemma inductiveBranchCurrent_formula
    (setup : ParallelRLRCCircuitSetup)
    (_physical : HasPhysicalParallelRLRCParameters setup)
    (_initial : HasUnenergizedInitialState setup)
    (_laws : SatisfiesIdealParallelRLRCTransientLaws setup)
    (t : ℝ) (_ht : 0 ≤ t) :
    electricCurrentInAmperes (setup.inductiveBranchCurrent t) =
      electricPotentialInVolts setup.sourceEmf /
          resistanceInOhms setup.resistorR1Resistance *
        (1 - Real.exp
          (-(resistanceInOhms setup.resistorR1Resistance /
              inductanceInHenries setup.inductorInductance) * t)) := by
  let E : ℝ := electricPotentialInVolts setup.sourceEmf
  let R : ℝ := resistanceInOhms setup.resistorR1Resistance
  let L : ℝ := inductanceInHenries setup.inductorInductance
  let i : ℝ → ℝ :=
    fun s => electricCurrentInAmperes (setup.inductiveBranchCurrent s)
  change i t = E / R * (1 - Real.exp (-(R / L) * t))
  have hR : 0 < R := by
    simpa [R] using _physical.resistorR1Positive
  have hL : 0 < L := by
    simpa [L] using _physical.inductancePositive
  have hi0 : i 0 = 0 := by
    simpa [i] using _initial.initialInductorCurrentZero
  have hODE : ∀ x : ℝ, 0 ≤ x →
      ∃ i' : ℝ, HasDerivWithinAt i i' (Set.Ici 0) x ∧
        E = R * i x + L * i' := by
    intro x hx
    simpa [i, E, R, L] using _laws.inductiveBranchLaw x hx
  let H : ℝ → ℝ :=
    fun x => Real.exp ((R / L) * x) * (i x - E / R)
  have hHderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt H 0 (Set.Ici 0) x := by
    intro x hx
    rcases hODE x hx with ⟨i', hi', hbranch⟩
    have hexp :
        HasDerivWithinAt
          (fun y : ℝ => Real.exp ((R / L) * y))
          (Real.exp ((R / L) * x) * (R / L)) (Set.Ici 0) x :=
      ((hasDerivAt_const_mul (x := x) (R / L)).exp).hasDerivWithinAt
    have hprod :
        HasDerivWithinAt H
          ((Real.exp ((R / L) * x) * (R / L)) * (i x - E / R) +
            Real.exp ((R / L) * x) * i') (Set.Ici 0) x := by
      convert hexp.smul (hi'.sub_const (E / R)) using 1 <;>
        first | rfl | (simp only [smul_eq_mul]; ring)
    have hbracket : R / L * (i x - E / R) + i' = 0 := by
      field_simp [hR.ne', hL.ne']
      nlinarith [hbranch]
    have hzero :
        (Real.exp ((R / L) * x) * (R / L)) * (i x - E / R) +
            Real.exp ((R / L) * x) * i' = 0 := by
      calc
        _ = Real.exp ((R / L) * x) *
              (R / L * (i x - E / R) + i') := by ring
        _ = 0 := by rw [hbracket, mul_zero]
    rw [hzero] at hprod
    exact hprod
  have hHdiff : DifferentiableOn ℝ H (Set.Ici 0) :=
    fun x hx => (hHderiv x hx).differentiableWithinAt
  have hHfderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      fderivWithin ℝ H (Set.Ici 0) x = 0 := by
    intro x hx
    simpa using
      (hHderiv x hx).hasFDerivWithinAt.fderivWithin
        ((uniqueDiffOn_Ici (0 : ℝ)) x hx)
  have hconstant : H 0 = H t :=
    (convex_Ici (0 : ℝ)).is_const_of_fderivWithin_eq_zero hHdiff hHfderiv
      (by simp) _ht
  dsimp only [H] at hconstant
  rw [hi0] at hconstant
  simp only [mul_zero, Real.exp_zero, one_mul, zero_sub] at hconstant
  rw [show -(R / L) * t = -((R / L) * t) by ring, Real.exp_neg]
  field_simp [hR.ne', Real.exp_ne_zero] at hconstant ⊢
  nlinarith [hconstant]

/--
For nonnegative coherent-SI time, the ideal series-`RC` branch current decays
exponentially from `E/R₂`.  The time constant `R₂ C` is measured in seconds.
-/
lemma capacitiveBranchCurrent_formula
    (setup : ParallelRLRCCircuitSetup)
    (_physical : HasPhysicalParallelRLRCParameters setup)
    (_initial : HasUnenergizedInitialState setup)
    (_laws : SatisfiesIdealParallelRLRCTransientLaws setup)
    (t : ℝ) (_ht : 0 ≤ t) :
    electricCurrentInAmperes (setup.capacitiveBranchCurrent t) =
      electricPotentialInVolts setup.sourceEmf /
          resistanceInOhms setup.resistorR2Resistance *
        Real.exp
          (-(t /
            (resistanceInOhms setup.resistorR2Resistance *
              capacitanceInFarads setup.capacitorCapacitance))) := by
  let E : ℝ := electricPotentialInVolts setup.sourceEmf
  let R : ℝ := resistanceInOhms setup.resistorR2Resistance
  let C : ℝ := capacitanceInFarads setup.capacitorCapacitance
  let q : ℝ → ℝ :=
    fun s => electricChargeInCoulombs (setup.capacitorCharge s)
  let i : ℝ → ℝ :=
    fun s => electricCurrentInAmperes (setup.capacitiveBranchCurrent s)
  change i t = E / R * Real.exp (-(t / (R * C)))
  have hR : 0 < R := by
    simpa [R] using _physical.resistorR2Positive
  have hC : 0 < C := by
    simpa [C] using _physical.capacitancePositive
  have hq0 : q 0 = 0 := by
    simpa [q] using _initial.initialCapacitorChargeZero
  have hODE : ∀ x : ℝ, 0 ≤ x →
      ∃ q' : ℝ, HasDerivWithinAt q q' (Set.Ici 0) x ∧
        E = R * q' + q x / C := by
    intro x hx
    rcases _laws.capacitorCurrentIsChargeRate x hx with
      ⟨q', hq', hcurrent⟩
    refine ⟨q', ?_, ?_⟩
    · simpa [q] using hq'
    · have hbranch := _laws.capacitiveBranchLaw x hx
      simpa [E, R, C, q, i] using hbranch.trans
        (by rw [hcurrent])
  let H : ℝ → ℝ :=
    fun x => Real.exp (x / (R * C)) * (q x - E * C)
  have hHderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt H 0 (Set.Ici 0) x := by
    intro x hx
    rcases hODE x hx with ⟨q', hq', hbranch⟩
    have hlinear :
        HasDerivAt (fun y : ℝ => y / (R * C)) (1 / (R * C)) x := by
      simpa only [one_div] using
        (hasDerivAt_id' x).div_const (R * C)
    have hexp :
        HasDerivWithinAt
          (fun y : ℝ => Real.exp (y / (R * C)))
          (Real.exp (x / (R * C)) * (1 / (R * C)))
          (Set.Ici 0) x :=
      hlinear.exp.hasDerivWithinAt
    have hprod :
        HasDerivWithinAt H
          ((Real.exp (x / (R * C)) * (1 / (R * C))) *
              (q x - E * C) +
            Real.exp (x / (R * C)) * q') (Set.Ici 0) x := by
      convert hexp.smul (hq'.sub_const (E * C)) using 1 <;>
        first | rfl | (simp only [smul_eq_mul]; ring)
    have hbracket : 1 / (R * C) * (q x - E * C) + q' = 0 := by
      field_simp [hC.ne'] at hbranch
      field_simp [hR.ne', hC.ne']
      nlinarith [hbranch]
    have hzero :
        (Real.exp (x / (R * C)) * (1 / (R * C))) *
              (q x - E * C) +
            Real.exp (x / (R * C)) * q' = 0 := by
      calc
        _ = Real.exp (x / (R * C)) *
              (1 / (R * C) * (q x - E * C) + q') := by ring
        _ = 0 := by rw [hbracket, mul_zero]
    rw [hzero] at hprod
    exact hprod
  have hHdiff : DifferentiableOn ℝ H (Set.Ici 0) :=
    fun x hx => (hHderiv x hx).differentiableWithinAt
  have hHfderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      fderivWithin ℝ H (Set.Ici 0) x = 0 := by
    intro x hx
    simpa using
      (hHderiv x hx).hasFDerivWithinAt.fderivWithin
        ((uniqueDiffOn_Ici (0 : ℝ)) x hx)
  have hconstant : H 0 = H t :=
    (convex_Ici (0 : ℝ)).is_const_of_fderivWithin_eq_zero hHdiff hHfderiv
      (by simp) _ht
  have hbranch := _laws.capacitiveBranchLaw t _ht
  change E = R * i t + q t / C at hbranch
  dsimp only [H] at hconstant
  rw [hq0] at hconstant
  simp only [zero_div, Real.exp_zero, one_mul, zero_sub] at hconstant
  have hbranch' : q t - E * C = -(R * C * i t) := by
    field_simp [hC.ne'] at hbranch
    nlinarith [hbranch]
  rw [hbranch'] at hconstant
  have hi : E = Real.exp (t / (R * C)) * R * i t := by
    have hcancel :
        C * (-E + Real.exp (t / (R * C)) * R * i t) = 0 := by
      nlinarith [hconstant]
    have hzero :=
      (mul_eq_zero.mp hcancel).resolve_left hC.ne'
    nlinarith [hzero]
  rw [Real.exp_neg]
  field_simp [hR.ne', hC.ne', Real.exp_ne_zero] at hi ⊢
  nlinarith [hi]

/-- The battery current is the sum of the two independently derived transients. -/
lemma batteryCurrent_formula
    (setup : ParallelRLRCCircuitSetup)
    (_physical : HasPhysicalParallelRLRCParameters setup)
    (_initial : HasUnenergizedInitialState setup)
    (_laws : SatisfiesIdealParallelRLRCTransientLaws setup)
    (t : ℝ) (_ht : 0 ≤ t) :
    electricCurrentInAmperes (setup.batteryCurrent t) =
      electricPotentialInVolts setup.sourceEmf /
          resistanceInOhms setup.resistorR1Resistance *
        (1 - Real.exp
          (-(resistanceInOhms setup.resistorR1Resistance /
              inductanceInHenries setup.inductorInductance) * t)) +
      electricPotentialInVolts setup.sourceEmf /
          resistanceInOhms setup.resistorR2Resistance *
        Real.exp
          (-(t /
            (resistanceInOhms setup.resistorR2Resistance *
              capacitanceInFarads setup.capacitorCapacitance))) := by
  rw [_laws.kirchhoffCurrentLaw t _ht,
    inductiveBranchCurrent_formula setup _physical _initial _laws t _ht,
    capacitiveBranchCurrent_formula setup _physical _initial _laws t _ht]

/-!
The queried time `t₂` is a half-final-current time exactly when it satisfies
the displayed parameter-dependent transcendental equation.  This is the
strongest time characterization supported by the source and figure: without
numerical values for `R₁`, `R₂`, `L`, and `C`, the equation does not select any
of the four displayed times.

Blueprint label: `thm:physics:phyx_mini_0991:target`.
-/
theorem problem_phyx_mini_0991
    (setup : ParallelRLRCCircuitSetup)
    (_scenario : MatchesSwitchClosingScenario setup)
    (_figure : MatchesPrimaryParallelRLRCFigure setup)
    (_physical : HasPhysicalParallelRLRCParameters setup)
    (_initial : HasUnenergizedInitialState setup)
    (_laws : SatisfiesIdealParallelRLRCTransientLaws setup) :
    (electricCurrentInAmperes
          (setup.batteryCurrent (elapsedTimeInSeconds setup.queriedTimeT2)) =
        electricCurrentInAmperes setup.finalBatteryCurrent / 2) ↔
      2 * resistanceInOhms setup.resistorR1Resistance *
          Real.exp
            (-(elapsedTimeInSeconds setup.queriedTimeT2 /
              (resistanceInOhms setup.resistorR2Resistance *
                capacitanceInFarads setup.capacitorCapacitance))) =
        resistanceInOhms setup.resistorR2Resistance *
          (2 * Real.exp
            (-(resistanceInOhms setup.resistorR1Resistance /
                inductanceInHenries setup.inductorInductance) *
              elapsedTimeInSeconds setup.queriedTimeT2) - 1) := by
  let E : ℝ := electricPotentialInVolts setup.sourceEmf
  let R₁ : ℝ := resistanceInOhms setup.resistorR1Resistance
  let R₂ : ℝ := resistanceInOhms setup.resistorR2Resistance
  let L : ℝ := inductanceInHenries setup.inductorInductance
  let C : ℝ := capacitanceInFarads setup.capacitorCapacitance
  let t : ℝ := elapsedTimeInSeconds setup.queriedTimeT2
  let A : ℝ := Real.exp (-(R₁ / L) * t)
  let B : ℝ := Real.exp (-(t / (R₂ * C)))
  have hE : 0 < E := by
    simpa [E] using _physical.sourceEmfPositive
  have hR₁ : 0 < R₁ := by
    simpa [R₁] using _physical.resistorR1Positive
  have hR₂ : 0 < R₂ := by
    simpa [R₂] using _physical.resistorR2Positive
  have ht : 0 ≤ t := by
    dsimp only [t, elapsedTimeInSeconds, nonnegativeSIReadout]
    positivity
  have hbattery :=
    batteryCurrent_formula setup _physical _initial _laws t ht
  change
    (electricCurrentInAmperes (setup.batteryCurrent t) =
        electricCurrentInAmperes setup.finalBatteryCurrent / 2) ↔
      2 * R₁ * B = R₂ * (2 * A - 1)
  rw [hbattery, _laws.steadyStateCurrentLaw]
  change
    (E / R₁ * (1 - A) + E / R₂ * B = E / R₁ / 2) ↔
      2 * R₁ * B = R₂ * (2 * A - 1)
  constructor
  · intro h
    have hfactor : E * (2 * R₁ * B - R₂ * (2 * A - 1)) = 0 := by
      field_simp [hR₁.ne', hR₂.ne'] at h ⊢
      nlinarith [h]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hE.ne')
  · intro h
    have hfactor : E * (2 * R₁ * B - R₂ * (2 * A - 1)) = 0 :=
      mul_eq_zero.mpr (Or.inr (sub_eq_zero.mpr h))
    field_simp [hR₁.ne', hR₂.ne'] at hfactor ⊢
    nlinarith [hfactor]

end PhyXMiniProblems.ProblemPhyXMini0991
