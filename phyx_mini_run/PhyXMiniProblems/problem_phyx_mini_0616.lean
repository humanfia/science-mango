import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.QuantumMechanics.RectangularBarrier.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0616

open Dimension

/-!
# Electron tunneling across an oxide gap between copper wires

Two cylindrical copper wires of diameter `1 mm` face each other across a
`1 nm` oxide gap.  Copper's free-electron number density is
`8.5 × 10^28 m⁻³`.  An electron of energy `5 eV` encounters a rectangular
oxide barrier of height `12 eV`.

Lengths, energy, mass, action, number density, electric potential, and current
are represented by unit-independent dimensionful quantities.  Real numbers
occur only at explicit unit readouts and for the dimensionless tunneling
probability.  Physlib's `QuantumMechanics.RectangularBarrier` supplies the
one-dimensional piecewise-constant barrier model; its scalar parameters are
calibrated below against the dimensionful setup.

Assumption/target split:

* governing laws: the rectangular potential, the evanescent decay relation,
  and the definition of the leading opaque-barrier exponential estimate;
* previous-part results: none;
* figure/data readouts: two cylindrical copper wires, oxide gap and current
  direction, labels `d`, `L`, `I_tunnel`, `V`, and `V_B`, the inequality
  `V_B > V`, a closed loop, and all numerical prose data;
* derived intermediate: the `7 eV` barrier-energy deficit;
* current conclusion: the leading opaque-barrier tunneling estimate lies
  between `1.6 × 10⁻¹²` and `1.8 × 10⁻¹²`.

The supplied answer choices are energies (`5`, `6`, `7`, and `8 eV`) even
though the question asks for a dimensionless probability.  They are retained
as malformed source metadata near the end of the file and are not used as
physical probability choices.
-/

/-! ## Dimensionful physical quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative free-particle number density, with dimension `length⁻³`. -/
abbrev NumberDensityQuantity : Type :=
  Dimensionful (WithDim (L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) NNReal)

/-- The dimension of action, `mass * length² / time`. -/
def actionDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- A nonnegative inverse length, used for the under-barrier decay constant. -/
abbrev InverseLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- Electric potential has dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A signed electric-potential difference. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- Electric current has dimension charge per time. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- A nonnegative tunneling-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in millimetres. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- Read a physical length in nanometres. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Read an energy in coherent SI units, hence in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read an energy in electron volts using Physlib's calibrated unit. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.kilograms}).val : ℝ)

/-- Read a physical action in coherent SI joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Read an inverse-length quantity in inverse metres. -/
def inverseLengthInInverseMeters
    (inverseLength : InverseLengthQuantity) : ℝ :=
  ((inverseLength UnitChoices.SI).val : ℝ)

/-- Read a free-electron number density in particles per cubic metre. -/
def numberDensityInPerCubicMeter
    (density : NumberDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Read an electric-potential difference in volts. -/
def potentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-- Read an electric-current magnitude in amperes. -/
def currentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  ((current UnitChoices.SI).val : ℝ)

/-! ## Physical roles and primary-figure vocabulary -/

/-- The two copper conductors on opposite sides of the gap. -/
inductive WireSide where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Material assigned to a conductor in the setup. -/
inductive WireMaterial where
  | copper
  | other
  deriving DecidableEq, Repr

/-- Geometric shape of a wire. -/
inductive WireShape where
  | cylindrical
  | other
  deriving DecidableEq, Repr

/-- Material occupying the junction gap. -/
inductive GapMaterial where
  | oxide
  | other
  deriving DecidableEq, Repr

/-- Particle species incident on the oxide barrier. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-- Shape assumed for the oxide potential-energy profile. -/
inductive PotentialProfileShape where
  | rectangularBarrier
  | other
  deriving DecidableEq, Repr

/-- Horizontal direction in the circuit diagram. -/
inductive HorizontalDirection where
  | leftToRight
  | rightToLeft
  deriving DecidableEq, Repr

/-- The two voltage-source labels printed in the primary image. -/
inductive VoltageSourceLabel where
  | V
  | VB
  deriving DecidableEq, Fintype, Repr

/-- Physical role assigned to each depicted voltage source. -/
inductive PotentialDifferenceRole where
  | leftWireRelativeToRightWire
  | oxideGapBias
  deriving DecidableEq, Fintype, Repr

/-- Quantity symbols explicitly printed in the primary image. -/
inductive FigureQuantityLabel where
  | wireDiameterD
  | gapLengthL
  | tunnelingCurrentI
  deriving DecidableEq, Fintype, Repr

/-!
Literal qualitative information visible in image `616.png`.  The figure
record contains no transmission probability and no numerical approximation
to it.
-/
structure CopperOxideJunctionFigure where
  wireMaterial : WireSide → WireMaterial
  wireShape : WireSide → WireShape
  gapMaterial : GapMaterial
  gapShownBetweenWires : Bool
  quantityLabelShown : FigureQuantityLabel → Bool
  voltageLabelShown : VoltageSourceLabel → Bool
  positiveTerminalShown : VoltageSourceLabel → Bool
  voltageRole : VoltageSourceLabel → PotentialDifferenceRole
  greaterVoltageLabel : VoltageSourceLabel
  lesserVoltageLabel : VoltageSourceLabel
  tunnelingCurrentDirection : HorizontalDirection
  closedCircuitLoopShown : Bool

/-!
Independent physical quantities for the junction.  In particular,
`leadingOpaqueBarrierEstimate` and `barrierDecayConstant` are stored
independently; the governing laws below constrain them without defining
either from the requested numerical result.  The former is explicitly the
dimensionless estimate produced by the leading exponential approximation,
not an assertion about the exact rectangular-barrier transmission coefficient.
-/
structure CopperOxideTunnelingSetup where
  particleSpecies : ParticleSpecies
  profileShape : PotentialProfileShape
  wireDiameter : WireSide → LengthQuantity
  copperFreeElectronNumberDensity : NumberDensityQuantity
  oxideGapLength : LengthQuantity
  barrierHeight : DimEnergy
  incidentElectronEnergy : DimEnergy
  electronRestMass : MassQuantity
  reducedPlanckAction : ActionQuantity
  barrierDecayConstant : InverseLengthQuantity
  leadingOpaqueBarrierEstimate : ℝ
  sourcePotentialDifference : PotentialDifferenceRole → ElectricPotentialQuantity
  tunnelingCurrentMagnitude : ElectricCurrentMagnitude
  scalarBarrierModel : QuantumMechanics.RectangularBarrier
  figure : CopperOxideJunctionFigure

/-! ## Scenario, data and figure readouts, and governing laws -/

/-- Qualitative physical scenario stated in the prose. -/
structure MatchesCopperOxideJunctionScenario
    (setup : CopperOxideTunnelingSetup) : Prop where
  particleIsElectron : setup.particleSpecies = .electron
  potentialIsRectangular : setup.profileShape = .rectangularBarrier
  bothWiresAreCopper :
    ∀ side, setup.figure.wireMaterial side = .copper
  bothWiresAreCylindrical :
    ∀ side, setup.figure.wireShape side = .cylindrical
  gapIsOxide : setup.figure.gapMaterial = .oxide

/-!
Numerical physical readouts from the prose.  They constrain geometry,
material density, and the two energy levels, but not the requested tunneling
probability.
-/
structure MatchesProblemNumericalReadouts
    (setup : CopperOxideTunnelingSetup) : Prop where
  eachWireDiameterMillimeters :
    ∀ side, lengthInMillimeters (setup.wireDiameter side) = 1
  freeElectronDensityPerCubicMeter :
    numberDensityInPerCubicMeter setup.copperFreeElectronNumberDensity =
      (85 / 10 : ℝ) * 10 ^ 28
  gapLengthNanometers : lengthInNanometers setup.oxideGapLength = 1
  barrierHeightElectronVolts :
    energyInElectronVolts setup.barrierHeight = 12
  incidentEnergyElectronVolts :
    energyInElectronVolts setup.incidentElectronEnergy = 5

/-!
Primary-raster evidence from image `616.png`: two copper cylinders separated
by an oxide gap, labels `d`, `L`, and `I_tunnel`, a right-pointing tunneling
current, sources `V` and `V_B` with positive terminals, the printed relation
`V_B > V`, and a closed circuit loop.
-/
structure MatchesSuppliedCopperOxideFigure
    (setup : CopperOxideTunnelingSetup) : Prop where
  gapIsBetweenWires : setup.figure.gapShownBetweenWires = true
  diameterLabelShown :
    setup.figure.quantityLabelShown .wireDiameterD = true
  gapLengthLabelShown :
    setup.figure.quantityLabelShown .gapLengthL = true
  tunnelingCurrentLabelShown :
    setup.figure.quantityLabelShown .tunnelingCurrentI = true
  driveVoltageLabelShown : setup.figure.voltageLabelShown .V = true
  barrierBiasLabelShown : setup.figure.voltageLabelShown .VB = true
  drivePositiveTerminalShown :
    setup.figure.positiveTerminalShown .V = true
  barrierBiasPositiveTerminalShown :
    setup.figure.positiveTerminalShown .VB = true
  drivePotentialRole :
    setup.figure.voltageRole .V = .leftWireRelativeToRightWire
  barrierBiasPotentialRole :
    setup.figure.voltageRole .VB = .oxideGapBias
  printedGreaterVoltageIsVB : setup.figure.greaterVoltageLabel = .VB
  printedLesserVoltageIsV : setup.figure.lesserVoltageLabel = .V
  depictedBiasExceedsDrive :
    potentialInVolts
        (setup.sourcePotentialDifference .oxideGapBias) >
      potentialInVolts
        (setup.sourcePotentialDifference .leftWireRelativeToRightWire)
  currentPointsLeftToRight :
    setup.figure.tunnelingCurrentDirection = .leftToRight
  circuitLoopIsClosed : setup.figure.closedCircuitLoopShown = true

/-!
Standard electron and quantum reference data.  Physlib supplies
`Constants.ℏ`; its searched API has no dimensionful electron-rest-mass
constant, so the mass is explicitly calibrated in kilograms.
-/
structure UsesStandardElectronReferenceData
    (setup : CopperOxideTunnelingSetup) : Prop where
  electronMassKilograms :
    massInKilograms setup.electronRestMass = 9.1093837015e-31
  reducedPlanckJouleSeconds :
    actionInJouleSeconds setup.reducedPlanckAction = (Constants.ℏ : ℝ)

/-!
Calibrate Physlib's scalar rectangular barrier against the coherent-SI
readouts of the dimensionful junction.  Only the separation of the two faces
is physically relevant here, so their absolute coordinate is left free.
-/
structure MatchesPhyslibRectangularBarrier
    (setup : CopperOxideTunnelingSetup) : Prop where
  scalarMassIsKilogramReadout :
    setup.scalarBarrierModel.m = massInKilograms setup.electronRestMass
  scalarWidthIsMeterReadout :
    setup.scalarBarrierModel.upper - setup.scalarBarrierModel.lower =
      lengthInMeters setup.oxideGapLength
  scalarHeightIsJouleReadout :
    setup.scalarBarrierModel.V₀ = energyInJoules setup.barrierHeight

/-- Positivity and branch conditions selecting a physical tunneling setup. -/
structure HasPhysicalTunnelingParameters
    (setup : CopperOxideTunnelingSetup) : Prop where
  positiveWireDiameter :
    ∀ side, 0 < lengthInMeters (setup.wireDiameter side)
  positiveFreeElectronDensity :
    0 < numberDensityInPerCubicMeter setup.copperFreeElectronNumberDensity
  positiveGapLength : 0 < lengthInMeters setup.oxideGapLength
  positiveIncidentEnergy :
    0 < energyInJoules setup.incidentElectronEnergy
  incidentEnergyBelowBarrier :
    energyInJoules setup.incidentElectronEnergy <
      energyInJoules setup.barrierHeight
  positiveElectronMass : 0 < massInKilograms setup.electronRestMass
  positiveReducedPlanckAction :
    0 < actionInJouleSeconds setup.reducedPlanckAction
  positiveDecayConstant :
    0 < inverseLengthInInverseMeters setup.barrierDecayConstant
  opaqueBarrierRegime :
    1 < inverseLengthInInverseMeters setup.barrierDecayConstant *
      lengthInMeters setup.oxideGapLength
  currentMagnitudeNonnegative :
    0 ≤ currentInAmperes setup.tunnelingCurrentMagnitude
  estimateNonnegative : 0 ≤ setup.leadingOpaqueBarrierEstimate
  estimateAtMostOne : setup.leadingOpaqueBarrierEstimate ≤ 1

/-!
For a rectangular barrier with incident energy below the barrier height, the
evanescent decay constant obeys

`κ = sqrt (2 m (U - E)) / ℏ`.

Both sides are coherent-SI inverse-metre readouts.  This general law contains
no numerical tunneling-probability answer.
-/
structure SatisfiesBarrierDecayRelation
    (setup : CopperOxideTunnelingSetup) : Prop where
  decayConstantLaw :
    inverseLengthInInverseMeters setup.barrierDecayConstant =
      Real.sqrt
          (2 * massInKilograms setup.electronRestMass *
            (energyInJoules setup.barrierHeight -
              energyInJoules setup.incidentElectronEnergy)) /
        actionInJouleSeconds setup.reducedPlanckAction

/-!
The leading opaque-barrier exponential estimate `T_lead = exp (-2 κ L)`.
This is the exact definition of the value produced by that approximation
scheme, not an exact claim about the physical transmission coefficient and
not the requested numerical specialization.
-/
structure DefinesLeadingOpaqueBarrierTransmissionEstimate
    (setup : CopperOxideTunnelingSetup) : Prop where
  leadingEstimateFormula :
    setup.leadingOpaqueBarrierEstimate =
      Real.exp
        (-2 * inverseLengthInInverseMeters setup.barrierDecayConstant *
          lengthInMeters setup.oxideGapLength)

/-! ## Malformed source choices and current conclusions -/

/-- Labels of the four source choices, whose printed values have energy units. -/
inductive MalformedSourceChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Electron-volt values printed beside the source choices. -/
def MalformedSourceChoice.energyInElectronVolts :
    MalformedSourceChoice → ℝ
  | .A => 5
  | .B => 6
  | .C => 7
  | .D => 8

/-- Dataset answer metadata; it is not a dimensionless probability answer. -/
def recordedMalformedSourceAnswer : MalformedSourceChoice := .A

/-- The supplied energies imply that the electron is `7 eV` below the top. -/
lemma barrier_energy_deficit_electronvolts_eq_seven
    (setup : CopperOxideTunnelingSetup)
    (_readouts : MatchesProblemNumericalReadouts setup) :
    energyInElectronVolts setup.barrierHeight -
        energyInElectronVolts setup.incidentElectronEnergy = 7 := by
  rw [_readouts.barrierHeightElectronVolts,
    _readouts.incidentEnergyElectronVolts]
  norm_num

/-!
For an electron facing a `12 eV` barrier with energy `5 eV` across a `1 nm`
gap, the leading opaque-barrier estimate gives `T_lead ≈ 1.685 × 10⁻¹²`.
The target interval states the estimate without claiming it is the exact
rectangular-barrier transmission coefficient or claiming spurious precision.
-/
lemma leading_opaque_barrier_estimate_between_1_6e_12_and_1_8e_12
    (setup : CopperOxideTunnelingSetup)
    (_readouts : MatchesProblemNumericalReadouts setup)
    (_reference : UsesStandardElectronReferenceData setup)
    (_physical : HasPhysicalTunnelingParameters setup)
    (_decay : SatisfiesBarrierDecayRelation setup)
    (_estimate : DefinesLeadingOpaqueBarrierTransmissionEstimate setup) :
    (16 : ℝ) / 10 ^ 13 < setup.leadingOpaqueBarrierEstimate ∧
      setup.leadingOpaqueBarrierEstimate < (18 : ℝ) / 10 ^ 13 := by
  have h_units := setup.oxideGapLength.2 UnitChoices.SI
    ({UnitChoices.SI with length := LengthUnit.nanometers} : UnitChoices)
  have h_units_val :=
    congrArg (fun q : WithDim L𝓭 NNReal => (q.val : ℝ)) h_units
  change lengthInNanometers setup.oxideGapLength = _ at h_units_val
  simp [UnitChoices.dimScale, LengthUnit.nanometers, LengthUnit.meters,
    LengthUnit.scale] at h_units_val
  norm_num [LengthUnit.div_eq_val, NNReal.coe_div] at h_units_val
  change lengthInNanometers setup.oxideGapLength =
    1000000000 * lengthInMeters setup.oxideGapLength at h_units_val
  have h_gap_meters :
      lengthInMeters setup.oxideGapLength = (1 / 1000000000 : ℝ) := by
    rw [_readouts.gapLengthNanometers] at h_units_val
    linarith

  have h_electronVolt :
      energyInJoules DimEnergy.electronVolt = 1.602176634e-19 := by
    norm_num [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply, UnitChoices.dimScale]
  have h_barrier_joules :
      energyInJoules setup.barrierHeight = 12 * 1.602176634e-19 := by
    apply (div_eq_iff (by norm_num : (1.602176634e-19 : ℝ) ≠ 0)).mp
    simpa [energyInElectronVolts, h_electronVolt] using
      _readouts.barrierHeightElectronVolts
  have h_incident_joules :
      energyInJoules setup.incidentElectronEnergy = 5 * 1.602176634e-19 := by
    apply (div_eq_iff (by norm_num : (1.602176634e-19 : ℝ) ≠ 0)).mp
    simpa [energyInElectronVolts, h_electronVolt] using
      _readouts.incidentEnergyElectronVolts

  have h_decay := _decay.decayConstantLaw
  rw [_reference.electronMassKilograms, h_barrier_joules,
    h_incident_joules, _reference.reducedPlanckJouleSeconds] at h_decay
  norm_num [Constants.ℏ] at h_decay
  let x : ℝ :=
    2 * inverseLengthInInverseMeters setup.barrierDecayConstant *
      lengthInMeters setup.oxideGapLength
  have h_x_formula :
      x =
        2 *
          (Real.sqrt 102163892016786115257 /
              Real.sqrt
                50000000000000000000000000000000000000000000000000000000000000000000 /
            (1054571817 /
              10000000000000000000000000000000000000000000)) *
          (1 / 1000000000) := by
    simp only [x]
    rw [h_decay, h_gap_meters]
  rw [_estimate.leadingEstimateFormula]
  have h_neg_x :
      -2 * inverseLengthInInverseMeters setup.barrierDecayConstant *
          lengthInMeters setup.oxideGapLength = -x := by
    simp only [x]
    ring
  rw [h_neg_x]
  have h_x_sq :
      x ^ 2 = (2454387796199065832 / 3339704856488533 : ℝ) := by
    rw [h_x_formula]
    have h_num_sq :
        Real.sqrt (102163892016786115257 : ℝ) ^ 2 =
          102163892016786115257 := by
      rw [Real.sq_sqrt]
      norm_num
    have h_den_sq :
        Real.sqrt
            (50000000000000000000000000000000000000000000000000000000000000000000 :
              ℝ) ^ 2 =
          50000000000000000000000000000000000000000000000000000000000000000000 := by
      rw [Real.sq_sqrt]
      norm_num
    have h_den_ne :
        Real.sqrt
            (50000000000000000000000000000000000000000000000000000000000000000000 :
              ℝ) ≠ 0 := by
      positivity
    field_simp
    nlinarith
  have h_x_pos : 0 < x := by
    rw [h_x_formula]
    positivity
  have h_x_lower : (271 / 10 : ℝ) < x := by
    by_contra h
    have hx_le : x ≤ (271 / 10 : ℝ) := le_of_not_gt h
    have hprod :
        0 ≤ ((271 / 10 : ℝ) - x) * ((271 / 10 : ℝ) + x) :=
      mul_nonneg (sub_nonneg.mpr hx_le) (by positivity)
    nlinarith
  have h_x_upper : x < (678 / 25 : ℝ) := by
    by_contra h
    have hx_ge : (678 / 25 : ℝ) ≤ x := le_of_not_gt h
    have hprod :
        0 ≤ (x - (678 / 25 : ℝ)) * (x + (678 / 25 : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hx_ge) (by positivity)
    nlinarith

  have h_exp_one_bounds :
      (2718 / 1000 : ℝ) < Real.exp 1 ∧
        Real.exp 1 < (2719 / 1000 : ℝ) := by
    have h_bound :=
      Real.exp_bound (x := (1 : ℝ)) (n := 8)
        (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h_bound
    rw [abs_le] at h_bound
    constructor <;> nlinarith
  have h_exp_fraction_upper :
      Real.exp (3 / 25 : ℝ) < (25 / 22 : ℝ) := by
    convert Real.exp_bound_div_one_sub_of_interval'
      (x := (3 / 25 : ℝ)) (by norm_num) (by norm_num) using 1 <;>
      norm_num
  have h_exp_fraction_lower :
      (11 / 10 : ℝ) < Real.exp (1 / 10 : ℝ) := by
    convert Real.add_one_lt_exp (x := (1 / 10 : ℝ)) (by norm_num) using 1 <;>
      norm_num
  have h_exp_upper :
      Real.exp (678 / 25 : ℝ) < (625000000000 : ℝ) := by
    calc
      Real.exp (678 / 25 : ℝ) =
          Real.exp 27 * Real.exp (3 / 25 : ℝ) := by
            rw [show (678 / 25 : ℝ) = 27 + 3 / 25 by norm_num,
              Real.exp_add]
      _ = Real.exp 1 ^ 27 * Real.exp (3 / 25 : ℝ) := by
            congr 1
            convert Real.exp_nat_mul (1 : ℝ) 27 using 1 <;> norm_num
      _ < (2719 / 1000 : ℝ) ^ 27 * (25 / 22 : ℝ) := by
            have hpow :
                Real.exp 1 ^ 27 < (2719 / 1000 : ℝ) ^ 27 := by
              gcongr
              exact h_exp_one_bounds.2
            exact mul_lt_mul hpow h_exp_fraction_upper.le
              (Real.exp_pos _) (by positivity)
      _ < (625000000000 : ℝ) := by norm_num
  have h_exp_lower :
      (5000000000000 / 9 : ℝ) < Real.exp (271 / 10 : ℝ) := by
    calc
      (5000000000000 / 9 : ℝ) <
          (2718 / 1000 : ℝ) ^ 27 * (11 / 10 : ℝ) := by norm_num
      _ < Real.exp 1 ^ 27 * Real.exp (1 / 10 : ℝ) := by
            have hpow :
                (2718 / 1000 : ℝ) ^ 27 < Real.exp 1 ^ 27 := by
              gcongr
              exact h_exp_one_bounds.1
            exact mul_lt_mul hpow h_exp_fraction_lower.le
              (by positivity) (by positivity)
      _ = Real.exp 27 * Real.exp (1 / 10 : ℝ) := by
            congr 1
            convert (Real.exp_nat_mul (1 : ℝ) 27).symm using 1 <;>
              norm_num
      _ = Real.exp (271 / 10 : ℝ) := by
            rw [← Real.exp_add]
            congr 1
            norm_num
  have h_upper_endpoint_inverse :
      (625000000000 : ℝ)⁻¹ <
        (Real.exp (678 / 25 : ℝ))⁻¹ :=
    (inv_lt_inv₀ (show 0 < (625000000000 : ℝ) by norm_num)
      (Real.exp_pos (678 / 25 : ℝ))).2 h_exp_upper
  have h_lower_endpoint_inverse :
      (Real.exp (271 / 10 : ℝ))⁻¹ <
        (5000000000000 / 9 : ℝ)⁻¹ :=
    (inv_lt_inv₀ (Real.exp_pos (271 / 10 : ℝ))
      (show 0 < (5000000000000 / 9 : ℝ) by norm_num)).2 h_exp_lower
  constructor
  · calc
      (16 : ℝ) / 10 ^ 13 = (625000000000 : ℝ)⁻¹ := by norm_num
      _ < (Real.exp (678 / 25 : ℝ))⁻¹ := h_upper_endpoint_inverse
      _ = Real.exp (-(678 / 25 : ℝ)) := (Real.exp_neg _).symm
      _ < Real.exp (-x) := Real.exp_lt_exp.mpr (by linarith)
  · calc
      Real.exp (-x) < Real.exp (-(271 / 10 : ℝ)) :=
        Real.exp_lt_exp.mpr (by linarith)
      _ = (Real.exp (271 / 10 : ℝ))⁻¹ := Real.exp_neg _
      _ < (5000000000000 / 9 : ℝ)⁻¹ := h_lower_endpoint_inverse
      _ = (18 : ℝ) / 10 ^ 13 := by norm_num

/-!
The requested dimensionless leading opaque-barrier tunneling estimate is
between `1.6 × 10⁻¹²` and `1.8 × 10⁻¹²`.  The separate lemma above derives
the `7 eV` barrier deficit used in that calculation; it is not presented as
an answer to the probability question.

This formalizes `thm:physics:phyx_mini_0616:target`.  Neither numerical bound
occurs in a scenario, figure, reference-data, positivity, calibration, or
governing-law premise.
-/
theorem problem_phyx_mini_0616
    (setup : CopperOxideTunnelingSetup)
    (_scenario : MatchesCopperOxideJunctionScenario setup)
    (_readouts : MatchesProblemNumericalReadouts setup)
    (_figure : MatchesSuppliedCopperOxideFigure setup)
    (_reference : UsesStandardElectronReferenceData setup)
    (_barrier : MatchesPhyslibRectangularBarrier setup)
    (_physical : HasPhysicalTunnelingParameters setup)
    (_decay : SatisfiesBarrierDecayRelation setup)
    (_estimate : DefinesLeadingOpaqueBarrierTransmissionEstimate setup) :
    (16 : ℝ) / 10 ^ 13 < setup.leadingOpaqueBarrierEstimate ∧
      setup.leadingOpaqueBarrierEstimate < (18 : ℝ) / 10 ^ 13 := by
  exact leading_opaque_barrier_estimate_between_1_6e_12_and_1_8e_12
    setup _readouts _reference _physical _decay _estimate

end PhyXMiniProblems.ProblemPhyXMini0616
