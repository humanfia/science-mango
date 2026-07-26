import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0919

open Dimension

/-!
# Resistive power dissipated by a moving slidewire

A vertical conducting rod of length `L` slides to the right with speed `v` on
a U-shaped conductor.  A uniform magnetic field `B` points into the page.  The
motion induces an upward emf and a counterclockwise current, while the magnetic
force on the rod points left and opposes its motion.  The total instantaneous
resistance `R` includes both the moving rod and the U-shaped conductor.

Physical magnitudes are unit-independent Physlib `Dimensionful` quantities.
Real numbers occur only as coherent-SI readouts.  The applied magnetic field
also retains Physlib's spacetime-dependent vector-field type.

Assumption/target split:

* governing laws: resistance addition, the uniform-field calibration,
  motional emf `E = B L v`, Ohm's law `E = I R`, electrical power `P = E I`,
  and the magnetic-force magnitude law `F = B I L`;
* previous-part results: none;
* figure/data readouts: the field is into the page, the rod length and induced
  emf point upward, the rod velocity points right, the magnetic force points
  left, and the displayed current is counterclockwise;
* current target conclusion: `P = B^2 L^2 v^2 / R` (answer C).

The target power formula is not a setup field definition and does not occur in
any premise structure.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The dimension `M T⁻¹ C⁻¹` of magnetic flux density (tesla). -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L² T⁻² C⁻¹` of electromotive force (volt). -/
def electromotiveForceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `C T⁻¹` of electric current (ampere). -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- The dimension `M L² T⁻¹ C⁻²` of electrical resistance (ohm). -/
def electricalResistanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L² T⁻³` of power (watt). -/
def powerDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- The dimension `M L T⁻²` of force (newton). -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent speed. -/
abbrev SpeedMagnitude : Type := DimSpeed

/-- A nonnegative, unit-independent electromotive-force magnitude. -/
abbrev ElectromotiveForceMagnitude : Type :=
  Dimensionful (WithDim electromotiveForceDimension NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent rate of energy dissipation. -/
abbrev PowerMagnitude : Type :=
  Dimensionful (WithDim powerDimension NNReal)

/-- A nonnegative, unit-independent magnetic-force magnitude. -/
abbrev ForceMagnitude : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Coherent-SI readout of magnetic flux density, in teslas. -/
def magneticFluxDensityInTeslas
    (fieldMagnitude : MagneticFluxDensityMagnitude) : ℝ :=
  ((fieldMagnitude UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of length, in metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of speed, in metres per second. -/
def speedInMetersPerSecond (speed : SpeedMagnitude) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of electromotive force, in volts. -/
def electromotiveForceInVolts
    (emf : ElectromotiveForceMagnitude) : ℝ :=
  ((emf UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of electric current, in amperes. -/
def electricCurrentInAmperes
    (current : ElectricCurrentMagnitude) : ℝ :=
  ((current UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of resistance, in ohms. -/
def resistanceInOhms (resistance : ResistanceMagnitude) : ℝ :=
  ((resistance UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of dissipated power, in watts. -/
def powerInWatts (power : PowerMagnitude) : ℝ :=
  ((power UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of force, in newtons. -/
def forceInNewtons (force : ForceMagnitude) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-! ## Physical apparatus and primary-figure labels -/

/-- The two conducting parts whose resistances make up the circuit resistance. -/
inductive ConductorPart where
  | movingSlidewire
  | uShapedConductor
  deriving DecidableEq, Fintype, Repr

/-- Named directions needed to transcribe the supplied side-view figure. -/
inductive SpatialDirection where
  | right
  | left
  | upward
  | downward
  | intoPage
  | outOfPage
  deriving DecidableEq, Repr

/-- Orientation of current around the rectangular circuit as seen on the page. -/
inductive CircuitSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-!
Literal content of image `919.png`.  The figure supplies directions and object
labels but no numerical values for `B`, `L`, `v`, `R`, `E`, `I`, `F`, or `P`.
-/
structure SlidewireFigure where
  conductorShown : ConductorPart → Bool
  formsClosedCircuit : Bool
  uniformFieldCrossesShown : Bool
  magneticFieldDirection : SpatialDirection
  slidewireLengthDirection : SpatialDirection
  slidewireVelocityDirection : SpatialDirection
  inducedEmfDirection : SpatialDirection
  magneticForceDirection : SpatialDirection
  currentOnTopRailDirection : SpatialDirection
  currentOnBottomRailDirection : SpatialDirection
  currentOnSlidewireDirection : SpatialDirection
  currentSense : CircuitSense

/-!
Independent observables at one instant of the slidewire's motion.  In
particular, `energyDissipationRate` is not defined from the answer formula.
-/
structure SlidewireCircuitSetup where
  magneticField : Electromagnetism.MagneticField 3
  uniformFieldRegion : Set (Time × Space 3)
  magneticFluxDensityMagnitude : MagneticFluxDensityMagnitude
  slidewireLength : LengthMagnitude
  slidewireSpeed : SpeedMagnitude
  slidewireResistance : ResistanceMagnitude
  uShapedConductorResistance : ResistanceMagnitude
  totalCircuitResistance : ResistanceMagnitude
  inducedEmf : ElectromotiveForceMagnitude
  inducedCurrent : ElectricCurrentMagnitude
  energyDissipationRate : PowerMagnitude
  magneticDragForceMagnitude : ForceMagnitude
  figure : SlidewireFigure

/-! ## Scenario, figure evidence, and governing laws -/

/-- The prose identifies the two displayed conductors as one closed circuit. -/
structure MatchesSlidewireCircuitScenario
    (setup : SlidewireCircuitSetup) : Prop where
  movingSlidewireShown :
    setup.figure.conductorShown .movingSlidewire = true
  uShapedConductorShown :
    setup.figure.conductorShown .uShapedConductor = true
  circuitIsClosed : setup.figure.formsClosedCircuit = true

/-!
Primary-raster evidence.  These are qualitative direction readouts only; no
power formula or answer-choice value occurs here.
-/
structure MatchesPrimarySlidewireFigure
    (setup : SlidewireCircuitSetup) : Prop where
  uniformFieldCrossesAreShown :
    setup.figure.uniformFieldCrossesShown = true
  fieldPointsIntoPage :
    setup.figure.magneticFieldDirection = .intoPage
  lengthArrowPointsUpward :
    setup.figure.slidewireLengthDirection = .upward
  velocityArrowPointsRight :
    setup.figure.slidewireVelocityDirection = .right
  emfArrowPointsUpward :
    setup.figure.inducedEmfDirection = .upward
  forceArrowPointsLeft :
    setup.figure.magneticForceDirection = .left
  topRailCurrentPointsLeft :
    setup.figure.currentOnTopRailDirection = .left
  bottomRailCurrentPointsRight :
    setup.figure.currentOnBottomRailDirection = .right
  slidewireCurrentPointsUpward :
    setup.figure.currentOnSlidewireDirection = .upward
  displayedCurrentIsCounterclockwise :
    setup.figure.currentSense = .counterclockwise

/-- Positivity and non-vacuity conditions for the physical slidewire state. -/
structure HasPhysicalSlidewireParameters
    (setup : SlidewireCircuitSetup) : Prop where
  fieldMagnitudePositive :
    0 < magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  slidewireLengthPositive :
    0 < lengthInMeters setup.slidewireLength
  slidewireSpeedPositive :
    0 < speedInMetersPerSecond setup.slidewireSpeed
  totalResistancePositive :
    0 < resistanceInOhms setup.totalCircuitResistance
  fieldRegionNonempty : setup.uniformFieldRegion.Nonempty

/-!
The resistance named `R` in the problem is the sum of the resistance of the
moving slidewire and that of the U-shaped conductor.
-/
structure SatisfiesCircuitResistanceComposition
    (setup : SlidewireCircuitSetup) : Prop where
  totalResistanceIsComponentSum :
    resistanceInOhms setup.totalCircuitResistance =
      resistanceInOhms setup.slidewireResistance +
        resistanceInOhms setup.uShapedConductorResistance

/-!
The scalar flux-density magnitude calibrates the norm of the Physlib magnetic
vector field throughout the region marked by uniform crosses.
-/
structure HasUniformAppliedMagneticField
    (setup : SlidewireCircuitSetup) : Prop where
  uniformMagnitude : ∀ time position,
    (time, position) ∈ setup.uniformFieldRegion →
      ‖setup.magneticField time position‖ =
        magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude

/-!
School-physics laws for a rod perpendicular to both its velocity and a uniform
magnetic field.  These laws relate independent observables and do not state the
requested expression for dissipated power.
-/
structure SatisfiesSlidewireInductionAndCircuitLaws
    (setup : SlidewireCircuitSetup) : Prop where
  motionalEmfLaw :
    electromotiveForceInVolts setup.inducedEmf =
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
        lengthInMeters setup.slidewireLength *
          speedInMetersPerSecond setup.slidewireSpeed
  ohmsLaw :
    electromotiveForceInVolts setup.inducedEmf =
      electricCurrentInAmperes setup.inducedCurrent *
        resistanceInOhms setup.totalCircuitResistance
  electricalPowerLaw :
    powerInWatts setup.energyDissipationRate =
      electromotiveForceInVolts setup.inducedEmf *
        electricCurrentInAmperes setup.inducedCurrent
  magneticForceMagnitudeLaw :
    forceInNewtons setup.magneticDragForceMagnitude =
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
        electricCurrentInAmperes setup.inducedCurrent *
          lengthInMeters setup.slidewireLength

/-!
The rate at which energy is dissipated in the circuit is answer C:
`B² L² v² / R` in coherent SI units.
-/
theorem slidewire_energy_dissipation_rate
    (setup : SlidewireCircuitSetup)
    (_scenario : MatchesSlidewireCircuitScenario setup)
    (_figure : MatchesPrimarySlidewireFigure setup)
    (_physical : HasPhysicalSlidewireParameters setup)
    (_resistance : SatisfiesCircuitResistanceComposition setup)
    (_uniformField : HasUniformAppliedMagneticField setup)
    (_laws : SatisfiesSlidewireInductionAndCircuitLaws setup) :
    powerInWatts setup.energyDissipationRate =
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude ^ 2 *
        lengthInMeters setup.slidewireLength ^ 2 *
          speedInMetersPerSecond setup.slidewireSpeed ^ 2 /
            resistanceInOhms setup.totalCircuitResistance := by
  have hResistanceNeZero :
      resistanceInOhms setup.totalCircuitResistance ≠ 0 :=
    ne_of_gt _physical.totalResistancePositive
  apply (eq_div_iff hResistanceNeZero).2
  rw [_laws.electricalPowerLaw, mul_assoc, ← _laws.ohmsLaw,
    _laws.motionalEmfLaw]
  ring

end PhyXMiniProblems.ProblemPhyXMini0919
