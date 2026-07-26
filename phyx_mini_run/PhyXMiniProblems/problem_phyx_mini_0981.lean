import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0981

open Dimension

/-!
# Thermal power in a bar sliding on inclined conducting rails

A metal bar of length `L`, mass `m`, and resistance `R` spans two
frictionless conducting rails inclined by `φ` above the horizontal.  The bar
is released from rest and eventually moves at terminal speed through a uniform
vertically downward magnetic field of magnitude `B`.

Physical magnitudes are represented by Physlib's unit-independent
`Dimensionful` quantities.  Real numbers occur only at coherent-SI readout
boundaries and for the dimensionless inclination angle.

Assumption/target split:

* governing laws: uniform-field calibration, projection of the vertical field
  onto the plane normal, motional emf, Ohm's law, Joule heating in the bar,
  magnetic drag, Newton's second law along the rails, resistance composition,
  and zero acceleration at terminal speed;
* previous-part results: none;
* figure/data readouts: metal and frictionless rails, negligible rail
  resistance, release from rest, bar endpoints `a` and `b`, bar length `L`,
  inclination `φ`, and two downward arrows labelled `B`;
* current target conclusion: the terminal thermal power is
  `R m^2 g^2 tan(φ)^2 / (L^2 B^2)`, answer B.

The terminal power is an independent observable in the setup.  No premise
below states the requested closed form or an answer-choice value.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- Acceleration has physical dimension `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Magnetic flux density (tesla) has physical dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Electromotive force (volt) has physical dimension `M L² T⁻² C⁻¹`. -/
def electromotiveForceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electric current (ampere) has physical dimension `C T⁻¹`. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Electrical resistance (ohm) has physical dimension `M L² T⁻¹ C⁻²`. -/
def electricalResistanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- Force (newton) has physical dimension `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Power (watt) has physical dimension `M L² T⁻³`. -/
def powerDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassMagnitude : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent speed. -/
abbrev SpeedMagnitude : Type := DimSpeed

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationMagnitude : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A signed tangential acceleration, positive down the rails. -/
abbrev TangentialAcceleration : Type :=
  Dimensionful (WithDim accelerationDimension ℝ)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative, unit-independent electromotive-force magnitude. -/
abbrev ElectromotiveForceMagnitude : Type :=
  Dimensionful (WithDim electromotiveForceDimension NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent force magnitude. -/
abbrev ForceMagnitude : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative, unit-independent rate of energy conversion. -/
abbrev PowerMagnitude : Type :=
  Dimensionful (WithDim powerDimension NNReal)

/-- Coherent-SI readout of length, in metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of mass, in kilograms. -/
def massInKilograms (mass : MassMagnitude) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of speed, in metres per second. -/
def speedInMetersPerSecond (speed : SpeedMagnitude) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of an acceleration magnitude. -/
def accelerationMagnitudeInMetersPerSecondSquared
    (acceleration : AccelerationMagnitude) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Signed coherent-SI readout of acceleration, in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : TangentialAcceleration) : ℝ :=
  (acceleration UnitChoices.SI).val

/-- Coherent-SI readout of magnetic flux density, in teslas. -/
def magneticFluxDensityInTeslas
    (fieldMagnitude : MagneticFluxDensityMagnitude) : ℝ :=
  ((fieldMagnitude UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of electromotive force, in volts. -/
def electromotiveForceInVolts
    (emf : ElectromotiveForceMagnitude) : ℝ :=
  ((emf UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of current, in amperes. -/
def electricCurrentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  ((current UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of resistance, in ohms. -/
def resistanceInOhms (resistance : ResistanceMagnitude) : ℝ :=
  ((resistance UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of force, in newtons. -/
def forceInNewtons (force : ForceMagnitude) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of power, in watts. -/
def powerInWatts (power : PowerMagnitude) : ℝ :=
  ((power UnitChoices.SI).val : ℝ)

/-! ## Physical apparatus and primary-raster vocabulary -/

/-- The two frictionless rails visible in image `981.png`. -/
inductive Rail where
  | throughA
  | throughB
  deriving DecidableEq, Fintype, Repr

/-- The printed endpoint names on the two ends of the bar. -/
inductive BarEndpoint where
  | a
  | b
  deriving DecidableEq, Fintype, Repr

/-- The two blue magnetic-field arrows drawn in the primary raster. -/
inductive FieldArrow where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Qualitative directions needed to transcribe the inclined-rail geometry. -/
inductive SpatialDirection where
  | verticallyDownward
  | downIncline
  | upIncline
  | acrossRails
  | aboveHorizontal
  deriving DecidableEq, Repr

/-- The rail on which each labelled end of the bar lies. -/
def expectedRailForEndpoint : BarEndpoint → Rail
  | .a => .throughA
  | .b => .throughB

/-!
Literal content of the supplied raster.  The symbols `a` and `b` label bar
endpoints; they are not additional scalar lengths.
-/
structure InclinedRailFigure where
  inclinedSupportShown : Bool
  railShown : Rail → Bool
  barShown : Bool
  barSpansRails : Bool
  endpointShown : BarEndpoint → Bool
  endpointLabelShown : BarEndpoint → Bool
  endpointOnRail : BarEndpoint → Rail
  barLengthLabelShown : Bool
  barLengthDirection : SpatialDirection
  inclinationArcShown : Bool
  inclinationLabelPhiShown : Bool
  inclinationDirection : SpatialDirection
  fieldArrowShown : FieldArrow → Bool
  fieldArrowLabelledB : FieldArrow → Bool
  fieldArrowDirection : FieldArrow → SpatialDirection

/-! Independent terminal observables and physical parameters of the setup. -/
structure InclinedRailBarSetup where
  figure : InclinedRailFigure
  magneticField : Electromagnetism.MagneticField 3
  uniformFieldRegion : Set (Time × Space 3)
  barLength : LengthMagnitude
  barMass : MassMagnitude
  barResistance : ResistanceMagnitude
  railResistance : ResistanceMagnitude
  totalCircuitResistance : ResistanceMagnitude
  gravityMagnitude : AccelerationMagnitude
  inclinationRadians : ℝ
  appliedFieldMagnitude : MagneticFluxDensityMagnitude
  normalFieldComponentMagnitude : MagneticFluxDensityMagnitude
  initialSpeed : SpeedMagnitude
  terminalSpeed : SpeedMagnitude
  terminalTangentialAcceleration : TangentialAcceleration
  terminalInducedEmf : ElectromotiveForceMagnitude
  terminalCurrent : ElectricCurrentMagnitude
  terminalMagneticDragForce : ForceMagnitude
  terminalBarThermalPower : PowerMagnitude
  barIsMetal : Bool
  railsAreMetal : Bool
  railsAreFrictionless : Bool
  railsFormClosedCircuit : Bool
  barHasBeenReleased : Bool
  terminalStateHasBeenReached : Bool

/-! ## Scenario evidence, physical domains, and governing laws -/

/-- The apparatus properties stated in the prose, including release from rest. -/
structure MatchesInclinedRailBarScenario
    (setup : InclinedRailBarSetup) : Prop where
  barIsMetal : setup.barIsMetal = true
  railsAreMetal : setup.railsAreMetal = true
  railsAreFrictionless : setup.railsAreFrictionless = true
  circuitIsClosed : setup.railsFormClosedCircuit = true
  barWasReleased : setup.barHasBeenReleased = true
  terminalStateReached : setup.terminalStateHasBeenReached = true
  releasedFromRest : speedInMetersPerSecond setup.initialSpeed = 0
  railsHaveNegligibleResistance :
    resistanceInOhms setup.railResistance = 0

/-- Primary-raster transcription for endpoints, length, incline, and field. -/
structure MatchesPrimaryInclinedRailFigure
    (setup : InclinedRailBarSetup) : Prop where
  supportIsShown : setup.figure.inclinedSupportShown = true
  bothRailsAreShown : ∀ rail, setup.figure.railShown rail = true
  barIsShown : setup.figure.barShown = true
  barSpansBothRails : setup.figure.barSpansRails = true
  bothEndpointsAreShown : ∀ endpoint, setup.figure.endpointShown endpoint = true
  endpointNamesAreShown :
    ∀ endpoint, setup.figure.endpointLabelShown endpoint = true
  endpointsMeetExpectedRails :
    ∀ endpoint,
      setup.figure.endpointOnRail endpoint = expectedRailForEndpoint endpoint
  lengthLabelLIsShown : setup.figure.barLengthLabelShown = true
  lengthRunsAcrossRails : setup.figure.barLengthDirection = .acrossRails
  inclinationArcIsShown : setup.figure.inclinationArcShown = true
  inclinationLabelPhiIsShown : setup.figure.inclinationLabelPhiShown = true
  inclineIsMeasuredAboveHorizontal :
    setup.figure.inclinationDirection = .aboveHorizontal
  bothFieldArrowsAreShown :
    ∀ arrow, setup.figure.fieldArrowShown arrow = true
  bothFieldArrowsAreLabelledB :
    ∀ arrow, setup.figure.fieldArrowLabelledB arrow = true
  bothFieldArrowsPointDownward :
    ∀ arrow,
      setup.figure.fieldArrowDirection arrow = .verticallyDownward

/-- Positivity and nondegeneracy assumptions for the physical apparatus. -/
structure HasPhysicalInclinedRailParameters
    (setup : InclinedRailBarSetup) : Prop where
  barLengthPositive : 0 < lengthInMeters setup.barLength
  barMassPositive : 0 < massInKilograms setup.barMass
  barResistancePositive : 0 < resistanceInOhms setup.barResistance
  gravityPositive :
    0 < accelerationMagnitudeInMetersPerSecondSquared setup.gravityMagnitude
  fieldMagnitudePositive :
    0 < magneticFluxDensityInTeslas setup.appliedFieldMagnitude
  normalFieldComponentPositive :
    0 < magneticFluxDensityInTeslas setup.normalFieldComponentMagnitude
  terminalSpeedPositive : 0 < speedInMetersPerSecond setup.terminalSpeed
  inclinationPositive : 0 < setup.inclinationRadians
  inclinationAcute : setup.inclinationRadians < Real.pi / 2
  fieldRegionNonempty : setup.uniformFieldRegion.Nonempty

/-- The rails and bar resistances compose the resistance of the closed circuit. -/
structure SatisfiesInclinedRailResistanceComposition
    (setup : InclinedRailBarSetup) : Prop where
  totalResistanceIsSum :
    resistanceInOhms setup.totalCircuitResistance =
      resistanceInOhms setup.barResistance +
        resistanceInOhms setup.railResistance

/-!
The Physlib magnetic vector field is constant throughout the marked region,
and its norm is calibrated by the independent dimensionful applied magnitude
`B`.
-/
structure HasUniformAppliedMagneticField
    (setup : InclinedRailBarSetup) : Prop where
  fieldVectorConstant : ∀ time₁ position₁ time₂ position₂,
    (time₁, position₁) ∈ setup.uniformFieldRegion →
      (time₂, position₂) ∈ setup.uniformFieldRegion →
        setup.magneticField time₁ position₁ =
          setup.magneticField time₂ position₂
  fieldMagnitudeCalibration : ∀ time position,
    (time, position) ∈ setup.uniformFieldRegion →
      ‖setup.magneticField time position‖ =
        magneticFluxDensityInTeslas setup.appliedFieldMagnitude

/-!
The vertically downward field contributes its plane-normal component
`B cos φ` to both motional induction and magnetic drag.
-/
structure SatisfiesInclinedRailFieldGeometry
    (setup : InclinedRailBarSetup) : Prop where
  normalComponentLaw :
    magneticFluxDensityInTeslas setup.normalFieldComponentMagnitude =
      magneticFluxDensityInTeslas setup.appliedFieldMagnitude *
        Real.cos setup.inclinationRadians

/-!
School-level electromechanical laws at terminal speed.  Each equation relates
independent observables; none contains the requested closed power expression.
-/
structure SatisfiesTerminalRailBarLaws
    (setup : InclinedRailBarSetup) : Prop where
  motionalEmfLaw :
    electromotiveForceInVolts setup.terminalInducedEmf =
      magneticFluxDensityInTeslas setup.normalFieldComponentMagnitude *
        lengthInMeters setup.barLength *
          speedInMetersPerSecond setup.terminalSpeed
  ohmsLaw :
    electromotiveForceInVolts setup.terminalInducedEmf =
      electricCurrentInAmperes setup.terminalCurrent *
        resistanceInOhms setup.totalCircuitResistance
  jouleHeatingLaw :
    powerInWatts setup.terminalBarThermalPower =
      electricCurrentInAmperes setup.terminalCurrent ^ 2 *
        resistanceInOhms setup.barResistance
  magneticDragMagnitudeLaw :
    forceInNewtons setup.terminalMagneticDragForce =
      magneticFluxDensityInTeslas setup.normalFieldComponentMagnitude *
        electricCurrentInAmperes setup.terminalCurrent *
          lengthInMeters setup.barLength
  newtonsSecondLawAlongRails :
    massInKilograms setup.barMass *
        accelerationInMetersPerSecondSquared
          setup.terminalTangentialAcceleration =
      massInKilograms setup.barMass *
          accelerationMagnitudeInMetersPerSecondSquared setup.gravityMagnitude *
            Real.sin setup.inclinationRadians -
        forceInNewtons setup.terminalMagneticDragForce
  terminalAccelerationIsZero :
    accelerationInMetersPerSecondSquared
        setup.terminalTangentialAcceleration = 0

/-!
At terminal speed, the electrical energy converted to heat in the bar per
second is answer B.
-/
theorem terminal_bar_thermal_power_matches_answer_B
    (setup : InclinedRailBarSetup)
    (_scenario : MatchesInclinedRailBarScenario setup)
    (_figure : MatchesPrimaryInclinedRailFigure setup)
    (_physical : HasPhysicalInclinedRailParameters setup)
    (_resistance : SatisfiesInclinedRailResistanceComposition setup)
    (_uniformField : HasUniformAppliedMagneticField setup)
    (_geometry : SatisfiesInclinedRailFieldGeometry setup)
    (_laws : SatisfiesTerminalRailBarLaws setup) :
    powerInWatts setup.terminalBarThermalPower =
      resistanceInOhms setup.barResistance *
          massInKilograms setup.barMass ^ 2 *
            accelerationMagnitudeInMetersPerSecondSquared setup.gravityMagnitude ^ 2 *
              Real.tan setup.inclinationRadians ^ 2 /
        (lengthInMeters setup.barLength ^ 2 *
          magneticFluxDensityInTeslas setup.appliedFieldMagnitude ^ 2) := by
  have h_length_ne : lengthInMeters setup.barLength ≠ 0 :=
    _physical.barLengthPositive.ne'
  have h_field_ne :
      magneticFluxDensityInTeslas setup.appliedFieldMagnitude ≠ 0 :=
    _physical.fieldMagnitudePositive.ne'
  have h_cos_ne : Real.cos setup.inclinationRadians ≠ 0 := by
    intro h_cos
    have h_normal := _geometry.normalComponentLaw
    rw [h_cos, mul_zero] at h_normal
    exact _physical.normalFieldComponentPositive.ne' h_normal
  have h_terminal_balance := _laws.newtonsSecondLawAlongRails
  rw [_laws.terminalAccelerationIsZero] at h_terminal_balance
  simp only [mul_zero] at h_terminal_balance
  have h_force_rearrange (field cosine current length : ℝ) :
      (field * cosine) * current * length =
        current * length * field * cosine := by
    ring
  have h_force_balance :
      massInKilograms setup.barMass *
          accelerationMagnitudeInMetersPerSecondSquared setup.gravityMagnitude *
          Real.sin setup.inclinationRadians =
        electricCurrentInAmperes setup.terminalCurrent *
          lengthInMeters setup.barLength *
          magneticFluxDensityInTeslas setup.appliedFieldMagnitude *
          Real.cos setup.inclinationRadians := by
    calc
      massInKilograms setup.barMass *
            accelerationMagnitudeInMetersPerSecondSquared setup.gravityMagnitude *
            Real.sin setup.inclinationRadians =
          forceInNewtons setup.terminalMagneticDragForce := by
        exact sub_eq_zero.mp h_terminal_balance.symm
      _ = magneticFluxDensityInTeslas setup.normalFieldComponentMagnitude *
            electricCurrentInAmperes setup.terminalCurrent *
              lengthInMeters setup.barLength :=
        _laws.magneticDragMagnitudeLaw
      _ = electricCurrentInAmperes setup.terminalCurrent *
            lengthInMeters setup.barLength *
            magneticFluxDensityInTeslas setup.appliedFieldMagnitude *
            Real.cos setup.inclinationRadians := by
        rw [_geometry.normalComponentLaw]
        exact h_force_rearrange _ _ _ _
  have h_current_rearrange (current length field cosine : ℝ) :
      current * (length * field) * cosine =
        current * length * field * cosine := by
    ring
  have h_current :
      electricCurrentInAmperes setup.terminalCurrent =
        massInKilograms setup.barMass *
            accelerationMagnitudeInMetersPerSecondSquared setup.gravityMagnitude *
            Real.tan setup.inclinationRadians /
          (lengthInMeters setup.barLength *
            magneticFluxDensityInTeslas setup.appliedFieldMagnitude) := by
    rw [Real.tan_eq_sin_div_cos]
    apply (eq_div_iff (mul_ne_zero h_length_ne h_field_ne)).2
    rw [← mul_div_assoc]
    apply (eq_div_iff h_cos_ne).2
    calc
      electricCurrentInAmperes setup.terminalCurrent *
            (lengthInMeters setup.barLength *
              magneticFluxDensityInTeslas setup.appliedFieldMagnitude) *
            Real.cos setup.inclinationRadians =
          electricCurrentInAmperes setup.terminalCurrent *
            lengthInMeters setup.barLength *
            magneticFluxDensityInTeslas setup.appliedFieldMagnitude *
            Real.cos setup.inclinationRadians :=
        h_current_rearrange _ _ _ _
      _ = massInKilograms setup.barMass *
            accelerationMagnitudeInMetersPerSecondSquared setup.gravityMagnitude *
            Real.sin setup.inclinationRadians :=
        h_force_balance.symm
  have h_joule_algebra
      (current resistance mass gravity tangent length field : ℝ)
      (h_current_value :
        current = mass * gravity * tangent / (length * field)) :
      current ^ 2 * resistance =
        resistance * mass ^ 2 * gravity ^ 2 * tangent ^ 2 /
          (length ^ 2 * field ^ 2) := by
    rw [h_current_value]
    simp only [div_pow, mul_pow]
    ring
  calc
    powerInWatts setup.terminalBarThermalPower =
        electricCurrentInAmperes setup.terminalCurrent ^ 2 *
          resistanceInOhms setup.barResistance :=
      _laws.jouleHeatingLaw
    _ = resistanceInOhms setup.barResistance *
          massInKilograms setup.barMass ^ 2 *
            accelerationMagnitudeInMetersPerSecondSquared setup.gravityMagnitude ^ 2 *
              Real.tan setup.inclinationRadians ^ 2 /
        (lengthInMeters setup.barLength ^ 2 *
          magneticFluxDensityInTeslas setup.appliedFieldMagnitude ^ 2) :=
      h_joule_algebra _ _ _ _ _ _ _ h_current

end PhyXMiniProblems.ProblemPhyXMini0981
