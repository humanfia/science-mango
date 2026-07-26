import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0937

open Dimension

/-!
# Magnetic force on a moving slidewire

A vertical conducting rod of length `0.10 m` moves to the right at `2.5 m/s`
on a U-shaped track.  A uniform magnetic field of flux-density magnitude
`0.60 T` points into the page, and the closed loop has total resistance
`0.030 Ω`.  The motion induces an upward emf and a counterclockwise current.

Physical magnitudes are unit-independent Physlib `Dimensionful` quantities;
real numbers are used only for coherent-SI readouts.  The applied magnetic
field also retains Physlib's spacetime-dependent vector-field type.

Assumption/target split:

* governing laws: uniform-field calibration, motional emf `E = B L v`, Ohm's
  law `E = I R`, magnetic-force magnitude `F = B I L`, and the fact that the
  induced magnetic force opposes the rod's motion;
* previous-part results: none;
* figure/data readouts: rail labels `a` and `b`, field crosses into the page,
  the displayed emf/current/velocity directions, and the four stated SI
  measurements;
* current target conclusion: the force magnitude is `0.3 N` (answer B).

The target force value is neither a setup-field definition nor a premise.
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

/-- Coherent-SI readout of force, in newtons. -/
def forceInNewtons (force : ForceMagnitude) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-! ## Apparatus and primary-raster labels -/

/-- The literal labels printed beside the upper and lower contact points. -/
inductive RailLabel where
  | a
  | b
  deriving DecidableEq, Repr

/-- The two conducting pieces in the closed slidewire circuit. -/
inductive ConductorPart where
  | uShapedTrack
  | movingRod
  deriving DecidableEq, Fintype, Repr

/-- Named side-view directions used by the supplied figure. -/
inductive SpatialDirection where
  | right
  | left
  | upward
  | downward
  | intoPage
  | outOfPage
  deriving DecidableEq, Repr

/-- Reversal of a displayed spatial direction. -/
def SpatialDirection.opposite : SpatialDirection → SpatialDirection
  | .right => .left
  | .left => .right
  | .upward => .downward
  | .downward => .upward
  | .intoPage => .outOfPage
  | .outOfPage => .intoPage

/-- Orientation of the current around the loop as seen on the page. -/
inductive CircuitSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Axis orientation of a drawn conductor. -/
inductive AxisOrientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-!
Literal qualitative content of image `937.png`.  The raster supplies the
labels and directions below but does not itself print the numerical data or a
force value.
-/
structure SlidewireFigure where
  conductorShown : ConductorPart → Bool
  contactsBothRails : Bool
  topContactLabel : RailLabel
  bottomContactLabel : RailLabel
  movingRodOrientation : AxisOrientation
  uniformFieldCrossesShown : Bool
  magneticFieldDirection : SpatialDirection
  rodVelocityDirection : SpatialDirection
  inducedEmfDirection : SpatialDirection
  topRailCurrentDirection : SpatialDirection
  bottomRailCurrentDirection : SpatialDirection
  inferredCurrentSense : CircuitSense

/-!
Independent observables at one instant.  In particular, the magnetic force is
not defined from the requested numerical answer.
-/
structure SlidewireForceSetup where
  magneticField : Electromagnetism.MagneticField 3
  uniformFieldRegion : Set (Time × Space 3)
  magneticFluxDensityMagnitude : MagneticFluxDensityMagnitude
  movingRodLength : LengthMagnitude
  movingRodSpeed : SpeedMagnitude
  totalLoopResistance : ResistanceMagnitude
  inducedEmf : ElectromotiveForceMagnitude
  inducedCurrent : ElectricCurrentMagnitude
  magneticForceMagnitude : ForceMagnitude
  magneticForceDirection : SpatialDirection
  figure : SlidewireFigure

/-! ## Scenario, data, and governing laws -/

/-- The prose and diagram identify a moving rod closing a U-shaped track. -/
structure MatchesSlidewireForceScenario
    (setup : SlidewireForceSetup) : Prop where
  uShapedTrackShown :
    setup.figure.conductorShown .uShapedTrack = true
  movingRodShown :
    setup.figure.conductorShown .movingRod = true
  rodContactsBothRails : setup.figure.contactsBothRails = true
  rodIsVertical : setup.figure.movingRodOrientation = .vertical

/-!
Primary-raster evidence, including the literal `a` and `b` labels.  No force
magnitude or answer choice is included here.
-/
structure MatchesPrimarySlidewireFigure
    (setup : SlidewireForceSetup) : Prop where
  topRailIsA : setup.figure.topContactLabel = .a
  bottomRailIsB : setup.figure.bottomContactLabel = .b
  uniformFieldCrossesAreShown :
    setup.figure.uniformFieldCrossesShown = true
  fieldPointsIntoPage :
    setup.figure.magneticFieldDirection = .intoPage
  rodMovesRight : setup.figure.rodVelocityDirection = .right
  emfPointsUpward : setup.figure.inducedEmfDirection = .upward
  topRailCurrentPointsLeft :
    setup.figure.topRailCurrentDirection = .left
  bottomRailCurrentPointsRight :
    setup.figure.bottomRailCurrentDirection = .right
  displayedRailArrowsGiveCounterclockwiseCurrent :
    setup.figure.inferredCurrentSense = .counterclockwise

/-- Exact coherent-SI measurements stated in the problem text. -/
structure MatchesGivenSlidewireMeasurements
    (setup : SlidewireForceSetup) : Prop where
  rodLengthMeters :
    lengthInMeters setup.movingRodLength = (1 : ℝ) / 10
  rodSpeedMetersPerSecond :
    speedInMetersPerSecond setup.movingRodSpeed = (5 : ℝ) / 2
  totalResistanceOhms :
    resistanceInOhms setup.totalLoopResistance = (3 : ℝ) / 100
  magneticFluxDensityTeslas :
    magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude =
      (3 : ℝ) / 5

/-- Positivity and non-vacuity conditions for the modeled physical state. -/
structure HasPhysicalSlidewireForceParameters
    (setup : SlidewireForceSetup) : Prop where
  fieldMagnitudePositive :
    0 < magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  movingRodLengthPositive :
    0 < lengthInMeters setup.movingRodLength
  movingRodSpeedPositive :
    0 < speedInMetersPerSecond setup.movingRodSpeed
  totalResistancePositive :
    0 < resistanceInOhms setup.totalLoopResistance
  fieldRegionNonempty : setup.uniformFieldRegion.Nonempty

/-!
The scalar flux-density magnitude calibrates the norm of Physlib's magnetic
vector field throughout the region marked by uniform crosses.
-/
structure HasUniformAppliedMagneticField
    (setup : SlidewireForceSetup) : Prop where
  uniformMagnitude : ∀ time position,
    (time, position) ∈ setup.uniformFieldRegion →
      ‖setup.magneticField time position‖ =
        magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude

/-!
School-physics laws for a rod perpendicular to its velocity and the uniform
field.  They relate independent observables; none gives the requested
`0.3 N` value.
-/
structure SatisfiesSlidewireForceLaws
    (setup : SlidewireForceSetup) : Prop where
  motionalEmfLaw :
    electromotiveForceInVolts setup.inducedEmf =
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
        lengthInMeters setup.movingRodLength *
          speedInMetersPerSecond setup.movingRodSpeed
  ohmsLaw :
    electromotiveForceInVolts setup.inducedEmf =
      electricCurrentInAmperes setup.inducedCurrent *
        resistanceInOhms setup.totalLoopResistance
  magneticForceMagnitudeLaw :
    forceInNewtons setup.magneticForceMagnitude =
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
        electricCurrentInAmperes setup.inducedCurrent *
          lengthInMeters setup.movingRodLength
  inducedForceOpposesMotion :
    setup.magneticForceDirection = setup.figure.rodVelocityDirection.opposite

/-!
Eliminating the induced emf and current gives the general drag-force magnitude
for this perpendicular slidewire geometry.
-/
lemma magnetic_force_magnitude_formula
    (setup : SlidewireForceSetup)
    (_physical : HasPhysicalSlidewireForceParameters setup)
    (_laws : SatisfiesSlidewireForceLaws setup) :
    forceInNewtons setup.magneticForceMagnitude =
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude ^ 2 *
        lengthInMeters setup.movingRodLength ^ 2 *
          speedInMetersPerSecond setup.movingRodSpeed /
            resistanceInOhms setup.totalLoopResistance := by
  have hR : resistanceInOhms setup.totalLoopResistance ≠ 0 :=
    ne_of_gt _physical.totalResistancePositive
  apply (eq_div_iff hR).2
  rw [_laws.magneticForceMagnitudeLaw]
  calc
    (magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
          electricCurrentInAmperes setup.inducedCurrent *
            lengthInMeters setup.movingRodLength) *
        resistanceInOhms setup.totalLoopResistance =
        magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
          lengthInMeters setup.movingRodLength *
            (electricCurrentInAmperes setup.inducedCurrent *
              resistanceInOhms setup.totalLoopResistance) := by
      ring
    _ = magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
          lengthInMeters setup.movingRodLength *
            (magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
              lengthInMeters setup.movingRodLength *
                speedInMetersPerSecond setup.movingRodSpeed) := by
      rw [← _laws.ohmsLaw, _laws.motionalEmfLaw]
    _ = magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude ^ 2 *
          lengthInMeters setup.movingRodLength ^ 2 *
            speedInMetersPerSecond setup.movingRodSpeed := by
      ring

/-!
For the four stated measurements, the force acting on the moving rod has
magnitude `0.3 N`, which is answer B.
-/
theorem force_on_moving_rod
    (setup : SlidewireForceSetup)
    (_scenario : MatchesSlidewireForceScenario setup)
    (_figure : MatchesPrimarySlidewireFigure setup)
    (_measurements : MatchesGivenSlidewireMeasurements setup)
    (_physical : HasPhysicalSlidewireForceParameters setup)
    (_uniformField : HasUniformAppliedMagneticField setup)
    (_laws : SatisfiesSlidewireForceLaws setup) :
    forceInNewtons setup.magneticForceMagnitude = (3 : ℝ) / 10 := by
  rw [magnetic_force_magnitude_formula setup _physical _laws,
    _measurements.magneticFluxDensityTeslas,
    _measurements.rodLengthMeters,
    _measurements.rodSpeedMetersPerSecond,
    _measurements.totalResistanceOhms]
  norm_num

end PhyXMiniProblems.ProblemPhyXMini0937
