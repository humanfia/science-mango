import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0561

open Dimension

/-!
# Earth's magnetic-field correction to Thomson's second `e/m` experiment

Thomson first selects the horizontal speed of an electron beam with crossed
electric and magnetic fields.  The beam is then deflected upward between the
parallel plates and travels to the screen.  The primary figure labels the
plate length `x₁`, exit height `y₁`, outside drift length `x₂`, total screen
height `y₂`, velocity components `uₓ` and `uᵧ`, and final angle `θ`.

The correction considered here is an oriented horizontal component of Earth's
magnetic field in the region outside the plates.  In the chosen coordinates,
a negative component gives a downward magnetic acceleration and reduces the
screen height relative to the electric-only prediction.

Dimensionful scalars use Physlib's unit-independent `Dimensionful` quantities.
Named real-valued functions below are their coherent SI readouts.  Electric
and magnetic fields themselves remain Physlib spacetime-dependent vector
fields rather than scalar aliases.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- The physical dimension `L T⁻¹` of a velocity component. -/
def speedDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension `L T⁻²` of an acceleration component. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension `M T⁻¹ C⁻¹` of magnetic-field strength. -/
def magneticFieldStrengthDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension `C M⁻¹` of a charge-to-mass ratio. -/
def chargeToMassDimension : Dimension := C𝓭 * M𝓭⁻¹

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical time interval. -/
abbrev TimeIntervalQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A signed physical velocity component. -/
abbrev VelocityComponentQuantity : Type :=
  Dimensionful (WithDim speedDimension ℝ)

/-- A signed physical acceleration component. -/
abbrev AccelerationComponentQuantity : Type :=
  Dimensionful (WithDim accelerationDimension ℝ)

/-- A nonnegative electric-field magnitude. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A nonnegative applied magnetic-field magnitude. -/
abbrev MagneticFieldStrengthQuantity : Type :=
  Dimensionful (WithDim magneticFieldStrengthDimension NNReal)

/-- An oriented magnetic-field component, which may have either sign. -/
abbrev SignedMagneticFieldComponentQuantity : Type :=
  Dimensionful (WithDim magneticFieldStrengthDimension ℝ)

/-- A nonnegative charge-to-mass magnitude. -/
abbrev ChargeToMassMagnitudeQuantity : Type :=
  Dimensionful (WithDim chargeToMassDimension NNReal)

/-- SI readout of a length, in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- SI readout of a time interval, in seconds. -/
def timeInSeconds (time : TimeIntervalQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- SI readout of a signed velocity component, in metres per second. -/
def velocityInMetersPerSecond (velocity : VelocityComponentQuantity) : ℝ :=
  (velocity UnitChoices.SI).val

/-- SI readout of a signed acceleration, in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationComponentQuantity) : ℝ :=
  (acceleration UnitChoices.SI).val

/-- SI readout of an electric-field strength, in volts per metre. -/
def electricFieldStrengthInVoltsPerMeter
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- SI readout of a magnetic-field magnitude, in teslas. -/
def magneticFieldStrengthInTeslas
    (strength : MagneticFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- SI readout of an oriented magnetic-field component, in teslas. -/
def magneticFieldComponentInTeslas
    (component : SignedMagneticFieldComponentQuantity) : ℝ :=
  (component UnitChoices.SI).val

/-- Read an oriented magnetic-field component in microteslas. -/
def magneticFieldComponentInMicroteslas
    (component : SignedMagneticFieldComponentQuantity) : ℝ :=
  10 ^ (6 : ℕ) * magneticFieldComponentInTeslas component

/-- SI readout of a charge-to-mass magnitude, in coulombs per kilogram. -/
def chargeToMassInCoulombsPerKilogram
    (ratio : ChargeToMassMagnitudeQuantity) : ℝ :=
  ((ratio UnitChoices.SI).val : ℝ)

/-! ## Particle, apparatus, and figure vocabulary -/

/-- Particle-species roles distinguished in the experiment. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-- The two deflection plates drawn above and below the beam. -/
inductive PlateLabel where
  | upper
  | lower
  deriving DecidableEq, Fintype, Repr

/-- Whether the two deflection plates have the pictured parallel geometry. -/
inductive PlateArrangement where
  | parallel
  | nonparallel
  deriving DecidableEq, Repr

/-- The two labeled axes of the trajectory diagram. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Named positions along the trajectory in the supplied figure. -/
inductive TrajectoryStation where
  | plateEntry
  | plateExit
  | screen
  deriving DecidableEq, Fintype, Repr

/-- The direction of the beam arrow labeled `uₓ`. -/
inductive HorizontalBeamDirection where
  | right
  | left
  deriving DecidableEq, Repr

/-- The unit direction of the rightward beam in three-dimensional space. -/
def beamDirection : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single (0 : Fin 3) 1

/-- The unit direction drawn upward in the trajectory plane. -/
def upwardDirection : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single (1 : Fin 3) 1

/-!
The horizontal direction normal to the vertical trajectory plane.  This is
the relevant component direction for Earth's magnetic field.
-/
def earthHorizontalDirection : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single (2 : Fin 3) 1

/-!
Independent physical quantities and labeled geometric observables in
Thomson's experiment.  In particular, `earthHorizontalComponent` is an
unknown observable: its requested value is not stored elsewhere in the setup.
-/
structure ThomsonSecondExperiment where
  unitSystem : UnitChoices
  particleSpecies : ParticleSpecies
  plateArrangement : PlateArrangement
  plateIsShown : PlateLabel → Bool
  screenIsShown : Bool
  horizontalAxisLabel : FigureAxis
  verticalAxisLabel : FigureAxis
  beamDirectionLabel : HorizontalBeamDirection
  electricField : Electromagnetism.ElectricField 3
  selectorMagneticField : Electromagnetism.MagneticField 3
  earthMagneticField : Electromagnetism.MagneticField 3
  betweenPlates : Set (Time × Space 3)
  outsidePlateDrift : Set (Time × Space 3)
  electricFieldStrength : ElectricFieldStrengthQuantity
  selectorMagneticFieldStrength : MagneticFieldStrengthQuantity
  earthHorizontalComponent : SignedMagneticFieldComponentQuantity
  acceptedElectronChargeToMass : ChargeToMassMagnitudeQuantity
  thomsonNeglectChargeToMass : ChargeToMassMagnitudeQuantity
  plateLengthX1 : LengthQuantity
  exitHeightY1 : LengthQuantity
  driftLengthX2 : LengthQuantity
  screenHeightY2 : LengthQuantity
  plateTransitTime : TimeIntervalQuantity
  driftTransitTime : TimeIntervalQuantity
  entryVerticalVelocity : VelocityComponentQuantity
  horizontalVelocityUx : VelocityComponentQuantity
  exitVerticalVelocityUy : VelocityComponentQuantity
  screenVerticalVelocity : VelocityComponentQuantity
  electricVerticalAcceleration : AccelerationComponentQuantity
  earthVerticalAcceleration : AccelerationComponentQuantity
  trajectoryAngleTheta : ℝ
  stationOrder : TrajectoryStation → Nat

/-! ## Supplied data and governing-law assumptions -/

/-!
Problem data and qualitative information read directly from the primary
figure.  The displayed `y₂ / x₂ = 8 / 110` is represented by the conventional
centimetre readouts `y₂ = 8 cm` and `x₂ = 110 cm`, together with the quotient.
The image shows that `y₂` is measured from the original beam line, not from
the plate-exit point at height `y₁`.  This predicate contains no value for
Earth's field and no answer-choice assertion.
-/
structure MatchesProblemAndFigureReadouts
    (experiment : ThomsonSecondExperiment) : Prop where
  usesSIUnits : experiment.unitSystem = UnitChoices.SI
  beamParticlesAreElectrons : experiment.particleSpecies = .electron
  platesAreParallel : experiment.plateArrangement = .parallel
  upperPlateShown : experiment.plateIsShown .upper = true
  lowerPlateShown : experiment.plateIsShown .lower = true
  screenShown : experiment.screenIsShown = true
  xAxisIsHorizontal : experiment.horizontalAxisLabel = .horizontal
  yAxisIsVertical : experiment.verticalAxisLabel = .vertical
  beamTravelsRight : experiment.beamDirectionLabel = .right
  stationOrdering :
    experiment.stationOrder .plateEntry < experiment.stationOrder .plateExit ∧
      experiment.stationOrder .plateExit < experiment.stationOrder .screen
  appliedMagneticFieldReadout :
    magneticFieldStrengthInTeslas experiment.selectorMagneticFieldStrength =
      55 / 100000
  electricFieldReadout :
    electricFieldStrengthInVoltsPerMeter experiment.electricFieldStrength =
      15000
  plateLengthReadout : lengthInMeters experiment.plateLengthX1 = 5 / 100
  driftLengthReadout : lengthInMeters experiment.driftLengthX2 = 110 / 100
  screenHeightReadout : lengthInMeters experiment.screenHeightY2 = 8 / 100
  displayedScreenRatio :
    lengthInMeters experiment.screenHeightY2 /
        lengthInMeters experiment.driftLengthX2 =
      8 / 110
  initialVerticalVelocityIsZero :
    velocityInMetersPerSecond experiment.entryVerticalVelocity = 0

/-!
The modern accepted magnitude of the electron charge-to-mass ratio used to
interpret the historical discrepancy.  This is external calibration data,
not a statement about the requested terrestrial magnetic field.
-/
structure HasAcceptedElectronChargeToMassCalibration
    (experiment : ThomsonSecondExperiment) : Prop where
  acceptedRatioReadout :
    chargeToMassInCoulombsPerKilogram
        experiment.acceptedElectronChargeToMass =
      176000000000

/-- Positivity and nondegeneracy conditions for the physical experiment. -/
structure HasPhysicalParameters
    (experiment : ThomsonSecondExperiment) : Prop where
  electricStrengthPositive :
    0 < electricFieldStrengthInVoltsPerMeter experiment.electricFieldStrength
  selectorFieldStrengthPositive :
    0 < magneticFieldStrengthInTeslas
      experiment.selectorMagneticFieldStrength
  acceptedRatioPositive :
    0 < chargeToMassInCoulombsPerKilogram
      experiment.acceptedElectronChargeToMass
  plateLengthPositive : 0 < lengthInMeters experiment.plateLengthX1
  exitHeightPositive : 0 < lengthInMeters experiment.exitHeightY1
  driftLengthPositive : 0 < lengthInMeters experiment.driftLengthX2
  screenHeightPositive : 0 < lengthInMeters experiment.screenHeightY2
  horizontalVelocityPositive :
    0 < velocityInMetersPerSecond experiment.horizontalVelocityUx
  plateTransitTimePositive : 0 < timeInSeconds experiment.plateTransitTime
  driftTransitTimePositive : 0 < timeInSeconds experiment.driftTransitTime
  plateRegionNonempty : experiment.betweenPlates.Nonempty
  driftRegionNonempty : experiment.outsidePlateDrift.Nonempty
  regionsAreDisjoint :
    Disjoint experiment.betweenPlates experiment.outsidePlateDrift

/-- A spacetime-dependent vector field vanishes outside a specified region. -/
def FieldVanishesOutside
    (region : Set (Time × Space 3))
    (field : Time → Space 3 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∀ time position, (time, position) ∉ region → field time position = 0

/-!
The Physlib vector fields realize the stored scalar SI readouts.  Applied
selector fields are confined to the plates.  The terrestrial field is
modeled in the outside drift region with its independent signed coefficient
along the horizontal direction normal to the trajectory plane.  The applied
selector field points opposite that positive direction, so its magnetic force
on a right-moving electron opposes the upward electric force.
-/
structure FieldsRealizeScalarReadouts
    (experiment : ThomsonSecondExperiment) : Prop where
  electricFieldBetweenPlates :
    ∀ time position, (time, position) ∈ experiment.betweenPlates →
      experiment.electricField time position =
        (-electricFieldStrengthInVoltsPerMeter
          experiment.electricFieldStrength) • upwardDirection
  selectorMagneticFieldBetweenPlates :
    ∀ time position, (time, position) ∈ experiment.betweenPlates →
      experiment.selectorMagneticField time position =
        (-magneticFieldStrengthInTeslas
          experiment.selectorMagneticFieldStrength) • earthHorizontalDirection
  earthFieldInDriftRegion :
    ∀ time position, (time, position) ∈ experiment.outsidePlateDrift →
      experiment.earthMagneticField time position =
        magneticFieldComponentInTeslas experiment.earthHorizontalComponent •
          earthHorizontalDirection
  electricFieldConfined :
    FieldVanishesOutside experiment.betweenPlates experiment.electricField
  selectorMagneticFieldConfined :
    FieldVanishesOutside
      experiment.betweenPlates experiment.selectorMagneticField

/-!
Crossed-field velocity selection: equality of electric and magnetic Lorentz
force magnitudes gives `E = uₓ B`.  This law contains no terrestrial-field
value.
-/
structure SatisfiesCrossedFieldVelocitySelection
    (experiment : ThomsonSecondExperiment) : Prop where
  selectorForceBalance :
    electricFieldStrengthInVoltsPerMeter experiment.electricFieldStrength =
      velocityInMetersPerSecond experiment.horizontalVelocityUx *
        magneticFieldStrengthInTeslas
          experiment.selectorMagneticFieldStrength

/-!
Uniform horizontal motion and constant upward electric acceleration between
the plates.  The acceleration is the electric Lorentz-force magnitude divided
by mass, `a_E = (|e|/m) E`.
-/
structure SatisfiesElectricDeflectionBetweenPlates
    (experiment : ThomsonSecondExperiment) : Prop where
  horizontalMotion :
    lengthInMeters experiment.plateLengthX1 =
      velocityInMetersPerSecond experiment.horizontalVelocityUx *
        timeInSeconds experiment.plateTransitTime
  electricLorentzAcceleration :
    accelerationInMetersPerSecondSquared
        experiment.electricVerticalAcceleration =
      chargeToMassInCoulombsPerKilogram
          experiment.acceptedElectronChargeToMass *
        electricFieldStrengthInVoltsPerMeter experiment.electricFieldStrength
  exitVerticalVelocity :
    velocityInMetersPerSecond experiment.exitVerticalVelocityUy =
      velocityInMetersPerSecond experiment.entryVerticalVelocity +
        accelerationInMetersPerSecondSquared
            experiment.electricVerticalAcceleration *
          timeInSeconds experiment.plateTransitTime
  exitHeight :
    lengthInMeters experiment.exitHeightY1 =
      velocityInMetersPerSecond experiment.entryVerticalVelocity *
          timeInSeconds experiment.plateTransitTime +
        (1 / 2 : ℝ) *
          accelerationInMetersPerSecondSquared
            experiment.electricVerticalAcceleration *
          timeInSeconds experiment.plateTransitTime ^ 2

/-!
Outside the plates, Earth's horizontal component is the only additional
source of vertical acceleration.  Its signed Lorentz acceleration is
`a_B = (|e|/m) uₓ B_E`.  The figure's `y₂` is the total height above the
original beam line, so the drift law begins from the nonzero exit height
`y₁`; it is not a displacement measured from the plate exit.
-/
structure SatisfiesEarthFieldDriftKinematics
    (experiment : ThomsonSecondExperiment) : Prop where
  horizontalDrift :
    lengthInMeters experiment.driftLengthX2 =
      velocityInMetersPerSecond experiment.horizontalVelocityUx *
        timeInSeconds experiment.driftTransitTime
  earthLorentzAcceleration :
    accelerationInMetersPerSecondSquared experiment.earthVerticalAcceleration =
      chargeToMassInCoulombsPerKilogram
          experiment.acceptedElectronChargeToMass *
        velocityInMetersPerSecond experiment.horizontalVelocityUx *
        magneticFieldComponentInTeslas experiment.earthHorizontalComponent
  screenVerticalVelocity :
    velocityInMetersPerSecond experiment.screenVerticalVelocity =
      velocityInMetersPerSecond experiment.exitVerticalVelocityUy +
        accelerationInMetersPerSecondSquared
            experiment.earthVerticalAcceleration *
          timeInSeconds experiment.driftTransitTime
  totalScreenHeight :
    lengthInMeters experiment.screenHeightY2 =
      lengthInMeters experiment.exitHeightY1 +
        velocityInMetersPerSecond experiment.exitVerticalVelocityUy *
          timeInSeconds experiment.driftTransitTime +
        (1 / 2 : ℝ) *
          accelerationInMetersPerSecondSquared
            experiment.earthVerticalAcceleration *
          timeInSeconds experiment.driftTransitTime ^ 2
  screenAngle :
    Real.tan experiment.trajectoryAngleTheta =
      velocityInMetersPerSecond experiment.screenVerticalVelocity /
        velocityInMetersPerSecond experiment.horizontalVelocityUx

/-!
Thomson's neglect calculation sets the outside magnetic acceleration to zero.
Eliminating `y₁`, `uᵧ`, and the transit times from the electric-only model
gives
`(|e|/m)_T = y₂ uₓ² / (E x₁ (x₂ + x₁/2))`.
This historical calculation law gives neither a numerical discrepancy nor a
value for Earth's field.
-/
structure SatisfiesThomsonNeglectCalculation
    (experiment : ThomsonSecondExperiment) : Prop where
  reportedRatioFromTotalScreenDeflection :
    chargeToMassInCoulombsPerKilogram
        experiment.thomsonNeglectChargeToMass =
      lengthInMeters experiment.screenHeightY2 *
          velocityInMetersPerSecond experiment.horizontalVelocityUx ^ 2 /
        (electricFieldStrengthInVoltsPerMeter
            experiment.electricFieldStrength *
          lengthInMeters experiment.plateLengthX1 *
          (lengthInMeters experiment.driftLengthX2 +
            lengthInMeters experiment.plateLengthX1 / 2))

/-! ## Derived discrepancy, correction, and multiple-choice conclusion -/

/-- The four signed horizontal field components printed as answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Signed magnetic-field component, in microteslas, displayed by a choice. -/
def displayedComponentInMicroteslas : AnswerChoice → ℝ
  | .A => -18
  | .B => -43
  | .C => -22
  | .D => -31

/-- A choice is at least as close to the inferred component as every choice. -/
def IsClosestDisplayedChoice
    (experiment : ThomsonSecondExperiment) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice,
    |magneticFieldComponentInMicroteslas experiment.earthHorizontalComponent -
        displayedComponentInMicroteslas choice| ≤
      |magneticFieldComponentInMicroteslas experiment.earthHorizontalComponent -
        displayedComponentInMicroteslas otherChoice|

/-!
Eliminating the two transit times and accelerations gives the general
correction formula.  The mean vertical slope during the outside drift is
`(y₂ - y₁) / x₂`; the second term is the true plate-exit slope.
-/
lemma earthHorizontalComponent_exactFormula
    (experiment : ThomsonSecondExperiment)
    (hData : MatchesProblemAndFigureReadouts experiment)
    (hPhysical : HasPhysicalParameters experiment)
    (hSelector : SatisfiesCrossedFieldVelocitySelection experiment)
    (hElectric : SatisfiesElectricDeflectionBetweenPlates experiment)
    (hDrift : SatisfiesEarthFieldDriftKinematics experiment) :
    magneticFieldComponentInTeslas experiment.earthHorizontalComponent =
      (2 * velocityInMetersPerSecond experiment.horizontalVelocityUx /
          (chargeToMassInCoulombsPerKilogram
              experiment.acceptedElectronChargeToMass *
            lengthInMeters experiment.driftLengthX2)) *
        ((lengthInMeters experiment.screenHeightY2 -
              lengthInMeters experiment.exitHeightY1) /
            lengthInMeters experiment.driftLengthX2 -
          chargeToMassInCoulombsPerKilogram
              experiment.acceptedElectronChargeToMass *
            electricFieldStrengthInVoltsPerMeter
              experiment.electricFieldStrength *
            lengthInMeters experiment.plateLengthX1 /
            velocityInMetersPerSecond experiment.horizontalVelocityUx ^ 2) := by
  have hUxNe :
      velocityInMetersPerSecond experiment.horizontalVelocityUx ≠ 0 :=
    ne_of_gt hPhysical.horizontalVelocityPositive
  have hChargeNe :
      chargeToMassInCoulombsPerKilogram
          experiment.acceptedElectronChargeToMass ≠ 0 :=
    ne_of_gt hPhysical.acceptedRatioPositive
  have hX2Ne : lengthInMeters experiment.driftLengthX2 ≠ 0 :=
    ne_of_gt hPhysical.driftLengthPositive
  have hPlateTime :
      timeInSeconds experiment.plateTransitTime =
        lengthInMeters experiment.plateLengthX1 /
          velocityInMetersPerSecond experiment.horizontalVelocityUx := by
    apply (eq_div_iff hUxNe).2
    simpa [mul_comm] using hElectric.horizontalMotion.symm
  have hDriftTime :
      timeInSeconds experiment.driftTransitTime =
        lengthInMeters experiment.driftLengthX2 /
          velocityInMetersPerSecond experiment.horizontalVelocityUx := by
    apply (eq_div_iff hUxNe).2
    simpa [mul_comm] using hDrift.horizontalDrift.symm
  have hExitVelocity :
      velocityInMetersPerSecond experiment.exitVerticalVelocityUy =
        chargeToMassInCoulombsPerKilogram
            experiment.acceptedElectronChargeToMass *
          electricFieldStrengthInVoltsPerMeter
            experiment.electricFieldStrength *
          lengthInMeters experiment.plateLengthX1 /
          velocityInMetersPerSecond experiment.horizontalVelocityUx := by
    rw [hElectric.exitVerticalVelocity,
      hData.initialVerticalVelocityIsZero,
      hElectric.electricLorentzAcceleration, hPlateTime]
    ring
  have hScreenHeight := hDrift.totalScreenHeight
  rw [hExitVelocity, hDrift.earthLorentzAcceleration, hDriftTime] at hScreenHeight
  field_simp [hUxNe, hChargeNe, hX2Ne] at hScreenHeight ⊢
  ring_nf at hScreenHeight ⊢
  nlinarith [hScreenHeight]

/-!
The electric-only calculation gives Thomson's inferred value, which is below
the accepted calibration.  This makes the discrepancy named in the question
explicit without assuming the requested Earth-field correction.
-/
lemma thomsonNeglectChargeToMass_readout
    (experiment : ThomsonSecondExperiment)
    (hData : MatchesProblemAndFigureReadouts experiment)
    (hPhysical : HasPhysicalParameters experiment)
    (hSelector : SatisfiesCrossedFieldVelocitySelection experiment)
    (hNeglect : SatisfiesThomsonNeglectCalculation experiment) :
    chargeToMassInCoulombsPerKilogram
        experiment.thomsonNeglectChargeToMass =
      (25600000000000 / 363 : ℝ) := by
  have hUx :
      velocityInMetersPerSecond experiment.horizontalVelocityUx =
        300000000 / 11 := by
    have hBalance := hSelector.selectorForceBalance
    rw [hData.electricFieldReadout, hData.appliedMagneticFieldReadout] at hBalance
    norm_num at hBalance ⊢
    linarith
  rw [hNeglect.reportedRatioFromTotalScreenDeflection,
    hData.screenHeightReadout, hUx, hData.electricFieldReadout,
    hData.plateLengthReadout, hData.driftLengthReadout]
  norm_num

/-!
With the supplied readouts and accepted electron ratio, the inferred
terrestrial component is exactly `-897375 / 29282 μT`, approximately
`-30.646 μT`.  The numerical field value remains a conclusion, not a
calibration or law premise.
-/
lemma earthHorizontalComponent_microteslas
    (experiment : ThomsonSecondExperiment)
    (hData : MatchesProblemAndFigureReadouts experiment)
    (hCalibration : HasAcceptedElectronChargeToMassCalibration experiment)
    (hPhysical : HasPhysicalParameters experiment)
    (hSelector : SatisfiesCrossedFieldVelocitySelection experiment)
    (hElectric : SatisfiesElectricDeflectionBetweenPlates experiment)
    (hDrift : SatisfiesEarthFieldDriftKinematics experiment) :
    magneticFieldComponentInMicroteslas
        experiment.earthHorizontalComponent =
      -(897375 / 29282 : ℝ) := by
  have hUx :
      velocityInMetersPerSecond experiment.horizontalVelocityUx =
        300000000 / 11 := by
    have hBalance := hSelector.selectorForceBalance
    rw [hData.electricFieldReadout, hData.appliedMagneticFieldReadout] at hBalance
    norm_num at hBalance ⊢
    linarith
  have hPlateTime :
      timeInSeconds experiment.plateTransitTime =
        11 / 6000000000 := by
    have hMotion := hElectric.horizontalMotion
    rw [hData.plateLengthReadout, hUx] at hMotion
    norm_num at hMotion ⊢
    linarith
  have hElectricAcceleration :
      accelerationInMetersPerSecondSquared
          experiment.electricVerticalAcceleration =
        2640000000000000 := by
    have hAcceleration := hElectric.electricLorentzAcceleration
    rw [hCalibration.acceptedRatioReadout, hData.electricFieldReadout] at hAcceleration
    norm_num at hAcceleration ⊢
    linarith
  have hExitHeight :
      lengthInMeters experiment.exitHeightY1 = 1331 / 300000 := by
    have hHeight := hElectric.exitHeight
    rw [hData.initialVerticalVelocityIsZero, hPlateTime,
      hElectricAcceleration] at hHeight
    norm_num at hHeight ⊢
    linarith
  have hFormula := earthHorizontalComponent_exactFormula
    experiment hData hPhysical hSelector hElectric hDrift
  rw [hUx, hCalibration.acceptedRatioReadout,
    hData.driftLengthReadout, hData.screenHeightReadout, hExitHeight,
    hData.electricFieldReadout, hData.plateLengthReadout] at hFormula
  unfold magneticFieldComponentInMicroteslas
  rw [hFormula]
  norm_num

/-!
Thomson's electric-only value is smaller than the accepted `|e|/m`.  Under the
hypothesis that the missing outside-region effect is entirely the horizontal
Earth field governed above, its inferred value is about `-30.646 μT` and the
closest displayed component is `-31 μT`, answer D.

This declaration formalizes `thm:physics:phyx_mini_0561:target`.
-/
theorem problem_phyx_mini_0561
    (experiment : ThomsonSecondExperiment)
    (hData : MatchesProblemAndFigureReadouts experiment)
    (hCalibration : HasAcceptedElectronChargeToMassCalibration experiment)
    (hPhysical : HasPhysicalParameters experiment)
    (hFields : FieldsRealizeScalarReadouts experiment)
    (hSelector : SatisfiesCrossedFieldVelocitySelection experiment)
    (hElectric : SatisfiesElectricDeflectionBetweenPlates experiment)
    (hDrift : SatisfiesEarthFieldDriftKinematics experiment)
    (hNeglect : SatisfiesThomsonNeglectCalculation experiment) :
    chargeToMassInCoulombsPerKilogram
          experiment.thomsonNeglectChargeToMass =
        (25600000000000 / 363 : ℝ) ∧
      chargeToMassInCoulombsPerKilogram
          experiment.thomsonNeglectChargeToMass <
        chargeToMassInCoulombsPerKilogram
          experiment.acceptedElectronChargeToMass ∧
      magneticFieldComponentInMicroteslas
          experiment.earthHorizontalComponent =
        -(897375 / 29282 : ℝ) ∧
      IsClosestDisplayedChoice experiment .D := by
  have hNeglectValue :=
    thomsonNeglectChargeToMass_readout
      experiment hData hPhysical hSelector hNeglect
  have hEarthValue :=
    earthHorizontalComponent_microteslas
      experiment hData hCalibration hPhysical hSelector hElectric hDrift
  refine ⟨hNeglectValue, ?_, hEarthValue, ?_⟩
  · rw [hNeglectValue, hCalibration.acceptedRatioReadout]
    norm_num
  · intro otherChoice
    rw [hEarthValue]
    fin_cases otherChoice <;>
      norm_num [displayedComponentInMicroteslas]

end PhyXMiniProblems.ProblemPhyXMini0561
