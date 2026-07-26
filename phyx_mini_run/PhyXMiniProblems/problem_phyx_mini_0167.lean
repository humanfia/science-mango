import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0167

open Dimension

/-!
# Lower-end tension in a submerged diver's cable

A diver is attached to the lower end of a cable whose upper end is fixed to a
boat.  The cable coordinate `x` is measured upward from the diver, as in the
figure, so the requested lower-end tension is the tension at `x = 0`.

All dimensional objects below are Physlib `Dimensionful` quantities.  Real
numbers are used only for named unit readouts and for the scalar cable
coordinate measured in meters.  The equilibrium law concerns the vertical
force balance while the diver sends a transverse signal toward the boat.
-/

/-- A physical length, independent of the unit chosen to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- A physical volume, with dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical mass density, with dimension `M L⁻³`. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) ℝ)

/-- A physical linear mass density, with dimension `M L⁻¹`. -/
abbrev LinearMassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) ℝ)

/-- A physical acceleration, with dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A physical force, with dimension `M L T⁻²`. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- The numerical readout of a physical length in meters. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- The numerical readout of a physical length in centimeters. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := LengthUnit.centimeters}).val

/-- The numerical readout of a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  (mass UnitChoices.SI).val

/-- The numerical readout of a physical volume in cubic meters. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- The numerical readout of a physical mass density in kilograms per cubic meter. -/
def massDensityInKilogramsPerCubicMeter (density : MassDensityQuantity) : ℝ :=
  (density UnitChoices.SI).val

/-- The numerical readout of a linear mass density in kilograms per meter. -/
def linearMassDensityInKilogramsPerMeter
    (density : LinearMassDensityQuantity) : ℝ :=
  (density UnitChoices.SI).val

/-- The numerical readout of a physical acceleration in meters per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  (acceleration UnitChoices.SI).val

/-- The numerical readout of a physical force in newtons. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  (force UnitChoices.SI).val

/-- The physical object attached to one end of the cable. -/
inductive CableAttachment where
  | boat
  | diver
  deriving DecidableEq, Repr

/-- The displacement type of the signal traveling on the cable. -/
inductive CableWaveKind where
  | longitudinal
  | transverse
  deriving DecidableEq, Repr

/-- The propagation direction of the cable signal. -/
inductive CableWaveDirection where
  | towardBoat
  | towardDiver
  deriving DecidableEq, Repr

/-!
The full physical setup.  `cableTensionAtHeightInMeters x` is the cable
tension at the figure coordinate `x`, measured upward from the diver.  The
length, diameter, and linear density are retained even though the cable lying
above the attachment point does not contribute to the tension at `x = 0`.
-/
structure DiverCableSetup where
  cableLength : LengthQuantity
  cableDiameter : LengthQuantity
  cableLinearMassDensity : LinearMassDensityQuantity
  diverMass : MassQuantity
  diverDisplacedVolume : VolumeQuantity
  waterMassDensity : MassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity
  diverWeight : ForceQuantity
  diverBuoyantForce : ForceQuantity
  cableTensionAtHeightInMeters : ℝ → ForceQuantity
  figureCoordinateXInMeters : ℝ
  upperAttachment : CableAttachment
  lowerAttachment : CableAttachment
  waveKind : CableWaveKind
  waveDirection : CableWaveDirection
  diverFullySubmerged : Bool
  diverAtFixedDepth : Bool
  cableVerticalAtEquilibrium : Bool

/-- The requested cable tension, at the lower endpoint `x = 0`. -/
def lowerEndTension (setup : DiverCableSetup) : ForceQuantity :=
  setup.cableTensionAtHeightInMeters 0

/-!
Data read directly from the prose and figure: the cable is 100 m long and
2.00 cm wide with linear density 1.10 kg/m; the diver has mass 120 kg and
displaces 0.0800 m³; `x` lies along the cable above the diver; and the
transverse signal travels upward to the boat.  No tension value occurs here.
-/
def MatchesProblemAndFigureReadouts (setup : DiverCableSetup) : Prop :=
  lengthInMeters setup.cableLength = 100 ∧
    lengthInCentimeters setup.cableDiameter = 2.00 ∧
    linearMassDensityInKilogramsPerMeter setup.cableLinearMassDensity = 1.10 ∧
    massInKilograms setup.diverMass = 120 ∧
    volumeInCubicMeters setup.diverDisplacedVolume = 0.0800 ∧
    setup.figureCoordinateXInMeters ∈
      Set.Icc 0 (lengthInMeters setup.cableLength) ∧
    setup.upperAttachment = .boat ∧
    setup.lowerAttachment = .diver ∧
    setup.waveKind = .transverse ∧
    setup.waveDirection = .towardBoat

/-!
The equilibrium configuration relevant to the vertical force balance.  Fixed
depth does not rule out the transverse back-and-forth motion used to signal.
-/
def HasSubmergedVerticalEquilibriumConfiguration
    (setup : DiverCableSetup) : Prop :=
  setup.diverFullySubmerged = true ∧
    setup.diverAtFixedDepth = true ∧
    setup.cableVerticalAtEquilibrium = true

/-!
The textbook environmental calibration implicit in the recorded answer:
fresh-water density is 1000 kg/m³ and gravitational acceleration is 9.80 m/s².
-/
def UsesFreshWaterAndStandardGravity (setup : DiverCableSetup) : Prop :=
  massDensityInKilogramsPerCubicMeter setup.waterMassDensity = 1000 ∧
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration = 9.80

/-- The weight magnitude obeys `W = m g`. -/
def ObeysWeightLaw
    (mass : MassQuantity) (gravity : AccelerationQuantity)
    (weight : ForceQuantity) : Prop :=
  forceInNewtons weight =
    massInKilograms mass * accelerationInMetersPerSecondSquared gravity

/-!
Archimedes' principle for a fully submerged body: the buoyant-force magnitude
is the weight of the displaced fluid, `B = ρ V g`.
-/
def ObeysArchimedesPrinciple
    (fluidDensity : MassDensityQuantity) (displacedVolume : VolumeQuantity)
    (gravity : AccelerationQuantity) (buoyantForce : ForceQuantity) : Prop :=
  forceInNewtons buoyantForce =
    massDensityInKilogramsPerCubicMeter fluidDensity *
      volumeInCubicMeters displacedVolume *
      accelerationInMetersPerSecondSquared gravity

/-!
Vertical equilibrium at the diver: upward cable tension plus upward buoyancy
equals downward weight.
-/
def IsInVerticalStaticEquilibrium
    (tension buoyantForce weight : ForceQuantity) : Prop :=
  forceInNewtons tension + forceInNewtons buoyantForce =
    forceInNewtons weight

/-!
The governing weight, buoyancy, and lower-end force-balance laws.  These laws
contain no numerical value for the requested cable tension.
-/
structure SatisfiesDiverStaticLaws (setup : DiverCableSetup) : Prop where
  weightLaw : ObeysWeightLaw
    setup.diverMass setup.gravitationalAcceleration setup.diverWeight
  archimedesPrinciple : ObeysArchimedesPrinciple
    setup.waterMassDensity setup.diverDisplacedVolume
    setup.gravitationalAcceleration setup.diverBuoyantForce
  lowerEndForceBalance : IsInVerticalStaticEquilibrium
    (lowerEndTension setup) setup.diverBuoyantForce setup.diverWeight

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The force readout in newtons printed beside each answer choice. -/
def AnswerChoice.forceInNewtons : AnswerChoice → ℝ
  | .A => 392
  | .B => 452
  | .C => 332
  | .D => 372

/-- A modeled lower-end tension agrees with the displayed answer choice. -/
def MatchesAnswerChoice (setup : DiverCableSetup) (choice : AnswerChoice) : Prop :=
  forceInNewtons (lowerEndTension setup) = choice.forceInNewtons

/-!
The three governing laws reduce the requested force to the diver's apparent
weight `(m - ρV)g`; this is a derived relation, not an input assumption.
-/
lemma lower_end_tension_apparent_weight
    (setup : DiverCableSetup)
    (h_laws : SatisfiesDiverStaticLaws setup) :
    forceInNewtons (lowerEndTension setup) =
      (massInKilograms setup.diverMass -
        massDensityInKilogramsPerCubicMeter setup.waterMassDensity *
          volumeInCubicMeters setup.diverDisplacedVolume) *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration := by
  rcases h_laws with ⟨h_weight, h_buoyancy, h_balance⟩
  unfold ObeysWeightLaw at h_weight
  unfold ObeysArchimedesPrinciple at h_buoyancy
  unfold IsInVerticalStaticEquilibrium at h_balance
  calc
    forceInNewtons (lowerEndTension setup) =
        massInKilograms setup.diverMass *
            accelerationInMetersPerSecondSquared setup.gravitationalAcceleration -
          massDensityInKilogramsPerCubicMeter setup.waterMassDensity *
            volumeInCubicMeters setup.diverDisplacedVolume *
            accelerationInMetersPerSecondSquared setup.gravitationalAcceleration := by
      linarith
    _ = (massInKilograms setup.diverMass -
          massDensityInKilogramsPerCubicMeter setup.waterMassDensity *
            volumeInCubicMeters setup.diverDisplacedVolume) *
          accelerationInMetersPerSecondSquared setup.gravitationalAcceleration := by
      ring

/-- The source data and governing laws give a lower-end tension of 392 N. -/
lemma lower_end_tension_is_392_newtons
    (setup : DiverCableSetup)
    (h_data : MatchesProblemAndFigureReadouts setup)
    (h_environment : UsesFreshWaterAndStandardGravity setup)
    (h_configuration : HasSubmergedVerticalEquilibriumConfiguration setup)
    (h_laws : SatisfiesDiverStaticLaws setup) :
    forceInNewtons (lowerEndTension setup) = 392 := by
  rcases h_configuration with ⟨_, _, _⟩
  have h_tension := lower_end_tension_apparent_weight setup h_laws
  rcases h_data with
    ⟨_, _, _, h_mass, h_volume, _, _, _, _, _⟩
  rcases h_environment with ⟨h_density, h_gravity⟩
  rw [h_mass, h_density, h_volume, h_gravity] at h_tension
  norm_num at h_tension
  exact h_tension

/-!
The lower-end cable tension is 392 N, which is answer choice A.

This formalizes `thm:physics:phyx_mini_0167:target`.
-/
theorem problem_phyx_mini_0167
    (setup : DiverCableSetup)
    (h_data : MatchesProblemAndFigureReadouts setup)
    (h_environment : UsesFreshWaterAndStandardGravity setup)
    (h_configuration : HasSubmergedVerticalEquilibriumConfiguration setup)
    (h_laws : SatisfiesDiverStaticLaws setup) :
    forceInNewtons (lowerEndTension setup) = 392 ∧
      MatchesAnswerChoice setup .A := by
  have h_tension :=
    lower_end_tension_is_392_newtons
      setup h_data h_environment h_configuration h_laws
  constructor
  · exact h_tension
  · simpa [MatchesAnswerChoice, AnswerChoice.forceInNewtons] using h_tension

end PhyXMiniProblems.ProblemPhyXMini0167
