import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0773

open Dimension

/-!
# Falling mass coupled to a uniform rotating drum

A `15.0 kg` mass hangs from a thin, very light wire wrapped around the rim
of a uniform drum.  The axle has negligible friction and both bodies start
from rest.  An Earth calibration records `250.0 J` of drum kinetic energy
after a `5.00 m` fall.  The same apparatus is then used on Mars, where
`g = 3.71 m/s^2`.  The requested quantity is the mass speed when the drum
again has `250.0 J` of kinetic energy.

Physical magnitudes use Physlib's unit-independent `Dimensionful (WithDim
...)` representation.  Real numbers occur only in coherent unit readouts,
dimensionless equations between those readouts, and displayed answer data.

Assumption/target split:

* `MatchesProblemStatement` contains the supplied masses, distances,
  energies, planetary acceleration, initial-rest conditions, and qualitative
  apparatus idealizations;
* `MatchesPrimaryFigure` contains only labels and geometry visible in image
  `773.png`;
* `UsesStandardEarthGravity` supplies the ordinary textbook Earth value
  needed to interpret the Earth calibration numerically;
* `SatisfiesUniformDrumInertiaLaw` states `I = M R^2 / 2`;
* `SatisfiesLosslessDrumTrialLaws` states the translational and rotational
  kinetic-energy laws, no-slip rim kinematics, and mechanical-energy balance;
* there are no previous-part results; and
* the Mars speed and its rounding to `8.04 m/s` occur only in derived lemmas,
  the final theorem, and the displayed answer table.
-/

/-! ## Dimensionful quantities and coherent readouts -/

/-- Linear acceleration has physical dimension `L T^-2`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Angular speed has inverse-time dimension because radians are dimensionless. -/
def angularSpeedDimension : Dimension := T𝓭⁻¹

/-- Axial moment of inertia has physical dimension `M L^2`. -/
def momentOfInertiaDimension : Dimension := M𝓭 * L𝓭 * L𝓭

/-- A nonnegative physical mass, independent of a choice of units. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length or falling distance. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative linear-speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative gravitational-acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative angular-speed magnitude. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim angularSpeedDimension NNReal)

/-- A nonnegative scalar moment of inertia about the drum axle. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- Physical energy with dimension `M L^2 T^-2`. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a linear speed in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read a gravitational acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read an angular speed in radians per second. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed UnitChoices.SI).val : ℝ)

/-- Read an axial moment of inertia in kilogram metres squared. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Read a physical energy in joules, calibrated by Physlib's joule. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-! ## Apparatus and primary-figure vocabulary -/

/-- The two planetary environments mentioned in the problem. -/
inductive Location where
  | earth
  | mars
  deriving DecidableEq, Fintype, Repr

/-- The release state and the later state at which data are read. -/
inductive MotionStage where
  | release
  | observed
  deriving DecidableEq, Fintype, Repr

/-- The drum is explicitly described as uniform. -/
inductive DrumMassModel where
  | uniform
  | other
  deriving DecidableEq, Repr

/-- The wire is described as thin and very light. -/
inductive WireMassModel where
  | thinVeryLight
  | other
  deriving DecidableEq, Repr

/-- The axle friction model used by the exercise. -/
inductive AxleFrictionModel where
  | negligible
  | other
  deriving DecidableEq, Repr

/-- The wire remains wrapped on the rim and does not slide there. -/
inductive WireDrumContact where
  | wrappedNoSlip
  | other
  deriving DecidableEq, Repr

/-- Literal labels visible in the supplied bitmap. -/
inductive FigureLabel where
  | drumWord
  | massSymbolM
  deriving DecidableEq, Fintype, Repr

/-- Physical and graphical objects visible in the supplied bitmap. -/
inductive FigureObject where
  | circularDrum
  | hangingMass
  | verticalWire
  | axleCenterDot
  deriving DecidableEq, Fintype, Repr

/-- Qualitative layout transcribed from image `773.png`. -/
structure SuppliedDrumFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  massIsBelowDrum : Bool
  wireIsVerticalBelowRim : Bool
  wireTouchesDrumRim : Bool
  axleDotIsAtDrumCenter : Bool

/-!
The physical apparatus.  The drum mass and radius are not numerically given,
but they remain explicit quantities because they determine its inertia.  No
field is defined from the requested Mars speed.
-/
structure FallingMassDrumSystem where
  fallingMass : MassQuantity
  drumMass : MassQuantity
  drumRadius : LengthQuantity
  drumAxialMomentOfInertia : MomentOfInertiaQuantity
  drumMassModel : DrumMassModel
  wireMassModel : WireMassModel
  axleFrictionModel : AxleFrictionModel
  wireDrumContact : WireDrumContact
  figure : SuppliedDrumFigure

/-!
A release-to-observation trial in one gravitational environment.  Kinetic
energies are independent response fields constrained by the governing laws;
in particular, the observed speed is not assigned a displayed answer value.
-/
structure FallingMassDrumTrial where
  location : Location
  gravitationalAcceleration : AccelerationQuantity
  fallingDistance : LengthQuantity
  massSpeed : MotionStage → SpeedQuantity
  drumAngularSpeed : MotionStage → AngularSpeedQuantity
  massKineticEnergy : MotionStage → EnergyQuantity
  drumKineticEnergy : MotionStage → EnergyQuantity

/-! ## Supplied data and governing laws -/

/-- Every literal label and qualitative relation visible in the primary image. -/
structure MatchesPrimaryFigure (system : FallingMassDrumSystem) : Prop where
  allObjectsAreShown :
    ∀ object : FigureObject, system.figure.showsObject object = true
  bothLabelsAreShown :
    ∀ label : FigureLabel, system.figure.showsLabel label = true
  hangingMassBelowDrum : system.figure.massIsBelowDrum = true
  verticalWireBelowRim : system.figure.wireIsVerticalBelowRim = true
  wireMeetsRim : system.figure.wireTouchesDrumRim = true
  centralAxleDot : system.figure.axleDotIsAtDrumCenter = true

/-!
Problem-text data for the common apparatus and the two trials.  The Earth
gravitational value is kept separate because it is standard environmental
data rather than a number printed in the question.
-/
structure MatchesProblemStatement
    (system : FallingMassDrumSystem)
    (earthTrial marsTrial : FallingMassDrumTrial) : Prop where
  fallingMassIs15Kilograms :
    massInKilograms system.fallingMass = 15.0
  drumIsUniform : system.drumMassModel = .uniform
  wireIsThinAndVeryLight : system.wireMassModel = .thinVeryLight
  axleFrictionIsNegligible :
    system.axleFrictionModel = .negligible
  wireIsWrappedWithoutSlip :
    system.wireDrumContact = .wrappedNoSlip
  earthLocation : earthTrial.location = .earth
  earthFallDistanceIs5Meters :
    lengthInMeters earthTrial.fallingDistance = 5.00
  earthObservedDrumEnergyIs250Joules :
    energyInJoules
        (earthTrial.drumKineticEnergy .observed) = 250.0
  marsLocation : marsTrial.location = .mars
  marsGravityIs3Point71 :
    accelerationInMetersPerSecondSquared
        marsTrial.gravitationalAcceleration = 3.71
  marsObservedDrumEnergyIs250Joules :
    energyInJoules
        (marsTrial.drumKineticEnergy .observed) = 250.0
  earthMassStartsFromRest :
    speedInMetersPerSecond (earthTrial.massSpeed .release) = 0
  earthDrumStartsFromRest :
    angularSpeedInRadiansPerSecond
        (earthTrial.drumAngularSpeed .release) = 0
  marsMassStartsFromRest :
    speedInMetersPerSecond (marsTrial.massSpeed .release) = 0
  marsDrumStartsFromRest :
    angularSpeedInRadiansPerSecond
        (marsTrial.drumAngularSpeed .release) = 0

/-- Standard near-Earth acceleration used to evaluate the calibration. -/
structure UsesStandardEarthGravity
    (earthTrial : FallingMassDrumTrial) : Prop where
  earthGravityIs9Point8 :
    accelerationInMetersPerSecondSquared
        earthTrial.gravitationalAcceleration = 9.8

/-- Positivity and nondegeneracy of the physical apparatus and both trials. -/
structure HasPhysicalParameters
    (system : FallingMassDrumSystem)
    (earthTrial marsTrial : FallingMassDrumTrial) : Prop where
  fallingMassPositive : 0 < massInKilograms system.fallingMass
  drumMassPositive : 0 < massInKilograms system.drumMass
  drumRadiusPositive : 0 < lengthInMeters system.drumRadius
  drumInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared
      system.drumAxialMomentOfInertia
  earthGravityPositive :
    0 < accelerationInMetersPerSecondSquared
      earthTrial.gravitationalAcceleration
  marsGravityPositive :
    0 < accelerationInMetersPerSecondSquared
      marsTrial.gravitationalAcceleration
  earthFallDistancePositive :
    0 < lengthInMeters earthTrial.fallingDistance
  marsFallDistancePositive :
    0 < lengthInMeters marsTrial.fallingDistance

/-- Axial inertia of a uniform drum, modeled as a uniform solid cylinder. -/
structure SatisfiesUniformDrumInertiaLaw
    (system : FallingMassDrumSystem) : Prop where
  uniformDrumAxialInertia :
    momentOfInertiaInKilogramMetersSquared
        system.drumAxialMomentOfInertia =
      (1 / 2 : ℝ) * massInKilograms system.drumMass *
        lengthInMeters system.drumRadius ^ 2

/-!
Lossless one-axis mechanics for a trial:

* `K_mass = m v^2 / 2`;
* `K_drum = I omega^2 / 2`;
* the unwinding wire imposes `v = R omega` at each stage; and
* the gravitational-potential loss plus initial kinetic energy equals final
  kinetic energy.

These laws constrain arbitrary response fields and contain no numerical Mars
speed or answer choice.
-/
structure SatisfiesLosslessDrumTrialLaws
    (system : FallingMassDrumSystem)
    (trial : FallingMassDrumTrial) : Prop where
  massTranslationalKineticEnergy :
    ∀ stage : MotionStage,
      energyInJoules (trial.massKineticEnergy stage) =
        (1 / 2 : ℝ) * massInKilograms system.fallingMass *
          speedInMetersPerSecond (trial.massSpeed stage) ^ 2
  drumRotationalKineticEnergy :
    ∀ stage : MotionStage,
      energyInJoules (trial.drumKineticEnergy stage) =
        (1 / 2 : ℝ) *
          momentOfInertiaInKilogramMetersSquared
            system.drumAxialMomentOfInertia *
          angularSpeedInRadiansPerSecond
            (trial.drumAngularSpeed stage) ^ 2
  noSlipRimKinematics :
    ∀ stage : MotionStage,
      speedInMetersPerSecond (trial.massSpeed stage) =
        lengthInMeters system.drumRadius *
          angularSpeedInRadiansPerSecond
            (trial.drumAngularSpeed stage)
  mechanicalEnergyConservation :
    massInKilograms system.fallingMass *
          accelerationInMetersPerSecondSquared
            trial.gravitationalAcceleration *
          lengthInMeters trial.fallingDistance +
        energyInJoules (trial.massKineticEnergy .release) +
        energyInJoules (trial.drumKineticEnergy .release) =
      energyInJoules (trial.massKineticEnergy .observed) +
        energyInJoules (trial.drumKineticEnergy .observed)

/-! ## Derived calibration and Mars-speed statements -/

/-- The Earth energy balance leaves `485 J` in the falling mass. -/
lemma earthObservedMassKineticEnergy_eq_485
    (system : FallingMassDrumSystem)
    (earthTrial marsTrial : FallingMassDrumTrial)
    (_data : MatchesProblemStatement system earthTrial marsTrial)
    (_earthGravity : UsesStandardEarthGravity earthTrial)
    (_laws : SatisfiesLosslessDrumTrialLaws system earthTrial) :
    energyInJoules (earthTrial.massKineticEnergy .observed) = 485 := by
  have hMassRelease :=
    _laws.massTranslationalKineticEnergy MotionStage.release
  have hDrumRelease :=
    _laws.drumRotationalKineticEnergy MotionStage.release
  have hEnergy := _laws.mechanicalEnergyConservation
  rw [_data.fallingMassIs15Kilograms,
    _data.earthMassStartsFromRest] at hMassRelease
  norm_num at hMassRelease
  rw [_data.earthDrumStartsFromRest] at hDrumRelease
  norm_num at hDrumRelease
  rw [_data.fallingMassIs15Kilograms,
    _earthGravity.earthGravityIs9Point8,
    _data.earthFallDistanceIs5Meters,
    hMassRelease, hDrumRelease,
    _data.earthObservedDrumEnergyIs250Joules] at hEnergy
  norm_num at hEnergy ⊢
  linarith

/-- The Earth calibration fixes the observed mass speed squared. -/
lemma earthObservedMassSpeed_squared_eq_194_over_3
    (system : FallingMassDrumSystem)
    (earthTrial marsTrial : FallingMassDrumTrial)
    (_data : MatchesProblemStatement system earthTrial marsTrial)
    (_earthGravity : UsesStandardEarthGravity earthTrial)
    (_laws : SatisfiesLosslessDrumTrialLaws system earthTrial) :
    speedInMetersPerSecond (earthTrial.massSpeed .observed) ^ 2 =
      194 / 3 := by
  have hMassEnergy :=
    earthObservedMassKineticEnergy_eq_485
      system earthTrial marsTrial _data _earthGravity _laws
  have hKinetic :=
    _laws.massTranslationalKineticEnergy MotionStage.observed
  rw [_data.fallingMassIs15Kilograms, hMassEnergy] at hKinetic
  norm_num at hKinetic ⊢
  linarith

/-!
For the same drum and rim radius, equal drum rotational energies together
with no slip give equal squared speeds of the attached mass.  This is the
reason the Mars gravitational acceleration affects the necessary fall
distance, but not the speed at the specified drum energy.
-/
lemma equalDrumEnergy_gives_equalMassSpeedSquared
    (system : FallingMassDrumSystem)
    (firstTrial secondTrial : FallingMassDrumTrial)
    (_physical :
      HasPhysicalParameters system firstTrial secondTrial)
    (_firstLaws :
      SatisfiesLosslessDrumTrialLaws system firstTrial)
    (_secondLaws :
      SatisfiesLosslessDrumTrialLaws system secondTrial)
    (_equalDrumEnergy :
      energyInJoules (firstTrial.drumKineticEnergy .observed) =
        energyInJoules (secondTrial.drumKineticEnergy .observed)) :
    speedInMetersPerSecond (firstTrial.massSpeed .observed) ^ 2 =
      speedInMetersPerSecond (secondTrial.massSpeed .observed) ^ 2 := by
  have hInertia :
      momentOfInertiaInKilogramMetersSquared
          system.drumAxialMomentOfInertia ≠ 0 :=
    ne_of_gt _physical.drumInertiaPositive
  have hAngularSpeedSquared :
      angularSpeedInRadiansPerSecond
            (firstTrial.drumAngularSpeed .observed) ^ 2 =
        angularSpeedInRadiansPerSecond
            (secondTrial.drumAngularSpeed .observed) ^ 2 := by
    have hCoefficient :
        (1 / 2 : ℝ) *
            momentOfInertiaInKilogramMetersSquared
              system.drumAxialMomentOfInertia ≠ 0 :=
      mul_ne_zero (by norm_num) hInertia
    apply mul_left_cancel₀ hCoefficient
    calc
      ((1 / 2 : ℝ) *
            momentOfInertiaInKilogramMetersSquared
              system.drumAxialMomentOfInertia) *
          angularSpeedInRadiansPerSecond
              (firstTrial.drumAngularSpeed .observed) ^ 2 =
          energyInJoules
            (firstTrial.drumKineticEnergy .observed) := by
              symm
              exact
                _firstLaws.drumRotationalKineticEnergy
                  MotionStage.observed
      _ = energyInJoules
            (secondTrial.drumKineticEnergy .observed) :=
        _equalDrumEnergy
      _ = ((1 / 2 : ℝ) *
            momentOfInertiaInKilogramMetersSquared
              system.drumAxialMomentOfInertia) *
          angularSpeedInRadiansPerSecond
              (secondTrial.drumAngularSpeed .observed) ^ 2 :=
        _secondLaws.drumRotationalKineticEnergy
          MotionStage.observed
  rw [_firstLaws.noSlipRimKinematics MotionStage.observed,
    _secondLaws.noSlipRimKinematics MotionStage.observed]
  calc
    (lengthInMeters system.drumRadius *
          angularSpeedInRadiansPerSecond
            (firstTrial.drumAngularSpeed .observed)) ^ 2 =
        lengthInMeters system.drumRadius ^ 2 *
          angularSpeedInRadiansPerSecond
            (firstTrial.drumAngularSpeed .observed) ^ 2 := by ring
    _ = lengthInMeters system.drumRadius ^ 2 *
          angularSpeedInRadiansPerSecond
            (secondTrial.drumAngularSpeed .observed) ^ 2 := by
      rw [hAngularSpeedSquared]
    _ = (lengthInMeters system.drumRadius *
          angularSpeedInRadiansPerSecond
            (secondTrial.drumAngularSpeed .observed)) ^ 2 := by ring

/-- Exact positive-root form of the requested Mars mass speed. -/
lemma marsObservedMassSpeed_eq_sqrt_194_over_3
    (system : FallingMassDrumSystem)
    (earthTrial marsTrial : FallingMassDrumTrial)
    (_data : MatchesProblemStatement system earthTrial marsTrial)
    (_earthGravity : UsesStandardEarthGravity earthTrial)
    (_physical : HasPhysicalParameters system earthTrial marsTrial)
    (_uniformDrum : SatisfiesUniformDrumInertiaLaw system)
    (_earthLaws :
      SatisfiesLosslessDrumTrialLaws system earthTrial)
    (_marsLaws :
      SatisfiesLosslessDrumTrialLaws system marsTrial) :
    speedInMetersPerSecond (marsTrial.massSpeed .observed) =
      Real.sqrt (194 / 3) := by
  have hEarthSpeedSquared :=
    earthObservedMassSpeed_squared_eq_194_over_3
      system earthTrial marsTrial _data _earthGravity _earthLaws
  have hEqualDrumEnergy :
      energyInJoules (earthTrial.drumKineticEnergy .observed) =
        energyInJoules (marsTrial.drumKineticEnergy .observed) := by
    rw [_data.earthObservedDrumEnergyIs250Joules,
      _data.marsObservedDrumEnergyIs250Joules]
  have hEqualSpeedSquared :=
    equalDrumEnergy_gives_equalMassSpeedSquared
      system earthTrial marsTrial _physical _earthLaws _marsLaws
        hEqualDrumEnergy
  have hMarsSpeedSquared :
      speedInMetersPerSecond (marsTrial.massSpeed .observed) ^ 2 =
        194 / 3 := by
    calc
      speedInMetersPerSecond (marsTrial.massSpeed .observed) ^ 2 =
          speedInMetersPerSecond
            (earthTrial.massSpeed .observed) ^ 2 :=
        hEqualSpeedSquared.symm
      _ = 194 / 3 := hEarthSpeedSquared
  have hMarsSpeedNonnegative :
      0 ≤ speedInMetersPerSecond
        (marsTrial.massSpeed .observed) := by
    unfold speedInMetersPerSecond
    positivity
  have hRadicandNonnegative : (0 : ℝ) ≤ 194 / 3 := by norm_num
  have hSquareRootSquared :
      Real.sqrt (194 / 3) ^ 2 = (194 / 3 : ℝ) :=
    Real.sq_sqrt hRadicandNonnegative
  have hSquareRootNonnegative :
      0 ≤ Real.sqrt (194 / 3) :=
    Real.sqrt_nonneg _
  nlinarith

/-! ## Displayed choices and final target -/

/-- Labels of the four mass-speed choices in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metres-per-second value printed beside each answer label. -/
def AnswerChoice.metersPerSecond : AnswerChoice → ℝ
  | .A => 7.61
  | .B => 8.04
  | .C => 12.34
  | .D => 16.12

/-- Dataset metadata recording the supplied answer label. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
`actual` rounds to `displayed` to the nearest hundredth.  The half-open
interval makes the tie convention explicit and avoids asserting that a
rounded decimal is an exact solution of the mechanics equations.
-/
def RoundsToNearestHundredth (actual displayed : ℝ) : Prop :=
  displayed - 1 / 200 ≤ actual ∧ actual < displayed + 1 / 200

/-- The Mars speed readout selects a displayed answer choice. -/
def MarsMassSpeedMatchesChoice
    (marsTrial : FallingMassDrumTrial) (choice : AnswerChoice) : Prop :=
  RoundsToNearestHundredth
    (speedInMetersPerSecond (marsTrial.massSpeed .observed))
    choice.metersPerSecond

/-!
When the drum has gained `250.0 J` on Mars, the `15.0 kg` mass moves at a
speed that rounds to `8.04 m/s`, answer B.

Blueprint environment: `thm:physics:phyx_mini_0773:target`.
-/
theorem marsMassSpeedWhenDrumHas250J_matches_recordedAnswerB
    (system : FallingMassDrumSystem)
    (earthTrial marsTrial : FallingMassDrumTrial)
    (_figure : MatchesPrimaryFigure system)
    (_data : MatchesProblemStatement system earthTrial marsTrial)
    (_earthGravity : UsesStandardEarthGravity earthTrial)
    (_physical : HasPhysicalParameters system earthTrial marsTrial)
    (_uniformDrum : SatisfiesUniformDrumInertiaLaw system)
    (_earthLaws :
      SatisfiesLosslessDrumTrialLaws system earthTrial)
    (_marsLaws :
      SatisfiesLosslessDrumTrialLaws system marsTrial) :
    MarsMassSpeedMatchesChoice marsTrial recordedAnswerChoice := by
  have hMarsSpeed :=
    marsObservedMassSpeed_eq_sqrt_194_over_3
      system earthTrial marsTrial _data _earthGravity _physical
        _uniformDrum _earthLaws _marsLaws
  simp only [MarsMassSpeedMatchesChoice, RoundsToNearestHundredth,
    recordedAnswerChoice, AnswerChoice.metersPerSecond]
  rw [hMarsSpeed]
  have hRadicandNonnegative : (0 : ℝ) ≤ 194 / 3 := by norm_num
  have hSquareRootSquared :
      Real.sqrt (194 / 3) ^ 2 = (194 / 3 : ℝ) :=
    Real.sq_sqrt hRadicandNonnegative
  have hSquareRootNonnegative :
      0 ≤ Real.sqrt (194 / 3) :=
    Real.sqrt_nonneg _
  constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0773
