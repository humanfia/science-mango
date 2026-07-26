import Mathlib
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0514

open Dimension

/-!
# Radius and mass of an edge-on spectroscopic binary

Two identical stars orbit their common center of mass on the same circular
path.  The orbit is viewed edge-on from Earth, so the amplitude of each star's
line-of-sight speed is its orbital speed.  The observed light-frequency cycle
has period `11.0 d`.  The supplied bitmap shows the stars at antipodal upper
and lower positions, labels both masses by `m`, labels the orbital radius by
`R`, and draws opposite tangential velocity arrows.

The prose asks for the radius and mass of each star, but the dataset's answer
choices instead give speeds and record `3.94 × 10^4 m/s` as choice D.  The
source report has no previous part and supplies no numerical frequency extrema,
so the recorded choice is retained only as metadata: it is not identified with
either star's speed.  The strongest supported conclusions are therefore the
symbolic speed, radius, mass, and comparison-ratio relations.

Dimensionful lengths, times, masses, speeds, frequencies, forces, and the
gravitational constant use Physlib quantities.  Real numbers occur only as
named SI readouts, dimensionless ratios, and numerical data.

Assumption/target split:

* governing laws: longitudinal light Doppler shift, edge-on projection,
  uniform circular kinematics, Newtonian gravitation, and centripetal force;
* previous-part result: none (the source report has `previous_parts = []`);
* data and figure readouts: identical stars, the `11.0 d` cycle, primary-image
  labels and directions, the solar mass, and Earth--Sun distance;
* target conclusions: the speed as a symbolic function of the observed
  frequency extrema, `R = vT/(2π)`, `m = 4Rv²/G`, and symbolic ratios to the
  Earth--Sun distance and solar mass.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- A nonnegative physical length, independent of a choice of unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical time interval. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical frequency, with dimension inverse time. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative force, whose coherent SI unit is the newton. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/--
The Newtonian gravitational constant, of physical dimension
`length³ * mass⁻¹ * time⁻²`.
-/
abbrev GravitationalConstantQuantity : Type :=
  Dimensionful
    (WithDim
      (L𝓭 * L𝓭 * L𝓭 * M𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹)
      NNReal)

/-- Read a physical length in SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical time interval in SI seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Read a physical mass in SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a nonnegative physical speed in SI metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read a physical frequency in SI hertz. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Read a physical force in SI newtons. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Read the gravitational constant in `m³ kg⁻¹ s⁻²`. -/
def gravitationalConstantInSI
    (constant : GravitationalConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-- Physlib's exact vacuum speed of light, read in metres per second. -/
def speedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-! ## Stars, orbit, and primary-image vocabulary -/

/-- The two otherwise identical stars of the binary system. -/
inductive BinaryStar where
  | star₁
  | star₂
  deriving DecidableEq, Fintype, Repr

/-- The companion of a selected star. -/
def otherStar : BinaryStar → BinaryStar
  | .star₁ => .star₂
  | .star₂ => .star₁

/-- Shape of the stellar trajectories about the common center. -/
inductive OrbitShape where
  | circular
  | noncircular
  deriving DecidableEq, Repr

/-- Orientation of the orbital plane relative to the terrestrial observer. -/
inductive ViewingOrientation where
  | edgeOn
  | faceOn
  | inclined
  deriving DecidableEq, Repr

/-- Location of a star in the particular snapshot shown by the bitmap. -/
inductive FigurePosition where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- Horizontal direction used by the Earth arrow and tangential arrows. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-!
Qualitative information transcribed from the primary bitmap.  The radius
segment is a geometrical radius of the blue orbital circle; it is not a local
definition of the requested numerical radius.
-/
structure BinaryStarFigure where
  position : BinaryStar → FigurePosition
  tangentialArrow : BinaryStar → HorizontalDirection
  massLabelShown : BinaryStar → Bool
  orbitCircleShown : Bool
  centerPointShown : Bool
  radiusSegmentFromCenterToOrbitShown : Bool
  radiusLabelShown : Bool
  earthDirectionArrow : HorizontalDirection
  toTheEarthLabelShown : Bool
  starsShownAntipodal : Bool

/-! ## Independent physical setup -/

/-!
Physical quantities belonging to the binary system and its observation.
None of the radius or mass fields is defined from a requested numerical
answer; their relations are supplied only by premise interfaces below.
-/
structure SpectroscopicBinarySetup where
  starMass : BinaryStar → MassQuantity
  orbitRadius : BinaryStar → LengthQuantity
  orbitalSpeed : BinaryStar → DimSpeed
  lineOfSightSpeedAmplitude : BinaryStar → DimSpeed
  emittedRestFrequency : BinaryStar → FrequencyQuantity
  maximumObservedFrequency : BinaryStar → FrequencyQuantity
  minimumObservedFrequency : BinaryStar → FrequencyQuantity
  frequencyVariationPeriod : BinaryStar → TimeQuantity
  orbitalPeriod : TimeQuantity
  starSeparation : LengthQuantity
  gravitationalForceOn : BinaryStar → ForceQuantity
  gravitationalConstant : GravitationalConstantQuantity
  solarMass : MassQuantity
  earthSunDistance : LengthQuantity
  orbitShape : OrbitShape
  viewingOrientation : ViewingOrientation
  figure : BinaryStarFigure

/-! ## Data, figure evidence, and previous-part result -/

/-- The equal-star, circular, edge-on physical scenario stated in the prose. -/
structure MatchesSpectroscopicBinaryScenario
    (setup : SpectroscopicBinarySetup) : Prop where
  equalMasses : setup.starMass .star₁ = setup.starMass .star₂
  equalOrbitRadii : setup.orbitRadius .star₁ = setup.orbitRadius .star₂
  equalOrbitalSpeeds : setup.orbitalSpeed .star₁ = setup.orbitalSpeed .star₂
  circularOrbits : setup.orbitShape = .circular
  orbitalPlaneViewedEdgeOn : setup.viewingOrientation = .edgeOn
  commonCenterOfMassOrbit :
    ∀ star,
      lengthInMeters (setup.orbitRadius star) =
        lengthInMeters (setup.orbitRadius (otherStar star))

/-!
The measured frequency pattern and the comparison constants printed in the
question.  A maximum-to-minimum-to-maximum cycle is one complete orbit in the
edge-on circular model.  No numerical radius or stellar mass is recorded.
-/
structure MatchesProblemReadouts (setup : SpectroscopicBinarySetup) : Prop where
  frequencyCycleIsElevenDays :
    ∀ star,
      timeInSeconds (setup.frequencyVariationPeriod star) =
        11 * 24 * 60 * 60
  frequencyCycleIsOrbitalPeriod :
    ∀ star,
      setup.frequencyVariationPeriod star = setup.orbitalPeriod
  minimumObservedBelowMaximum :
    ∀ star,
      frequencyInHertz (setup.minimumObservedFrequency star) <
        frequencyInHertz (setup.maximumObservedFrequency star)
  solarMassKilograms : massInKilograms setup.solarMass = 199 * 10 ^ 28
  earthSunDistanceMeters :
    lengthInMeters setup.earthSunDistance = 150 * 10 ^ 9

/-! Primary-image evidence, kept separate from dynamical laws. -/
structure MatchesPrimaryBinaryStarFigure
    (setup : SpectroscopicBinarySetup) : Prop where
  star₁ShownUpper : setup.figure.position .star₁ = .upper
  star₂ShownLower : setup.figure.position .star₂ = .lower
  upperArrowPointsLeft : setup.figure.tangentialArrow .star₁ = .left
  lowerArrowPointsRight : setup.figure.tangentialArrow .star₂ = .right
  bothMassLabelsShown :
    ∀ star, setup.figure.massLabelShown star = true
  blueCircularPathShown : setup.figure.orbitCircleShown = true
  blackCenterPointShown : setup.figure.centerPointShown = true
  radiusSegmentShown :
    setup.figure.radiusSegmentFromCenterToOrbitShown = true
  radiusRLabelShown : setup.figure.radiusLabelShown = true
  earthArrowPointsLeft : setup.figure.earthDirectionArrow = .left
  toTheEarthTextShown : setup.figure.toTheEarthLabelShown = true
  oppositePositionsShown : setup.figure.starsShownAntipodal = true

/-- Labels of the four speed choices supplied by the inconsistent source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metres-per-second readout printed beside each answer label. -/
def answerSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 456 * 10 ^ 2
  | .B => 417 * 10 ^ 2
  | .C => 362 * 10 ^ 2
  | .D => 394 * 10 ^ 2

/-!
The dataset records choice D, but its speed-valued choices do not answer the
radius-and-mass question.  Keeping this definition private makes the record
available as source metadata without turning it into physical evidence.
-/
private def recordedAnswerChoice : AnswerChoice := .D

/-! ## Governing physics -/

/-- Positivity and subluminality conditions for the physical model. -/
structure HasPhysicalBinaryParameters
    (setup : SpectroscopicBinarySetup) : Prop where
  massesPositive :
    ∀ star, 0 < massInKilograms (setup.starMass star)
  radiiPositive :
    ∀ star, 0 < lengthInMeters (setup.orbitRadius star)
  orbitalSpeedsPositive :
    ∀ star, 0 < speedInMetersPerSecond (setup.orbitalSpeed star)
  orbitalSpeedsSubluminal :
    ∀ star,
      speedInMetersPerSecond (setup.orbitalSpeed star) <
        speedOfLightInMetersPerSecond
  periodPositive : 0 < timeInSeconds setup.orbitalPeriod
  separationPositive : 0 < lengthInMeters setup.starSeparation
  gravitationalConstantPositive :
    0 < gravitationalConstantInSI setup.gravitationalConstant
  comparisonScalesPositive :
    0 < massInKilograms setup.solarMass ∧
      0 < lengthInMeters setup.earthSunDistance
  emittedFrequenciesPositive :
    ∀ star, 0 < frequencyInHertz (setup.emittedRestFrequency star)

/-!
Longitudinal relativistic Doppler shift for approaching and receding extrema.
For an edge-on circular orbit, the line-of-sight speed amplitude equals the
orbital speed.  These laws contain no radius or stellar-mass answer.
-/
structure SatisfiesSpectroscopicDopplerLaws
    (setup : SpectroscopicBinarySetup) : Prop where
  edgeOnRadialAmplitude :
    ∀ star,
      speedInMetersPerSecond (setup.lineOfSightSpeedAmplitude star) =
        speedInMetersPerSecond (setup.orbitalSpeed star)
  approachingFrequency :
    ∀ star,
      frequencyInHertz (setup.maximumObservedFrequency star) =
        frequencyInHertz (setup.emittedRestFrequency star) *
          Real.sqrt
            ((speedOfLightInMetersPerSecond +
                speedInMetersPerSecond
                  (setup.lineOfSightSpeedAmplitude star)) /
              (speedOfLightInMetersPerSecond -
                speedInMetersPerSecond
                  (setup.lineOfSightSpeedAmplitude star)))
  recedingFrequency :
    ∀ star,
      frequencyInHertz (setup.minimumObservedFrequency star) =
        frequencyInHertz (setup.emittedRestFrequency star) *
          Real.sqrt
            ((speedOfLightInMetersPerSecond -
                speedInMetersPerSecond
                  (setup.lineOfSightSpeedAmplitude star)) /
              (speedOfLightInMetersPerSecond +
                speedInMetersPerSecond
                  (setup.lineOfSightSpeedAmplitude star)))

/-!
Uniform circular kinematics: in one orbital period, each star travels one
circumference of its own radius about the common center of mass.
-/
structure SatisfiesUniformCircularKinematics
    (setup : SpectroscopicBinarySetup) : Prop where
  oneCircumferencePerPeriod :
    ∀ star,
      speedInMetersPerSecond (setup.orbitalSpeed star) *
          timeInSeconds setup.orbitalPeriod =
        2 * Real.pi * lengthInMeters (setup.orbitRadius star)

/-!
Newtonian two-body dynamics in the center-of-mass frame.  Antipodal geometry
makes the center-to-center separation the sum of the two orbital radii;
inverse-square gravity supplies the mutual force, and that same force is the
centripetal force for each circular trajectory.  These are unsolved laws, not
the requested formulas for `R` or `m`.
-/
structure SatisfiesNewtonianBinaryDynamics
    (setup : SpectroscopicBinarySetup) : Prop where
  antipodalCenterSeparation :
    ∀ star,
      lengthInMeters setup.starSeparation =
        lengthInMeters (setup.orbitRadius star) +
          lengthInMeters (setup.orbitRadius (otherStar star))
  inverseSquareGravitationalForce :
    ∀ star,
      forceInNewtons (setup.gravitationalForceOn star) =
        gravitationalConstantInSI setup.gravitationalConstant *
          massInKilograms (setup.starMass star) *
          massInKilograms (setup.starMass (otherStar star)) /
          lengthInMeters setup.starSeparation ^ 2
  circularCentripetalForce :
    ∀ star,
      forceInNewtons (setup.gravitationalForceOn star) =
        massInKilograms (setup.starMass star) *
          speedInMetersPerSecond (setup.orbitalSpeed star) ^ 2 /
          lengthInMeters (setup.orbitRadius star)

/-! ## Derived relations and strongest source-supported comparison -/

/-- Circular kinematics determines each orbital radius from speed and period. -/
lemma orbitRadius_eq_speed_mul_period_div_two_pi
    (setup : SpectroscopicBinarySetup)
    (_physical : HasPhysicalBinaryParameters setup)
    (_kinematics : SatisfiesUniformCircularKinematics setup) :
    ∀ star,
      lengthInMeters (setup.orbitRadius star) =
        speedInMetersPerSecond (setup.orbitalSpeed star) *
          timeInSeconds setup.orbitalPeriod / (2 * Real.pi) := by
  sorry

/-!
Equal masses and radii reduce Newtonian gravity plus centripetal motion to
`m = 4 R v² / G` for either star.
-/
lemma starMass_eq_four_radius_speed_sq_div_gravitationalConstant
    (setup : SpectroscopicBinarySetup)
    (_scenario : MatchesSpectroscopicBinaryScenario setup)
    (_physical : HasPhysicalBinaryParameters setup)
    (_dynamics : SatisfiesNewtonianBinaryDynamics setup) :
    ∀ star,
      massInKilograms (setup.starMass star) =
        4 * lengthInMeters (setup.orbitRadius star) *
          speedInMetersPerSecond (setup.orbitalSpeed star) ^ 2 /
          gravitationalConstantInSI setup.gravitationalConstant := by
  sorry

/-!
The source does not give numerical frequency extrema, so it does not determine
a numerical orbital speed and hence cannot determine numerical values of `R`
or `m`.  The relativistic Doppler laws nevertheless determine the speed
symbolically from the extrema.  Circular kinematics and Newtonian dynamics
then determine the requested radius and mass symbolically, including exact
comparison ratios to the supplied Earth--Sun distance and solar mass.

Blueprint: `thm:physics:phyx_mini_0514:target`.
-/
theorem spectroscopicBinary_orbitalRadius_and_stellarMass
    (setup : SpectroscopicBinarySetup)
    (_scenario : MatchesSpectroscopicBinaryScenario setup)
    (_readouts : MatchesProblemReadouts setup)
    (_figure : MatchesPrimaryBinaryStarFigure setup)
    (_physical : HasPhysicalBinaryParameters setup)
    (_doppler : SatisfiesSpectroscopicDopplerLaws setup)
    (_kinematics : SatisfiesUniformCircularKinematics setup)
    (_dynamics : SatisfiesNewtonianBinaryDynamics setup) :
    (∀ star,
        speedInMetersPerSecond (setup.orbitalSpeed star) =
            speedOfLightInMetersPerSecond *
              (frequencyInHertz (setup.maximumObservedFrequency star) -
                frequencyInHertz (setup.minimumObservedFrequency star)) /
              (frequencyInHertz (setup.maximumObservedFrequency star) +
                frequencyInHertz (setup.minimumObservedFrequency star)) ∧
          lengthInMeters (setup.orbitRadius star) =
            speedInMetersPerSecond (setup.orbitalSpeed star) *
              timeInSeconds setup.orbitalPeriod / (2 * Real.pi) ∧
          lengthInMeters (setup.orbitRadius star) /
              lengthInMeters setup.earthSunDistance =
            (speedInMetersPerSecond (setup.orbitalSpeed star) *
                timeInSeconds setup.orbitalPeriod / (2 * Real.pi)) /
              lengthInMeters setup.earthSunDistance) ∧
      (∀ star,
        massInKilograms (setup.starMass star) =
            4 * lengthInMeters (setup.orbitRadius star) *
              speedInMetersPerSecond (setup.orbitalSpeed star) ^ 2 /
              gravitationalConstantInSI setup.gravitationalConstant ∧
          massInKilograms (setup.starMass star) /
              massInKilograms setup.solarMass =
            (4 * lengthInMeters (setup.orbitRadius star) *
                speedInMetersPerSecond (setup.orbitalSpeed star) ^ 2 /
                gravitationalConstantInSI setup.gravitationalConstant) /
              massInKilograms setup.solarMass) := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0514
