import Mathlib
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0611

open Dimension

/-!
# Stellar mass in an edge-on spectroscopic binary

Two identical stars of mass `m` move on opposite sides of the same circular
orbit of radius `R` about their common center of mass.  The orbit is viewed
edge-on from Earth.  The supplied bitmap labels both stars by `m`, labels the
center-to-orbit radius by `R`, and shows opposite tangential velocity arrows.
The maximum-to-minimum-to-maximum light-frequency cycle lasts `11.0 d`.

The source records the mass answer `5.55 × 10²⁹ kg`, but it does not supply
the numerical frequency extrema needed to recover the orbital speed, and its
metadata identifies no previous part.  Consequently the answer choices are
retained only as source metadata.  The theorem gives the strongest supported
symbolic result: the Doppler-inferred speed and the resulting radius and mass
relations, without asserting a numerical radius, mass, or answer label.

Physical length, time, mass, speed, frequency, force, and the gravitational
constant are dimensionful Physlib quantities.  Real numbers occur only as
named SI readouts, numerical observations, dimensionless ratios inside the
Doppler law, and answer-choice values.

Assumption/target split:

* governing laws: longitudinal relativistic light Doppler shift, edge-on
  projection, uniform circular kinematics, inverse-square Newtonian gravity,
  and centripetal force;
* previous results: none (the source report's previous-parts list is empty);
* figure/data readouts: identical stars, circular edge-on geometry, an
  `11.0 d` cycle, all visible labels and arrow directions, the four mass
  choices, and the standard textbook value of `G`;
* target conclusions: the line-of-sight speed expressed through the symbolic
  maximum and minimum observed frequencies, `R = v(11 d)/(2π)`, and
  `m = 4Rv²/G`.
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
The Newtonian gravitational constant, with dimension
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

/-- Location of a star in the snapshot shown by the primary bitmap. -/
inductive FigurePosition where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- Horizontal direction used by the Earth arrow and tangential arrows. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Literal symbolic labels visible in the supplied image. -/
inductive FigureLabel where
  | massM
  | radiusR
  | toTheEarth
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative information transcribed from the primary bitmap.  In particular,
the radius segment records the geometrical role of `R`; it does not define a
numerical radius or mass answer.
-/
structure BinaryStarFigure where
  position : BinaryStar → FigurePosition
  tangentialVelocityArrow : BinaryStar → HorizontalDirection
  labelShownAtStar : BinaryStar → FigureLabel → Bool
  sceneLabelShown : FigureLabel → Bool
  orbitCircleShown : Bool
  centerPointShown : Bool
  radiusSegmentFromCenterToOrbitShown : Bool
  earthDirectionArrow : HorizontalDirection
  starsShownAntipodal : Bool

/-! ## Independent physical setup -/

/-!
The physical quantities belonging to the binary system and its observation.
Mass and radius are independent fields, not definitions manufactured from the
recorded answer.
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
  orbitShape : OrbitShape
  viewingOrientation : ViewingOrientation
  figure : BinaryStarFigure

/-! ## Scenario, observations, and primary-image evidence -/

/-- The equal-star, circular, edge-on scenario stated in the prose. -/
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
The frequency-cycle observation printed in the problem.  No numerical radius
or stellar mass is included here.
-/
structure MatchesProblemReadouts (setup : SpectroscopicBinarySetup) : Prop where
  frequencyCycleIsElevenDays :
    ∀ star,
      timeInSeconds (setup.frequencyVariationPeriod star) =
        11 * 24 * 60 * 60
  frequencyCycleIsOrbitalPeriod :
    ∀ star,
      setup.frequencyVariationPeriod star = setup.orbitalPeriod
  minimumBelowRestBelowMaximum :
    ∀ star,
      frequencyInHertz (setup.minimumObservedFrequency star) <
          frequencyInHertz (setup.emittedRestFrequency star) ∧
        frequencyInHertz (setup.emittedRestFrequency star) <
          frequencyInHertz (setup.maximumObservedFrequency star)

/-- Primary-image evidence, kept separate from all dynamical laws. -/
structure MatchesPrimaryBinaryStarFigure
    (setup : SpectroscopicBinarySetup) : Prop where
  star₁ShownUpper : setup.figure.position .star₁ = .upper
  star₂ShownLower : setup.figure.position .star₂ = .lower
  upperVelocityArrowPointsLeft :
    setup.figure.tangentialVelocityArrow .star₁ = .left
  lowerVelocityArrowPointsRight :
    setup.figure.tangentialVelocityArrow .star₂ = .right
  bothMassLabelsShown :
    ∀ star, setup.figure.labelShownAtStar star .massM = true
  blueCircularPathShown : setup.figure.orbitCircleShown = true
  blackCenterPointShown : setup.figure.centerPointShown = true
  radiusSegmentShown :
    setup.figure.radiusSegmentFromCenterToOrbitShown = true
  radiusRLabelShown : setup.figure.sceneLabelShown .radiusR = true
  earthArrowPointsLeft : setup.figure.earthDirectionArrow = .left
  toTheEarthTextShown : setup.figure.sceneLabelShown .toTheEarth = true
  oppositePositionsShown : setup.figure.starsShownAntipodal = true

/-! ## Source answer metadata and numerical calibration -/

/-- Labels of the four stellar-mass choices in the source. -/
inductive MassAnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Kilogram readout printed beside each answer label. -/
def answerMassInKilograms : MassAnswerChoice → ℝ
  | .A => 555 * 10 ^ 27
  | .B => 553 * 10 ^ 26
  | .C => 545 * 10 ^ 27
  | .D => 533 * 10 ^ 26

/-- Standard textbook calibration `G = 6.67 × 10⁻¹¹ m³ kg⁻¹ s⁻²`. -/
structure UsesTextbookGravitationalConstant
    (setup : SpectroscopicBinarySetup) : Prop where
  constantValueInSI :
    gravitationalConstantInSI setup.gravitationalConstant = 667 / 10 ^ 13

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
  gravitationalForcesPositive :
    ∀ star, 0 < forceInNewtons (setup.gravitationalForceOn star)
  gravitationalConstantPositive :
    0 < gravitationalConstantInSI setup.gravitationalConstant
  emittedFrequenciesPositive :
    ∀ star, 0 < frequencyInHertz (setup.emittedRestFrequency star)

/-!
Longitudinal relativistic Doppler shift for approaching and receding extrema.
For an edge-on circular orbit, the line-of-sight speed amplitude equals the
orbital speed.  These laws contain no radius or mass answer.
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
Uniform circular kinematics: during one orbital period each star travels one
circumference of its orbit about the common center.
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
makes the stellar separation the sum of the orbital radii.  Mutual gravity is
also the centripetal force for each star.  These are governing laws, not the
solved mass formula.
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

/-! ## Derived relations and requested answer -/

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
For identical stars on antipodal equal-radius orbits, Newtonian gravity and
centripetal motion give `m = 4 R v² / G`.
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
The numerical frequency extrema needed for a numerical speed are absent from
the source.  For each star, the exact longitudinal Doppler law nevertheless
determines the speed symbolically from the frequency contrast.  The given
`11.0 d` cycle then determines the radius, and equal-mass Newtonian binary
dynamics determines the mass.  The historical declaration name is retained
for the blueprint pin, but the conclusion deliberately makes no choice-A
claim.

Blueprint: `thm:physics:phyx_mini_0611:target`.
-/
theorem spectroscopicBinary_stellarMass_is_choiceA
    (setup : SpectroscopicBinarySetup)
    (_scenario : MatchesSpectroscopicBinaryScenario setup)
    (_readouts : MatchesProblemReadouts setup)
    (_figure : MatchesPrimaryBinaryStarFigure setup)
    (_constant : UsesTextbookGravitationalConstant setup)
    (_physical : HasPhysicalBinaryParameters setup)
    (_doppler : SatisfiesSpectroscopicDopplerLaws setup)
    (_kinematics : SatisfiesUniformCircularKinematics setup)
    (_dynamics : SatisfiesNewtonianBinaryDynamics setup) :
    ∀ star,
      let maximumFrequency :=
        frequencyInHertz (setup.maximumObservedFrequency star)
      let minimumFrequency :=
        frequencyInHertz (setup.minimumObservedFrequency star)
      let dopplerInferredSpeed :=
        speedOfLightInMetersPerSecond *
          (maximumFrequency - minimumFrequency) /
          (maximumFrequency + minimumFrequency)
      speedInMetersPerSecond (setup.lineOfSightSpeedAmplitude star) =
          dopplerInferredSpeed ∧
        lengthInMeters (setup.orbitRadius star) =
          dopplerInferredSpeed * (11 * 24 * 60 * 60) / (2 * Real.pi) ∧
        massInKilograms (setup.starMass star) =
          4 * lengthInMeters (setup.orbitRadius star) *
              dopplerInferredSpeed ^ 2 /
            gravitationalConstantInSI setup.gravitationalConstant := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0611
