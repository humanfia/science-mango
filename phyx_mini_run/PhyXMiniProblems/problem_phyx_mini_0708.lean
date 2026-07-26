import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0708

open Dimension

/-!
# Speed of Earth after a radial fall into the Sun

The Earth is initially at rest relative to a fixed central Sun and then falls
radially under Newtonian gravity.  The primary image labels the initial
center-to-center separation by `r₁ = 1.50 × 10¹¹ m` and the separation at
surface contact by `r₂ = Rₛ + Rₑ = 7.02 × 10⁸ m`.  It labels the initial
speed by `v₁ = 0 m/s` and the impact speed by `v₂`.

Masses, radii, separations, speeds, energies, and the gravitational constant
are dimensionful Physlib quantities.  Real numbers occur only as SI readouts,
rounded numerical data, and answer-choice values.

Assumption/target split:

* governing laws: Newtonian kinetic energy, central gravitational potential
  energy `-G Mₛ Mₑ / r`, and conservation of mechanical energy;
* previous-part results: none;
* figure/data readouts: the two panels and labels, radial/contact geometry,
  `v₁ = 0`, `r₁ = 1.50 × 10¹¹ m`, `r₂ = Rₛ + Rₑ = 7.02 × 10⁸ m`, and the
  standard textbook values of `G` and the solar mass needed by the recorded
  numerical answer;
* target conclusions: the derived impact-speed-squared relation and that the
  resulting impact speed is approximately `6.13 × 10⁵ m/s`, uniquely selecting
  answer choice C.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A nonnegative physical length, independent of a choice of units. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical mass, independent of a choice of units. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

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

/-- Read a physical mass in SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a nonnegative physical speed in SI metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read a physical energy in SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read the gravitational constant in `m³ kg⁻¹ s⁻²`. -/
def gravitationalConstantInSI
    (constant : GravitationalConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-! ## Bodies, states, and primary-image vocabulary -/

/-- The two physical bodies whose masses and radii enter the model. -/
inductive CelestialBody where
  | earth
  | sun
  deriving DecidableEq, Fintype, Repr

/-- The two states compared by conservation of mechanical energy. -/
inductive FallState where
  | before
  | surfaceContact
  deriving DecidableEq, Fintype, Repr

/-- Radial motion of the Earth's center relative to the Sun's center. -/
inductive RadialMotion where
  | stationary
  | towardSun
  | awayFromSun
  deriving DecidableEq, Repr

/-- The idealization of the trajectory after orbital motion suddenly stops. -/
inductive TrajectoryGeometry where
  | radial
  | nonradial
  deriving DecidableEq, Repr

/-- Which interactions are retained in the fall model. -/
inductive InteractionModel where
  | solarGravityOnly
  | includesOtherInteractions
  deriving DecidableEq, Repr

/-- Whether recoil of the much heavier central body is neglected. -/
inductive CentralBodyApproximation where
  | sunFixed
  | twoBodyRecoil
  deriving DecidableEq, Repr

/-- Horizontal direction of the green impact-velocity arrow in the bitmap. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- Literal labels visible in the supplied primary image. -/
inductive FigureLabel where
  | beforePanel
  | afterPanel
  | earth
  | sun
  | earthRadiusRe
  | sunRadiusRs
  | initialSpeedV1
  | impactSpeedV2
  | initialSeparationR1
  | contactSeparationR2
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative evidence transcribed from image `708.png`.  The numerical values
attached to `r₁`, `r₂`, and `v₁` are related to physical quantities only by
`MatchesPrimaryEarthSunFigure` below.
-/
structure EarthSunFallFigure where
  labelShown : FigureLabel → Bool
  radiusArrowShown : CelestialBody → Bool
  velocityArrowShown : FallState → Bool
  earthShownBefore : Bool
  earthShownAtContact : Bool
  sunShown : Bool
  earthIsLeftOfSunAtContact : Bool
  surfacesTangentAtContact : Bool
  initialSeparationDimensionLineShown : Bool
  contactSeparationDimensionLineShown : Bool
  impactVelocityArrowDirection : HorizontalDirection

/-! ## Independent physical setup -/

/-!
The fields are independent physical quantities.  In particular, `earthSpeed`
at contact is not defined from an answer choice or from the desired formula.
-/
structure EarthSunRadialFallSetup where
  radius : CelestialBody → LengthQuantity
  mass : CelestialBody → MassQuantity
  centerSeparation : FallState → LengthQuantity
  earthSpeed : FallState → DimSpeed
  earthMotion : FallState → RadialMotion
  earthKineticEnergy : FallState → DimEnergy
  sunEarthPotentialEnergy : FallState → DimEnergy
  gravitationalConstant : GravitationalConstantQuantity
  trajectoryGeometry : TrajectoryGeometry
  interactionModel : InteractionModel
  centralBodyApproximation : CentralBodyApproximation
  figure : EarthSunFallFigure

/-! ## Scenario, figure evidence, and independent numerical data -/

/-!
The prose scenario: the Earth has stopped revolving, is initially stationary,
and subsequently moves radially toward a Sun treated as the fixed central
body.  No impact-speed value occurs here.
-/
structure MatchesStoppedEarthScenario
    (setup : EarthSunRadialFallSetup) : Prop where
  radialTrajectory : setup.trajectoryGeometry = .radial
  gravityIsOnlyInteraction : setup.interactionModel = .solarGravityOnly
  sunTreatedAsFixed : setup.centralBodyApproximation = .sunFixed
  earthInitiallyStationary : setup.earthMotion .before = .stationary
  initialSpeedIsZero : speedInMetersPerSecond (setup.earthSpeed .before) = 0
  earthMovesTowardSunAtContact :
    setup.earthMotion .surfaceContact = .towardSun

/-!
Facts read from the primary bitmap.  The two distances are center-to-center
separations; at contact this equals the sum of the two physical radii.  These
are input geometry and measurement readouts, not the requested impact speed.
-/
structure MatchesPrimaryEarthSunFigure
    (setup : EarthSunRadialFallSetup) : Prop where
  allLiteralLabelsShown : ∀ label, setup.figure.labelShown label = true
  bothRadiusArrowsShown :
    ∀ body, setup.figure.radiusArrowShown body = true
  initialVelocityAnnotationShown :
    setup.figure.velocityArrowShown .before = true
  impactVelocityArrowShown :
    setup.figure.velocityArrowShown .surfaceContact = true
  earthShownInBothPanels :
    setup.figure.earthShownBefore = true ∧
      setup.figure.earthShownAtContact = true
  sunShownInAfterPanel : setup.figure.sunShown = true
  earthLiesLeftOfSunAtContact :
    setup.figure.earthIsLeftOfSunAtContact = true
  surfacesShownTangentAtContact :
    setup.figure.surfacesTangentAtContact = true
  separationDimensionLinesShown :
    setup.figure.initialSeparationDimensionLineShown = true ∧
      setup.figure.contactSeparationDimensionLineShown = true
  impactArrowPointsRightTowardSun :
    setup.figure.impactVelocityArrowDirection = .rightward
  initialSeparationMeters :
    lengthInMeters (setup.centerSeparation .before) = 150 * 10 ^ 9
  contactSeparationIsRadiusSum :
    lengthInMeters (setup.centerSeparation .surfaceContact) =
      lengthInMeters (setup.radius .sun) +
        lengthInMeters (setup.radius .earth)
  contactSeparationMeters :
    lengthInMeters (setup.centerSeparation .surfaceContact) = 702 * 10 ^ 6

/-!
Independent textbook constants required to evaluate the numerical answer.
The source image supplies the geometry but does not print `G` or the solar
mass, so their use is made explicit rather than hidden in a local definition.
-/
structure UsesTextbookSolarParameters
    (setup : EarthSunRadialFallSetup) : Prop where
  gravitationalConstantSI :
    gravitationalConstantInSI setup.gravitationalConstant = 667 / 10 ^ 13
  solarMassKilograms :
    massInKilograms (setup.mass .sun) = 199 * 10 ^ 28

/-! Physical-domain conditions needed to use and cancel the model quantities. -/
structure HasPhysicalEarthSunParameters
    (setup : EarthSunRadialFallSetup) : Prop where
  bodyMassesPositive :
    ∀ body, 0 < massInKilograms (setup.mass body)
  bodyRadiiPositive :
    ∀ body, 0 < lengthInMeters (setup.radius body)
  separationsPositive :
    ∀ state, 0 < lengthInMeters (setup.centerSeparation state)
  initialSeparationGreaterThanContact :
    lengthInMeters (setup.centerSeparation .surfaceContact) <
      lengthInMeters (setup.centerSeparation .before)
  gravitationalConstantPositive :
    0 < gravitationalConstantInSI setup.gravitationalConstant

/-! ## Governing Newtonian energy laws -/

/-!
The kinetic-energy formula, point-mass central gravitational potential, and
conservation of mechanical energy.  These are governing laws at two independent
states; they do not contain the solved speed-squared relation or a numerical
impact speed.
-/
structure SatisfiesNewtonianRadialFallEnergyLaws
    (setup : EarthSunRadialFallSetup) : Prop where
  kineticEnergyFormula :
    ∀ state,
      energyInJoules (setup.earthKineticEnergy state) =
        massInKilograms (setup.mass .earth) *
          speedInMetersPerSecond (setup.earthSpeed state) ^ 2 / 2
  centralGravitationalPotentialFormula :
    ∀ state,
      energyInJoules (setup.sunEarthPotentialEnergy state) =
        -(gravitationalConstantInSI setup.gravitationalConstant *
          massInKilograms (setup.mass .sun) *
          massInKilograms (setup.mass .earth) /
          lengthInMeters (setup.centerSeparation state))
  mechanicalEnergyConserved :
    energyInJoules (setup.earthKineticEnergy .before) +
        energyInJoules (setup.sunEarthPotentialEnergy .before) =
      energyInJoules (setup.earthKineticEnergy .surfaceContact) +
        energyInJoules (setup.sunEarthPotentialEnergy .surfaceContact)

/-! ## Answer choices and current target -/

/-- Labels of the four impact-speed choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metres-per-second readout printed beside each answer label. -/
def answerSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 513 * 10 ^ 3
  | .B => 613 * 10 ^ 2
  | .C => 613 * 10 ^ 3
  | .D => 713 * 10 ^ 3

/-!
A choice is uniquely closest when every distinct printed alternative has
strictly larger absolute error from the independent physical impact speed.
-/
def IsUniqueClosestImpactSpeedChoice
    (setup : EarthSunRadialFallSetup) (choice : AnswerChoice) : Prop :=
  ∀ other,
    other ≠ choice →
      |speedInMetersPerSecond (setup.earthSpeed .surfaceContact) -
          answerSpeedInMetersPerSecond choice| <
        |speedInMetersPerSecond (setup.earthSpeed .surfaceContact) -
          answerSpeedInMetersPerSecond other|

/-!
Energy conservation gives the general change in squared speed between the
initial and contact separations.
-/
lemma speedSquaredChange_eq_newtonianPotentialDrop
    (setup : EarthSunRadialFallSetup)
    (_physical : HasPhysicalEarthSunParameters setup)
    (_laws : SatisfiesNewtonianRadialFallEnergyLaws setup) :
    speedInMetersPerSecond (setup.earthSpeed .surfaceContact) ^ 2 -
        speedInMetersPerSecond (setup.earthSpeed .before) ^ 2 =
      2 * gravitationalConstantInSI setup.gravitationalConstant *
        massInKilograms (setup.mass .sun) *
        (1 / lengthInMeters (setup.centerSeparation .surfaceContact) -
          1 / lengthInMeters (setup.centerSeparation .before)) := by
  have hm := _physical.bodyMassesPositive .earth
  have hr₀ := _physical.separationsPositive .before
  have hr₁ := _physical.separationsPositive .surfaceContact
  have h := _laws.mechanicalEnergyConserved
  simp only [_laws.kineticEnergyFormula,
    _laws.centralGravitationalPotentialFormula] at h
  field_simp [ne_of_gt hr₀, ne_of_gt hr₁] at h ⊢
  nlinarith

/-! With the initial speed zero, the general energy relation is the impact law. -/
lemma impactSpeedSquared_eq_newtonianPotentialDrop
    (setup : EarthSunRadialFallSetup)
    (_scenario : MatchesStoppedEarthScenario setup)
    (_physical : HasPhysicalEarthSunParameters setup)
    (_laws : SatisfiesNewtonianRadialFallEnergyLaws setup) :
    speedInMetersPerSecond (setup.earthSpeed .surfaceContact) ^ 2 =
      2 * gravitationalConstantInSI setup.gravitationalConstant *
        massInKilograms (setup.mass .sun) *
        (1 / lengthInMeters (setup.centerSeparation .surfaceContact) -
          1 / lengthInMeters (setup.centerSeparation .before)) := by
  simpa [_scenario.initialSpeedIsZero] using
    speedSquaredChange_eq_newtonianPotentialDrop setup _physical _laws

/-!
For `r₁ = 1.50 × 10¹¹ m`, `r₂ = 7.02 × 10⁸ m`,
`G = 6.67 × 10⁻¹¹ m³ kg⁻¹ s⁻²`, and `Mₛ = 1.99 × 10³⁰ kg`, the
Newtonian energy model gives an impact speed within `10³ m/s` of
`6.13 × 10⁵ m/s`.  It is therefore uniquely closest to recorded choice C.

Blueprint: `thm:physics:phyx_mini_0708:target`.
-/
theorem earthImpactSpeed_is_recordedChoiceC
    (setup : EarthSunRadialFallSetup)
    (_scenario : MatchesStoppedEarthScenario setup)
    (_figure : MatchesPrimaryEarthSunFigure setup)
    (_solarParameters : UsesTextbookSolarParameters setup)
    (_physical : HasPhysicalEarthSunParameters setup)
    (_laws : SatisfiesNewtonianRadialFallEnergyLaws setup) :
    speedInMetersPerSecond (setup.earthSpeed .surfaceContact) ^ 2 =
        2 * gravitationalConstantInSI setup.gravitationalConstant *
          massInKilograms (setup.mass .sun) *
          (1 / lengthInMeters (setup.centerSeparation .surfaceContact) -
            1 / lengthInMeters (setup.centerSeparation .before)) ∧
      |speedInMetersPerSecond (setup.earthSpeed .surfaceContact) -
          answerSpeedInMetersPerSecond .C| ≤ 10 ^ 3 ∧
      IsUniqueClosestImpactSpeedChoice setup .C := by
  constructor
  · exact
      impactSpeedSquared_eq_newtonianPotentialDrop
        setup _scenario _physical _laws
  have hsq :=
    impactSpeedSquared_eq_newtonianPotentialDrop
      setup _scenario _physical _laws
  rw [_solarParameters.gravitationalConstantSI,
    _solarParameters.solarMassKilograms,
    _figure.contactSeparationMeters,
    _figure.initialSeparationMeters] at hsq
  norm_num at hsq
  have hv : 0 ≤ speedInMetersPerSecond
      (setup.earthSpeed .surfaceContact) := NNReal.coe_nonneg _
  have hlo : (613000 : ℝ) ≤ speedInMetersPerSecond
      (setup.earthSpeed .surfaceContact) := by
    nlinarith
  have hhi : speedInMetersPerSecond
      (setup.earthSpeed .surfaceContact) ≤ (614000 : ℝ) := by
    nlinarith
  constructor
  · rw [abs_of_nonneg]
    · norm_num [answerSpeedInMetersPerSecond]
      linarith
    · norm_num [answerSpeedInMetersPerSecond]
      linarith
  · intro other hother
    fin_cases other
    · norm_num [answerSpeedInMetersPerSecond]
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      norm_num
    · norm_num [answerSpeedInMetersPerSecond]
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      norm_num
    · exact (hother rfl).elim
    · norm_num [answerSpeedInMetersPerSecond]
      rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
      linarith

end PhyXMiniProblems.ProblemPhyXMini0708
