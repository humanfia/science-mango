import Mathlib
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0564

open Dimension

/-!
# Mean-speed strike position in Stern's rotating-drum experiment

An oven at `850 K` emits a beam of `Bi₂` molecules.  Slit `S₁` collimates
the beam and slit `S₂` admits it into a rotating circular drum.  The primary
image shows the beam crossing the drum from `S₂` to the diametrically opposite
point `A`; a curved glass plate is fixed to the inside wall from near `A`
toward `B`.  During a molecule's flight, the plate rotates, so the molecule
lands at an offset from `A` determined by its speed.  The stated drum diameter
is `10 cm` and its rotation rate is `6250 rev/min`.

Physlib dimensionful quantities represent length, time, temperature, mass,
frequency, speed, and the molar gas constant.  Since Physlib's foundational
`Dimension` has no amount-of-substance coordinate, molar mass is represented
by a mass-dimension quantity whose named scalar readout is kilograms per mole;
similarly the gas-constant readout is joules per mole-kelvin.  Real numbers are
used only for these explicit readouts, dimensionless revolution fractions,
answer choices, and densitometer signals.

Assumption/target split:

* governing laws: Maxwell's mean-speed law, straight-line time of flight,
  uniform drum rotation, circular arc geometry, inverse speed sorting, and
  densitometer proportionality;
* previous-part results: none;
* data and figure readouts: `Bi₂`, `850 K`, `418 g/mol`, `R = 8.31
  J/(mol K)`, a `10 cm` drum, `6250 rev/min`, labels `S₁`, `S₂`, `A`, `B`,
  and the diameter flight path visible in the bitmap;
* target conclusions: the derived mean-speed impact offset is within
  `10⁻⁵ rev` of `0.05021 rev` and D is the unique nearest displayed choice.
-/

/-! ## Dimensionful quantities and named readouts -/

/-- A nonnegative physical length independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative absolute temperature. -/
abbrev TemperatureQuantity : Type := Dimensionful (WithDim Θ𝓭 NNReal)

/--
A nonnegative molar mass.  Amount of substance is treated as a fixed one-mole
reference because Physlib's current `Dimension` has no mole coordinate.
-/
abbrev MolarMassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative rotation frequency, with revolutions counted dimensionlessly. -/
abbrev RotationFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/--
The universal molar gas constant, with the mole count treated dimensionlessly:
`mass * length² * time⁻² * temperature⁻¹`.
-/
abbrev MolarGasConstantQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical duration in a selected time unit. -/
def timeReadout (unit : TimeUnit) (duration : TimeQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read an absolute temperature in a selected temperature unit. -/
def temperatureReadout
    (unit : TemperatureUnit) (temperature : TemperatureQuantity) : ℝ :=
  ((temperature {UnitChoices.SI with temperature := unit}).val : ℝ)

/-- Read molar mass in the selected mass unit per mole. -/
def molarMassReadout
    (unit : MassUnit) (molarMass : MolarMassQuantity) : ℝ :=
  ((molarMass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read drum rotation frequency in revolutions per selected time unit. -/
def rotationFrequencyReadout
    (unit : TimeUnit) (frequency : RotationFrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read the molar gas constant in coherent SI joules per mole-kelvin. -/
def molarGasConstantInSI (constant : MolarGasConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-! ## Molecules and primary-image vocabulary -/

/-- Molecular species admitted into the drum. -/
inductive MolecularSpecies where
  | bismuthDimer
  | other
  deriving DecidableEq, Repr

/-- Literal apparatus and marker labels visible in the supplied bitmap. -/
inductive FigureLabel where
  | oven
  | slitS₁
  | slitS₂
  | drum
  | glassPlate
  | markerA
  | markerB
  | angularVelocityW
  deriving DecidableEq, Fintype, Repr

/-- The two marked endpoints relevant to position along the curved plate. -/
inductive PlateMarker where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- Direction of traversal along the visible front portion of the plate. -/
inductive PlateTraversal where
  | fromAToB
  | fromBToA
  deriving DecidableEq, Repr

/--
Qualitative geometry transcribed from the primary image.  The image contains
no numerical impact offset or answer value.
-/
structure SternRotatingDrumFigure where
  labelShown : FigureLabel → Bool
  ovenBeamReachesS₁ : Bool
  beamFromS₁PassesThroughS₂ : Bool
  beamFromS₂ContinuesToA : Bool
  AIsDiametricallyOppositeS₂ : Bool
  glassPlateFollowsInsideWall : Bool
  plateRunsBetweenAAndB : Bool
  drumMotionAtVisibleFront : PlateTraversal

/-! ## Independent physical setup -/

/-!
Physical quantities and observables of the experiment.  The speed-to-impact
map and the mean speed are independent fields.  They are related to the input
data only by the governing-law interfaces below, never by an answer-valued
definition.
-/
structure SternSpeedDistributionSetup where
  molecularSpecies : MolecularSpecies
  ovenTemperature : TemperatureQuantity
  molecularMolarMass : MolarMassQuantity
  molarGasConstant : MolarGasConstantQuantity
  drumDiameter : LengthQuantity
  beamFlightDistance : LengthQuantity
  drumRotationFrequency : RotationFrequencyQuantity
  maxwellMeanSpeed : DimSpeed
  flightTimeForSpeed : DimSpeed → TimeQuantity
  impactOffsetRevolutionsFromA : DimSpeed → ℝ
  impactArcDistanceFromA : DimSpeed → LengthQuantity
  depositedMoleculeCountSignal : ℝ → ℝ
  depositDensitySignal : ℝ → ℝ
  densitometerScale : ℝ
  bunchMoleculeCount : ℕ → ℕ
  figure : SternRotatingDrumFigure
  beamDefinedByS₁ : Bool
  beamAdmittedThroughS₂ : Bool
  moleculesAdhereToGlass : Bool
  fastestMoleculesStrikeNearA : Bool
  slowestMoleculesStrikeNearB : Bool
  intermediateSpeedsStrikeBetweenAAndB : Bool

/-- Flight time of molecules traveling at the Maxwell mean speed. -/
def meanSpeedFlightTime (setup : SternSpeedDistributionSetup) : TimeQuantity :=
  setup.flightTimeForSpeed setup.maxwellMeanSpeed

/-- Dimensionless plate offset from `A`, measured as a fraction of one turn. -/
def meanSpeedStrikeOffsetRevolutions
    (setup : SternSpeedDistributionSetup) : ℝ :=
  setup.impactOffsetRevolutionsFromA setup.maxwellMeanSpeed

/-- Physical arc distance along the plate from `A` for mean-speed molecules. -/
def meanSpeedStrikeArcDistance
    (setup : SternSpeedDistributionSetup) : LengthQuantity :=
  setup.impactArcDistanceFromA setup.maxwellMeanSpeed

/-! ## Scenario, source data, and figure readouts -/

/-- The qualitative experimental scenario stated in the prose. -/
structure MatchesSternExperimentScenario
    (setup : SternSpeedDistributionSetup) : Prop where
  speciesIsBismuthDimer : setup.molecularSpecies = .bismuthDimer
  firstSlitDefinesBeam : setup.beamDefinedByS₁ = true
  secondSlitAdmitsBeam : setup.beamAdmittedThroughS₂ = true
  depositsAdhereToPlate : setup.moleculesAdhereToGlass = true
  identicalBunches : ∀ i j, setup.bunchMoleculeCount i = setup.bunchMoleculeCount j
  fastDepositsNearA : setup.fastestMoleculesStrikeNearA = true
  slowDepositsNearB : setup.slowestMoleculesStrikeNearB = true
  otherDepositsBetween : setup.intermediateSpeedsStrikeBetweenAAndB = true

/-!
Numerical readouts stated by the problem.  No flight time, impact offset,
arc distance, or displayed answer occurs here.
-/
structure MatchesSternProblemReadouts
    (setup : SternSpeedDistributionSetup) : Prop where
  ovenTemperatureKelvin :
    temperatureReadout TemperatureUnit.kelvin setup.ovenTemperature = 850
  drumDiameterCentimeters :
    lengthReadout LengthUnit.centimeters setup.drumDiameter = 10
  drumRateRevolutionsPerMinute :
    rotationFrequencyReadout TimeUnit.minutes setup.drumRotationFrequency = 6250

/-!
Standard rounded classroom data for `Bi₂` and the universal molar gas
constant.  These determine the Maxwell speed but do not state an impact
position.
-/
structure UsesBismuthDimerReferenceData
    (setup : SternSpeedDistributionSetup) : Prop where
  bismuthDimerMolarMassGramsPerMole :
    molarMassReadout MassUnit.grams setup.molecularMolarMass = 418
  gasConstantJoulesPerMoleKelvin :
    molarGasConstantInSI setup.molarGasConstant = 831 / 100

/-! Evidence read directly from the primary bitmap. -/
structure MatchesPrimarySternFigure
    (setup : SternSpeedDistributionSetup) : Prop where
  everyLiteralLabelShown : ∀ label, setup.figure.labelShown label = true
  ovenToFirstSlit : setup.figure.ovenBeamReachesS₁ = true
  firstSlitToSecondSlit : setup.figure.beamFromS₁PassesThroughS₂ = true
  secondSlitToA : setup.figure.beamFromS₂ContinuesToA = true
  AOppositeSecondSlit : setup.figure.AIsDiametricallyOppositeS₂ = true
  beamCrossesOneDiameter : setup.beamFlightDistance = setup.drumDiameter
  curvedPlateAtInsideWall : setup.figure.glassPlateFollowsInsideWall = true
  plateBetweenMarkers : setup.figure.plateRunsBetweenAAndB = true
  frontRimMovesFromBToA :
    setup.figure.drumMotionAtVisibleFront = .fromBToA

/-! ## Governing physics -/

/-- Positivity conditions selecting the intended physical regime. -/
structure HasPhysicalSternParameters
    (setup : SternSpeedDistributionSetup) : Prop where
  positiveTemperature :
    0 < temperatureReadout TemperatureUnit.kelvin setup.ovenTemperature
  positiveMolarMass :
    0 < molarMassReadout MassUnit.kilograms setup.molecularMolarMass
  positiveGasConstant : 0 < molarGasConstantInSI setup.molarGasConstant
  positiveDiameter : 0 < lengthReadout LengthUnit.meters setup.drumDiameter
  positiveFlightDistance :
    0 < lengthReadout LengthUnit.meters setup.beamFlightDistance
  positiveRotationRate :
    0 < rotationFrequencyReadout TimeUnit.seconds setup.drumRotationFrequency
  positiveMeanSpeed : 0 < speedInMetersPerSecond setup.maxwellMeanSpeed
  positiveMeanFlightTime :
    0 < timeReadout TimeUnit.seconds (meanSpeedFlightTime setup)
  positiveDensitometerScale : 0 < setup.densitometerScale

/-!
Maxwell's theoretical mean-speed relation
`⟨v⟩ = sqrt (8 R T / (π M))` for a gas with molar mass `M`.
-/
structure SatisfiesMaxwellMeanSpeedLaw
    (setup : SternSpeedDistributionSetup) : Prop where
  meanSpeedFormula :
    speedInMetersPerSecond setup.maxwellMeanSpeed =
      Real.sqrt
        (8 * molarGasConstantInSI setup.molarGasConstant *
            temperatureReadout TemperatureUnit.kelvin setup.ovenTemperature /
          (Real.pi *
            molarMassReadout MassUnit.kilograms setup.molecularMolarMass))

/-!
Straight-line flight, uniform rotation, and circular plate geometry.  These
relations hold generically for every positive molecular speed; in particular,
they do not contain `0.05021`, choice D, or any problem-specific offset.
-/
structure SatisfiesRotatingDrumKinematics
    (setup : SternSpeedDistributionSetup) : Prop where
  timeOfFlight : ∀ speed,
    0 < speedInMetersPerSecond speed →
      speedInMetersPerSecond speed *
          timeReadout TimeUnit.seconds (setup.flightTimeForSpeed speed) =
        lengthReadout LengthUnit.meters setup.beamFlightDistance
  uniformRotation : ∀ speed,
    0 < speedInMetersPerSecond speed →
      setup.impactOffsetRevolutionsFromA speed =
        rotationFrequencyReadout TimeUnit.seconds
            setup.drumRotationFrequency *
          timeReadout TimeUnit.seconds (setup.flightTimeForSpeed speed)
  circularArcDistance : ∀ speed,
    0 ≤ setup.impactOffsetRevolutionsFromA speed →
      lengthReadout LengthUnit.meters (setup.impactArcDistanceFromA speed) =
        Real.pi * lengthReadout LengthUnit.meters setup.drumDiameter *
          setup.impactOffsetRevolutionsFromA speed

/-- Faster molecules have a smaller rotation-normalized offset from `A`. -/
structure SatisfiesInverseSpeedSorting
    (setup : SternSpeedDistributionSetup) : Prop where
  fasterStrikesCloserToA : ∀ slow fast,
    0 < speedInMetersPerSecond slow →
      speedInMetersPerSecond slow < speedInMetersPerSecond fast →
        setup.impactOffsetRevolutionsFromA fast <
          setup.impactOffsetRevolutionsFromA slow

/-- Deposit density is proportional to molecule count at each plate offset. -/
structure SatisfiesDensitometerLaw
    (setup : SternSpeedDistributionSetup) : Prop where
  countSignalNonnegative : ∀ offset, 0 ≤ setup.depositedMoleculeCountSignal offset
  densitySignalNonnegative : ∀ offset, 0 ≤ setup.depositDensitySignal offset
  densityProportionalToCount : ∀ offset,
    setup.depositDensitySignal offset =
      setup.densitometerScale * setup.depositedMoleculeCountSignal offset

/-! ## Displayed choices and current target -/

/-- Labels of the four revolution-fraction choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed normalized plate distances from `A`, in revolutions. -/
def displayedOffsetRevolutions : AnswerChoice → ℝ
  | .A => 0.04625
  | .B => 0.05667
  | .C => 0.05317
  | .D => 0.05021

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A dimensionless modeled offset agrees with a display within `tolerance`. -/
def AgreesWithinRevolutions
    (actual displayed tolerance : ℝ) : Prop :=
  |actual - displayed| < tolerance

/-- A choice is strictly nearer to the modeled offset than every other choice. -/
def IsUniqueNearestDisplayedOffset
    (setup : SternSpeedDistributionSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |meanSpeedStrikeOffsetRevolutions setup -
        displayedOffsetRevolutions choice| <
      |meanSpeedStrikeOffsetRevolutions setup -
        displayedOffsetRevolutions other|

/-!
Combining straight-line flight with uniform rotation gives the generic
time-of-flight expression for the normalized impact offset.
-/
lemma meanSpeedStrikeOffset_eq_rotationRate_mul_distance_div_speed
    (setup : SternSpeedDistributionSetup)
    (_physical : HasPhysicalSternParameters setup)
    (_kinematics : SatisfiesRotatingDrumKinematics setup) :
    meanSpeedStrikeOffsetRevolutions setup =
      rotationFrequencyReadout TimeUnit.seconds setup.drumRotationFrequency *
        lengthReadout LengthUnit.meters setup.beamFlightDistance /
          speedInMetersPerSecond setup.maxwellMeanSpeed := by
  have hspeed :
      speedInMetersPerSecond setup.maxwellMeanSpeed ≠ 0 :=
    ne_of_gt _physical.positiveMeanSpeed
  rw [meanSpeedStrikeOffsetRevolutions,
    _kinematics.uniformRotation setup.maxwellMeanSpeed
      _physical.positiveMeanSpeed]
  field_simp
  calc
    _ = rotationFrequencyReadout TimeUnit.seconds
          setup.drumRotationFrequency *
        (speedInMetersPerSecond setup.maxwellMeanSpeed *
          timeReadout TimeUnit.seconds
            (setup.flightTimeForSpeed setup.maxwellMeanSpeed)) := by ring
    _ = _ := by
      rw [_kinematics.timeOfFlight setup.maxwellMeanSpeed
        _physical.positiveMeanSpeed]

/-!
For `Bi₂` at `850 K`, Maxwell's law gives a mean speed near `207 m/s`.
Crossing the `0.10 m` diameter while the drum turns at `6250 rev/min`
therefore produces a normalized plate distance within `10⁻⁵ rev` of
`0.05021 rev`.  This is strictly closer than the other three displayed
values, so the model selects choice D.

This formalizes blueprint label `thm:physics:phyx_mini_0564:target`.
-/
theorem problem_phyx_mini_0564
    (setup : SternSpeedDistributionSetup)
    (_scenario : MatchesSternExperimentScenario setup)
    (_readouts : MatchesSternProblemReadouts setup)
    (_reference : UsesBismuthDimerReferenceData setup)
    (_figure : MatchesPrimarySternFigure setup)
    (_physical : HasPhysicalSternParameters setup)
    (_maxwell : SatisfiesMaxwellMeanSpeedLaw setup)
    (_kinematics : SatisfiesRotatingDrumKinematics setup)
    (_sorting : SatisfiesInverseSpeedSorting setup)
    (_densitometer : SatisfiesDensitometerLaw setup) :
    meanSpeedStrikeOffsetRevolutions setup =
        rotationFrequencyReadout TimeUnit.seconds setup.drumRotationFrequency *
          lengthReadout LengthUnit.meters setup.beamFlightDistance /
            speedInMetersPerSecond setup.maxwellMeanSpeed ∧
      AgreesWithinRevolutions
        (meanSpeedStrikeOffsetRevolutions setup)
        (displayedOffsetRevolutions .D)
        (1 / 10 ^ 5) ∧
      IsUniqueNearestDisplayedOffset setup .D := by
  have hLengthConversion (length : LengthQuantity) :
      lengthReadout LengthUnit.centimeters length =
        100 * lengthReadout LengthUnit.meters length := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (length.2 UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.centimeters})
    norm_num [lengthReadout, UnitChoices.dimScale,
      LengthUnit.centimeters, LengthUnit.meters, LengthUnit.scale,
      LengthUnit.div_eq_val, NNReal.smul_def, smul_eq_mul] at h ⊢
    exact h
  have hMassConversion (mass : MolarMassQuantity) :
      molarMassReadout MassUnit.grams mass =
        1000 * molarMassReadout MassUnit.kilograms mass := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (mass.2 UnitChoices.SI
        {UnitChoices.SI with mass := MassUnit.grams})
    norm_num [molarMassReadout, UnitChoices.dimScale, M𝓭,
      MassUnit.grams, MassUnit.kilograms, MassUnit.scale,
      MassUnit.div_eq_val, NNReal.smul_def, smul_eq_mul] at h ⊢
    exact h
  have hFrequencyConversion
      (frequency : RotationFrequencyQuantity) :
      rotationFrequencyReadout TimeUnit.minutes frequency =
        60 * rotationFrequencyReadout TimeUnit.seconds frequency := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (frequency.2 UnitChoices.SI
        {UnitChoices.SI with time := TimeUnit.minutes})
    norm_num [rotationFrequencyReadout, UnitChoices.dimScale,
      TimeUnit.minutes, TimeUnit.seconds, TimeUnit.scale,
      TimeUnit.div_eq_val, NNReal.rpow_neg_one, NNReal.smul_def,
      smul_eq_mul] at h ⊢
    rw [h]
    congr 1
    change (1 / 60 : ℝ)⁻¹ = 60
    norm_num
  have hDiameter :
      lengthReadout LengthUnit.meters setup.drumDiameter = 1 / 10 := by
    have h := hLengthConversion setup.drumDiameter
    rw [_readouts.drumDiameterCentimeters] at h
    norm_num at h ⊢
    linarith
  have hFlightDistance :
      lengthReadout LengthUnit.meters setup.beamFlightDistance = 1 / 10 := by
    rw [_figure.beamCrossesOneDiameter, hDiameter]
  have hMolarMass :
      molarMassReadout MassUnit.kilograms setup.molecularMolarMass =
        209 / 500 := by
    have h := hMassConversion setup.molecularMolarMass
    rw [_reference.bismuthDimerMolarMassGramsPerMole] at h
    norm_num at h ⊢
    linarith
  have hRotationRate :
      rotationFrequencyReadout TimeUnit.seconds
          setup.drumRotationFrequency =
        625 / 6 := by
    have h := hFrequencyConversion setup.drumRotationFrequency
    rw [_readouts.drumRateRevolutionsPerMinute] at h
    norm_num at h ⊢
    linarith
  have hSpeed :
      speedInMetersPerSecond setup.maxwellMeanSpeed =
        Real.sqrt (28254000 / (209 * Real.pi)) := by
    rw [_maxwell.meanSpeedFormula,
      _reference.gasConstantJoulesPerMoleKelvin,
      _readouts.ovenTemperatureKelvin, hMolarMass]
    congr 1
    field_simp [Real.pi_ne_zero]
    ring
  have hOffset :=
    meanSpeedStrikeOffset_eq_rotationRate_mul_distance_div_speed
      setup _physical _kinematics
  have hSpeedSq :
      (speedInMetersPerSecond setup.maxwellMeanSpeed) ^ 2 =
        28254000 / (209 * Real.pi) := by
    rw [hSpeed, Real.sq_sqrt]
    positivity
  have hOffsetTimesSpeed :
      meanSpeedStrikeOffsetRevolutions setup *
          speedInMetersPerSecond setup.maxwellMeanSpeed =
        125 / 12 := by
    rw [hOffset, hRotationRate, hFlightDistance]
    field_simp [ne_of_gt _physical.positiveMeanSpeed]
    ring
  have hOffsetSq :
      (meanSpeedStrikeOffsetRevolutions setup) ^ 2 =
        (26125 / 32548608) * Real.pi := by
    have hProductSq :
        (meanSpeedStrikeOffsetRevolutions setup) ^ 2 *
            (speedInMetersPerSecond setup.maxwellMeanSpeed) ^ 2 =
          (125 / 12) ^ 2 := by
      calc
        _ = (meanSpeedStrikeOffsetRevolutions setup *
              speedInMetersPerSecond setup.maxwellMeanSpeed) ^ 2 := by ring
        _ = _ := by rw [hOffsetTimesSpeed]
    rw [hSpeedSq] at hProductSq
    field_simp [Real.pi_ne_zero] at hProductSq
    nlinarith
  have hOffsetPositive :
      0 < meanSpeedStrikeOffsetRevolutions setup := by
    rw [hOffset, hRotationRate, hFlightDistance]
    exact div_pos (mul_pos (by norm_num) (by norm_num))
      _physical.positiveMeanSpeed
  have hOffsetLowerSq :
      (251 / 5000 : ℝ) ^ 2 <
        (meanSpeedStrikeOffsetRevolutions setup) ^ 2 := by
    rw [hOffsetSq]
    nlinarith [Real.pi_gt_d2]
  have hOffsetUpperSq :
      (meanSpeedStrikeOffsetRevolutions setup) ^ 2 <
        (2511 / 50000 : ℝ) ^ 2 := by
    rw [hOffsetSq]
    nlinarith [Real.pi_lt_d4]
  have hOffsetLower :
      (251 / 5000 : ℝ) <
        meanSpeedStrikeOffsetRevolutions setup :=
    (sq_lt_sq₀ (by norm_num) hOffsetPositive.le).mp hOffsetLowerSq
  have hOffsetUpper :
      meanSpeedStrikeOffsetRevolutions setup <
        (2511 / 50000 : ℝ) :=
    (sq_lt_sq₀ hOffsetPositive.le (by norm_num)).mp hOffsetUpperSq
  have hAgree :
      AgreesWithinRevolutions
        (meanSpeedStrikeOffsetRevolutions setup)
        (displayedOffsetRevolutions .D)
        (1 / 10 ^ 5) := by
    rw [AgreesWithinRevolutions, displayedOffsetRevolutions, abs_lt]
    norm_num at hOffsetLower hOffsetUpper ⊢
    constructor <;> linarith
  refine ⟨hOffset, ?_, ?_⟩
  · exact hAgree
  · rw [IsUniqueNearestDisplayedOffset]
    intro other hOther
    have hClose :
        |meanSpeedStrikeOffsetRevolutions setup -
            displayedOffsetRevolutions .D| <
          1 / 10 ^ 5 := hAgree
    cases other with
    | A =>
        have hFar :
            1 / 10 ^ 5 <
              |meanSpeedStrikeOffsetRevolutions setup -
                displayedOffsetRevolutions .A| := by
          rw [displayedOffsetRevolutions,
            abs_of_pos (by
              norm_num at hOffsetLower ⊢
              linarith)]
          norm_num at hOffsetLower ⊢
          linarith
        exact hClose.trans hFar
    | B =>
        have hFar :
            1 / 10 ^ 5 <
              |meanSpeedStrikeOffsetRevolutions setup -
                displayedOffsetRevolutions .B| := by
          rw [displayedOffsetRevolutions,
            abs_of_neg (by
              norm_num at hOffsetUpper ⊢
              linarith)]
          norm_num at hOffsetUpper ⊢
          linarith
        exact hClose.trans hFar
    | C =>
        have hFar :
            1 / 10 ^ 5 <
              |meanSpeedStrikeOffsetRevolutions setup -
                displayedOffsetRevolutions .C| := by
          rw [displayedOffsetRevolutions,
            abs_of_neg (by
              norm_num at hOffsetUpper ⊢
              linarith)]
          norm_num at hOffsetUpper ⊢
          linarith
        exact hClose.trans hFar
    | D =>
        exact (hOther rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0564
