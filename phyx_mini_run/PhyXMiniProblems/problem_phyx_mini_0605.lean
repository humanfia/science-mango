import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0605

open Dimension

/-!
# Carbon-monoxide bond length from its rotational spectrum

The molecule is modeled as two point masses at the ends of a massless rigid
rod.  It rotates in three dimensions about its fixed center of mass.  The
primary raster shows a sequence of nearly equally spaced absorption troughs;
calibrating its horizontal ticks as wavenumbers gives a representative spacing
of about `4 cm⁻¹`.

Masses, lengths, moment of inertia, energy, action, frequency, wavenumber, and
speed are unit-independent dimensionful quantities.  Real numbers below occur
only as named-unit readouts, plot coordinates, and displayed answer values.
In particular, the adjacent frequency separation and interatomic distance are
independent fields of the physical setup, not definitions of the answer.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- The physical dimension of a moment of inertia, `mass * length²`. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- A nonnegative, unit-independent moment of inertia. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- The physical dimension of action, equivalently energy times time. -/
def actionDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- A nonnegative ordinary frequency, with dimension inverse time. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative spectroscopic wavenumber, with dimension inverse length. -/
abbrev WavenumberQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-!
A unit-independent speed with a real carrier.  This is the exact type of
Physlib's dimensionful constant `DimSpeed.speedOfLight`.
-/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- A mass expressed as a dimensionless multiple of one atomic mass unit. -/
def massInAtomicMassUnits
    (mass atomicMassUnit : MassQuantity) : ℝ :=
  massInKilograms mass / massInKilograms atomicMassUnit

/-- Coherent-SI readout of a moment of inertia, in `kg m²`. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of an action, in joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of an energy, in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Coherent-SI readout of an ordinary frequency, in hertz. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Wavenumber readout in inverse centimeters. -/
def wavenumberInInverseCentimeters
    (wavenumber : WavenumberQuantity) : ℝ :=
  ((wavenumber
    { UnitChoices.SI with length := LengthUnit.centimeters }).val : ℝ)

/-- Coherent-SI speed readout, in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  (speed UnitChoices.SI).val

/-! ## Molecular roles and primary-spectrum vocabulary -/

/-- The two atomic sites at the ends of the massless rod. -/
inductive AtomSite where
  | carbon
  | oxygen
  deriving DecidableEq, Fintype, Repr

/-- Isotopes specified by the problem. -/
inductive IsotopeLabel where
  | carbon12
  | oxygen16
  deriving DecidableEq, Repr

/-- Mechanical model assigned to the bond joining the atoms. -/
inductive BondModel where
  | masslessRigidRod
  | other
  deriving DecidableEq, Repr

/-- Point about which the molecular system rotates. -/
inductive RotationCenter where
  | fixedCenterOfMass
  | other
  deriving DecidableEq, Repr

/-- Spatial freedom of the molecular rotation. -/
inductive RotationFreedom where
  | threeDimensional
  | planar
  deriving DecidableEq, Repr

/-- The two axes visible in image 605. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical interpretation of each plotted axis. -/
inductive SpectrumAxisQuantity where
  | rotationalWavenumber
  | relativeIntensity
  deriving DecidableEq, Repr

/-- Unit convention assigned to each plotted axis. -/
inductive SpectrumAxisUnit where
  | inverseCentimeters
  | arbitraryIntensity
  deriving DecidableEq, Repr

/-- The four numerical horizontal-axis ticks visible in the raster. -/
inductive HorizontalTick where
  | tick10
  | tick30
  | tick50
  | tick70
  deriving DecidableEq, Fintype, Repr

/-- Three consecutive central absorption troughs used for the spacing readout. -/
inductive RepresentativeSpectrumLine where
  | left
  | middle
  | right
  deriving DecidableEq, Fintype, Repr

/-!
Data carried by the supplied spectrum image.  The wavenumbers are physical
quantities; the remaining scalar fields are literal raster labels or display
features.  Frequencies are stored separately in the physical setup below.
-/
structure CarbonMonoxideSpectrumFigure where
  axisQuantity : FigureAxis → SpectrumAxisQuantity
  axisUnit : FigureAxis → SpectrumAxisUnit
  axisTextLabelPresent : FigureAxis → Bool
  horizontalTickIsVisible : HorizontalTick → Bool
  horizontalTickValue : HorizontalTick → ℝ
  troughIsVisible : RepresentativeSpectrumLine → Bool
  troughWavenumber : RepresentativeSpectrumLine → WavenumberQuantity
  traceShowsAbsorptionMinima : Bool

/-! ## Independent setup quantities -/

/-!
The physical carbon-monoxide rotor and the observables appearing in its
spectrum.  No field is defined from a displayed answer.  The line frequencies,
their common separation, the moment of inertia, and the bond length are related
only by the governing-law structures below.
-/
structure CarbonMonoxideRotorSetup where
  isotopeAt : AtomSite → IsotopeLabel
  atomMass : AtomSite → MassQuantity
  atomicMassUnit : MassQuantity
  bondModel : BondModel
  rotationCenter : RotationCenter
  rotationFreedom : RotationFreedom
  interatomicDistance : LengthQuantity
  distanceFromCenterOfMass : AtomSite → LengthQuantity
  reducedMass : MassQuantity
  momentOfInertiaAboutCenterOfMass : MomentOfInertiaQuantity
  rotationalEnergy : ℕ → DimEnergy
  adjacentTransitionFrequency : ℕ → FrequencyQuantity
  representedLowerQuantumNumber : RepresentativeSpectrumLine → ℕ
  representedLineFrequency : RepresentativeSpectrumLine → FrequencyQuantity
  adjacentLineFrequencySeparation : FrequencyQuantity
  reducedPlanckAction : ActionQuantity
  vacuumSpeedOfLight : SpeedQuantity
  spectrumFigure : CarbonMonoxideSpectrumFigure

/-! ## Scenario assumptions and figure/data readouts -/

/-- Qualitative model stated in the problem prose. -/
structure MatchesCarbonMonoxideRotorScenario
    (setup : CarbonMonoxideRotorSetup) : Prop where
  carbonIsCarbon12 : setup.isotopeAt .carbon = .carbon12
  oxygenIsOxygen16 : setup.isotopeAt .oxygen = .oxygen16
  bondIsMasslessRigidRod : setup.bondModel = .masslessRigidRod
  rotatesAboutFixedCenterOfMass :
    setup.rotationCenter = .fixedCenterOfMass
  rotationIsThreeDimensional :
    setup.rotationFreedom = .threeDimensional

/-!
Literal and calibrated readouts from image 605.  The ticks at `10`, `30`,
`50`, and `70` are visible.  Three central consecutive troughs lie, to the
precision supported by the raster, at approximately `42`, `46`, and `50 cm⁻¹`.
These are wavenumber data, not a premise about frequency separation or bond
length.
-/
structure MatchesPrimaryCarbonMonoxideSpectrum
    (setup : CarbonMonoxideRotorSetup) : Prop where
  horizontalAxisIsWavenumber :
    setup.spectrumFigure.axisQuantity .horizontal =
      .rotationalWavenumber
  verticalAxisIsRelativeIntensity :
    setup.spectrumFigure.axisQuantity .vertical = .relativeIntensity
  horizontalAxisUsesInverseCentimeters :
    setup.spectrumFigure.axisUnit .horizontal = .inverseCentimeters
  verticalAxisUsesArbitraryIntensity :
    setup.spectrumFigure.axisUnit .vertical = .arbitraryIntensity
  axesHaveNoVisibleTextLabels :
    ∀ axis, setup.spectrumFigure.axisTextLabelPresent axis = false
  everyNamedTickVisible :
    ∀ tick, setup.spectrumFigure.horizontalTickIsVisible tick = true
  tick10Value : setup.spectrumFigure.horizontalTickValue .tick10 = 10
  tick30Value : setup.spectrumFigure.horizontalTickValue .tick30 = 30
  tick50Value : setup.spectrumFigure.horizontalTickValue .tick50 = 50
  tick70Value : setup.spectrumFigure.horizontalTickValue .tick70 = 70
  everyRepresentativeTroughVisible :
    ∀ line, setup.spectrumFigure.troughIsVisible line = true
  traceHasAbsorptionMinima :
    setup.spectrumFigure.traceShowsAbsorptionMinima = true
  leftTroughInverseCentimeters :
    wavenumberInInverseCentimeters
        (setup.spectrumFigure.troughWavenumber .left) = 42
  middleTroughInverseCentimeters :
    wavenumberInInverseCentimeters
        (setup.spectrumFigure.troughWavenumber .middle) = 46
  rightTroughInverseCentimeters :
    wavenumberInInverseCentimeters
        (setup.spectrumFigure.troughWavenumber .right) = 50

/-!
Looked-up isotope data and calibrated universal constants.  Physlib grounds
the reduced Planck constant `Constants.ℏ` and the dimensionful speed of light
`DimSpeed.speedOfLight`.  No target separation or bond length occurs here.
-/
structure UsesCarbonMonoxideReferenceData
    (setup : CarbonMonoxideRotorSetup) : Prop where
  atomicMassUnitKilograms :
    massInKilograms setup.atomicMassUnit = 1.66053906660e-27
  carbon12MassAtomicMassUnits :
    massInAtomicMassUnits
        (setup.atomMass .carbon) setup.atomicMassUnit = 12
  oxygen16MassAtomicMassUnits :
    massInAtomicMassUnits
        (setup.atomMass .oxygen) setup.atomicMassUnit = 15.99491461957
  reducedPlanckActionJouleSeconds :
    actionInJouleSeconds setup.reducedPlanckAction =
      (Constants.ℏ : ℝ)
  standardSpeedOfLight :
    speedInMetersPerSecond setup.vacuumSpeedOfLight =
      speedInMetersPerSecond DimSpeed.speedOfLight

/-- Positivity and nondegeneracy conditions selecting the physical branch. -/
structure HasPhysicalCarbonMonoxideParameters
    (setup : CarbonMonoxideRotorSetup) : Prop where
  atomMassesPositive :
    ∀ site, 0 < massInKilograms (setup.atomMass site)
  atomicMassUnitPositive : 0 < massInKilograms setup.atomicMassUnit
  interatomicDistancePositive :
    0 < lengthInMeters setup.interatomicDistance
  centerOfMassDistancesPositive :
    ∀ site, 0 < lengthInMeters (setup.distanceFromCenterOfMass site)
  reducedMassPositive : 0 < massInKilograms setup.reducedMass
  momentOfInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.momentOfInertiaAboutCenterOfMass
  rotationalEnergiesNonnegative :
    ∀ angularMomentum, 0 ≤ energyInJoules
      (setup.rotationalEnergy angularMomentum)
  transitionFrequenciesPositive :
    ∀ angularMomentum, 0 < frequencyInHertz
      (setup.adjacentTransitionFrequency angularMomentum)
  lineSeparationPositive :
    0 < frequencyInHertz setup.adjacentLineFrequencySeparation
  reducedPlanckActionPositive :
    0 < actionInJouleSeconds setup.reducedPlanckAction
  speedOfLightPositive :
    0 < speedInMetersPerSecond setup.vacuumSpeedOfLight

/-! ## Governing geometry and rigid-rotor laws -/

/-!
Center-of-mass geometry for two point masses on opposite ends of the rod.  The
two lever arms add to the interatomic distance and their mass moments balance.
-/
structure SatisfiesTwoBodyCenterOfMassGeometry
    (setup : CarbonMonoxideRotorSetup) : Prop where
  leverArmsSpanBond :
    lengthInMeters (setup.distanceFromCenterOfMass .carbon) +
        lengthInMeters (setup.distanceFromCenterOfMass .oxygen) =
      lengthInMeters setup.interatomicDistance
  centerOfMassBalance :
    massInKilograms (setup.atomMass .carbon) *
        lengthInMeters (setup.distanceFromCenterOfMass .carbon) =
      massInKilograms (setup.atomMass .oxygen) *
        lengthInMeters (setup.distanceFromCenterOfMass .oxygen)

/-!
Rigid-rotor and spectrometer laws:

* `I = m_C r_C² + m_O r_O²`;
* `μ (m_C + m_O) = m_C m_O`;
* `E_l = ℏ² l(l+1)/(2I)`;
* `h ν_l = E_{l+1} - E_l`, with `h = 2πℏ`;
* the three representative troughs are consecutive rotor transitions;
* `ν = c` times wavenumber, including `100 m⁻¹` per `cm⁻¹`; and
* the independent separation observable is the difference of adjacent lines.

These are general physical and calibration relations.  None inserts a numeric
frequency separation or interatomic distance.
-/
structure SatisfiesCarbonMonoxideRigidRotorLaws
    (setup : CarbonMonoxideRotorSetup) : Prop where
  pointMassMomentOfInertia :
    momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutCenterOfMass =
      massInKilograms (setup.atomMass .carbon) *
          lengthInMeters (setup.distanceFromCenterOfMass .carbon) ^ 2 +
        massInKilograms (setup.atomMass .oxygen) *
          lengthInMeters (setup.distanceFromCenterOfMass .oxygen) ^ 2
  reducedMassRelation :
    massInKilograms setup.reducedMass *
        (massInKilograms (setup.atomMass .carbon) +
          massInKilograms (setup.atomMass .oxygen)) =
      massInKilograms (setup.atomMass .carbon) *
        massInKilograms (setup.atomMass .oxygen)
  rigidRotorSpectrum : ∀ angularMomentum : ℕ,
    energyInJoules (setup.rotationalEnergy angularMomentum) =
      actionInJouleSeconds setup.reducedPlanckAction ^ 2 *
          (angularMomentum : ℝ) * ((angularMomentum : ℝ) + 1) /
        (2 * momentOfInertiaInKilogramMetersSquared
          setup.momentOfInertiaAboutCenterOfMass)
  transitionEnergyFrequency : ∀ angularMomentum : ℕ,
    2 * Real.pi * actionInJouleSeconds setup.reducedPlanckAction *
        frequencyInHertz
          (setup.adjacentTransitionFrequency angularMomentum) =
      energyInJoules (setup.rotationalEnergy (angularMomentum + 1)) -
        energyInJoules (setup.rotationalEnergy angularMomentum)
  representedLineIsRotorTransition : ∀ line,
    frequencyInHertz (setup.representedLineFrequency line) =
      frequencyInHertz
        (setup.adjacentTransitionFrequency
          (setup.representedLowerQuantumNumber line))
  representativeLinesAreConsecutive :
    setup.representedLowerQuantumNumber .middle =
        setup.representedLowerQuantumNumber .left + 1 ∧
      setup.representedLowerQuantumNumber .right =
        setup.representedLowerQuantumNumber .middle + 1
  spectrometerWavenumberCalibration : ∀ line,
    frequencyInHertz (setup.representedLineFrequency line) =
      speedInMetersPerSecond setup.vacuumSpeedOfLight * 100 *
        wavenumberInInverseCentimeters
          (setup.spectrumFigure.troughWavenumber line)
  adjacentSeparationFromRepresentativeLines :
    frequencyInHertz setup.adjacentLineFrequencySeparation =
        frequencyInHertz (setup.representedLineFrequency .middle) -
          frequencyInHertz (setup.representedLineFrequency .left) ∧
      frequencyInHertz setup.adjacentLineFrequencySeparation =
        frequencyInHertz (setup.representedLineFrequency .right) -
          frequencyInHertz (setup.representedLineFrequency .middle)

/-! ## Derived relations and answer semantics -/

/-- The calibrated central troughs are separated by `4 cm⁻¹`. -/
lemma representativeWavenumberSpacing_eq_four
    (setup : CarbonMonoxideRotorSetup)
    (_figure : MatchesPrimaryCarbonMonoxideSpectrum setup) :
    wavenumberInInverseCentimeters
          (setup.spectrumFigure.troughWavenumber .middle) -
        wavenumberInInverseCentimeters
          (setup.spectrumFigure.troughWavenumber .left) = 4 ∧
      wavenumberInInverseCentimeters
          (setup.spectrumFigure.troughWavenumber .right) -
        wavenumberInInverseCentimeters
          (setup.spectrumFigure.troughWavenumber .middle) = 4 := by
  constructor
  · rw [_figure.middleTroughInverseCentimeters,
      _figure.leftTroughInverseCentimeters]
    norm_num
  · rw [_figure.rightTroughInverseCentimeters,
      _figure.middleTroughInverseCentimeters]
    norm_num

/-!
For two point masses at their common center of mass, the point-mass inertia
reduces to `I = μ a²`.
-/
lemma momentOfInertia_eq_reducedMass_mul_bondLength_sq
    (setup : CarbonMonoxideRotorSetup)
    (_physical : HasPhysicalCarbonMonoxideParameters setup)
    (_geometry : SatisfiesTwoBodyCenterOfMassGeometry setup)
    (_laws : SatisfiesCarbonMonoxideRigidRotorLaws setup) :
    momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutCenterOfMass =
      massInKilograms setup.reducedMass *
        lengthInMeters setup.interatomicDistance ^ 2 := by
  let mC := massInKilograms (setup.atomMass .carbon)
  let mO := massInKilograms (setup.atomMass .oxygen)
  let rC := lengthInMeters (setup.distanceFromCenterOfMass .carbon)
  let rO := lengthInMeters (setup.distanceFromCenterOfMass .oxygen)
  let a := lengthInMeters setup.interatomicDistance
  let μ := massInKilograms setup.reducedMass
  let I := momentOfInertiaInKilogramMetersSquared
    setup.momentOfInertiaAboutCenterOfMass
  have hmC : 0 < mC := _physical.atomMassesPositive .carbon
  have hmO : 0 < mO := _physical.atomMassesPositive .oxygen
  have hsum : 0 < mC + mO := add_pos hmC hmO
  have hspan : rC + rO = a := _geometry.leverArmsSpanBond
  have hbalance : mC * rC = mO * rO := _geometry.centerOfMassBalance
  have hreduced : μ * (mC + mO) = mC * mO :=
    _laws.reducedMassRelation
  have hinertia : I = mC * rC ^ 2 + mO * rO ^ 2 :=
    _laws.pointMassMomentOfInertia
  have hscaled : I * (mC + mO) = μ * a ^ 2 * (mC + mO) := by
    rw [hinertia]
    calc
      (mC * rC ^ 2 + mO * rO ^ 2) * (mC + mO) =
          (mC * rC) ^ 2 + (mO * rO) ^ 2 +
            mC * mO * (rC ^ 2 + rO ^ 2) := by ring
      _ = 2 * (mC * rC) * (mO * rO) +
            mC * mO * (rC ^ 2 + rO ^ 2) := by
              rw [hbalance]
              ring
      _ = mC * mO * (rC + rO) ^ 2 := by ring
      _ = mC * mO * a ^ 2 := by rw [hspan]
      _ = μ * a ^ 2 * (mC + mO) := by rw [← hreduced]; ring
  have hzero : (I - μ * a ^ 2) * (mC + mO) = 0 := by
    nlinarith [hscaled]
  have hsum_ne : mC + mO ≠ 0 := ne_of_gt hsum
  have hmain : I - μ * a ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_right hsum_ne
  exact sub_eq_zero.mp hmain

/-!
The figure-derived adjacent-line separation agrees with
`1.20 × 10¹¹ Hz` to within `10⁹ Hz`.
-/
def AgreesWithFigureFrequencySeparation
    (setup : CarbonMonoxideRotorSetup) : Prop :=
  |frequencyInHertz setup.adjacentLineFrequencySeparation - 1.20e11| < 1e9

/-- The calibrated spectrum determines the stated hertz-scale separation. -/
lemma adjacentFrequencySeparation_agrees_with_figure
    (setup : CarbonMonoxideRotorSetup)
    (_figure : MatchesPrimaryCarbonMonoxideSpectrum setup)
    (_reference : UsesCarbonMonoxideReferenceData setup)
    (_laws : SatisfiesCarbonMonoxideRigidRotorLaws setup) :
    AgreesWithFigureFrequencySeparation setup := by
  have hc :
      speedInMetersPerSecond setup.vacuumSpeedOfLight = 299792458 := by
    calc
      speedInMetersPerSecond setup.vacuumSpeedOfLight =
          speedInMetersPerSecond DimSpeed.speedOfLight :=
        _reference.standardSpeedOfLight
      _ = 299792458 := by simp [speedInMetersPerSecond]
  unfold AgreesWithFigureFrequencySeparation
  rw [_laws.adjacentSeparationFromRepresentativeLines.1,
    _laws.spectrometerWavenumberCalibration .middle,
    _laws.spectrometerWavenumberCalibration .left,
    _figure.middleTroughInverseCentimeters,
    _figure.leftTroughInverseCentimeters, hc]
  norm_num [abs_of_nonpos]

/-- Labels of the four interatomic-distance choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Bond length printed beside an answer choice, in metres. -/
def AnswerChoice.bondLengthMeters : AnswerChoice → ℝ
  | .A => 1.6e-10
  | .B => 2.2e-10
  | .C => 1.1e-10
  | .D => 7.5e-11

/-- Dataset metadata records choice C; this is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Absolute error between the physical bond length and a displayed choice. -/
def answerChoiceErrorMeters
    (setup : CarbonMonoxideRotorSetup) (choice : AnswerChoice) : ℝ :=
  |lengthInMeters setup.interatomicDistance - choice.bondLengthMeters|

/-!
Agreement at the precision of the displayed two-significant-figure bond
length, allowing `5 × 10⁻¹² m` for graph and isotope-mass readout precision.
-/
def AgreesWithDisplayedBondLength
    (setup : CarbonMonoxideRotorSetup) (choice : AnswerChoice) : Prop :=
  answerChoiceErrorMeters setup choice < 5e-12

/-- A choice is strictly closer than every other displayed bond length. -/
def IsUniqueClosestBondLengthChoice
    (setup : CarbonMonoxideRotorSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    answerChoiceErrorMeters setup choice <
      answerChoiceErrorMeters setup other

/-!
The approximately `4 cm⁻¹` trough spacing corresponds to about
`1.20 × 10¹¹ Hz`.  Combining the rigid-rotor spectrum with the looked-up
`¹²C` and `¹⁶O` masses gives an interatomic distance agreeing with
`1.1 × 10⁻¹⁰ m`, uniquely selecting choice C.

Blueprint: `thm:physics:phyx_mini_0605:target`.
-/
theorem carbonMonoxideSpectrum_determines_frequencySeparation_and_choiceC
    (setup : CarbonMonoxideRotorSetup)
    (_scenario : MatchesCarbonMonoxideRotorScenario setup)
    (_figure : MatchesPrimaryCarbonMonoxideSpectrum setup)
    (_reference : UsesCarbonMonoxideReferenceData setup)
    (_physical : HasPhysicalCarbonMonoxideParameters setup)
    (_geometry : SatisfiesTwoBodyCenterOfMassGeometry setup)
    (_laws : SatisfiesCarbonMonoxideRigidRotorLaws setup) :
    AgreesWithFigureFrequencySeparation setup ∧
      AgreesWithDisplayedBondLength setup .C ∧
        IsUniqueClosestBondLengthChoice setup .C := by
  let a := lengthInMeters setup.interatomicDistance
  let u := massInKilograms setup.atomicMassUnit
  let mC := massInKilograms (setup.atomMass .carbon)
  let mO := massInKilograms (setup.atomMass .oxygen)
  let μ := massInKilograms setup.reducedMass
  let I := momentOfInertiaInKilogramMetersSquared
    setup.momentOfInertiaAboutCenterOfMass
  let ℏr := actionInJouleSeconds setup.reducedPlanckAction
  let Δν := frequencyInHertz setup.adjacentLineFrequencySeparation
  have ha_pos : 0 < a := _physical.interatomicDistancePositive
  have hu_pos : 0 < u := _physical.atomicMassUnitPositive
  have hmC_pos : 0 < mC := _physical.atomMassesPositive .carbon
  have hmO_pos : 0 < mO := _physical.atomMassesPositive .oxygen
  have hμ_pos : 0 < μ := _physical.reducedMassPositive
  have hI_pos : 0 < I := _physical.momentOfInertiaPositive
  have hℏ_pos : 0 < ℏr := _physical.reducedPlanckActionPositive
  have hu : u = 1.66053906660e-27 :=
    _reference.atomicMassUnitKilograms
  have hmC_div : mC / u = 12 :=
    _reference.carbon12MassAtomicMassUnits
  have hmO_div : mO / u = 15.99491461957 :=
    _reference.oxygen16MassAtomicMassUnits
  have hu_ne : u ≠ 0 := ne_of_gt hu_pos
  have hmC : mC = 12 * u := (div_eq_iff hu_ne).mp hmC_div
  have hmO : mO = 15.99491461957 * u :=
    (div_eq_iff hu_ne).mp hmO_div
  have hmassSum_ne : mC + mO ≠ 0 :=
    ne_of_gt (add_pos hmC_pos hmO_pos)
  have hμ_relation : μ * (mC + mO) = mC * mO :=
    _laws.reducedMassRelation
  have hμ :
      μ = mC * mO / (mC + mO) :=
    (eq_div_iff hmassSum_ne).2 hμ_relation
  have hμ_num := hμ
  rw [hmC, hmO, hu] at hμ_num
  norm_num at hμ_num
  have hI : I = μ * a ^ 2 :=
    momentOfInertia_eq_reducedMass_mul_bondLength_sq
      setup _physical _geometry _laws
  have hc :
      speedInMetersPerSecond setup.vacuumSpeedOfLight = 299792458 := by
    calc
      speedInMetersPerSecond setup.vacuumSpeedOfLight =
          speedInMetersPerSecond DimSpeed.speedOfLight :=
        _reference.standardSpeedOfLight
      _ = 299792458 := by simp [speedInMetersPerSecond]
  have hΔν : Δν = 119916983200 := by
    calc
      Δν =
          frequencyInHertz (setup.representedLineFrequency .middle) -
            frequencyInHertz (setup.representedLineFrequency .left) :=
        _laws.adjacentSeparationFromRepresentativeLines.1
      _ =
          speedInMetersPerSecond setup.vacuumSpeedOfLight * 100 *
              wavenumberInInverseCentimeters
                (setup.spectrumFigure.troughWavenumber .middle) -
            speedInMetersPerSecond setup.vacuumSpeedOfLight * 100 *
              wavenumberInInverseCentimeters
                (setup.spectrumFigure.troughWavenumber .left) := by
          rw [_laws.spectrometerWavenumberCalibration .middle,
            _laws.spectrometerWavenumberCalibration .left]
      _ = 119916983200 := by
        rw [_figure.middleTroughInverseCentimeters,
          _figure.leftTroughInverseCentimeters, hc]
        norm_num
  have hℏ : ℏr = 1.054571817e-34 := by
    calc
      ℏr = (Constants.ℏ : ℝ) :=
        _reference.reducedPlanckActionJouleSeconds
      _ = 1.054571817e-34 := rfl
  have htransition (angularMomentum : ℕ) :
      2 * Real.pi * ℏr * I *
          frequencyInHertz
            (setup.adjacentTransitionFrequency angularMomentum) =
        ℏr ^ 2 * ((angularMomentum : ℝ) + 1) := by
    have henergy := _laws.transitionEnergyFrequency angularMomentum
    rw [_laws.rigidRotorSpectrum (angularMomentum + 1),
      _laws.rigidRotorSpectrum angularMomentum] at henergy
    have hI_ne :
        momentOfInertiaInKilogramMetersSquared
            setup.momentOfInertiaAboutCenterOfMass ≠ 0 :=
      ne_of_gt _physical.momentOfInertiaPositive
    field_simp [hI_ne] at henergy
    norm_num [Nat.cast_add, Nat.cast_one] at henergy
    nlinarith only [henergy]
  let n := setup.representedLowerQuantumNumber .left
  have hnMiddle :
      setup.representedLowerQuantumNumber .middle = n + 1 :=
    _laws.representativeLinesAreConsecutive.1
  have hΔν_transition :
      Δν =
        frequencyInHertz (setup.adjacentTransitionFrequency (n + 1)) -
          frequencyInHertz (setup.adjacentTransitionFrequency n) := by
    change
      frequencyInHertz setup.adjacentLineFrequencySeparation =
        frequencyInHertz (setup.adjacentTransitionFrequency (n + 1)) -
          frequencyInHertz (setup.adjacentTransitionFrequency n)
    rw [_laws.adjacentSeparationFromRepresentativeLines.1,
      _laws.representedLineIsRotorTransition .middle,
      _laws.representedLineIsRotorTransition .left, hnMiddle]
  have htransition_left := htransition n
  have htransition_middle := htransition (n + 1)
  norm_num [Nat.cast_add, Nat.cast_one] at htransition_middle
  have htransition_difference :
      2 * Real.pi * ℏr * I *
          (frequencyInHertz
              (setup.adjacentTransitionFrequency (n + 1)) -
            frequencyInHertz
              (setup.adjacentTransitionFrequency n)) =
        ℏr ^ 2 := by
    nlinarith only [htransition_left, htransition_middle]
  have hrotor :
      2 * Real.pi * ℏr * I * Δν = ℏr ^ 2 := by
    rw [hΔν_transition]
    exact htransition_difference
  have hcancel :
      ℏr * (2 * Real.pi * I * Δν - ℏr) = 0 := by
    nlinarith only [hrotor]
  have hrotor_reduced :
      2 * Real.pi * I * Δν = ℏr := by
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hcancel).resolve_left (ne_of_gt hℏ_pos))
  rw [hI, hμ_num, hΔν, hℏ] at hrotor_reduced
  have hlow_sq : (1.05e-10 : ℝ) ^ 2 < a ^ 2 := by
    by_contra hnot
    have hsq_le : a ^ 2 ≤ (1.05e-10 : ℝ) ^ 2 :=
      le_of_not_gt hnot
    have hmul_le :
        Real.pi * a ^ 2 ≤ Real.pi * (1.05e-10 : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq_le Real.pi_pos.le
    have hmul_lt :
        Real.pi * (1.05e-10 : ℝ) ^ 2 <
          3.15 * (1.05e-10 : ℝ) ^ 2 :=
      mul_lt_mul_of_pos_right Real.pi_lt_d2 (by norm_num)
    nlinarith only [hrotor_reduced, hmul_le, hmul_lt]
  have hupp_sq : a ^ 2 < (1.15e-10 : ℝ) ^ 2 := by
    by_contra hnot
    have hsq_le : (1.15e-10 : ℝ) ^ 2 ≤ a ^ 2 :=
      le_of_not_gt hnot
    have hmul_le :
        Real.pi * (1.15e-10 : ℝ) ^ 2 ≤ Real.pi * a ^ 2 :=
      mul_le_mul_of_nonneg_left hsq_le Real.pi_pos.le
    have hmul_lt :
        3.14 * (1.15e-10 : ℝ) ^ 2 <
          Real.pi * (1.15e-10 : ℝ) ^ 2 :=
      mul_lt_mul_of_pos_right Real.pi_gt_d2 (by norm_num)
    nlinarith only [hrotor_reduced, hmul_le, hmul_lt]
  have ha_low : (1.05e-10 : ℝ) < a := by
    nlinarith only [hlow_sq, ha_pos]
  have ha_upp : a < (1.15e-10 : ℝ) := by
    nlinarith only [hupp_sq, ha_pos]
  have hchoiceC : AgreesWithDisplayedBondLength setup .C := by
    unfold AgreesWithDisplayedBondLength answerChoiceErrorMeters
    change |a - 1.1e-10| < 5e-12
    rw [abs_lt]
    constructor <;> nlinarith only [ha_low, ha_upp]
  refine ⟨adjacentFrequencySeparation_agrees_with_figure
    setup _figure _reference _laws, hchoiceC, ?_⟩
  intro other hother
  cases other with
  | A =>
      change |a - 1.1e-10| < |a - 1.6e-10|
      have hAabs :
          |a - 1.6e-10| = 1.6e-10 - a := by
        rw [abs_of_nonpos (by nlinarith only [ha_upp])]
        ring
      rw [hAabs]
      have hC := hchoiceC
      unfold AgreesWithDisplayedBondLength answerChoiceErrorMeters at hC
      change |a - 1.1e-10| < 5e-12 at hC
      nlinarith only [hC, ha_upp]
  | B =>
      change |a - 1.1e-10| < |a - 2.2e-10|
      have hBabs :
          |a - 2.2e-10| = 2.2e-10 - a := by
        rw [abs_of_nonpos (by nlinarith only [ha_upp])]
        ring
      rw [hBabs]
      have hC := hchoiceC
      unfold AgreesWithDisplayedBondLength answerChoiceErrorMeters at hC
      change |a - 1.1e-10| < 5e-12 at hC
      nlinarith only [hC, ha_upp]
  | C =>
      exact (hother rfl).elim
  | D =>
      change |a - 1.1e-10| < |a - 7.5e-11|
      have hDabs :
          |a - 7.5e-11| = a - 7.5e-11 := by
        rw [abs_of_nonneg (by nlinarith only [ha_low])]
      rw [hDabs]
      have hC := hchoiceC
      unfold AgreesWithDisplayedBondLength answerChoiceErrorMeters at hC
      change |a - 1.1e-10| < 5e-12 at hC
      nlinarith only [hC, ha_low]

end PhyXMiniProblems.ProblemPhyXMini0605
