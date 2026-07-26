import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Area

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0932

open Dimension

/-!
# Crank frequency of a semicircular-loop tent-light generator

A single semicircular conductor of radius `5.0 cm` rotates about its diameter
between pole tips separated by `10 cm`.  The uniform magnetic flux density is
`0.20 T`.  The generator drives a `1.0 Ω`, `4.0 W` bulb, and the question asks
for the crank frequency at which the *peak* current supplies the rated power.

Physical magnitudes are unit-independent Physlib `Dimensionful` quantities.
Real numbers occur only as explicitly named coherent-SI readouts, numerical
answer choices, and dimensionless constants.

Assumption/target split:

* governing laws: semicircle area, uniform-field flux amplitude,
  `ω = 2 π f`, the peak form of Faraday's law, Ohm's law, and Joule heating;
* previous-part results: none;
* figure/data readouts: radius `5.0 cm`, pole-tip gap `10 cm`, field `0.20 T`,
  bulb resistance `1.0 Ω`, bulb rating `4.0 W`, and the qualitative labels and
  geometry visible in image `932.png`;
* current target conclusions: the exact frequency `4000 / π² Hz` and its
  agreement, to the displayed two-significant-figure precision, with answer B
  (`4.1 × 10² Hz`).

Neither target conclusion occurs in a premise structure or setup definition.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The dimension `M T⁻¹ C⁻¹` of magnetic flux density (tesla). -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L² T⁻¹ C⁻¹` of magnetic flux (weber). -/
def magneticFluxDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L² T⁻² C⁻¹` of electromotive force (volt). -/
def electromotiveForceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `C T⁻¹` of electric current (ampere). -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- The dimension `M L² T⁻¹ C⁻²` of electrical resistance (ohm). -/
def electricalResistanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L² T⁻³` of power (watt). -/
def powerDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaMagnitude : Type := DimArea

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux amplitude. -/
abbrev MagneticFluxMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDimension NNReal)

/-- A nonnegative ordinary or angular frequency, of inverse-time dimension. -/
abbrev FrequencyMagnitude : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative, unit-independent electromotive-force magnitude. -/
abbrev ElectromotiveForceMagnitude : Type :=
  Dimensionful (WithDim electromotiveForceDimension NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent rate of energy transfer. -/
abbrev PowerMagnitude : Type :=
  Dimensionful (WithDim powerDimension NNReal)

/-- Coherent-SI readout of length, in metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of area, in square metres. -/
def areaInSquareMeters (area : AreaMagnitude) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of magnetic flux density, in teslas. -/
def magneticFluxDensityInTeslas
    (fieldMagnitude : MagneticFluxDensityMagnitude) : ℝ :=
  ((fieldMagnitude UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of magnetic flux, in webers. -/
def magneticFluxInWebers (flux : MagneticFluxMagnitude) : ℝ :=
  ((flux UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of ordinary frequency, in hertz. -/
def frequencyInHertz (frequency : FrequencyMagnitude) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of angular frequency, in radians per second. -/
def angularFrequencyInRadiansPerSecond
    (angularFrequency : FrequencyMagnitude) : ℝ :=
  ((angularFrequency UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of electromotive force, in volts. -/
def electromotiveForceInVolts
    (emf : ElectromotiveForceMagnitude) : ℝ :=
  ((emf UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of electric current, in amperes. -/
def electricCurrentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  ((current UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of electrical resistance, in ohms. -/
def resistanceInOhms (resistance : ResistanceMagnitude) : ℝ :=
  ((resistance UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of power, in watts. -/
def powerInWatts (power : PowerMagnitude) : ℝ :=
  ((power UnitChoices.SI).val : ℝ)

/-! ## Apparatus and labels from the primary figure -/

/-- Physical components visibly present in image `932.png`. -/
inductive FigureObject where
  | semicircularConductor
  | leftAxle
  | rightAxle
  | crank
  | bulb
  | magneticFieldRegion
  | connectingWire
  deriving DecidableEq, Fintype, Repr

/-- Textual or symbolic labels printed in image `932.png`. -/
inductive FigureLabel where
  | radiusFiveCentimeters
  | fieldZeroPointTwoTeslas
  | bulbOneOhmFourWatts
  | crank
  deriving DecidableEq, Fintype, Repr

/-- The dot glyph in the figure denotes a field directed out of the page. -/
inductive NormalFieldGlyph where
  | dot
  | cross
  deriving DecidableEq, Repr

/-- Named directions needed to transcribe the supplied front-view figure. -/
inductive DiagramDirection where
  | left
  | right
  | upward
  | downward
  | intoPage
  | outOfPage
  deriving DecidableEq, Repr

/-- The rotation axis selected by the two axle points in the diagram. -/
inductive LoopRotationAxis where
  | diameterThroughEndpoints
  | other
  deriving DecidableEq, Repr

/-- The conducting geometry idealized by this school-physics model. -/
inductive GeneratorConductorModel where
  | singleSemicircularLoop
  | other
  deriving DecidableEq, Repr

/-!
Typed presentation data copied from the primary raster.  It contains no crank
frequency or answer-choice value.
-/
structure SemicircularGeneratorFigure where
  objectShown : FigureObject → Bool
  labelShown : FigureLabel → Bool
  magneticFieldGlyph : NormalFieldGlyph
  magneticFieldDirection : DiagramDirection
  rotationAxis : LoopRotationAxis
  semicircularArcLiesInPageAtReference : Bool
  radiusGuideRunsFromCenterToArc : Bool
  crankAttachedToRightAxle : Bool
  bulbConnectedInSeries : Bool
  rotationArrowsShownAtBothAxles : Bool

/-!
Independent physical quantities describing the generator and bulb.  The crank
frequency is an unknown observable, not a definition made from the requested
answer.  Peak emf, current, flux, and power are likewise independent fields
related only by the law predicates below.
-/
structure SemicircularGeneratorSetup where
  conductorModel : GeneratorConductorModel
  magneticField : Electromagnetism.MagneticField 3
  uniformFieldRegion : Set (Time × Space 3)
  semicircularArcAt : Time → Set (Space 3)
  poleTipSeparation : LengthMagnitude
  loopRadius : LengthMagnitude
  loopArea : AreaMagnitude
  magneticFluxDensityMagnitude : MagneticFluxDensityMagnitude
  magneticFluxAmplitude : MagneticFluxMagnitude
  crankFrequency : FrequencyMagnitude
  angularFrequency : FrequencyMagnitude
  peakInducedEmf : ElectromotiveForceMagnitude
  peakInducedCurrent : ElectricCurrentMagnitude
  totalCircuitResistance : ResistanceMagnitude
  bulbResistance : ResistanceMagnitude
  bulbRatedPower : PowerMagnitude
  peakBulbPower : PowerMagnitude
  figure : SemicircularGeneratorFigure

/-! ## Scenario, data readouts, and governing laws -/

/-!
Numerical prose data and literal qualitative evidence from image `932.png`.
The unknown crank frequency and all equivalent formulas for it are absent.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : SemicircularGeneratorSetup) : Prop where
  conductorIsSingleSemicircularLoop :
    setup.conductorModel = .singleSemicircularLoop
  everyObjectShown : ∀ object, setup.figure.objectShown object = true
  everyLabelShown : ∀ label, setup.figure.labelShown label = true
  fieldUsesDots : setup.figure.magneticFieldGlyph = .dot
  fieldPointsOutOfPage :
    setup.figure.magneticFieldDirection = .outOfPage
  axisIsSemicircleDiameter :
    setup.figure.rotationAxis = .diameterThroughEndpoints
  arcInitiallyLiesInPage :
    setup.figure.semicircularArcLiesInPageAtReference = true
  radiusGuideIsShownCorrectly :
    setup.figure.radiusGuideRunsFromCenterToArc = true
  crankIsOnRight : setup.figure.crankAttachedToRightAxle = true
  bulbIsInSeries : setup.figure.bulbConnectedInSeries = true
  rotationArrowsAtBothEnds :
    setup.figure.rotationArrowsShownAtBothAxles = true
  poleTipSeparationMeters : lengthInMeters setup.poleTipSeparation = 1 / 10
  loopRadiusMeters : lengthInMeters setup.loopRadius = 1 / 20
  diameterSpansPoleTipGap :
    lengthInMeters setup.poleTipSeparation =
      2 * lengthInMeters setup.loopRadius
  magneticFluxDensityTeslas :
    magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude = 1 / 5
  bulbResistanceOhms : resistanceInOhms setup.bulbResistance = 1
  bulbRatedPowerWatts : powerInWatts setup.bulbRatedPower = 4

/-- Positivity and nondegeneracy conditions for the operating generator. -/
structure HasPhysicalGeneratorParameters
    (setup : SemicircularGeneratorSetup) : Prop where
  poleTipSeparationPositive : 0 < lengthInMeters setup.poleTipSeparation
  loopRadiusPositive : 0 < lengthInMeters setup.loopRadius
  loopAreaPositive : 0 < areaInSquareMeters setup.loopArea
  magneticFieldPositive :
    0 < magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  magneticFluxAmplitudePositive :
    0 < magneticFluxInWebers setup.magneticFluxAmplitude
  crankFrequencyPositive : 0 < frequencyInHertz setup.crankFrequency
  angularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond setup.angularFrequency
  peakEmfPositive : 0 < electromotiveForceInVolts setup.peakInducedEmf
  peakCurrentPositive :
    0 < electricCurrentInAmperes setup.peakInducedCurrent
  totalResistancePositive : 0 < resistanceInOhms setup.totalCircuitResistance
  bulbResistancePositive : 0 < resistanceInOhms setup.bulbResistance
  ratedPowerPositive : 0 < powerInWatts setup.bulbRatedPower
  uniformFieldRegionNonempty : setup.uniformFieldRegion.Nonempty

/-!
The physical field is uniform in magnitude over the region between the pole
tips, and the rotating semicircular conductor remains in that active region.
-/
structure ModelsUniformFieldAcrossRotatingLoop
    (setup : SemicircularGeneratorSetup) : Prop where
  arcInsideUniformField : ∀ time,
    setup.semicircularArcAt time ⊆
      {position | (time, position) ∈ setup.uniformFieldRegion}
  uniformMagnitude : ∀ time position,
    (time, position) ∈ setup.uniformFieldRegion →
      ‖setup.magneticField time position‖ =
        magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude

/-! The area enclosed by a semicircle of radius `r` is `π r² / 2`. -/
structure SatisfiesSemicircularLoopGeometry
    (setup : SemicircularGeneratorSetup) : Prop where
  semicircleAreaLaw :
    areaInSquareMeters setup.loopArea =
      Real.pi * lengthInMeters setup.loopRadius ^ 2 / 2

/-! Uniform crank rotation relates angular and ordinary frequency by `ω=2πf`. -/
structure SatisfiesUniformCrankRotation
    (setup : SemicircularGeneratorSetup) : Prop where
  angularFrequencyLaw :
    angularFrequencyInRadiansPerSecond setup.angularFrequency =
      2 * Real.pi * frequencyInHertz setup.crankFrequency

/-!
For the single rotating semicircular loop, the flux amplitude is `B A`, and
the peak form of Faraday's law is `E_max = Φ_max ω`.  These are generic
generator laws and do not state a numerical crank frequency.
-/
structure SatisfiesRotatingLoopFaradayLaw
    (setup : SemicircularGeneratorSetup) : Prop where
  magneticFluxAmplitudeLaw :
    magneticFluxInWebers setup.magneticFluxAmplitude =
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
        areaInSquareMeters setup.loopArea
  peakFaradayLaw :
    electromotiveForceInVolts setup.peakInducedEmf =
      magneticFluxInWebers setup.magneticFluxAmplitude *
        angularFrequencyInRadiansPerSecond setup.angularFrequency

/-!
The bulb is the only appreciable resistance.  At the requested operating
point, Ohm's law and Joule heating make the peak bulb power equal its rating.
-/
structure SatisfiesRatedResistiveBulbCircuit
    (setup : SemicircularGeneratorSetup) : Prop where
  negligibleOtherResistance :
    resistanceInOhms setup.totalCircuitResistance =
      resistanceInOhms setup.bulbResistance
  peakOhmsLaw :
    electromotiveForceInVolts setup.peakInducedEmf =
      electricCurrentInAmperes setup.peakInducedCurrent *
        resistanceInOhms setup.totalCircuitResistance
  peakJoulePowerLaw :
    powerInWatts setup.peakBulbPower =
      electricCurrentInAmperes setup.peakInducedCurrent ^ 2 *
        resistanceInOhms setup.bulbResistance
  fullyLitAtPeak :
    powerInWatts setup.peakBulbPower = powerInWatts setup.bulbRatedPower

/-!
The exact school-physics result before answer-choice rounding is
`4000 / π² Hz`.
-/
lemma requiredCrankFrequency_exact
    (setup : SemicircularGeneratorSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalGeneratorParameters setup)
    (_uniformField : ModelsUniformFieldAcrossRotatingLoop setup)
    (_geometry : SatisfiesSemicircularLoopGeometry setup)
    (_rotation : SatisfiesUniformCrankRotation setup)
    (_faraday : SatisfiesRotatingLoopFaradayLaw setup)
    (_circuit : SatisfiesRatedResistiveBulbCircuit setup) :
    frequencyInHertz setup.crankFrequency = 4000 / Real.pi ^ 2 := by
  have hcurrent_sq :
      electricCurrentInAmperes setup.peakInducedCurrent ^ 2 = 4 := by
    calc
      electricCurrentInAmperes setup.peakInducedCurrent ^ 2 =
          electricCurrentInAmperes setup.peakInducedCurrent ^ 2 * 1 := by ring
      _ = electricCurrentInAmperes setup.peakInducedCurrent ^ 2 *
            resistanceInOhms setup.bulbResistance := by
        rw [_problem.bulbResistanceOhms]
      _ = powerInWatts setup.peakBulbPower :=
        _circuit.peakJoulePowerLaw.symm
      _ = powerInWatts setup.bulbRatedPower := _circuit.fullyLitAtPeak
      _ = 4 := _problem.bulbRatedPowerWatts
  have hcurrent :
      electricCurrentInAmperes setup.peakInducedCurrent = 2 := by
    apply
      (sq_eq_sq₀ _physical.peakCurrentPositive.le (by norm_num)).mp
    norm_num [hcurrent_sq]
  have hemf : electromotiveForceInVolts setup.peakInducedEmf = 2 := by
    calc
      electromotiveForceInVolts setup.peakInducedEmf =
          electricCurrentInAmperes setup.peakInducedCurrent *
            resistanceInOhms setup.totalCircuitResistance :=
        _circuit.peakOhmsLaw
      _ = electricCurrentInAmperes setup.peakInducedCurrent *
            resistanceInOhms setup.bulbResistance := by
        rw [_circuit.negligibleOtherResistance]
      _ = 2 * 1 := by
        rw [hcurrent, _problem.bulbResistanceOhms]
      _ = 2 := by norm_num
  have harea :
      areaInSquareMeters setup.loopArea = Real.pi / 800 := by
    calc
      areaInSquareMeters setup.loopArea =
          Real.pi * lengthInMeters setup.loopRadius ^ 2 / 2 :=
        _geometry.semicircleAreaLaw
      _ = Real.pi * (1 / 20) ^ 2 / 2 := by
        rw [_problem.loopRadiusMeters]
      _ = Real.pi / 800 := by ring
  have hflux :
      magneticFluxInWebers setup.magneticFluxAmplitude =
        Real.pi / 4000 := by
    calc
      magneticFluxInWebers setup.magneticFluxAmplitude =
          magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
            areaInSquareMeters setup.loopArea :=
        _faraday.magneticFluxAmplitudeLaw
      _ = (1 / 5) * (Real.pi / 800) := by
        rw [_problem.magneticFluxDensityTeslas, harea]
      _ = Real.pi / 4000 := by ring
  have hangular :
      angularFrequencyInRadiansPerSecond setup.angularFrequency =
        2 * Real.pi * frequencyInHertz setup.crankFrequency :=
    _rotation.angularFrequencyLaw
  have hemf_formula :
      electromotiveForceInVolts setup.peakInducedEmf =
        Real.pi ^ 2 * frequencyInHertz setup.crankFrequency / 2000 := by
    calc
      electromotiveForceInVolts setup.peakInducedEmf =
          magneticFluxInWebers setup.magneticFluxAmplitude *
            angularFrequencyInRadiansPerSecond setup.angularFrequency :=
        _faraday.peakFaradayLaw
      _ = (Real.pi / 4000) *
            (2 * Real.pi * frequencyInHertz setup.crankFrequency) := by
        rw [hflux, hangular]
      _ = Real.pi ^ 2 * frequencyInHertz setup.crankFrequency / 2000 := by
        ring
  apply (eq_div_iff (pow_ne_zero 2 Real.pi_ne_zero)).2
  calc
    frequencyInHertz setup.crankFrequency * Real.pi ^ 2 =
        2000 *
          (Real.pi ^ 2 * frequencyInHertz setup.crankFrequency / 2000) := by
      ring
    _ = 2000 * electromotiveForceInVolts setup.peakInducedEmf := by
      rw [hemf_formula]
    _ = 2000 * 2 := by rw [hemf]
    _ = 4000 := by norm_num

/-! ## Displayed answers and current target -/

/-- Labels of the four answer choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Frequency in hertz printed beside each answer label. -/
def AnswerChoice.frequencyInHertz : AnswerChoice → ℝ
  | .A => 46 * 10
  | .B => 41 * 10
  | .C => 24 * 10
  | .D => 31 * 10

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
Agreement with a frequency displayed to the nearest `10 Hz`: the exact value
lies within half of one displayed `10 Hz` step.
-/
def MatchesAnswerChoice
    (frequency : FrequencyMagnitude) (choice : AnswerChoice) : Prop :=
  |frequencyInHertz frequency - choice.frequencyInHertz| ≤ 5

/-!
The required frequency is exactly `4000 / π² Hz`, approximately
`4.1 × 10² Hz`, hence recorded answer B.

This formalizes blueprint label `thm:physics:phyx_mini_0932:target`.
-/
theorem requiredCrankFrequency_matches_recordedAnswerB
    (setup : SemicircularGeneratorSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalGeneratorParameters setup)
    (_uniformField : ModelsUniformFieldAcrossRotatingLoop setup)
    (_geometry : SatisfiesSemicircularLoopGeometry setup)
    (_rotation : SatisfiesUniformCrankRotation setup)
    (_faraday : SatisfiesRotatingLoopFaradayLaw setup)
    (_circuit : SatisfiesRatedResistiveBulbCircuit setup) :
    frequencyInHertz setup.crankFrequency = 4000 / Real.pi ^ 2 ∧
      MatchesAnswerChoice setup.crankFrequency recordedAnswerChoice := by
  have hexact :=
    requiredCrankFrequency_exact setup _problem _physical _uniformField
      _geometry _rotation _faraday _circuit
  refine ⟨hexact, ?_⟩
  have arctan_lower_bound (x : ℝ) (hx : 0 ≤ x) :
      x - x ^ 3 / 3 ≤ Real.arctan x := by
    let f : ℝ → ℝ := fun y =>
      Real.arctan y - (y - y ^ 3 / 3)
    have hf (y : ℝ) :
        HasDerivAt f (y ^ 4 / (1 + y ^ 2)) y := by
      dsimp [f]
      convert
        (Real.hasDerivAt_arctan y).sub
          ((hasDerivAt_id y).sub
            (((hasDerivAt_id y).pow 3).div_const 3)) using 1
      all_goals first | rfl |
        (simp only [id_eq]; field_simp; ring)
    have hmono : Monotone f :=
      monotone_of_hasDerivAt_nonneg hf (fun y => by positivity)
    have h := hmono hx
    simpa [f] using h
  have arctan_upper_bound (x : ℝ) (hx : 0 ≤ x) :
      Real.arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5 := by
    let f : ℝ → ℝ := fun y =>
      y - y ^ 3 / 3 + y ^ 5 / 5 - Real.arctan y
    have hf (y : ℝ) :
        HasDerivAt f (y ^ 6 / (1 + y ^ 2)) y := by
      dsimp [f]
      convert
        (((hasDerivAt_id y).sub
            (((hasDerivAt_id y).pow 3).div_const 3)).add
              (((hasDerivAt_id y).pow 5).div_const 5)).sub
          (Real.hasDerivAt_arctan y) using 1
      all_goals first | rfl |
        (simp only [id_eq]; field_simp; ring)
    have hmono : Monotone f :=
      monotone_of_hasDerivAt_nonneg hf (fun y => by positivity)
    have h := hmono hx
    simpa [f] using h
  have hatanFiveLower :=
    arctan_lower_bound (1 / 5 : ℝ) (by norm_num)
  have hatanFiveUpper :=
    arctan_upper_bound (1 / 5 : ℝ) (by norm_num)
  have hatanTwoThirtyNineLower :=
    arctan_lower_bound (1 / 239 : ℝ) (by norm_num)
  have hatanTwoThirtyNineUpper :=
    arctan_upper_bound (1 / 239 : ℝ) (by norm_num)
  norm_num at hatanFiveLower hatanFiveUpper hatanTwoThirtyNineLower hatanTwoThirtyNineUpper
  have hatanFiveLower' :
      (1973 / 10000 : ℝ) ≤ Real.arctan (1 / 5) := by
    linarith [hatanFiveLower]
  have hatanFiveUpper' :
      Real.arctan (1 / 5) ≤ (1974 / 10000 : ℝ) := by
    linarith [hatanFiveUpper]
  have hatanTwoThirtyNineLower' :
      (418 / 100000 : ℝ) ≤ Real.arctan (1 / 239) := by
    linarith [hatanTwoThirtyNineLower]
  have hatanTwoThirtyNineUpper' :
      Real.arctan (1 / 239) ≤ (419 / 100000 : ℝ) := by
    linarith [hatanTwoThirtyNineUpper]
  have hMachin :=
    Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  norm_num [inv_eq_one_div] at hMachin
  have hpiLower : (3.14 : ℝ) < Real.pi := by
    linarith [hatanFiveLower', hatanTwoThirtyNineUpper', hMachin]
  have hpiUpper : Real.pi < (3.142 : ℝ) := by
    linarith [hatanFiveUpper', hatanTwoThirtyNineLower', hMachin]
  have hpiSqLower : (3.14 : ℝ) ^ 2 < Real.pi ^ 2 :=
    (sq_lt_sq₀ (by norm_num) Real.pi_pos.le).2 hpiLower
  have hpiSqUpper : Real.pi ^ 2 < (3.142 : ℝ) ^ 2 :=
    (sq_lt_sq₀ Real.pi_pos.le (by norm_num)).2 hpiUpper
  have hpiSqPositive : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  unfold MatchesAnswerChoice recordedAnswerChoice
  simp only [AnswerChoice.frequencyInHertz]
  rw [hexact, abs_le]
  constructor
  · have hlower : (405 : ℝ) ≤ 4000 / Real.pi ^ 2 := by
      rw [le_div_iff₀ hpiSqPositive]
      norm_num at hpiSqUpper ⊢
      linarith
    linarith
  · have hupper : 4000 / Real.pi ^ 2 ≤ (415 : ℝ) := by
      rw [div_le_iff₀ hpiSqPositive]
      norm_num at hpiSqLower ⊢
      linarith
    linarith

end PhyXMiniProblems.ProblemPhyXMini0932
