import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0956

open Dimension

/-!
# Electron frequency in a cyclotron calibrated with alpha particles

An alpha particle follows a circular orbit in a magnetic field perpendicular
to its path.  The supplied graph plots its revolution frequency `f` against
the magnetic-flux-density magnitude `B`.  The question asks for the electron
cyclotron frequency at `B = 0.300 T`.

Physical charge, mass, magnetic flux density, and frequency are represented by
unit-independent Physlib quantities.  Reals occur only as coherent-SI
readouts, graph coordinates, and displayed answer values.

Assumption/target split:

* `MatchesProblemStatement` contains the supplied field setting, orbit model,
  and the four displayed answer values;
* `MatchesPrimaryCyclotronGraph` contains only labels, scales, ranges, the
  seven plotted alpha-particle points, and the positive straight-line fit read
  from image 956;
* `UsesStandardParticleData` supplies electron and alpha-particle charge and
  mass data;
* `SatisfiesCyclotronFrequencyLaw` states the governing relation
  `f = |q| B / (2 π m)`; and
* `electronCyclotronFrequency_matches_answer_B` alone concludes that the
  electron frequency rounds to `8.4 GHz` and that B is the uniquely closest
  displayed choice.  No premise contains either conclusion.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Magnetic flux density has physical dimension `M T⁻¹ C⁻¹` (tesla in SI). -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative physical electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative physical rest mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitudeQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative revolution frequency, with physical dimension `T⁻¹`. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read an electric-charge magnitude in coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout charge

/-- Read a rest mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Read a magnetic-flux-density magnitude in tesla. -/
def magneticFluxDensityInTeslas
    (field : MagneticFluxDensityMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout field

/-- Read a revolution frequency in hertz (revolutions per second). -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  nonnegativeSIReadout frequency

/-! ## Particle, apparatus, and graph vocabulary -/

/-- Particle species used in the calibration and in the requested prediction. -/
inductive ParticleSpecies where
  | alphaParticle
  | electron
  deriving DecidableEq, Fintype, Repr

/-- The idealized shape of the particle trajectory. -/
inductive OrbitGeometry where
  | circular
  | other
  deriving DecidableEq, Repr

/-- The orientation of the magnetic-field vector relative to the orbit. -/
inductive MagneticFieldOrbitOrientation where
  | perpendicular
  | other
  deriving DecidableEq, Repr

/-- The dynamical regime in which the elementary cyclotron law is used. -/
inductive CyclotronRegime where
  | nonrelativisticUniformField
  | other
  deriving DecidableEq, Repr

/-- The four answer labels printed with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The symbol printed on the graph's horizontal axis. -/
inductive HorizontalAxisLabel where
  | magneticFluxDensityB
  deriving DecidableEq, Repr

/-- The symbol printed on the graph's vertical axis. -/
inductive VerticalAxisLabel where
  | revolutionFrequencyF
  deriving DecidableEq, Repr

/-- One plotted graph point, recorded in the units displayed on the axes. -/
structure DisplayedGraphPoint where
  magneticFluxDensityInTeslas : ℝ
  frequencyInDisplayedUnits : ℝ

/-!
The physical cyclotron configuration at the field setting in the question.
Charge, mass, and frequency remain species-indexed so that the alpha-particle
calibration and electron prediction refer to the same apparatus.
-/
structure CyclotronTestSetup where
  magneticFluxDensityMagnitude : MagneticFluxDensityMagnitudeQuantity
  chargeMagnitude : ParticleSpecies → ChargeMagnitudeQuantity
  restMass : ParticleSpecies → MassQuantity
  cyclotronFrequency : ParticleSpecies → FrequencyQuantity
  orbitGeometry : ParticleSpecies → OrbitGeometry
  fieldOrbitOrientation : ParticleSpecies → MagneticFieldOrbitOrientation
  regime : CyclotronRegime
  answerFrequencyInHertz : AnswerChoice → ℝ

/-!
Typed information carried by the primary raster `956.png`.  `dataPoint` has
domain `Fin 7`, so the declaration records exactly the seven visible black
points without inventing precise coordinates for all of them.
-/
structure CyclotronFrequencyGraph where
  plottedParticle : ParticleSpecies
  horizontalAxisLabel : HorizontalAxisLabel
  verticalAxisLabel : VerticalAxisLabel
  horizontalAxisMinimum : ℝ
  horizontalAxisMaximum : ℝ
  horizontalMajorTickStep : ℝ
  verticalAxisMinimum : ℝ
  verticalAxisMaximum : ℝ
  verticalMajorTickStep : ℝ
  verticalAxisUnitInHertz : ℝ
  dataPoint : Fin 7 → DisplayedGraphPoint
  bestFitFrequencyInDisplayedUnits : ℝ → ℝ

/-! ## Source data, figure readouts, and governing physics -/

/-- Prose data and answer values supplied by the problem statement. -/
structure MatchesProblemStatement (setup : CyclotronTestSetup) : Prop where
  fieldSetting :
    magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude = 0.300
  alphaOrbitIsCircular :
    setup.orbitGeometry .alphaParticle = .circular
  fieldIsPerpendicularToAlphaOrbit :
    setup.fieldOrbitOrientation .alphaParticle = .perpendicular
  electronPredictionUsesSameOrbitModel :
    setup.orbitGeometry .electron = .circular
  fieldIsPerpendicularToElectronOrbit :
    setup.fieldOrbitOrientation .electron = .perpendicular
  nonrelativisticUniformFieldModel :
    setup.regime = .nonrelativisticUniformField
  displayedChoiceA :
    setup.answerFrequencyInHertz .A = 4_580_000
  displayedChoiceB :
    setup.answerFrequencyInHertz .B = 8_400_000_000
  displayedChoiceC :
    setup.answerFrequencyInHertz .C = 8_400_000
  displayedChoiceD :
    setup.answerFrequencyInHertz .D = 16_800_000

/-!
Primary-image readouts.  Vertical graph coordinates are multiples of `10⁵ Hz`.
The fit value `23` at `0.300 T` is the visual graph estimate, not the requested
electron answer.
-/
structure MatchesPrimaryCyclotronGraph
    (setup : CyclotronTestSetup) (figure : CyclotronFrequencyGraph) : Prop where
  plottedSpecies :
    figure.plottedParticle = .alphaParticle
  horizontalLabel :
    figure.horizontalAxisLabel = .magneticFluxDensityB
  verticalLabel :
    figure.verticalAxisLabel = .revolutionFrequencyF
  horizontalRange :
    figure.horizontalAxisMinimum = 0 ∧
    figure.horizontalAxisMaximum = 0.40 ∧
    figure.horizontalMajorTickStep = 0.10
  verticalRange :
    figure.verticalAxisMinimum = 6 ∧
    figure.verticalAxisMaximum = 34 ∧
    figure.verticalMajorTickStep = 4
  verticalScale :
    figure.verticalAxisUnitInHertz = 100_000
  dataPointsLieInDisplayedWindow :
    ∀ index,
      figure.horizontalAxisMinimum ≤
          (figure.dataPoint index).magneticFluxDensityInTeslas ∧
      (figure.dataPoint index).magneticFluxDensityInTeslas ≤
          figure.horizontalAxisMaximum ∧
      figure.verticalAxisMinimum ≤
          (figure.dataPoint index).frequencyInDisplayedUnits ∧
      (figure.dataPoint index).frequencyInDisplayedUnits ≤
          figure.verticalAxisMaximum
  positiveStraightLineFit :
    ∃ slope intercept : ℝ,
      0 < slope ∧
      ∀ fieldInTeslas,
        figure.bestFitFrequencyInDisplayedUnits fieldInTeslas =
          slope * fieldInTeslas + intercept
  fitReadoutAtPointThreeTesla :
    figure.bestFitFrequencyInDisplayedUnits 0.300 = 23
  alphaMeasurementAgreesWithGraph :
    |frequencyInHertz (setup.cyclotronFrequency .alphaParticle) -
        figure.verticalAxisUnitInHertz *
          figure.bestFitFrequencyInDisplayedUnits 0.300| ≤ 50_000

/-- Standard charge-magnitude and rest-mass data used for the two species. -/
structure UsesStandardParticleData (setup : CyclotronTestSetup) : Prop where
  electronChargeMagnitude :
    chargeMagnitudeInCoulombs (setup.chargeMagnitude .electron) =
      (1_602_176_634 : ℝ) / (10 : ℝ) ^ 28
  electronRestMass :
    massInKilograms (setup.restMass .electron) =
      (91_093_837_015 : ℝ) / (10 : ℝ) ^ 41
  alphaChargeIsTwiceElementaryCharge :
    chargeMagnitudeInCoulombs (setup.chargeMagnitude .alphaParticle) =
      2 * chargeMagnitudeInCoulombs (setup.chargeMagnitude .electron)
  alphaRestMass :
    massInKilograms (setup.restMass .alphaParticle) =
      (66_446_573_357 : ℝ) / (10 : ℝ) ^ 37

/-!
The governing nonrelativistic cyclotron law.  This is a species-independent
physical relation, not a restatement of the requested electron value.
-/
structure SatisfiesCyclotronFrequencyLaw
    (setup : CyclotronTestSetup) : Prop where
  frequencyLaw :
    ∀ species,
      frequencyInHertz (setup.cyclotronFrequency species) =
        chargeMagnitudeInCoulombs (setup.chargeMagnitude species) *
            magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude /
          (2 * Real.pi * massInKilograms (setup.restMass species))

/-! ## Reporting the requested multiple-choice prediction -/

/-- `reported` is the nearest multiple of `quantum` to `actual`. -/
def RoundsToNearest (quantum actual reported : ℝ) : Prop :=
  0 < quantum ∧ |actual - reported| ≤ quantum / 2

/-- A displayed answer is strictly closer than every other displayed answer. -/
def IsUniqueClosestAnswer
    (actual : ℝ) (displayed : AnswerChoice → ℝ)
    (choice : AnswerChoice) : Prop :=
  ∀ alternative,
    alternative ≠ choice →
      |actual - displayed choice| < |actual - displayed alternative|

/--
At `B = 0.300 T`, the electron cyclotron frequency rounds to `8.4 GHz`, and
choice B is uniquely closest among the four frequencies printed in the source.
-/
theorem electronCyclotronFrequency_matches_answer_B
    (setup : CyclotronTestSetup)
    (figure : CyclotronFrequencyGraph)
    (_statement : MatchesProblemStatement setup)
    (_figureReadouts : MatchesPrimaryCyclotronGraph setup figure)
    (_particleData : UsesStandardParticleData setup)
    (_cyclotronPhysics : SatisfiesCyclotronFrequencyLaw setup) :
    RoundsToNearest
        100_000_000
        (frequencyInHertz (setup.cyclotronFrequency .electron))
        8_400_000_000 ∧
      IsUniqueClosestAnswer
        (frequencyInHertz (setup.cyclotronFrequency .electron))
        setup.answerFrequencyInHertz
        .B := by
  have h_frequency :=
    _cyclotronPhysics.frequencyLaw ParticleSpecies.electron
  rw [_particleData.electronChargeMagnitude, _statement.fieldSetting,
    _particleData.electronRestMass] at h_frequency
  have h_denominator_positive :
      0 <
        2 * Real.pi *
          ((91_093_837_015 : ℝ) / (10 : ℝ) ^ 41) := by
    positivity
  have h_frequency_lower :
      (8_350_000_000 : ℝ) <
        frequencyInHertz (setup.cyclotronFrequency .electron) := by
    rw [h_frequency]
    rw [lt_div_iff₀ h_denominator_positive]
    nlinarith [Real.pi_lt_d2]
  have h_frequency_upper :
      frequencyInHertz (setup.cyclotronFrequency .electron) <
        (8_450_000_000 : ℝ) := by
    rw [h_frequency]
    rw [div_lt_iff₀ h_denominator_positive]
    nlinarith [Real.pi_gt_d2]
  have h_rounding_error :
      |frequencyInHertz (setup.cyclotronFrequency .electron) -
          8_400_000_000| ≤ (50_000_000 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  constructor
  · refine ⟨by norm_num, ?_⟩
    norm_num
    exact h_rounding_error
  · intro alternative h_alternative
    cases alternative with
    | A =>
        rw [_statement.displayedChoiceB, _statement.displayedChoiceA]
        calc
          |frequencyInHertz (setup.cyclotronFrequency .electron) -
              8_400_000_000| ≤ 50_000_000 := h_rounding_error
          _ < |frequencyInHertz (setup.cyclotronFrequency .electron) -
              4_580_000| := by
            rw [abs_of_pos (by linarith [h_frequency_lower])]
            linarith
    | B =>
        exact (h_alternative rfl).elim
    | C =>
        rw [_statement.displayedChoiceB, _statement.displayedChoiceC]
        calc
          |frequencyInHertz (setup.cyclotronFrequency .electron) -
              8_400_000_000| ≤ 50_000_000 := h_rounding_error
          _ < |frequencyInHertz (setup.cyclotronFrequency .electron) -
              8_400_000| := by
            rw [abs_of_pos (by linarith [h_frequency_lower])]
            linarith
    | D =>
        rw [_statement.displayedChoiceB, _statement.displayedChoiceD]
        calc
          |frequencyInHertz (setup.cyclotronFrequency .electron) -
              8_400_000_000| ≤ 50_000_000 := h_rounding_error
          _ < |frequencyInHertz (setup.cyclotronFrequency .electron) -
              16_800_000| := by
            rw [abs_of_pos (by linarith [h_frequency_lower])]
            linarith

end PhyXMiniProblems.ProblemPhyXMini0956
