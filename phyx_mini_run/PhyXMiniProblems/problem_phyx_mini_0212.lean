import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Sound level at a greater distance from a jet plane

A sound level of `140 dB` is measured `30 m` from a jet plane.  The requested
estimate is the level at `300 m` when ground reflections are ignored.  The
idealized model treats the jet as a constant-power isotropic point source in a
free field, so its acoustic intensity obeys the inverse-square law.

Distances, acoustic power, and acoustic intensity are represented by Physlib
dimensionful quantities.  Real numbers are used only for named coherent-unit
readouts, dimensionless intensity ratios, and logarithmic levels in decibels.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0212

open Dimension

/-! ## Dimensionful acoustic quantities and coherent-unit readouts -/

/-- A nonnegative physical source-to-observer distance. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-!
Acoustic power has SI unit watt and dimension
`mass * length^2 / time^3`.
-/
abbrev AcousticPowerQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-!
Acoustic intensity is power per area, with SI unit watt per square metre and
dimension `mass / time^3`.
-/
abbrev AcousticIntensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical distance in a coherent choice of units. -/
def distanceReadout
    (units : UnitChoices) (distance : LengthMagnitude) : ℝ :=
  ((distance units).val : ℝ)

/-- Read a physical acoustic power in a coherent choice of units. -/
def acousticPowerReadout
    (units : UnitChoices) (power : AcousticPowerQuantity) : ℝ :=
  ((power units).val : ℝ)

/-- Read a physical acoustic intensity in a coherent choice of units. -/
def acousticIntensityReadout
    (units : UnitChoices) (intensity : AcousticIntensityQuantity) : ℝ :=
  ((intensity units).val : ℝ)

/-- SI metre readout of a source-to-observer distance. -/
def distanceInMeters (distance : LengthMagnitude) : ℝ :=
  distanceReadout UnitChoices.SI distance

/-- SI watt readout of an emitted acoustic power. -/
def acousticPowerInWatts (power : AcousticPowerQuantity) : ℝ :=
  acousticPowerReadout UnitChoices.SI power

/-- SI watt-per-square-metre readout of an acoustic intensity. -/
def acousticIntensityInWattsPerSquareMeter
    (intensity : AcousticIntensityQuantity) : ℝ :=
  acousticIntensityReadout UnitChoices.SI intensity

/-! ## Physical setup, observation labels, and primary-image evidence -/

/-- The measured and requested observer positions in the problem text. -/
inductive ObservationPoint where
  | nearMeasurement
  | farEstimate
  deriving DecidableEq, Repr

/-- Qualitative objects visible in the supplied airport photograph. -/
inductive AirportFigureLabel where
  | foregroundAircraft
  | groundCrewWorker
  | hearingProtectors
  | leftSignalWand
  | rightSignalWand
  | backgroundAircraft
  deriving DecidableEq, Repr

/-- Visibility information extracted from the supplied airport photograph. -/
structure AirportFigure where
  visible : AirportFigureLabel → Prop

/-- Type of idealized acoustic source used for the estimate. -/
inductive AcousticSourceKind where
  | isotropicJetPointSource
  | other
  deriving DecidableEq, Repr

/-- Time dependence of the jet's emitted acoustic power. -/
inductive EmissionRegime where
  | constantPower
  | timeVarying
  deriving DecidableEq, Repr

/-- Propagation medium between the jet and the observers. -/
inductive AcousticMedium where
  | ambientAir
  | other
  deriving DecidableEq, Repr

/-- Geometric spreading model used for the sound field. -/
inductive SpreadingGeometry where
  | freeFieldSpherical
  | other
  deriving DecidableEq, Repr

/-- How sound reflected from the ground is treated in the model. -/
inductive GroundReflectionTreatment where
  | ignored
  | included
  deriving DecidableEq, Repr

/-!
Physical quantities for the two-position jet-sound estimate.

The intensity at the far observation point is an independent physical field;
neither its numerical value nor the requested far sound level is stored in
this structure.
-/
structure JetPlaneSoundSetup where
  sourceKind : AcousticSourceKind
  emissionRegime : EmissionRegime
  propagationMedium : AcousticMedium
  spreadingGeometry : SpreadingGeometry
  groundReflectionTreatment : GroundReflectionTreatment
  emittedAcousticPower : AcousticPowerQuantity
  referenceIntensity : AcousticIntensityQuantity
  distanceFromJet : ObservationPoint → LengthMagnitude
  acousticIntensityAt : ObservationPoint → AcousticIntensityQuantity
  figure : AirportFigure

/-!
The sound-intensity level at an observation point, in decibels.  This is the
standard generic definition `10 log10 (I / I_ref)` applied to same-unit SI
readouts; it contains no distance-specific numerical answer.
-/
def soundLevelInDecibels
    (setup : JetPlaneSoundSetup) (point : ObservationPoint) : ℝ :=
  10 * Real.logb 10
    (acousticIntensityInWattsPerSquareMeter
        (setup.acousticIntensityAt point) /
      acousticIntensityInWattsPerSquareMeter setup.referenceIntensity)

/-! ## Assumptions: scenario, figure/data readouts, and governing laws -/

/-!
The idealized physical scenario used for the estimate: a constant-power jet
point source radiates spherically through ambient air, and ground reflections
are omitted as required by the problem statement.
-/
def MatchesJetPlaneScenario (setup : JetPlaneSoundSetup) : Prop :=
  setup.sourceKind = .isotropicJetPointSource ∧
    setup.emissionRegime = .constantPower ∧
    setup.propagationMedium = .ambientAir ∧
    setup.spreadingGeometry = .freeFieldSpherical ∧
    setup.groundReflectionTreatment = .ignored

/-!
Qualitative evidence in the primary image: a ground-crew worker wearing
hearing protection raises two signal wands beside a foreground aircraft, with
another aircraft in the background.  The image supplies no numerical distance
or sound-level readout.
-/
structure MatchesSuppliedAirportFigure (setup : JetPlaneSoundSetup) : Prop where
  foregroundAircraftVisible : setup.figure.visible .foregroundAircraft
  groundCrewWorkerVisible : setup.figure.visible .groundCrewWorker
  hearingProtectorsVisible : setup.figure.visible .hearingProtectors
  leftSignalWandVisible : setup.figure.visible .leftSignalWand
  rightSignalWandVisible : setup.figure.visible .rightSignalWand
  backgroundAircraftVisible : setup.figure.visible .backgroundAircraft

/-!
The numerical data stated in the problem.  The near measurement is `140 dB`
at `30 m`, while the requested observation position is `300 m` away.  No far
sound level or answer choice occurs in these data.
-/
structure MatchesProblemData (setup : JetPlaneSoundSetup) : Prop where
  nearDistanceMeters :
    distanceInMeters (setup.distanceFromJet .nearMeasurement) = 30
  farDistanceMeters :
    distanceInMeters (setup.distanceFromJet .farEstimate) = 300
  nearSoundLevelDecibels :
    soundLevelInDecibels setup .nearMeasurement = 140

/-!
The conventional reference intensity for sound intensity level is
`10^-12 W/m^2`.  This convention is independent of either observation distance
and does not determine the requested far level by itself.
-/
def UsesStandardSoundIntensityReference (setup : JetPlaneSoundSetup) : Prop :=
  acousticIntensityInWattsPerSquareMeter setup.referenceIntensity =
    1 / (10 : ℝ) ^ 12

/-- Strict positivity and nondegeneracy of the physical acoustic quantities. -/
def HasPhysicalAcousticParameters (setup : JetPlaneSoundSetup) : Prop :=
  0 < acousticPowerInWatts setup.emittedAcousticPower ∧
    0 < acousticIntensityInWattsPerSquareMeter setup.referenceIntensity ∧
    ∀ point : ObservationPoint,
      0 < distanceInMeters (setup.distanceFromJet point) ∧
        0 < acousticIntensityInWattsPerSquareMeter
          (setup.acousticIntensityAt point)

/-!
The free-field inverse-square intensity law for an isotropic point source.  In
every coherent unit system, the acoustic power crossing the sphere of radius
`r` is `4 * pi * r^2 * I`.  This general law contains neither the `1/100`
far-intensity result nor the requested `120 dB` conclusion.
-/
structure SatisfiesIsotropicInverseSquareLaw
    (setup : JetPlaneSoundSetup) : Prop where
  inverseSquare : ∀ point : ObservationPoint, ∀ units : UnitChoices,
    4 * Real.pi *
          distanceReadout units (setup.distanceFromJet point) ^ 2 *
          acousticIntensityReadout units (setup.acousticIntensityAt point) =
      acousticPowerReadout units setup.emittedAcousticPower

/-! ## Derived relations and displayed answers -/

/-!
Increasing the distance from `30 m` to `300 m` reduces the acoustic intensity
by a factor of `100`.  This is a derived result, not a model assumption.
-/
lemma farIntensity_eq_nearIntensity_div_hundred
    (setup : JetPlaneSoundSetup)
    (h_data : MatchesProblemData setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_inverseSquare : SatisfiesIsotropicInverseSquareLaw setup) :
    acousticIntensityInWattsPerSquareMeter
        (setup.acousticIntensityAt .farEstimate) =
      acousticIntensityInWattsPerSquareMeter
        (setup.acousticIntensityAt .nearMeasurement) / 100 := by
  have h_near :=
    h_inverseSquare.inverseSquare
      ObservationPoint.nearMeasurement UnitChoices.SI
  have h_far :=
    h_inverseSquare.inverseSquare
      ObservationPoint.farEstimate UnitChoices.SI
  change
    4 * Real.pi *
          distanceInMeters (setup.distanceFromJet .nearMeasurement) ^ 2 *
          acousticIntensityInWattsPerSquareMeter
            (setup.acousticIntensityAt .nearMeasurement) =
      acousticPowerInWatts setup.emittedAcousticPower at h_near
  change
    4 * Real.pi *
          distanceInMeters (setup.distanceFromJet .farEstimate) ^ 2 *
          acousticIntensityInWattsPerSquareMeter
            (setup.acousticIntensityAt .farEstimate) =
      acousticPowerInWatts setup.emittedAcousticPower at h_far
  rw [h_data.nearDistanceMeters] at h_near
  rw [h_data.farDistanceMeters] at h_far
  nlinarith [Real.pi_pos]

/-!
The inverse-square intensity change across a tenfold distance increase lowers
the sound intensity level by `20 dB`.  This conclusion is derived directly
from the problem data and governing law.
-/
lemma farSoundLevel_eq_nearSoundLevel_sub_twenty
    (setup : JetPlaneSoundSetup)
    (h_data : MatchesProblemData setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_inverseSquare : SatisfiesIsotropicInverseSquareLaw setup) :
    soundLevelInDecibels setup .farEstimate =
      soundLevelInDecibels setup .nearMeasurement - 20 := by
  have h_intensity :=
    farIntensity_eq_nearIntensity_div_hundred
      setup h_data h_physical h_inverseSquare
  rcases h_physical with ⟨_, h_reference_pos, h_point_pos⟩
  have h_near_ne :
      acousticIntensityInWattsPerSquareMeter
          (setup.acousticIntensityAt .nearMeasurement) ≠ 0 :=
    ne_of_gt (h_point_pos .nearMeasurement).2
  have h_reference_ne :
      acousticIntensityInWattsPerSquareMeter setup.referenceIntensity ≠ 0 :=
    ne_of_gt h_reference_pos
  have h_log_ten_ne : Real.log (10 : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have h_logb_hundred : Real.logb 10 (100 : ℝ) = 2 := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num]
    simp [Real.logb, Real.log_pow, h_log_ten_ne]
  rw [soundLevelInDecibels, soundLevelInDecibels, h_intensity]
  rw [show
    (acousticIntensityInWattsPerSquareMeter
          (setup.acousticIntensityAt .nearMeasurement) / 100) /
        acousticIntensityInWattsPerSquareMeter setup.referenceIntensity =
      (acousticIntensityInWattsPerSquareMeter
          (setup.acousticIntensityAt .nearMeasurement) /
        acousticIntensityInWattsPerSquareMeter setup.referenceIntensity) /
          100 by ring]
  rw [Real.logb_div (div_ne_zero h_near_ne h_reference_ne) (by norm_num),
    h_logb_hundred]
  ring

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Sound-level readout in decibels printed beside each answer label. -/
def AnswerChoice.decibels : AnswerChoice → ℝ
  | .A => 160
  | .B => 140
  | .C => 100
  | .D => 120

/-- The answer label recorded by the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
A displayed choice is uniquely closest to a computed sound-level estimate.
This generic comparison does not privilege the recorded choice by definition.
-/
def IsClosestDisplayedAnswer
    (actualDecibels : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |actualDecibels - choice.decibels| <
      |actualDecibels - other.decibels|

/-!
Physics formalization target for
`thm:physics:phyx_mini_0212:target`.

Under free-field spherical spreading, moving ten times farther from the jet
reduces the level by `20 dB`, from `140 dB` to `120 dB`.  Thus the unique
closest displayed answer is the recorded choice D.  Neither conclusion occurs
in any premise.
-/
theorem problem_phyx_mini_0212
    (setup : JetPlaneSoundSetup)
    (h_scenario : MatchesJetPlaneScenario setup)
    (h_figure : MatchesSuppliedAirportFigure setup)
    (h_data : MatchesProblemData setup)
    (h_reference : UsesStandardSoundIntensityReference setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_inverseSquare : SatisfiesIsotropicInverseSquareLaw setup) :
    soundLevelInDecibels setup .farEstimate = 120 ∧
      IsClosestDisplayedAnswer
        (soundLevelInDecibels setup .farEstimate) recordedAnswerChoice := by
  have h_far :=
    farSoundLevel_eq_nearSoundLevel_sub_twenty
      setup h_data h_physical h_inverseSquare
  rw [h_data.nearSoundLevelDecibels] at h_far
  norm_num at h_far
  refine ⟨h_far, ?_⟩
  rw [h_far]
  intro other
  cases other <;>
    norm_num [recordedAnswerChoice, AnswerChoice.decibels]

end PhyXMiniProblems.ProblemPhyXMini0212
