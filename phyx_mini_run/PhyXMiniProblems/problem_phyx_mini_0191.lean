import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0191

open Dimension

/-!
# Sound-level drop after doubling the distance from a bird

The bird is modeled as an isotropic acoustic point source emitting constant
sound power.  The supplied image labels the nearer and farther listeners
`P₁` and `P₂` and depicts concentric wavefronts centered on the bird.  The
move from `P₁` to `P₂` doubles the radial distance from the source.

Distances, acoustic power, and acoustic intensity are unit-independent
Physlib quantities.  Real scalars occur only as coherent unit readouts and as
dimensionless logarithmic sound-level differences measured in decibels.
-/

/-- A nonnegative physical distance from the point source. -/
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

/-- Read an acoustic power in a coherent choice of units. -/
def acousticPowerReadout
    (units : UnitChoices) (power : AcousticPowerQuantity) : ℝ :=
  ((power units).val : ℝ)

/-- Read an acoustic intensity in a coherent choice of units. -/
def acousticIntensityReadout
    (units : UnitChoices) (intensity : AcousticIntensityQuantity) : ℝ :=
  ((intensity units).val : ℝ)

/-- SI metre readout of a source-to-listener distance. -/
def distanceInMeters (distance : LengthMagnitude) : ℝ :=
  distanceReadout UnitChoices.SI distance

/-- SI watt readout of the emitted acoustic power. -/
def acousticPowerInWatts (power : AcousticPowerQuantity) : ℝ :=
  acousticPowerReadout UnitChoices.SI power

/-- SI watt-per-square-metre readout of an acoustic intensity. -/
def acousticIntensityInWattsPerSquareMeter
    (intensity : AcousticIntensityQuantity) : ℝ :=
  acousticIntensityReadout UnitChoices.SI intensity

/-- The two listener positions labeled in the supplied figure. -/
inductive ListenerLabel where
  | P₁
  | P₂
  deriving DecidableEq, Repr

/-- All labeled physical objects visible in the supplied figure. -/
inductive FigureLabel where
  | bird
  | P₁
  | P₂
  deriving DecidableEq, Repr

/-- Physical roles assigned to the three figure labels. -/
inductive FigureRole where
  | isotropicPointSource
  | nearListener
  | farListener
  deriving DecidableEq, Repr

/-- Qualitative geometry of the blue sound-wave fronts in the image. -/
inductive WavefrontGeometry where
  | concentricSpherical
  | other
  deriving DecidableEq, Repr

/-- Type of acoustic source used in the idealized model. -/
inductive AcousticSourceKind where
  | birdPointSource
  | other
  deriving DecidableEq, Repr

/-- Time dependence of the sound power emitted by the source. -/
inductive EmissionRegime where
  | constantPower
  | timeVarying
  deriving DecidableEq, Repr

/-- The propagation medium shown in the outdoor scene. -/
inductive AcousticMedium where
  | ambientAir
  | other
  deriving DecidableEq, Repr

/-- Figure-specific qualitative labels and wavefront geometry. -/
structure BirdSoundFigure where
  role : FigureLabel → FigureRole
  wavefrontGeometry : WavefrontGeometry

/-!
Physical quantities and observations for the two listener positions.

There is one emitted-power field, expressing that the same source power is
used at both positions.  The two intensities remain independent until related
by the inverse-square law; neither their ratio nor the requested decibel drop
is stored in this structure.
-/
structure BirdPointSourceSoundSetup where
  sourceKind : AcousticSourceKind
  emissionRegime : EmissionRegime
  propagationMedium : AcousticMedium
  emittedAcousticPower : AcousticPowerQuantity
  distanceFromBird : ListenerLabel → LengthMagnitude
  acousticIntensityAt : ListenerLabel → AcousticIntensityQuantity
  figure : BirdSoundFigure

/-!
Textual physical model: an idealized bird is a point source with constant
sound power, and sound propagates through ambient air.
-/
def MatchesPointSourceScenario
    (setup : BirdPointSourceSoundSetup) : Prop :=
  setup.sourceKind = .birdPointSource ∧
    setup.emissionRegime = .constantPower ∧
    setup.propagationMedium = .ambientAir

/-!
Primary-image evidence.  `P₁` is the nearer listener, `P₂` is the farther
listener, and the blue curves represent concentric wavefronts centered on the
bird.  No numerical intensity ratio or decibel answer is asserted here.
-/
def MatchesSuppliedFigure
    (setup : BirdPointSourceSoundSetup) : Prop :=
  setup.figure.role .bird = .isotropicPointSource ∧
    setup.figure.role .P₁ = .nearListener ∧
    setup.figure.role .P₂ = .farListener ∧
    setup.figure.wavefrontGeometry = .concentricSpherical ∧
    distanceInMeters (setup.distanceFromBird .P₁) <
      distanceInMeters (setup.distanceFromBird .P₂)

/-!
The stated move: the distance at `P₂` is twice the distance at `P₁` in every
coherent choice of units.  This premise contains no intensity or decibel
conclusion.
-/
def MovedToTwiceTheDistance
    (setup : BirdPointSourceSoundSetup) : Prop :=
  ∀ units : UnitChoices,
    distanceReadout units (setup.distanceFromBird .P₂) =
      2 * distanceReadout units (setup.distanceFromBird .P₁)

/-- Positivity and nondegeneracy of the physical quantities in the model. -/
def HasPhysicalAcousticParameters
    (setup : BirdPointSourceSoundSetup) : Prop :=
  0 < acousticPowerInWatts setup.emittedAcousticPower ∧
    ∀ listener : ListenerLabel,
      0 < distanceInMeters (setup.distanceFromBird listener) ∧
        0 < acousticIntensityInWattsPerSquareMeter
          (setup.acousticIntensityAt listener)

/-!
The inverse-square intensity law for an isotropic point source.  In every
coherent unit system, the acoustic power through the sphere of radius `r` is
`4 * pi * r^2 * I`.  This general law does not state the quarter-intensity or
decibel conclusion for the doubled distance.
-/
structure SatisfiesIsotropicInverseSquareLaw
    (setup : BirdPointSourceSoundSetup) : Prop where
  inverseSquare : ∀ listener : ListenerLabel, ∀ units : UnitChoices,
    4 * Real.pi *
          distanceReadout units (setup.distanceFromBird listener) ^ 2 *
          acousticIntensityReadout units
            (setup.acousticIntensityAt listener) =
      acousticPowerReadout units setup.emittedAcousticPower

/-!
The drop in sound intensity level, in decibels, when moving from `P₁` to
`P₂`.  This is the standard general conversion
`10 log10 (I_before / I_after)` applied to same-unit SI readouts; it contains
no built-in value for the doubled-distance case.
-/
def soundLevelDropInDecibels (setup : BirdPointSourceSoundSetup) : ℝ :=
  10 * Real.logb 10
    (acousticIntensityInWattsPerSquareMeter
        (setup.acousticIntensityAt .P₁) /
      acousticIntensityInWattsPerSquareMeter
        (setup.acousticIntensityAt .P₂))

/-- Labels of the four decibel choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The decibel drop printed beside each answer label. -/
def displayedDropInDecibels : AnswerChoice → ℝ
  | .A => 60 / 10
  | .B => 82 / 10
  | .C => 75 / 10
  | .D => 91 / 10

/-!
Agreement with a displayed decibel value rounded to the nearest tenth.  The
half-tenth tolerance does not make choice A true by definition.
-/
def MatchesAnswerToNearestTenthDecibel
    (setup : BirdPointSourceSoundSetup) (choice : AnswerChoice) : Prop :=
  |soundLevelDropInDecibels setup - displayedDropInDecibels choice| ≤
    (1 / 20 : ℝ)

/-!
Doubling the source distance makes the acoustic intensity one quarter as
large.  This is a derived intermediate result, not a model assumption.
-/
lemma intensityAtP₂_eq_oneQuarter_intensityAtP₁
    (setup : BirdPointSourceSoundSetup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_twice : MovedToTwiceTheDistance setup)
    (h_inverseSquare : SatisfiesIsotropicInverseSquareLaw setup) :
    acousticIntensityInWattsPerSquareMeter
        (setup.acousticIntensityAt .P₂) =
      acousticIntensityInWattsPerSquareMeter
        (setup.acousticIntensityAt .P₁) / 4 := by
  have hd₁ : 0 < distanceInMeters (setup.distanceFromBird .P₁) :=
    (h_physical.2 .P₁).1
  have htwiceSI := h_twice UnitChoices.SI
  have hP₁ := h_inverseSquare.inverseSquare .P₁ UnitChoices.SI
  have hP₂ := h_inverseSquare.inverseSquare .P₂ UnitChoices.SI
  unfold distanceInMeters at hd₁
  unfold acousticIntensityInWattsPerSquareMeter
  rw [htwiceSI] at hP₂
  have hdne :
      distanceReadout UnitChoices.SI (setup.distanceFromBird .P₁) ≠ 0 :=
    ne_of_gt hd₁
  nlinarith [mul_pos Real.pi_pos (sq_pos_of_ne_zero hdne)]

/-!
The intensity ratio is therefore four, so the exact sound-level drop is
`10 log10 4`, approximately `6.0206 dB`.  Rounded to the displayed tenth of a
decibel this is `6.0 dB`, source choice A.

This formalizes `thm:physics:phyx_mini_0191:target`.  Neither the exact
logarithmic value nor the matching answer occurs in any premise.
-/
theorem problem_phyx_mini_0191
    (setup : BirdPointSourceSoundSetup)
    (h_scenario : MatchesPointSourceScenario setup)
    (h_figure : MatchesSuppliedFigure setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_twice : MovedToTwiceTheDistance setup)
    (h_inverseSquare : SatisfiesIsotropicInverseSquareLaw setup) :
    soundLevelDropInDecibels setup = 10 * Real.logb 10 4 ∧
      MatchesAnswerToNearestTenthDecibel setup .A := by
  have hquarter := intensityAtP₂_eq_oneQuarter_intensityAtP₁
    setup h_physical h_twice h_inverseSquare
  have hI₁pos : 0 < acousticIntensityInWattsPerSquareMeter
      (setup.acousticIntensityAt .P₁) := (h_physical.2 .P₁).2
  have hratio :
      acousticIntensityInWattsPerSquareMeter (setup.acousticIntensityAt .P₁) /
          acousticIntensityInWattsPerSquareMeter (setup.acousticIntensityAt .P₂) = 4 := by
    rw [hquarter]
    field_simp
  have hdrop : soundLevelDropInDecibels setup = 10 * Real.logb 10 4 := by
    rw [soundLevelDropInDecibels, hratio]
  constructor
  · exact hdrop
  · unfold MatchesAnswerToNearestTenthDecibel
    rw [hdrop]
    simp only [displayedDropInDecibels]
    have hpowLower : (10 : ℝ) ^ 119 ≤ (4 : ℝ) ^ 200 := by
      norm_num
    have hpowUpper : (4 : ℝ) ^ 200 ≤ (10 : ℝ) ^ 121 := by
      norm_num
    have hlogLower :=
      (Real.logb_le_logb (b := (10 : ℝ)) (x := (10 : ℝ) ^ 119)
        (y := (4 : ℝ) ^ 200) (by norm_num) (by positivity) (by positivity)).2
        hpowLower
    have hlogUpper :=
      (Real.logb_le_logb (b := (10 : ℝ)) (x := (4 : ℝ) ^ 200)
        (y := (10 : ℝ) ^ 121) (by norm_num) (by positivity) (by positivity)).2
        hpowUpper
    rw [Real.logb_pow, Real.logb_pow] at hlogLower hlogUpper
    norm_num at hlogLower hlogUpper
    rw [abs_le]
    constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0191
