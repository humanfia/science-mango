import Mathlib.Analysis.SpecialFunctions.Log.Base
import Physlib.SpaceAndTime.Space.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0216

open Dimension

/-!
# Sound-level advantage for the listener below a fireworks explosion

A fireworks shell explodes 100 m above level ground.  One listener is directly
below the shell, and a second listener is 200 m away horizontally.  The
two-dimensional `Space 2` coordinates below are metre readouts in the vertical
cross-section shown by the primary figure.

Physical lengths, the effective acoustic power of the common explosion, and
the received acoustic intensities are Physlib dimensionful quantities.  Real
scalars are used only for coordinate/unit readouts, dimensionless intensity
ratios, and sound-level differences measured in decibels.
-/

/-! ## Dimensionful acoustic quantities and unit readouts -/

/-- A nonnegative physical distance, independent of the chosen unit system. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 NNReal)

/--
Effective acoustic power of the explosion, with SI unit watt and dimension
`mass * length^2 / time^3`.
-/
abbrev AcousticPowerQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/--
Acoustic intensity, with SI unit watt per square metre and dimension
`mass / time^3`.
-/
abbrev AcousticIntensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical length in a coherent choice of units. -/
def lengthReadout (units : UnitChoices) (length : AcousticLength) : ℝ :=
  ((length units).val : ℝ)

/-- Read an acoustic power in a coherent choice of units. -/
def acousticPowerReadout
    (units : UnitChoices) (power : AcousticPowerQuantity) : ℝ :=
  ((power units).val : ℝ)

/-- Read an acoustic intensity in a coherent choice of units. -/
def acousticIntensityReadout
    (units : UnitChoices) (intensity : AcousticIntensityQuantity) : ℝ :=
  ((intensity units).val : ℝ)

/-- SI-metre readout of a physical length. -/
def lengthInMeters (length : AcousticLength) : ℝ :=
  lengthReadout UnitChoices.SI length

/-- SI-watt readout of the effective emitted acoustic power. -/
def acousticPowerInWatts (power : AcousticPowerQuantity) : ℝ :=
  acousticPowerReadout UnitChoices.SI power

/-- SI watt-per-square-metre readout of an acoustic intensity. -/
def acousticIntensityInWattsPerSquareMeter
    (intensity : AcousticIntensityQuantity) : ℝ :=
  acousticIntensityReadout UnitChoices.SI intensity

/-! ## Physical and figure labels -/

/-- The two people whose received sound levels are compared. -/
inductive ListenerLabel where
  | directlyBelow
  | horizontallyDisplaced
  deriving DecidableEq, Repr

/-- All labeled physical objects in the supplied figure. -/
inductive FigureLabel where
  | fireworksShell
  | personDirectlyBelow
  | personHorizontallyDisplaced
  deriving DecidableEq, Repr

/-- Physical roles assigned to the three figure labels. -/
inductive FigureRole where
  | acousticSource
  | directlyBelowListener
  | horizontallyDisplacedListener
  deriving DecidableEq, Repr

/-- Type of acoustic source used by the idealized problem model. -/
inductive AcousticSourceKind where
  | fireworksShellExplosion
  | other
  deriving DecidableEq, Repr

/-- Propagation geometry used to compare the two sound intensities. -/
inductive AcousticSpreadingModel where
  | isotropicSphericalFreeField
  | other
  deriving DecidableEq, Repr

/-- Medium through which the explosion sound reaches both listeners. -/
inductive AcousticMedium where
  | ambientAir
  | other
  deriving DecidableEq, Repr

/-- Associate each listener with the corresponding person in the figure. -/
def figureLabelOfListener : ListenerLabel → FigureLabel
  | .directlyBelow => .personDirectlyBelow
  | .horizontallyDisplaced => .personHorizontallyDisplaced

/--
Qualitative roles and metre-coordinate positions read from the primary image.
The horizontal coordinate is index `0` and the vertical coordinate is index
`1`; the ground is represented by vertical coordinate zero.
-/
structure FireworksFigure where
  role : FigureLabel → FigureRole
  positionInMeterCoordinates : FigureLabel → Space 2

/-!
Physical quantities for the common explosion and the two listeners.

The two source-to-listener distances and intensities are independent fields
until the Euclidean-geometry and inverse-square premises below relate them.
In particular, neither the factor-five intensity ratio nor a decibel answer is
stored in the setup.
-/
structure FireworksSoundSetup where
  sourceKind : AcousticSourceKind
  spreadingModel : AcousticSpreadingModel
  propagationMedium : AcousticMedium
  shellHeightAboveGround : AcousticLength
  horizontalListenerSeparation : AcousticLength
  effectiveEmittedAcousticPower : AcousticPowerQuantity
  sourceToListenerDistance : ListenerLabel → AcousticLength
  acousticIntensityAt : ListenerLabel → AcousticIntensityQuantity
  figure : FireworksFigure

/-! ## Scenario, figure data, geometry, and governing acoustics -/

/--
The idealized physical model used by the textbook comparison: the one
fireworks explosion is an isotropic source in ambient air with free-field
spherical spreading.
-/
def MatchesFireworksScenario (setup : FireworksSoundSetup) : Prop :=
  setup.sourceKind = .fireworksShellExplosion ∧
    setup.spreadingModel = .isotropicSphericalFreeField ∧
    setup.propagationMedium = .ambientAir

/-!
Primary-image evidence and the two printed measurements.  This predicate
places the shell 100 m above the directly-below person and places the second
person 200 m away along level ground.  It contains no path-length ratio,
intensity ratio, logarithmic value, or selected answer.
-/
def MatchesSuppliedFigure (setup : FireworksSoundSetup) : Prop :=
  setup.figure.role .fireworksShell = .acousticSource ∧
    setup.figure.role .personDirectlyBelow = .directlyBelowListener ∧
    setup.figure.role .personHorizontallyDisplaced =
      .horizontallyDisplacedListener ∧
    lengthInMeters setup.shellHeightAboveGround = 100 ∧
    lengthInMeters setup.horizontalListenerSeparation = 200 ∧
    setup.figure.positionInMeterCoordinates .fireworksShell 0 = 0 ∧
    setup.figure.positionInMeterCoordinates .fireworksShell 1 =
      lengthInMeters setup.shellHeightAboveGround ∧
    setup.figure.positionInMeterCoordinates .personDirectlyBelow 0 = 0 ∧
    setup.figure.positionInMeterCoordinates .personDirectlyBelow 1 = 0 ∧
    setup.figure.positionInMeterCoordinates .personHorizontallyDisplaced 0 =
      lengthInMeters setup.horizontalListenerSeparation ∧
    setup.figure.positionInMeterCoordinates .personHorizontallyDisplaced 1 = 0

/-!
The physical source-to-listener path length is the Euclidean distance between
the corresponding metre-coordinate points in the depicted vertical section.
This general geometry bridge does not state the problem-specific ratio of the
two distances.
-/
structure SourceDistancesFollowFigureGeometry
    (setup : FireworksSoundSetup) : Prop where
  distance_is_euclidean : ∀ listener : ListenerLabel,
    lengthInMeters (setup.sourceToListenerDistance listener) =
      dist (setup.figure.positionInMeterCoordinates .fireworksShell)
        (setup.figure.positionInMeterCoordinates
          (figureLabelOfListener listener))

/-- Positivity and nondegeneracy conditions for the physical quantities. -/
def HasPhysicalAcousticParameters (setup : FireworksSoundSetup) : Prop :=
  0 < acousticPowerInWatts setup.effectiveEmittedAcousticPower ∧
    0 < lengthInMeters setup.shellHeightAboveGround ∧
    0 < lengthInMeters setup.horizontalListenerSeparation ∧
    ∀ listener : ListenerLabel,
      0 < lengthInMeters (setup.sourceToListenerDistance listener) ∧
        0 < acousticIntensityInWattsPerSquareMeter
          (setup.acousticIntensityAt listener)

/-!
The general inverse-square intensity law for an isotropic point source.  In
every coherent unit system, the common source power equals the received
intensity times the area of the sphere through the listener.  This premise
does not state a factor-five intensity ratio or any decibel conclusion.
-/
structure SatisfiesIsotropicInverseSquareLaw
    (setup : FireworksSoundSetup) : Prop where
  inverseSquare : ∀ listener : ListenerLabel, ∀ units : UnitChoices,
    4 * Real.pi *
          lengthReadout units (setup.sourceToListenerDistance listener) ^ 2 *
          acousticIntensityReadout units
            (setup.acousticIntensityAt listener) =
      acousticPowerReadout units setup.effectiveEmittedAcousticPower

/-! ## Requested sound-level comparison -/

/-!
How many decibels greater the sound intensity level is for the person directly
below the shell than for the horizontally displaced person.  This is the
standard general conversion `10 log10 (I_near / I_far)` and has no built-in
numerical answer.
-/
def directlyBelowSoundLevelAdvantageInDecibels
    (setup : FireworksSoundSetup) : ℝ :=
  10 * Real.logb 10
    (acousticIntensityInWattsPerSquareMeter
        (setup.acousticIntensityAt .directlyBelow) /
      acousticIntensityInWattsPerSquareMeter
        (setup.acousticIntensityAt .horizontallyDisplaced))

/-- Labels of the four answer choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The displayed whole-decibel value beside each answer label. -/
def displayedSoundLevelDifferenceInDecibels : AnswerChoice → ℝ
  | .A => 13
  | .B => 11
  | .C => 9
  | .D => 7

/-!
Agreement with a displayed answer after rounding the exact level difference
to the nearest whole decibel.  This predicate is generic in the answer choice
and does not select D by definition.
-/
def MatchesAnswerToNearestWholeDecibel
    (setup : FireworksSoundSetup) (choice : AnswerChoice) : Prop :=
  |directlyBelowSoundLevelAdvantageInDecibels setup -
      displayedSoundLevelDifferenceInDecibels choice| ≤ (1 / 2 : ℝ)

/-!
The 100 m vertical leg and 200 m horizontal leg imply that the squared slant
distance to the displaced listener is five times the squared vertical
distance to the directly-below listener.  This is a derived geometric result,
not a premise of the physical model.
-/
lemma displacedDistance_sq_eq_five_mul_directDistance_sq
    (setup : FireworksSoundSetup)
    (h_figure : MatchesSuppliedFigure setup)
    (h_geometry : SourceDistancesFollowFigureGeometry setup) :
    lengthInMeters
          (setup.sourceToListenerDistance .horizontallyDisplaced) ^ 2 =
      5 * lengthInMeters
          (setup.sourceToListenerDistance .directlyBelow) ^ 2 := by
  rcases h_figure with
    ⟨_, _, _, hheight, hseparation, hsx, hsy, hdx, hdy, hfx, hfy⟩
  rw [h_geometry.distance_is_euclidean .horizontallyDisplaced,
    h_geometry.distance_is_euclidean .directlyBelow]
  norm_num [Space.dist_eq, Fin.sum_univ_two, figureLabelOfListener,
    hsx, hsy, hdx, hdy, hfx, hfy, hheight, hseparation]

/-!
Combining the derived distance relation with spherical spreading makes the
far listener's acoustic intensity one fifth of the directly-below listener's
intensity.  This is an intermediate conclusion, not a governing-law field.
-/
lemma displacedIntensity_eq_oneFifth_directIntensity
    (setup : FireworksSoundSetup)
    (h_figure : MatchesSuppliedFigure setup)
    (h_geometry : SourceDistancesFollowFigureGeometry setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_inverseSquare : SatisfiesIsotropicInverseSquareLaw setup) :
    acousticIntensityInWattsPerSquareMeter
        (setup.acousticIntensityAt .horizontallyDisplaced) =
      acousticIntensityInWattsPerSquareMeter
        (setup.acousticIntensityAt .directlyBelow) / 5 := by
  have hdist := displacedDistance_sq_eq_five_mul_directDistance_sq
    setup h_figure h_geometry
  have hfar :=
    h_inverseSquare.inverseSquare .horizontallyDisplaced UnitChoices.SI
  have hnear :=
    h_inverseSquare.inverseSquare .directlyBelow UnitChoices.SI
  change 4 * Real.pi *
      lengthInMeters
        (setup.sourceToListenerDistance .horizontallyDisplaced) ^ 2 *
      acousticIntensityInWattsPerSquareMeter
        (setup.acousticIntensityAt .horizontallyDisplaced) =
      acousticPowerInWatts setup.effectiveEmittedAcousticPower at hfar
  change 4 * Real.pi *
      lengthInMeters (setup.sourceToListenerDistance .directlyBelow) ^ 2 *
      acousticIntensityInWattsPerSquareMeter
        (setup.acousticIntensityAt .directlyBelow) =
      acousticPowerInWatts setup.effectiveEmittedAcousticPower at hnear
  rw [hdist] at hfar
  have hnearDistancePos :=
    (h_physical.2.2.2 .directlyBelow).1
  have hcoeff : 4 * Real.pi *
      lengthInMeters (setup.sourceToListenerDistance .directlyBelow) ^ 2 ≠
        0 := by
    positivity
  have hratio : 5 *
        acousticIntensityInWattsPerSquareMeter
          (setup.acousticIntensityAt .horizontallyDisplaced) =
      acousticIntensityInWattsPerSquareMeter
        (setup.acousticIntensityAt .directlyBelow) := by
    apply (mul_left_cancel₀ hcoeff)
    calc
      (4 * Real.pi *
          lengthInMeters
            (setup.sourceToListenerDistance .directlyBelow) ^ 2) *
          (5 * acousticIntensityInWattsPerSquareMeter
            (setup.acousticIntensityAt .horizontallyDisplaced)) =
        4 * Real.pi *
          (5 * lengthInMeters
            (setup.sourceToListenerDistance .directlyBelow) ^ 2) *
          acousticIntensityInWattsPerSquareMeter
            (setup.acousticIntensityAt .horizontallyDisplaced) := by ring
      _ = acousticPowerInWatts setup.effectiveEmittedAcousticPower := hfar
      _ = (4 * Real.pi *
          lengthInMeters
            (setup.sourceToListenerDistance .directlyBelow) ^ 2) *
          acousticIntensityInWattsPerSquareMeter
            (setup.acousticIntensityAt .directlyBelow) := hnear.symm
  linarith

/-!
The person directly below the fireworks therefore receives an intensity five
times as large, so the exact sound-level advantage is `10 log10 5`, which
rounds to 7 dB and hence selects answer D.

This formalizes `thm:physics:phyx_mini_0216:target`.  Neither the factor-five
result, the logarithmic value, nor choice D appears in any premise.
-/
theorem problem_phyx_mini_0216
    (setup : FireworksSoundSetup)
    (h_scenario : MatchesFireworksScenario setup)
    (h_figure : MatchesSuppliedFigure setup)
    (h_geometry : SourceDistancesFollowFigureGeometry setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_inverseSquare : SatisfiesIsotropicInverseSquareLaw setup) :
    directlyBelowSoundLevelAdvantageInDecibels setup =
        10 * Real.logb 10 5 ∧
      MatchesAnswerToNearestWholeDecibel setup .D := by
  have hIntensity := displacedIntensity_eq_oneFifth_directIntensity
    setup h_figure h_geometry h_physical h_inverseSquare
  have hDirectIntensityPos :=
    (h_physical.2.2.2 .directlyBelow).2
  have hDirectIntensityNe :
      acousticIntensityInWattsPerSquareMeter
        (setup.acousticIntensityAt .directlyBelow) ≠ 0 :=
    ne_of_gt hDirectIntensityPos
  have hAdvantage : directlyBelowSoundLevelAdvantageInDecibels setup =
      10 * Real.logb 10 5 := by
    simp [directlyBelowSoundLevelAdvantageInDecibels, hIntensity,
      hDirectIntensityNe]
  have hLogTenPos : 0 < Real.log 10 :=
    Real.log_pos (by norm_num)
  have hLowerPower : (10 : ℝ) ^ 13 ≤ (5 : ℝ) ^ 20 := by
    norm_num
  have hLowerLog :=
    Real.log_le_log (by positivity : 0 < (10 : ℝ) ^ 13) hLowerPower
  rw [Real.log_pow, Real.log_pow] at hLowerLog
  norm_num at hLowerLog
  have hUpperPower : (5 : ℝ) ^ 4 ≤ (10 : ℝ) ^ 3 := by
    norm_num
  have hUpperLog :=
    Real.log_le_log (by positivity : 0 < (5 : ℝ) ^ 4) hUpperPower
  rw [Real.log_pow, Real.log_pow] at hUpperLog
  norm_num at hUpperLog
  have hLogbLower : (13 : ℝ) / 20 ≤ Real.log 5 / Real.log 10 := by
    rw [le_div_iff₀ hLogTenPos]
    nlinarith [hLowerLog]
  have hLogbUpper : Real.log 5 / Real.log 10 ≤ (3 : ℝ) / 4 := by
    rw [div_le_iff₀ hLogTenPos]
    nlinarith [hUpperLog]
  constructor
  · exact hAdvantage
  · rw [MatchesAnswerToNearestWholeDecibel, hAdvantage]
    change |10 * (Real.log 5 / Real.log 10) - 7| ≤ (1 / 2 : ℝ)
    rw [abs_le]
    constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0216
