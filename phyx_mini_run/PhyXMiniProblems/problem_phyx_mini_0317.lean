import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Sound-level difference between two atmospheric point sources

Two atmospheric sources `A` and `B` emit sound isotropically with constant
power.  The supplied graph plots sound intensity level `β` against radial
distance `r`.  Its marked vertical levels are `β₁ = 85 dB` and `β₂ = 65 dB`;
these marks are four equal grid intervals apart.  At the graph's `100 m` mark,
curve `B` passes through `β₁`, while curve `A` is one grid interval higher.

The question asks for the level difference at `10 m`, outside the displayed
`100 m` to `1000 m` range.  The constant-power inverse-square model makes the
intensity ratio, and hence the decibel difference, independent of radius.

Distance, acoustic power, and acoustic intensity are represented by Physlib
dimensionful quantities.  Real numbers occur only as coherent-unit readouts,
dimensionless ratios, and logarithmic sound levels measured in decibels.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0317

open Dimension

/-! ## Dimensionful acoustic quantities and coherent-unit readouts -/

/-- A nonnegative physical radial distance from a sound source. -/
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

/-- SI metre readout of a radial distance. -/
def distanceInMeters (distance : LengthMagnitude) : ℝ :=
  distanceReadout UnitChoices.SI distance

/-- SI watt readout of an emitted acoustic power. -/
def acousticPowerInWatts (power : AcousticPowerQuantity) : ℝ :=
  acousticPowerReadout UnitChoices.SI power

/-- SI watt-per-square-metre readout of an acoustic intensity. -/
def acousticIntensityInWattsPerSquareMeter
    (intensity : AcousticIntensityQuantity) : ℝ :=
  acousticIntensityReadout UnitChoices.SI intensity

/-! ## Source, radius, and graph labels -/

/-- The two curves and atmospheric sound sources labeled in the figure. -/
inductive SourceLabel where
  | A
  | B
  deriving DecidableEq, Repr

/-!
Named radial positions.  The `requested10m` point comes from the question;
the remaining positions are the labeled marks on the supplied graph.
-/
inductive RadialPosition where
  | requested10m
  | graph100m
  | graph500m
  | graph1000m
  deriving DecidableEq, Repr

/-- Physical type of an idealized atmospheric acoustic source. -/
inductive AcousticSourceKind where
  | isotropicPointSource
  | other
  deriving DecidableEq, Repr

/-- Time dependence of a source's emitted acoustic power. -/
inductive EmissionRegime where
  | constantPower
  | timeVarying
  deriving DecidableEq, Repr

/-- Propagation medium named in the physical scenario. -/
inductive AcousticMedium where
  | atmosphere
  | other
  deriving DecidableEq, Repr

/-- Physical quantity represented by a graph axis. -/
inductive GraphAxisQuantity where
  | radialDistanceInMeters
  | soundLevelInDecibels
  deriving DecidableEq, Repr

/-!
Metadata and scalar readouts attached to the supplied graph.  The two `β`
fields are sound-level readouts in decibels, not physical intensities.
-/
structure SoundLevelGraph where
  horizontalAxisQuantity : GraphAxisQuantity
  verticalAxisQuantity : GraphAxisQuantity
  curveVisible : SourceLabel → Prop
  beta1Decibels : ℝ
  beta2Decibels : ℝ

/-!
The size of one vertical grid step.  In the image, `β₁` and `β₂` are separated
by four equal grid intervals.  This is a generic graph-scale conversion and
does not mention the requested `10 m` sound-level difference.
-/
def verticalGridStepInDecibels (graph : SoundLevelGraph) : ℝ :=
  (graph.beta1Decibels - graph.beta2Decibels) / 4

/-!
Physical setup for the two-source comparison.  Intensities at all named
radii remain independent fields until related by the governing inverse-square
law.  In particular, no intensity ratio or requested level difference is
stored here.
-/
structure AtmosphericTwoSourceSetup where
  sourceKind : SourceLabel → AcousticSourceKind
  emissionRegime : SourceLabel → EmissionRegime
  propagationMedium : AcousticMedium
  emittedAcousticPower : SourceLabel → AcousticPowerQuantity
  referenceIntensity : AcousticIntensityQuantity
  radius : RadialPosition → LengthMagnitude
  acousticIntensityAt : SourceLabel → RadialPosition → AcousticIntensityQuantity
  graph : SoundLevelGraph

/-!
Sound intensity level in decibels, using the standard general relation
`β = 10 log10 (I / I_ref)` and same-unit SI intensity readouts.
-/
def soundLevelInDecibels
    (setup : AtmosphericTwoSourceSetup)
    (source : SourceLabel) (position : RadialPosition) : ℝ :=
  10 * Real.logb 10
    (acousticIntensityInWattsPerSquareMeter
        (setup.acousticIntensityAt source position) /
      acousticIntensityInWattsPerSquareMeter setup.referenceIntensity)

/-!
The positive magnitude of the level difference between curves `A` and `B` at
a common radius.  This definition contains no expected numerical answer.
-/
def soundLevelDifferenceInDecibels
    (setup : AtmosphericTwoSourceSetup) (position : RadialPosition) : ℝ :=
  |soundLevelInDecibels setup .A position -
    soundLevelInDecibels setup .B position|

/-! ## Assumptions: scenario, figure/data readouts, and governing law -/

/-!
Both labeled atmospheric sources are isotropic point sources emitting at
constant (not necessarily equal) power through the atmosphere.
-/
def MatchesAtmosphericSourceScenario
    (setup : AtmosphericTwoSourceSetup) : Prop :=
  (∀ source : SourceLabel,
      setup.sourceKind source = .isotropicPointSource ∧
        setup.emissionRegime source = .constantPower) ∧
    setup.propagationMedium = .atmosphere

/-!
The numerical distance readouts in the question and on the horizontal graph
axis.  Recording `10 m` identifies the requested position but says nothing
about either source's level there.
-/
structure MatchesProblemDistanceData
    (setup : AtmosphericTwoSourceSetup) : Prop where
  requestedRadiusMeters :
    distanceInMeters (setup.radius .requested10m) = 10
  graphLeftRadiusMeters :
    distanceInMeters (setup.radius .graph100m) = 100
  graphMiddleRadiusMeters :
    distanceInMeters (setup.radius .graph500m) = 500
  graphRightRadiusMeters :
    distanceInMeters (setup.radius .graph1000m) = 1000

/-!
Primary-image evidence from the plotted graph:

* the horizontal axis is radial distance in metres and the vertical axis is
  sound level in decibels;
* curves `A` and `B` are both visible;
* `β₁ = 85 dB` and `β₂ = 65 dB`;
* at `100 m`, curve `B` meets `β₁`, while curve `A` is one of the four equal
  vertical grid steps higher; and
* both plotted curves decrease across the labeled graph range.

These are graph readouts at `100 m`, `500 m`, and `1000 m`; no level or level
difference at the requested `10 m` position occurs in this structure.
-/
structure MatchesSuppliedSoundLevelGraph
    (setup : AtmosphericTwoSourceSetup) : Prop where
  horizontalAxis :
    setup.graph.horizontalAxisQuantity = .radialDistanceInMeters
  verticalAxis :
    setup.graph.verticalAxisQuantity = .soundLevelInDecibels
  curveAVisible : setup.graph.curveVisible .A
  curveBVisible : setup.graph.curveVisible .B
  beta1Value : setup.graph.beta1Decibels = 85
  beta2Value : setup.graph.beta2Decibels = 65
  curveBAt100m :
    soundLevelInDecibels setup .B .graph100m = setup.graph.beta1Decibels
  curveAAt100m :
    soundLevelInDecibels setup .A .graph100m =
      setup.graph.beta1Decibels + verticalGridStepInDecibels setup.graph
  curveADecreasesTo500m :
    soundLevelInDecibels setup .A .graph500m <
      soundLevelInDecibels setup .A .graph100m
  curveADecreasesTo1000m :
    soundLevelInDecibels setup .A .graph1000m <
      soundLevelInDecibels setup .A .graph500m
  curveBDecreasesTo500m :
    soundLevelInDecibels setup .B .graph500m <
      soundLevelInDecibels setup .B .graph100m
  curveBDecreasesTo1000m :
    soundLevelInDecibels setup .B .graph1000m <
      soundLevelInDecibels setup .B .graph500m

/-!
The conventional common reference intensity for sound intensity level is
`10⁻¹² W/m²`.  This calibration is independent of the source and radius and
does not determine the requested difference, which cancels the common
reference.
-/
def UsesStandardSoundIntensityReference
    (setup : AtmosphericTwoSourceSetup) : Prop :=
  acousticIntensityInWattsPerSquareMeter setup.referenceIntensity =
    1 / (10 : ℝ) ^ 12

/-! Strict positivity and nondegeneracy of all physical acoustic quantities. -/
def HasPhysicalAcousticParameters
    (setup : AtmosphericTwoSourceSetup) : Prop :=
  0 < acousticIntensityInWattsPerSquareMeter setup.referenceIntensity ∧
    (∀ source : SourceLabel,
      0 < acousticPowerInWatts (setup.emittedAcousticPower source)) ∧
    (∀ position : RadialPosition,
      0 < distanceInMeters (setup.radius position)) ∧
    ∀ source : SourceLabel, ∀ position : RadialPosition,
      0 < acousticIntensityInWattsPerSquareMeter
        (setup.acousticIntensityAt source position)

/-!
The spherical inverse-square intensity law for each isotropic source.  For
every named radius and coherent unit system, the emitted power equals
`4 * π * r^2 * I`.  This generic law contains neither a particular power
ratio nor the requested `5 dB` conclusion.
-/
structure SatisfiesIsotropicInverseSquareLaw
    (setup : AtmosphericTwoSourceSetup) : Prop where
  inverseSquare :
    ∀ source : SourceLabel, ∀ position : RadialPosition,
      ∀ units : UnitChoices,
        4 * Real.pi * distanceReadout units (setup.radius position) ^ 2 *
              acousticIntensityReadout units
                (setup.acousticIntensityAt source position) =
          acousticPowerReadout units (setup.emittedAcousticPower source)

/-! ## Derived relations and displayed answers -/

/-!
Because both sources obey the inverse-square law, their intensity ratio and
therefore their decibel-level difference are independent of the common radial
position.  This is derived from the governing law, not assumed in the setup.
-/
lemma soundLevelDifference_independentOfRadius
    (setup : AtmosphericTwoSourceSetup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_inverseSquare : SatisfiesIsotropicInverseSquareLaw setup)
    (first second : RadialPosition) :
    soundLevelDifferenceInDecibels setup first =
      soundLevelDifferenceInDecibels setup second := by
  have intensityRatio_eq_powerRatio (position : RadialPosition) :
      acousticIntensityInWattsPerSquareMeter
            (setup.acousticIntensityAt .A position) /
          acousticIntensityInWattsPerSquareMeter
            (setup.acousticIntensityAt .B position) =
        acousticPowerInWatts (setup.emittedAcousticPower .A) /
          acousticPowerInWatts (setup.emittedAcousticPower .B) := by
    have hRadius := h_physical.2.2.1 position
    have hA :=
      h_inverseSquare.inverseSquare .A position UnitChoices.SI
    have hB :=
      h_inverseSquare.inverseSquare .B position UnitChoices.SI
    change
      4 * Real.pi * distanceInMeters (setup.radius position) ^ 2 *
            acousticIntensityInWattsPerSquareMeter
              (setup.acousticIntensityAt .A position) =
        acousticPowerInWatts (setup.emittedAcousticPower .A) at hA
    change
      4 * Real.pi * distanceInMeters (setup.radius position) ^ 2 *
            acousticIntensityInWattsPerSquareMeter
              (setup.acousticIntensityAt .B position) =
        acousticPowerInWatts (setup.emittedAcousticPower .B) at hB
    rw [← hA, ← hB]
    field_simp [Real.pi_ne_zero, ne_of_gt hRadius]
  have levelDifference_eq_abs_intensityRatio (position : RadialPosition) :
      soundLevelDifferenceInDecibels setup position =
        |10 * Real.logb 10
          (acousticIntensityInWattsPerSquareMeter
                (setup.acousticIntensityAt .A position) /
            acousticIntensityInWattsPerSquareMeter
                (setup.acousticIntensityAt .B position))| := by
    have hA := h_physical.2.2.2 .A position
    have hB := h_physical.2.2.2 .B position
    have hRef := h_physical.1
    rw [soundLevelDifferenceInDecibels, soundLevelInDecibels,
      soundLevelInDecibels, ← mul_sub,
      ← Real.logb_div
        (div_ne_zero hA.ne' hRef.ne') (div_ne_zero hB.ne' hRef.ne')]
    have hCancelReference :
        (acousticIntensityInWattsPerSquareMeter
              (setup.acousticIntensityAt .A position) /
            acousticIntensityInWattsPerSquareMeter setup.referenceIntensity) /
          (acousticIntensityInWattsPerSquareMeter
              (setup.acousticIntensityAt .B position) /
            acousticIntensityInWattsPerSquareMeter setup.referenceIntensity) =
        acousticIntensityInWattsPerSquareMeter
              (setup.acousticIntensityAt .A position) /
          acousticIntensityInWattsPerSquareMeter
              (setup.acousticIntensityAt .B position) := by
      field_simp
    rw [hCancelReference]
  rw [levelDifference_eq_abs_intensityRatio first,
    levelDifference_eq_abs_intensityRatio second,
    intensityRatio_eq_powerRatio first,
    intensityRatio_eq_powerRatio second]

/-!
The graph scale and the two curve readings at `100 m` give a one-grid-step
separation of `(85 - 65) / 4 = 5 dB`.  This remains a derived statement.
-/
lemma graphSoundLevelDifferenceAt100m
    (setup : AtmosphericTwoSourceSetup)
    (h_graph : MatchesSuppliedSoundLevelGraph setup) :
    soundLevelDifferenceInDecibels setup .graph100m = 5 := by
  rw [soundLevelDifferenceInDecibels, h_graph.curveAAt100m,
    h_graph.curveBAt100m]
  norm_num [verticalGridStepInDecibels, h_graph.beta1Value,
    h_graph.beta2Value]

/-- Labels of the four multiple-choice answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Sound-level difference in decibels printed beside each answer label. -/
def AnswerChoice.decibels : AnswerChoice → ℝ
  | .A => 35 / 10
  | .B => 4
  | .C => 45 / 10
  | .D => 5

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
A displayed answer is uniquely closest to the physically derived sound-level
difference.  This generic comparison does not privilege choice D.
-/
def IsClosestDisplayedAnswer
    (actualDecibels : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |actualDecibels - choice.decibels| <
      |actualDecibels - other.decibels|

/-!
Physics formalization target for
`thm:physics:phyx_mini_0317:target`.

The graph fixes the `100 m` separation at one `5 dB` grid step.  The two
constant-power inverse-square laws preserve this difference when extrapolating
to the requested `10 m` radius, making the recorded choice D uniquely closest.
Neither the requested level difference nor its answer choice is an assumption.
-/
theorem problem_phyx_mini_0317
    (setup : AtmosphericTwoSourceSetup)
    (h_scenario : MatchesAtmosphericSourceScenario setup)
    (h_distances : MatchesProblemDistanceData setup)
    (h_graph : MatchesSuppliedSoundLevelGraph setup)
    (h_reference : UsesStandardSoundIntensityReference setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_inverseSquare : SatisfiesIsotropicInverseSquareLaw setup) :
    soundLevelDifferenceInDecibels setup .requested10m = 5 ∧
      IsClosestDisplayedAnswer
        (soundLevelDifferenceInDecibels setup .requested10m)
        recordedAnswerChoice := by
  have hRequestedDifference :
      soundLevelDifferenceInDecibels setup .requested10m = 5 :=
    (soundLevelDifference_independentOfRadius setup h_physical h_inverseSquare
      .requested10m .graph100m).trans
        (graphSoundLevelDifferenceAt100m setup h_graph)
  refine ⟨hRequestedDifference, ?_⟩
  rw [hRequestedDifference]
  intro other hOther
  cases other with
  | A => norm_num [recordedAnswerChoice, AnswerChoice.decibels]
  | B => norm_num [recordedAnswerChoice, AnswerChoice.decibels]
  | C => norm_num [recordedAnswerChoice, AnswerChoice.decibels]
  | D => exact (hOther rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0317
