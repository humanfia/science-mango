import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/-!
# Four equally spaced in-phase point sources

This file models problem `phyx_mini_0313`.  The primary figure places four
isotropic point sources `S₁`, `S₂`, `S₃`, and `S₄`, in that order, on one
horizontal axis, with adjacent separation `d`; the observation point `P` lies
to the right of all four sources.  The sources have common wavelength `λ`,
common displacement amplitude `s_m`, and common initial phase.  The stated
case is `d = λ`, and propagation attenuation on the way to `P` is neglected.

The notation `s_m` is modeled as a nonnegative longitudinal-displacement
amplitude, hence as a Physlib dimensionful length.  Signed source coordinates
are kept separate from nonnegative path lengths and amplitudes.  Phase lives
in `Real.Angle`, so equality already means equality modulo a full turn.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0313

open Dimension
open scoped BigOperators

/-! ## Dimensionful acoustic quantities and readouts -/

/-- A nonnegative physical length such as a wavelength or ray-path length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical coordinate on the horizontal axis in the figure. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative longitudinal-displacement amplitude of a sound wave. -/
abbrev AcousticDisplacementAmplitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- Read a nonnegative physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed horizontal coordinate in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (coordinate : SignedLengthQuantity) : ℝ :=
  (coordinate {UnitChoices.SI with length := unit}).val

/-- Read a sound-displacement amplitude in a selected length unit. -/
def amplitudeReadout
    (unit : LengthUnit) (amplitude : AcousticDisplacementAmplitude) : ℝ :=
  ((amplitude {UnitChoices.SI with length := unit}).val : ℝ)

/-! ## Sources and figure-derived geometry -/

/-- The four source labels printed from left to right in the figure. -/
inductive SourceLabel where
  | S1
  | S2
  | S3
  | S4
  deriving DecidableEq, Fintype, Repr

/-- The angular radiation pattern of a sound source. -/
inductive RadiationPattern where
  | isotropic
  | anisotropic
  deriving DecidableEq, Repr

/-- A monochromatic point source with physical wavelength and amplitude. -/
structure PointSoundSource where
  wavelength : LengthQuantity
  displacementAmplitude : AcousticDisplacementAmplitude
  initialPhase : Real.Angle
  radiationPattern : RadiationPattern

/-!
The independent objects, physical quantities, and observables in the problem.

The received amplitudes and phases, and especially `netAmplitudeAtP`, are left
as independent physical observables.  They acquire their physical meaning only
through the propagation, attenuation, and superposition laws below; no field
assigns the requested multiple of `s_m`.
-/
structure FourSourceSoundSetup where
  coordinateUnit : LengthUnit
  source : SourceLabel → PointSoundSource
  sourcePositionX : SourceLabel → SignedLengthQuantity
  pointPPositionX : SignedLengthQuantity
  adjacentSpacingD : LengthQuantity
  commonWavelengthLambda : LengthQuantity
  commonSourceAmplitudeSm : AcousticDisplacementAmplitude
  rayPathLengthToP : SourceLabel → LengthQuantity
  receivedAmplitudeAtP : SourceLabel → AcousticDisplacementAmplitude
  receivedPhaseAtP : SourceLabel → Real.Angle
  netAmplitudeAtP : AcousticDisplacementAmplitude

/-!
The one-dimensional layout read from the primary image.  The four sources are
ordered `S₁, S₂, S₃, S₄`, point `P` is to their right, and each adjacent source
coordinate differs by the physical spacing `d`.  The image does not label the
distance from `S₄` to `P`, so no value is imposed on that distance.
-/
structure MatchesFourSourceFigure
    (setup : FourSourceSoundSetup) : Prop where
  sourceOrder12 :
    signedLengthReadout setup.coordinateUnit (setup.sourcePositionX .S1) <
      signedLengthReadout setup.coordinateUnit (setup.sourcePositionX .S2)
  sourceOrder23 :
    signedLengthReadout setup.coordinateUnit (setup.sourcePositionX .S2) <
      signedLengthReadout setup.coordinateUnit (setup.sourcePositionX .S3)
  sourceOrder34 :
    signedLengthReadout setup.coordinateUnit (setup.sourcePositionX .S3) <
      signedLengthReadout setup.coordinateUnit (setup.sourcePositionX .S4)
  pointPToRight :
    signedLengthReadout setup.coordinateUnit (setup.sourcePositionX .S4) <
      signedLengthReadout setup.coordinateUnit setup.pointPPositionX
  spacing12 : ∀ unit : LengthUnit,
    signedLengthReadout unit (setup.sourcePositionX .S2) -
        signedLengthReadout unit (setup.sourcePositionX .S1) =
      lengthReadout unit setup.adjacentSpacingD
  spacing23 : ∀ unit : LengthUnit,
    signedLengthReadout unit (setup.sourcePositionX .S3) -
        signedLengthReadout unit (setup.sourcePositionX .S2) =
      lengthReadout unit setup.adjacentSpacingD
  spacing34 : ∀ unit : LengthUnit,
    signedLengthReadout unit (setup.sourcePositionX .S4) -
        signedLengthReadout unit (setup.sourcePositionX .S3) =
      lengthReadout unit setup.adjacentSpacingD

/-!
The stated source data: all four point sources are isotropic, use the named
common wavelength and displacement amplitude, and emit with one initial phase.
This does not assert that the waves arrive in phase at `P`.
-/
structure HasIdenticalCoherentPointSources
    (setup : FourSourceSoundSetup) : Prop where
  isotropic : ∀ label : SourceLabel,
    (setup.source label).radiationPattern = .isotropic
  commonWavelength : ∀ label : SourceLabel,
    (setup.source label).wavelength = setup.commonWavelengthLambda
  commonAmplitude : ∀ label : SourceLabel,
    (setup.source label).displacementAmplitude =
      setup.commonSourceAmplitudeSm
  commonInitialPhase : ∀ label : SourceLabel,
    (setup.source label).initialPhase = (setup.source .S4).initialPhase

/-! The condition in the question, namely that adjacent spacing is `d = λ`. -/
def SpacingEqualsWavelength (setup : FourSourceSoundSetup) : Prop :=
  setup.adjacentSpacingD = setup.commonWavelengthLambda

/-- Positivity and nondegeneracy of the physical lengths and amplitudes. -/
structure HasPhysicalParameters
    (setup : FourSourceSoundSetup) : Prop where
  spacingPositive :
    0 < lengthReadout setup.coordinateUnit setup.adjacentSpacingD
  wavelengthPositive :
    0 < lengthReadout setup.coordinateUnit setup.commonWavelengthLambda
  sourceAmplitudePositive :
    0 < amplitudeReadout setup.coordinateUnit setup.commonSourceAmplitudeSm
  pathLengthPositive : ∀ label : SourceLabel,
    0 < lengthReadout setup.coordinateUnit (setup.rayPathLengthToP label)

/-! ## Governing geometry, propagation, and superposition laws -/

/-!
Because all objects lie on the same axis and `P` is to the right, each ray
length is the coordinate of `P` minus the corresponding source coordinate.
-/
structure SatisfiesCollinearRayGeometry
    (setup : FourSourceSoundSetup) : Prop where
  rayLength : ∀ (unit : LengthUnit) (label : SourceLabel),
    lengthReadout unit (setup.rayPathLengthToP label) =
      signedLengthReadout unit setup.pointPPositionX -
        signedLengthReadout unit (setup.sourcePositionX label)

/-!
Monochromatic propagation subtracts `2π r / λ` from the source phase.  The
phase is an element of `Real.Angle`, so paths differing by one wavelength
produce the same arrival phase.
-/
structure SatisfiesMonochromaticPropagation
    (setup : FourSourceSoundSetup) : Prop where
  phaseAtP : ∀ label : SourceLabel,
    setup.receivedPhaseAtP label =
      (setup.source label).initialPhase -
        (((2 * Real.pi) *
              (lengthReadout setup.coordinateUnit
                  (setup.rayPathLengthToP label) /
                lengthReadout setup.coordinateUnit
                  (setup.source label).wavelength) : ℝ) : Real.Angle)

/-!
The stated negligible-decrease approximation: propagation does not change
the displacement amplitude of any one source before it reaches `P`.
-/
structure SatisfiesNegligibleAttenuation
    (setup : FourSourceSoundSetup) : Prop where
  receivedAmplitude : ∀ (unit : LengthUnit) (label : SourceLabel),
    amplitudeReadout unit (setup.receivedAmplitudeAtP label) =
      amplitudeReadout unit (setup.source label).displacementAmplitude

/-!
General coherent superposition at `P`.  The net amplitude is the magnitude of
the sum of the four received phasors.  This law is uniform in the received
phases and amplitudes and contains neither the value `4 s_m` nor an answer
choice.
-/
structure SatisfiesCoherentPhasorSuperposition
    (setup : FourSourceSoundSetup) : Prop where
  netAmplitudeMagnitude : ∀ unit : LengthUnit,
    amplitudeReadout unit setup.netAmplitudeAtP =
      Real.sqrt
        ((∑ label : SourceLabel,
              amplitudeReadout unit (setup.receivedAmplitudeAtP label) *
                Real.Angle.cos (setup.receivedPhaseAtP label)) ^ 2 +
          (∑ label : SourceLabel,
              amplitudeReadout unit (setup.receivedAmplitudeAtP label) *
                Real.Angle.sin (setup.receivedPhaseAtP label)) ^ 2)

/-! ## Derived interference facts -/

/-!
The depicted equal spacing together with `d = λ` makes every source-to-`P`
path differ from the `S₄` path by an integral number of wavelengths.
-/
lemma rayPathDifferencesAreWholeWavelengths
    (setup : FourSourceSoundSetup)
    (_figure : MatchesFourSourceFigure setup)
    (_spacing : SpacingEqualsWavelength setup)
    (_geometry : SatisfiesCollinearRayGeometry setup) :
    ∀ (unit : LengthUnit) (label : SourceLabel),
      ∃ order : ℤ,
        lengthReadout unit (setup.rayPathLengthToP label) -
            lengthReadout unit (setup.rayPathLengthToP .S4) =
          (order : ℝ) *
            lengthReadout unit setup.commonWavelengthLambda := by
  intro unit label
  have hspacing :
      lengthReadout unit setup.adjacentSpacingD =
        lengthReadout unit setup.commonWavelengthLambda :=
    congrArg (lengthReadout unit) _spacing
  have h12 := _figure.spacing12 unit
  have h23 := _figure.spacing23 unit
  have h34 := _figure.spacing34 unit
  have hr1 := _geometry.rayLength unit .S1
  have hr2 := _geometry.rayLength unit .S2
  have hr3 := _geometry.rayLength unit .S3
  have hr4 := _geometry.rayLength unit .S4
  cases label with
  | S1 =>
      refine ⟨3, ?_⟩
      norm_num
      linarith
  | S2 =>
      refine ⟨2, ?_⟩
      norm_num
      linarith
  | S3 =>
      refine ⟨1, ?_⟩
      norm_num
      linarith
  | S4 =>
      refine ⟨0, ?_⟩
      norm_num

/-!
Equal source phases and integral-wavelength path differences imply that all
four received waves have the same phase at `P`.
-/
lemma allReceivedPhasesAgree
    (setup : FourSourceSoundSetup)
    (_figure : MatchesFourSourceFigure setup)
    (_sources : HasIdenticalCoherentPointSources setup)
    (_spacing : SpacingEqualsWavelength setup)
    (_physical : HasPhysicalParameters setup)
    (_geometry : SatisfiesCollinearRayGeometry setup)
    (_propagation : SatisfiesMonochromaticPropagation setup) :
    ∀ label : SourceLabel,
      setup.receivedPhaseAtP label = setup.receivedPhaseAtP .S4 := by
  intro label
  obtain ⟨order, hpath⟩ :=
    rayPathDifferencesAreWholeWavelengths setup _figure _spacing _geometry
      setup.coordinateUnit label
  have hw :
      0 < lengthReadout setup.coordinateUnit
        setup.commonWavelengthLambda :=
    _physical.wavelengthPositive
  rw [_propagation.phaseAtP label, _propagation.phaseAtP .S4,
    _sources.commonInitialPhase label, _sources.commonWavelength label,
    _sources.commonWavelength .S4]
  congr 1
  apply Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr
  refine ⟨order, ?_⟩
  calc
    (2 * Real.pi) *
          (lengthReadout setup.coordinateUnit
              (setup.rayPathLengthToP label) /
            lengthReadout setup.coordinateUnit
              setup.commonWavelengthLambda) -
        (2 * Real.pi) *
          (lengthReadout setup.coordinateUnit
              (setup.rayPathLengthToP .S4) /
            lengthReadout setup.coordinateUnit
              setup.commonWavelengthLambda) =
        (2 * Real.pi) *
          ((lengthReadout setup.coordinateUnit
                (setup.rayPathLengthToP label) -
              lengthReadout setup.coordinateUnit
                (setup.rayPathLengthToP .S4)) /
            lengthReadout setup.coordinateUnit
              setup.commonWavelengthLambda) := by ring
    _ = (2 * Real.pi) *
          (((order : ℝ) *
              lengthReadout setup.coordinateUnit
                setup.commonWavelengthLambda) /
            lengthReadout setup.coordinateUnit
              setup.commonWavelengthLambda) := by rw [hpath]
    _ = 2 * Real.pi * (order : ℝ) := by
      field_simp [ne_of_gt hw]

/-!
With negligible attenuation and equal arrival phases, the Cartesian phasor
components are four times the corresponding component of one source.
-/
lemma coherentPhasorComponents
    (setup : FourSourceSoundSetup)
    (_sources : HasIdenticalCoherentPointSources setup)
    (_attenuation : SatisfiesNegligibleAttenuation setup)
    (_phases : ∀ label : SourceLabel,
      setup.receivedPhaseAtP label = setup.receivedPhaseAtP .S4) :
    ∀ unit : LengthUnit,
      (∑ label : SourceLabel,
          amplitudeReadout unit (setup.receivedAmplitudeAtP label) *
            Real.Angle.cos (setup.receivedPhaseAtP label)) =
          4 * amplitudeReadout unit setup.commonSourceAmplitudeSm *
            Real.Angle.cos (setup.receivedPhaseAtP .S4) ∧
        (∑ label : SourceLabel,
          amplitudeReadout unit (setup.receivedAmplitudeAtP label) *
            Real.Angle.sin (setup.receivedPhaseAtP label)) =
          4 * amplitudeReadout unit setup.commonSourceAmplitudeSm *
            Real.Angle.sin (setup.receivedPhaseAtP .S4) := by
  intro unit
  have hcard : Fintype.card SourceLabel = 4 := by decide
  constructor
  · simp_rw [_attenuation.receivedAmplitude unit,
      _sources.commonAmplitude, _phases]
    simp [Finset.sum_const, hcard]
    ring
  · simp_rw [_attenuation.receivedAmplitude unit,
      _sources.commonAmplitude, _phases]
    simp [Finset.sum_const, hcard]
    ring

/-! ## Displayed choices and final target -/

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The multiple of `s_m` printed beside each answer label. -/
def AnswerChoice.amplitudeMultiplier : AnswerChoice → ℝ
  | .A => 1
  | .B => 2
  | .C => 3
  | .D => 4

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
A displayed choice matches when its multiplier gives the physical net
amplitude in every length unit.  This generic definition does not select D.
-/
def MatchesDisplayedAmplitudeChoice
    (setup : FourSourceSoundSetup) (choice : AnswerChoice) : Prop :=
  ∀ unit : LengthUnit,
    amplitudeReadout unit setup.netAmplitudeAtP =
      choice.amplitudeMultiplier *
        amplitudeReadout unit setup.commonSourceAmplitudeSm

/-- A displayed multiplier is the unique one matching the physical result. -/
def IsUniqueMatchingDisplayedChoice
    (setup : FourSourceSoundSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedAmplitudeChoice setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedAmplitudeChoice setup other → other = choice

/-!
When adjacent spacing equals the common wavelength, the additional path from
each successively more distant source is a whole wavelength.  Thus all four
equal, unattenuated contributions arrive in phase and their displacement
amplitudes add to `4 s_m`, uniquely selecting answer D.

This formalizes blueprint label `thm:physics:phyx_mini_0313:target`.
-/
theorem problem_phyx_mini_0313
    (setup : FourSourceSoundSetup)
    (_figure : MatchesFourSourceFigure setup)
    (_sources : HasIdenticalCoherentPointSources setup)
    (_spacing : SpacingEqualsWavelength setup)
    (_physical : HasPhysicalParameters setup)
    (_geometry : SatisfiesCollinearRayGeometry setup)
    (_propagation : SatisfiesMonochromaticPropagation setup)
    (_attenuation : SatisfiesNegligibleAttenuation setup)
    (_superposition : SatisfiesCoherentPhasorSuperposition setup) :
    (∀ unit : LengthUnit,
        amplitudeReadout unit setup.netAmplitudeAtP =
          4 * amplitudeReadout unit setup.commonSourceAmplitudeSm) ∧
      IsUniqueMatchingDisplayedChoice setup recordedAnswerChoice := by
  have hphases :
      ∀ label : SourceLabel,
        setup.receivedPhaseAtP label = setup.receivedPhaseAtP .S4 :=
    allReceivedPhasesAgree setup _figure _sources _spacing _physical
      _geometry _propagation
  have hcomponents :=
    coherentPhasorComponents setup _sources _attenuation hphases
  have hnet :
      ∀ unit : LengthUnit,
        amplitudeReadout unit setup.netAmplitudeAtP =
          4 * amplitudeReadout unit setup.commonSourceAmplitudeSm := by
    intro unit
    have hnonneg :
        0 ≤ amplitudeReadout unit setup.commonSourceAmplitudeSm := by
      unfold amplitudeReadout
      positivity
    have htrig :=
      Real.Angle.cos_sq_add_sin_sq (setup.receivedPhaseAtP .S4)
    have hmagnitude :
        (4 * amplitudeReadout unit setup.commonSourceAmplitudeSm *
              Real.Angle.cos (setup.receivedPhaseAtP .S4)) ^ 2 +
            (4 * amplitudeReadout unit setup.commonSourceAmplitudeSm *
              Real.Angle.sin (setup.receivedPhaseAtP .S4)) ^ 2 =
          (4 * amplitudeReadout unit setup.commonSourceAmplitudeSm) ^ 2 := by
      calc
        (4 * amplitudeReadout unit setup.commonSourceAmplitudeSm *
                Real.Angle.cos (setup.receivedPhaseAtP .S4)) ^ 2 +
              (4 * amplitudeReadout unit setup.commonSourceAmplitudeSm *
                Real.Angle.sin (setup.receivedPhaseAtP .S4)) ^ 2 =
            (4 * amplitudeReadout unit setup.commonSourceAmplitudeSm) ^ 2 *
              (Real.Angle.cos (setup.receivedPhaseAtP .S4) ^ 2 +
                Real.Angle.sin (setup.receivedPhaseAtP .S4) ^ 2) := by ring
        _ = (4 * amplitudeReadout unit
              setup.commonSourceAmplitudeSm) ^ 2 := by rw [htrig, mul_one]
    rw [_superposition.netAmplitudeMagnitude unit,
      (hcomponents unit).1, (hcomponents unit).2, hmagnitude,
      Real.sqrt_sq (by positivity)]
  refine ⟨hnet, ?_⟩
  change MatchesDisplayedAmplitudeChoice setup .D ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedAmplitudeChoice setup other → other = .D
  constructor
  · simpa [MatchesDisplayedAmplitudeChoice,
      AnswerChoice.amplitudeMultiplier] using hnet
  · intro other hother
    have ho := hother setup.coordinateUnit
    have hn := hnet setup.coordinateUnit
    have hpositive := _physical.sourceAmplitudePositive
    cases other <;>
      norm_num [AnswerChoice.amplitudeMultiplier] at ho ⊢ <;>
      nlinarith

end PhyXMiniProblems.ProblemPhyXMini0313
