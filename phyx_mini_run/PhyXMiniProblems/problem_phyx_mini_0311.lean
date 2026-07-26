import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0311

open Dimension

/-!
# Second out-of-phase separation in a reflected sound-wave apparatus

The primary figure shows initially in-phase sound waves `A` and `B` traveling
rightward.  Wave `A` follows a four-reflection rectangular detour and wave `B`
follows a two-reflection detour; both emerge rightward.  Three dimension arrows
are labeled `L`: the upper horizontal mirror separation, the upper-to-middle
vertical separation, and the middle-to-lower vertical separation.

The apparatus is considered while `L` varies through `L = q * lambda`.  The
figure geometry makes the propagation distance of `A` exceed that of `B` by
one `L`.  Consequently the relative propagation phase is `2 * pi * q`.
The two extra reflections of `A` make no relative phase change modulo a full
turn.  The positive out-of-phase ratios are therefore the positive odd
half-integers, whose second member is `3/2`.

Lengths below are genuine unit-independent Physlib quantities.  Real numbers
are used only for coherent metre readouts and the dimensionless ratio `q`;
phases are represented by Mathlib's `Real.Angle`, hence modulo `2 * pi`.
-/

/-! ## Dimensionful acoustic quantities -/

/-- A nonnegative physical length carrying Physlib's length dimension. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Read a physical length in the SI length unit (metres). -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-! ## Wave, mirror, and figure labels -/

/-- The two sound-wave rays labeled in the problem. -/
inductive WaveLabel where
  | A
  | B
  deriving DecidableEq, Repr

/-- The propagation directions used by the red ray segments in the figure. -/
inductive PropagationDirection where
  | rightward
  | upward
  | downward
  deriving DecidableEq, Repr

/-- The physical type of both waves in the problem. -/
inductive AcousticWaveKind where
  | longitudinalSoundWave
  deriving DecidableEq, Repr

/-!
The five reflecting surfaces visible in the primary image.  The central-left
surface is encountered by both rays, from different incident directions.
-/
inductive MirrorLabel where
  | upperLeft
  | upperRight
  | centralLeft
  | centralRight
  | lowerLeft
  deriving DecidableEq, Repr

/-- The three arrows in the primary image that each carry the label `L`. -/
inductive FigureLengthLabel where
  | upperHorizontal
  | upperToMiddleVertical
  | middleToLowerVertical
  deriving DecidableEq, Repr

/-- A sound wave before it enters the reflected-ray apparatus. -/
structure SoundWave where
  kind : AcousticWaveKind
  wavelength : LengthQuantity
  initialPhase : Real.Angle
  initialDirection : PropagationDirection

/-!
Discrete routes, output directions, and scalable metric data supplied by the
figure.  The real argument to the length fields is a proposed ratio `q`; only
nonnegative ratios are assigned physical meaning by the premises below.
-/
structure ReflectionFigure where
  mirrorShown : MirrorLabel → Bool
  route : WaveLabel → List MirrorLabel
  emergentDirection : WaveLabel → PropagationDirection
  labeledLengthAtRatio : FigureLengthLabel → ℝ → LengthQuantity
  travelLengthAtRatio : WaveLabel → ℝ → LengthQuantity

/-!
The physical experiment, including the unknown output phases.  The output
phase field is constrained by the propagation law below and is not defined to
make an answer choice true.
-/
structure SoundReflectionSetup where
  wave : WaveLabel → SoundWave
  commonWavelength : LengthQuantity
  figure : ReflectionFigure
  phaseShiftPerReflection : Real.Angle
  outputPhaseAtRatio : WaveLabel → ℝ → Real.Angle

/-- Use the upper horizontal `L` arrow as the canonical separation length. -/
def separationAtRatio
    (setup : SoundReflectionSetup) (q : ℝ) : LengthQuantity :=
  setup.figure.labeledLengthAtRatio .upperHorizontal q

/-! ## Figure readouts and governing physics -/

/-!
The prose data and quantitative relations read from the primary figure.

The last two fields express, for every nonnegative proposed ratio, the stated
relation `L = q * lambda` and the geometric path excess `d_A = d_B + L`.
They do not assert that any particular ratio produces opposite phase.
-/
structure MatchesProblemAndFigure (setup : SoundReflectionSetup) : Prop where
  waveAIsSound : (setup.wave .A).kind = .longitudinalSoundWave
  waveBIsSound : (setup.wave .B).kind = .longitudinalSoundWave
  waveAWavelength : (setup.wave .A).wavelength = setup.commonWavelength
  waveBWavelength : (setup.wave .B).wavelength = setup.commonWavelength
  initiallyInPhase : (setup.wave .A).initialPhase = (setup.wave .B).initialPhase
  waveAInitiallyRightward :
    (setup.wave .A).initialDirection = .rightward
  waveBInitiallyRightward :
    (setup.wave .B).initialDirection = .rightward
  everyMirrorShown : ∀ mirror, setup.figure.mirrorShown mirror = true
  waveARoute :
    setup.figure.route .A =
      [.upperLeft, .centralLeft, .centralRight, .upperRight]
  waveBRoute : setup.figure.route .B = [.centralLeft, .lowerLeft]
  waveAHasFourReflections : (setup.figure.route .A).length = 4
  waveBHasTwoReflections : (setup.figure.route .B).length = 2
  waveAEmergesRightward : setup.figure.emergentDirection .A = .rightward
  waveBEmergesRightward : setup.figure.emergentDirection .B = .rightward
  allThreeLabelsAreTheSameL :
    ∀ q : ℝ,
      0 ≤ q →
        setup.figure.labeledLengthAtRatio .upperToMiddleVertical q =
            separationAtRatio setup q ∧
          setup.figure.labeledLengthAtRatio .middleToLowerVertical q =
            separationAtRatio setup q
  separationIsQWavelengths :
    ∀ q : ℝ,
      0 ≤ q →
        lengthInMeters (separationAtRatio setup q) =
          q * lengthInMeters setup.commonWavelength
  waveAPathExceedsWaveBByL :
    ∀ q : ℝ,
      0 ≤ q →
        lengthInMeters (setup.figure.travelLengthAtRatio .A q) =
          lengthInMeters (setup.figure.travelLengthAtRatio .B q) +
            lengthInMeters (separationAtRatio setup q)

/-- Positivity of the common wavelength, excluding a degenerate wave. -/
structure HasPhysicalAcousticParameters
    (setup : SoundReflectionSetup) : Prop where
  wavelengthPositive : 0 < lengthInMeters setup.commonWavelength

/-!
The standard path-accumulation law for phase.  Traveling distance `d` at
wavelength `lambda` contributes `2*pi*d/lambda`; every encounter with one of
the identical reflecting surfaces contributes the same angle.

The final field says that the two additional reflections on route `A` have a
net phase equivalent to a full turn (or no turn).  It is a boundary/reflection
law, not a statement about the requested separation ratio.
-/
structure SatisfiesReflectedSoundPhaseLaw
    (setup : SoundReflectionSetup) : Prop where
  accumulatedOutputPhase :
    ∀ (wave : WaveLabel) (q : ℝ),
      0 ≤ q →
        setup.outputPhaseAtRatio wave q =
          (setup.wave wave).initialPhase +
            ((2 * Real.pi *
                lengthInMeters (setup.figure.travelLengthAtRatio wave q) /
                lengthInMeters setup.commonWavelength : ℝ) : Real.Angle) +
            (setup.figure.route wave).length •
              setup.phaseShiftPerReflection
  twoExtraReflectionsArePhaseNeutral :
    2 • setup.phaseShiftPerReflection = 0

/-! ## Out-of-phase ratios and order statistic -/

/-- Two phases differ by exactly half a turn. -/
def ExactlyOutOfPhase (phaseA phaseB : Real.Angle) : Prop :=
  phaseA = phaseB + (Real.pi : Real.Angle)

/-- A positive ratio `q` makes the two emerging waves exactly out of phase. -/
def OutOfPhaseAtRatio (setup : SoundReflectionSetup) (q : ℝ) : Prop :=
  0 < q ∧
    ExactlyOutOfPhase
      (setup.outputPhaseAtRatio .A q)
      (setup.outputPhaseAtRatio .B q)

/-!
`candidate` is the second-smallest number satisfying `property`: there is a
least satisfying number strictly below it, and every satisfying number below
`candidate` is that least number.
-/
def IsSecondSmallest (property : ℝ → Prop) (candidate : ℝ) : Prop :=
  property candidate ∧
    ∃ first : ℝ,
      property first ∧
        first < candidate ∧
        (∀ q : ℝ, property q → first ≤ q) ∧
        (∀ q : ℝ, property q → q < candidate → q = first)

/-! ## Displayed choices and formalization target -/

/-- Labels of the four dimensionless ratios displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The value of `q` printed beside each answer label. -/
def displayedRatio : AnswerChoice → ℝ
  | .A => 3 / 4
  | .B => 1
  | .C => 5 / 4
  | .D => 3 / 2

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
The general propagation and reflection laws reduce exact opposition to a
positive odd half-integer wavelength ratio.  This is a derived intermediate
result, not a premise of the main theorem.
-/
lemma outOfPhase_iff_positive_odd_half_integer
    (setup : SoundReflectionSetup)
    (hFigure : MatchesProblemAndFigure setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hPhaseLaw : SatisfiesReflectedSoundPhaseLaw setup)
    (q : ℝ) :
    OutOfPhaseAtRatio setup q ↔
      ∃ n : ℕ, q = ((2 * n + 1 : ℕ) : ℝ) / 2 := by
  constructor
  · rintro ⟨hq, hOutOfPhase⟩
    have hqNonnegative : 0 ≤ q := le_of_lt hq
    have hWavelengthNe :
        lengthInMeters setup.commonWavelength ≠ 0 :=
      ne_of_gt hPhysical.wavelengthPositive
    have hPropagation :
        2 * Real.pi *
              lengthInMeters
                (setup.figure.travelLengthAtRatio .A q) /
            lengthInMeters setup.commonWavelength =
          2 * Real.pi *
                lengthInMeters
                  (setup.figure.travelLengthAtRatio .B q) /
              lengthInMeters setup.commonWavelength +
            2 * Real.pi * q := by
      rw [hFigure.waveAPathExceedsWaveBByL q hqNonnegative,
        hFigure.separationIsQWavelengths q hqNonnegative]
      field_simp [hWavelengthNe]
    have hReflections :
        (setup.figure.route .A).length •
              setup.phaseShiftPerReflection =
            (setup.figure.route .B).length •
              setup.phaseShiftPerReflection := by
      rw [hFigure.waveAHasFourReflections,
        hFigure.waveBHasTwoReflections,
        show (4 : ℕ) = 2 + 2 by norm_num,
        add_nsmul,
        hPhaseLaw.twoExtraReflectionsArePhaseNeutral]
      simp
    have hOutput :
        setup.outputPhaseAtRatio .A q =
          setup.outputPhaseAtRatio .B q +
            ((2 * Real.pi * q : ℝ) : Real.Angle) := by
      rw [hPhaseLaw.accumulatedOutputPhase .A q hqNonnegative,
        hPhaseLaw.accumulatedOutputPhase .B q hqNonnegative,
        hFigure.initiallyInPhase, hPropagation, hReflections]
      simp only [Real.Angle.coe_add]
      abel
    unfold ExactlyOutOfPhase at hOutOfPhase
    rw [hOutput] at hOutOfPhase
    have hAngle :
        ((2 * Real.pi * q : ℝ) : Real.Angle) =
          (Real.pi : Real.Angle) :=
      add_left_cancel hOutOfPhase
    obtain ⟨k, hk⟩ :=
      Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hAngle
    have hTwoPiNe : (2 * Real.pi : ℝ) ≠ 0 :=
      mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)
    have hFactor :
        (2 * Real.pi) * (q - (k : ℝ) - 1 / 2) = 0 := by
      calc
        (2 * Real.pi) * (q - (k : ℝ) - 1 / 2) =
            (2 * Real.pi * q - Real.pi) -
              2 * Real.pi * (k : ℝ) := by ring
        _ = 0 := by rw [hk]; ring
    have hkFormula : q = (k : ℝ) + 1 / 2 := by
      have : q - (k : ℝ) - 1 / 2 = 0 :=
        (mul_eq_zero.mp hFactor).resolve_left hTwoPiNe
      linarith
    have hkLowerReal : (-1 : ℝ) < (k : ℝ) := by
      linarith
    have hkLower : (-1 : ℤ) < k := by
      exact_mod_cast hkLowerReal
    have hkNonnegative : 0 ≤ k := by omega
    refine ⟨k.toNat, ?_⟩
    have hkToNat : ((k.toNat : ℕ) : ℤ) = k :=
      Int.toNat_of_nonneg hkNonnegative
    have hkCast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
      exact_mod_cast hkToNat
    push_cast
    rw [hkCast, hkFormula]
    ring
  · rintro ⟨n, rfl⟩
    have hq :
        0 < (((2 * n + 1 : ℕ) : ℝ) / 2) := by positivity
    have hqNonnegative :
        0 ≤ (((2 * n + 1 : ℕ) : ℝ) / 2) :=
      le_of_lt hq
    have hWavelengthNe :
        lengthInMeters setup.commonWavelength ≠ 0 :=
      ne_of_gt hPhysical.wavelengthPositive
    have hPropagation :
        2 * Real.pi *
              lengthInMeters
                (setup.figure.travelLengthAtRatio .A
                  (((2 * n + 1 : ℕ) : ℝ) / 2)) /
            lengthInMeters setup.commonWavelength =
          2 * Real.pi *
                lengthInMeters
                  (setup.figure.travelLengthAtRatio .B
                    (((2 * n + 1 : ℕ) : ℝ) / 2)) /
              lengthInMeters setup.commonWavelength +
            2 * Real.pi * (((2 * n + 1 : ℕ) : ℝ) / 2) := by
      rw [hFigure.waveAPathExceedsWaveBByL _ hqNonnegative,
        hFigure.separationIsQWavelengths _ hqNonnegative]
      field_simp [hWavelengthNe]
    have hReflections :
        (setup.figure.route .A).length •
              setup.phaseShiftPerReflection =
            (setup.figure.route .B).length •
              setup.phaseShiftPerReflection := by
      rw [hFigure.waveAHasFourReflections,
        hFigure.waveBHasTwoReflections,
        show (4 : ℕ) = 2 + 2 by norm_num,
        add_nsmul,
        hPhaseLaw.twoExtraReflectionsArePhaseNeutral]
      simp
    have hOutput :
        setup.outputPhaseAtRatio .A
              (((2 * n + 1 : ℕ) : ℝ) / 2) =
            setup.outputPhaseAtRatio .B
                (((2 * n + 1 : ℕ) : ℝ) / 2) +
              ((2 * Real.pi *
                  (((2 * n + 1 : ℕ) : ℝ) / 2) : ℝ) :
                Real.Angle) := by
      rw [hPhaseLaw.accumulatedOutputPhase .A _ hqNonnegative,
        hPhaseLaw.accumulatedOutputPhase .B _ hqNonnegative,
        hFigure.initiallyInPhase, hPropagation, hReflections]
      simp only [Real.Angle.coe_add]
      abel
    have hAngle :
        ((2 * Real.pi * (((2 * n + 1 : ℕ) : ℝ) / 2) : ℝ) :
            Real.Angle) =
          (Real.pi : Real.Angle) := by
      apply Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr
      refine ⟨(n : ℤ), ?_⟩
      push_cast
      ring
    refine ⟨hq, ?_⟩
    unfold ExactlyOutOfPhase
    rw [hOutput]
    exact congrArg
      (fun angle =>
        setup.outputPhaseAtRatio .B
            (((2 * n + 1 : ℕ) : ℝ) / 2) + angle)
      hAngle

/-!
The second positive odd half-integer is `3/2`, so choice `D` is the recorded
answer.  This formalizes `thm:physics:phyx_mini_0311:target`.
-/
theorem secondSmallestOutOfPhaseSeparationRatio
    (setup : SoundReflectionSetup)
    (hFigure : MatchesProblemAndFigure setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hPhaseLaw : SatisfiesReflectedSoundPhaseLaw setup) :
    IsSecondSmallest (OutOfPhaseAtRatio setup) (3 / 2) ∧
      displayedRatio recordedAnswerChoice = 3 / 2 := by
  constructor
  · unfold IsSecondSmallest
    refine ⟨
      (outOfPhase_iff_positive_odd_half_integer
          setup hFigure hPhysical hPhaseLaw _).2
        ⟨1, by norm_num⟩,
      1 / 2,
      (outOfPhase_iff_positive_odd_half_integer
          setup hFigure hPhysical hPhaseLaw _).2
        ⟨0, by norm_num⟩,
      by norm_num,
      ?_,
      ?_⟩
    · intro q hq
      obtain ⟨n, rfl⟩ :=
        (outOfPhase_iff_positive_odd_half_integer
          setup hFigure hPhysical hPhaseLaw q).1 hq
      push_cast
      have hnNonnegative : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith
    · intro q hq hlt
      obtain ⟨n, rfl⟩ :=
        (outOfPhase_iff_positive_odd_half_integer
          setup hFigure hPhysical hPhaseLaw q).1 hq
      have hnReal : (n : ℝ) < 1 := by
        push_cast at hlt
        linarith
      have hn : n < 1 := by
        exact_mod_cast hnReal
      have : n = 0 := by omega
      subst n
      norm_num
  · rfl

end PhyXMiniProblems.ProblemPhyXMini0311
