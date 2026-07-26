import Mathlib.Data.NNReal.Defs
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0245

open Dimension

/-!
# Next-longer longitudinal mode of a helium--neon laser cavity

The laser has a full reflector on the left and a partial reflector on the
right.  A longitudinal standing light wave occupies the cavity, while the
output beam leaves through the partial reflector.  The reported operating
wavelength is `632.9924 nm`, and the displayed mirror spacing is
`310.372 mm`.

Lengths are unit-independent Physlib quantities.  Real numbers below are only
readouts in named units or displayed multiple-choice data.

If both printed decimals are interpreted as exact, the ratio
`2 L / lambda = 980650.0046...` is not an integer.  To avoid an inconsistent
physical model, this formalization respects the word "precisely" for the
operating wavelength and treats the mirror spacing as a measurement rounded
to the displayed `0.001 mm` resolution.  The requested answer is likewise a
wavelength rounded to the displayed `0.0001 nm` resolution.
-/

/-! ## Dimensionful length quantities and named-unit readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Read a physical length as a real number in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Nanometre readout, used for the laser wavelengths and answer choices. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Millimetre readout, used for the stated mirror separation. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- Metre readout, used to state positivity independently of printed scales. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-!
`RoundsToDisplayedValue actual displayed resolution` means that `actual` is
in the half-open rounding bin centered on `displayed`.  The half-open choice
fixes the usual tie convention without affecting this problem's values.
-/
def RoundsToDisplayedValue
    (actual displayed resolution : ℝ) : Prop :=
  displayed - resolution / 2 ≤ actual ∧
    actual < displayed + resolution / 2

/-! ## Physical roles and primary-figure information -/

/-- The gain medium named in the problem statement. -/
inductive LaserGainMedium where
  | heliumNeonGas
  deriving DecidableEq, Repr

/-- The visible color of the emitted laser light. -/
inductive LaserLightColor where
  | red
  deriving DecidableEq, Repr

/-- The two ends of the horizontal laser cavity in the primary figure. -/
inductive CavityEnd where
  | left
  | right
  deriving DecidableEq, Repr

/-- Optical behavior of a cavity reflector. -/
inductive ReflectorKind where
  | fullReflector
  | partialReflector
  deriving DecidableEq, Repr

/-- The five labeled physical elements visible in the primary figure. -/
inductive FigureElement where
  | laserCavity
  | fullReflector
  | partialReflector
  | standingLightWave
  | laserBeam
  deriving DecidableEq, Repr

/-- Qualitative horizontal placement of a labeled element in the figure. -/
inductive FigurePlacement where
  | cavityInterior
  | leftCavityBoundary
  | rightCavityBoundary
  | rightExterior
  deriving DecidableEq, Repr

/-!
Independent physical quantities and qualitative attributes of the laser.
`formsLongitudinalStandingWave` is an observational predicate; its governing
relation to mode number and mirror separation is stated separately below.
No next-longer wavelength or answer choice is stored in this setup.
-/
structure HeliumNeonLaserCavitySetup where
  gainMedium : LaserGainMedium
  emittedColor : LaserLightColor
  mirrorSeparation : LengthQuantity
  operatingWavelength : LengthQuantity
  reflectorAt : CavityEnd → ReflectorKind
  outputBeamExitEnd : CavityEnd
  figureElementVisible : FigureElement → Bool
  figurePlacement : FigureElement → FigurePlacement
  formsLongitudinalStandingWave : LengthQuantity → Prop

/-!
Information read from the primary image.  The purple standing wave is inside
the cavity, between a full left reflector and a partial right reflector; the
red output beam extends to the right of the partial reflector.
-/
structure MatchesPrimaryLaserFigure
    (setup : HeliumNeonLaserCavitySetup) : Prop where
  leftReflectorIsFull :
    setup.reflectorAt .left = .fullReflector
  rightReflectorIsPartial :
    setup.reflectorAt .right = .partialReflector
  beamExitsAtRight : setup.outputBeamExitEnd = .right
  allLabeledElementsVisible :
    ∀ element : FigureElement, setup.figureElementVisible element = true
  cavityPlacement :
    setup.figurePlacement .laserCavity = .cavityInterior
  fullReflectorPlacement :
    setup.figurePlacement .fullReflector = .leftCavityBoundary
  partialReflectorPlacement :
    setup.figurePlacement .partialReflector = .rightCavityBoundary
  standingWavePlacement :
    setup.figurePlacement .standingLightWave = .cavityInterior
  outputBeamPlacement :
    setup.figurePlacement .laserBeam = .rightExterior

/-!
Problem-statement data.  The wavelength marked "precisely" is an exact
nanometre readout.  The mirror spacing is placed in the rounding bin denoted by
the printed `310.372 mm`, so the data remain compatible with an integral
longitudinal mode.  Neither the next wavelength nor answer A occurs here.
-/
structure MatchesProblemReadouts
    (setup : HeliumNeonLaserCavitySetup) : Prop where
  gainMediumIsHeliumNeon : setup.gainMedium = .heliumNeonGas
  emittedLightIsRed : setup.emittedColor = .red
  operatingWavelengthNanometers :
    lengthInNanometers setup.operatingWavelength =
      (1582481 / 2500 : ℝ)
  mirrorSpacingMillimeters :
    RoundsToDisplayedValue
      (lengthInMillimeters setup.mirrorSeparation)
      (77593 / 250 : ℝ) (1 / 1000 : ℝ)
  operatingWavelengthIsStandingWave :
    setup.formsLongitudinalStandingWave setup.operatingWavelength

/-- Positivity conditions for the nondegenerate optical cavity and wave. -/
structure HasPhysicalLaserParameters
    (setup : HeliumNeonLaserCavitySetup) : Prop where
  mirrorSeparationPositive :
    0 < lengthInMeters setup.mirrorSeparation
  operatingWavelengthPositive :
    0 < lengthInMeters setup.operatingWavelength

/-!
The longitudinal cavity-resonance law.  A wavelength forms a standing wave
exactly when a positive integral number of half-wavelengths fits between the
reflectors: `2 L = n lambda`.  It is stated in every length unit and for every
candidate wavelength, so it is a general governing law rather than the
requested adjacent-mode formula.
-/
structure SatisfiesLongitudinalCavityResonanceLaw
    (setup : HeliumNeonLaserCavitySetup) : Prop where
  standingWave_iff_positiveIntegralHalfWaves :
    ∀ wavelength : LengthQuantity,
      setup.formsLongitudinalStandingWave wavelength ↔
        ∃ modeNumber : ℕ, 0 < modeNumber ∧
          ∀ unit : LengthUnit,
            2 * lengthReadout unit setup.mirrorSeparation =
              (modeNumber : ℝ) * lengthReadout unit wavelength

/-!
A candidate is the next longer standing wavelength when it is resonant,
strictly longer than the operating wavelength, and no other resonant
wavelength lies strictly between them.  This definition characterizes the
question being asked; it contains no numerical candidate or answer value.
-/
def IsNextLongerStandingWavelength
    (setup : HeliumNeonLaserCavitySetup)
    (candidate : LengthQuantity) : Prop :=
  setup.formsLongitudinalStandingWave candidate ∧
    lengthInNanometers setup.operatingWavelength <
      lengthInNanometers candidate ∧
    ∀ other : LengthQuantity,
      setup.formsLongitudinalStandingWave other →
        lengthInNanometers setup.operatingWavelength <
          lengthInNanometers other →
        lengthInNanometers candidate ≤ lengthInNanometers other

/-! ## Displayed answers -/

/-- Labels attached to the four wavelength choices in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Nanometre values printed beside the four answer labels. -/
def displayedAnswerWavelengthInNanometers : AnswerChoice → ℝ
  | .A => 632993 / 1000
  | .B => 622993 / 1000
  | .C => 6425693 / 10000
  | .D => 630913 / 1000

/-- Dataset answer metadata, recorded as data rather than used as a premise. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-- A physical wavelength rounds to the value printed for an answer choice. -/
def MatchesDisplayedAnswer
    (wavelength : LengthQuantity) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedValue
    (lengthInNanometers wavelength)
    (displayedAnswerWavelengthInNanometers choice)
    (1 / 10000 : ℝ)

/-!
The exact operating wavelength and rounded mirror spacing restrict the current
longitudinal mode to one of three adjacent large integers.  This intermediate
statement records the arithmetic route without assuming the next wavelength.
-/
lemma operatingModeNumber_is_near_980650
    (setup : HeliumNeonLaserCavitySetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hLaw : SatisfiesLongitudinalCavityResonanceLaw setup) :
    ∃ modeNumber : ℕ,
      (modeNumber = 980649 ∨
        modeNumber = 980650 ∨
        modeNumber = 980651) ∧
      ∀ unit : LengthUnit,
        2 * lengthReadout unit setup.mirrorSeparation =
          (modeNumber : ℝ) *
            lengthReadout unit setup.operatingWavelength := by
  have nanometers_eq_million_mul_millimeters (length : LengthQuantity) :
      lengthInNanometers length =
        1000000 * lengthInMillimeters length := by
    have hscale :
        ({UnitChoices.SI with length := LengthUnit.millimeters}).dimScale
          ({UnitChoices.SI with length := LengthUnit.nanometers}) L𝓭 =
            (1000000 : NNReal) := by
      apply NNReal.eq
      simp [UnitChoices.dimScale, LengthUnit.nanometers,
        LengthUnit.millimeters, LengthUnit.scale, LengthUnit.div_eq_val,
        LengthUnit.meters]
      change ((10 : ℝ) ^ 3)⁻¹ * 10 ^ 9 = 1000000
      norm_num
    unfold lengthInNanometers lengthInMillimeters lengthReadout
    have h := length.2
      ({UnitChoices.SI with length := LengthUnit.millimeters})
      ({UnitChoices.SI with length := LengthUnit.nanometers})
    simp only [WithDim.dim_apply] at h
    rw [h, hscale]
    simp only [WithDim.smul_val, smul_eq_mul, NNReal.coe_mul,
      NNReal.coe_ofNat]
  obtain ⟨modeNumber, hModePositive, hResonance⟩ :=
    (hLaw.standingWave_iff_positiveIntegralHalfWaves
      setup.operatingWavelength).mp
      hReadouts.operatingWavelengthIsStandingWave
  have hResonanceNanometers :=
    hResonance LengthUnit.nanometers
  have hSpacingBounds := hReadouts.mirrorSpacingMillimeters
  change
    2 * lengthInNanometers setup.mirrorSeparation =
      (modeNumber : ℝ) *
        lengthInNanometers setup.operatingWavelength
    at hResonanceNanometers
  rw [nanometers_eq_million_mul_millimeters setup.mirrorSeparation,
    hReadouts.operatingWavelengthNanometers] at hResonanceNanometers
  have hModeLowerReal : (980648 : ℝ) < modeNumber := by
    rcases hSpacingBounds with ⟨hSpacingLower, hSpacingUpper⟩
    norm_num [RoundsToDisplayedValue] at hSpacingLower hSpacingUpper
    norm_num at hResonanceNanometers
    linarith
  have hModeUpperReal : (modeNumber : ℝ) < 980652 := by
    rcases hSpacingBounds with ⟨hSpacingLower, hSpacingUpper⟩
    norm_num [RoundsToDisplayedValue] at hSpacingLower hSpacingUpper
    norm_num at hResonanceNanometers
    linarith
  have hModeLower : 980648 < modeNumber := by
    exact_mod_cast hModeLowerReal
  have hModeUpper : modeNumber < 980652 := by
    exact_mod_cast hModeUpperReal
  refine ⟨modeNumber, ?_, hResonance⟩
  omega

/-!
There exists a physically resonant wavelength immediately above the operating
wavelength, and at the four-decimal-nanometre precision of the choices it
rounds to `632.9930 nm`.  Moreover A is the unique printed choice in that
rounding bin.

This is the formal target corresponding to
`thm:physics:phyx_mini_0245:target`.
-/
theorem problem_phyx_mini_0245
    (setup : HeliumNeonLaserCavitySetup)
    (hFigure : MatchesPrimaryLaserFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalLaserParameters setup)
    (hLaw : SatisfiesLongitudinalCavityResonanceLaw setup) :
    ∃ nextWavelength : LengthQuantity,
      IsNextLongerStandingWavelength setup nextWavelength ∧
        RoundsToDisplayedValue
          (lengthInNanometers nextWavelength)
          (632993 / 1000 : ℝ) (1 / 10000 : ℝ) ∧
        MatchesDisplayedAnswer nextWavelength .A ∧
        ∀ choice : AnswerChoice,
          MatchesDisplayedAnswer nextWavelength choice → choice = .A := by
  obtain ⟨modeNumber, hModeCases, hOperatingResonance⟩ :=
    operatingModeNumber_is_near_980650 setup hReadouts hLaw
  let scaleFactor : NNReal :=
    (modeNumber : NNReal) / ((modeNumber : NNReal) - 1)
  let nextMode : ℕ := modeNumber - 1
  let nextWavelength : LengthQuantity :=
    scaleFactor • setup.operatingWavelength
  have hNextReadout (unit : LengthUnit) :
      lengthReadout unit nextWavelength =
        (scaleFactor : ℝ) *
          lengthReadout unit setup.operatingWavelength := by
    simp [nextWavelength, lengthReadout, Dimensionful.smul_apply,
      WithDim.smul_val, smul_eq_mul]
  rcases hModeCases with hMode | hMode | hMode <;>
    subst modeNumber
  all_goals
    have hNextModePositive : 0 < nextMode := by
      norm_num [nextMode]
    have hNextResonance :
        ∀ unit : LengthUnit,
          2 * lengthReadout unit setup.mirrorSeparation =
            (nextMode : ℝ) * lengthReadout unit nextWavelength := by
      intro unit
      rw [hNextReadout, hOperatingResonance unit]
      norm_num [nextMode, scaleFactor]
      ring
    have hNextStandingWave :
        setup.formsLongitudinalStandingWave nextWavelength :=
      (hLaw.standingWave_iff_positiveIntegralHalfWaves
        nextWavelength).mpr
        ⟨nextMode, hNextModePositive, hNextResonance⟩
    have hNextNanometers := hNextReadout LengthUnit.nanometers
    change
      lengthInNanometers nextWavelength =
        (scaleFactor : ℝ) *
          lengthInNanometers setup.operatingWavelength
      at hNextNanometers
    rw [hReadouts.operatingWavelengthNanometers] at hNextNanometers
    refine ⟨nextWavelength, ?_, ?_, ?_, ?_⟩
    · refine ⟨hNextStandingWave, ?_, ?_⟩
      · rw [hNextNanometers, hReadouts.operatingWavelengthNanometers]
        norm_num [scaleFactor]
      · intro other hOtherStandingWave hOtherLonger
        obtain ⟨otherMode, hOtherModePositive, hOtherResonance⟩ :=
          (hLaw.standingWave_iff_positiveIntegralHalfWaves other).mp
            hOtherStandingWave
        have hOperatingResonanceNanometers :=
          hOperatingResonance LengthUnit.nanometers
        have hOtherResonanceNanometers :=
          hOtherResonance LengthUnit.nanometers
        have hNextResonanceNanometers :=
          hNextResonance LengthUnit.nanometers
        change
          2 * lengthInNanometers setup.mirrorSeparation =
            ((nextMode + 1 : ℕ) : ℝ) *
              lengthInNanometers setup.operatingWavelength
          at hOperatingResonanceNanometers
        change
          2 * lengthInNanometers setup.mirrorSeparation =
            (otherMode : ℝ) * lengthInNanometers other
          at hOtherResonanceNanometers
        change
          2 * lengthInNanometers setup.mirrorSeparation =
            (nextMode : ℝ) * lengthInNanometers nextWavelength
          at hNextResonanceNanometers
        have hOperatingPositive :
            0 < lengthInNanometers setup.operatingWavelength := by
          rw [hReadouts.operatingWavelengthNanometers]
          norm_num
        have hOtherPositive :
            0 < lengthInNanometers other :=
          lt_trans hOperatingPositive hOtherLonger
        have hOtherModeLess : otherMode < nextMode + 1 := by
          by_contra hNotLess
          have hModeGe : nextMode + 1 ≤ otherMode :=
            Nat.le_of_not_gt hNotLess
          have hModeGeReal :
              (((nextMode + 1 : ℕ) : ℝ) : ℝ) ≤ (otherMode : ℝ) := by
            exact_mod_cast hModeGe
          have hProductStrict :
              ((nextMode + 1 : ℕ) : ℝ) *
                  lengthInNanometers setup.operatingWavelength <
                (otherMode : ℝ) * lengthInNanometers other := by
            calc
              ((nextMode + 1 : ℕ) : ℝ) *
                    lengthInNanometers setup.operatingWavelength <
                  ((nextMode + 1 : ℕ) : ℝ) *
                    lengthInNanometers other :=
                mul_lt_mul_of_pos_left hOtherLonger (by
                  norm_num [nextMode])
              _ ≤ (otherMode : ℝ) * lengthInNanometers other :=
                mul_le_mul_of_nonneg_right hModeGeReal
                  (le_of_lt hOtherPositive)
          linarith
        have hOtherModeLe : otherMode ≤ nextMode := by
          omega
        have hOtherModeLeReal :
            (otherMode : ℝ) ≤ (nextMode : ℝ) := by
          exact_mod_cast hOtherModeLe
        have hProductLe :
            (otherMode : ℝ) * lengthInNanometers other ≤
              (nextMode : ℝ) * lengthInNanometers other :=
          mul_le_mul_of_nonneg_right hOtherModeLeReal
            (le_of_lt hOtherPositive)
        have hNextModePositiveReal : (0 : ℝ) < nextMode := by
          exact_mod_cast hNextModePositive
        nlinarith
    · rw [hNextNanometers]
      norm_num [RoundsToDisplayedValue, scaleFactor]
    · unfold MatchesDisplayedAnswer
      rw [hNextNanometers]
      norm_num [displayedAnswerWavelengthInNanometers,
        RoundsToDisplayedValue, scaleFactor]
    · intro choice hChoice
      cases choice <;>
        norm_num [MatchesDisplayedAnswer,
          displayedAnswerWavelengthInNanometers, RoundsToDisplayedValue,
          hNextNanometers, scaleFactor] at hChoice
      rfl

end PhyXMiniProblems.ProblemPhyXMini0245
