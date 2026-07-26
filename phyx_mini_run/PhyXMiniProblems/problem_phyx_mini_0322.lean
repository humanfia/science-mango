import Mathlib
import Physlib.Units.WithDim.Basic

/-!
# Four-reflection path putting two sound waves out of phase

The primary figure shows initially in-phase sound waves `A` and `B` travelling
to the right with one common wavelength `lambda`.  Wave `A` is redirected by
four reflecting surfaces.  Its staircase path has two vertical legs, each
labelled `L`, before it again travels to the right; wave `B` follows the
straight horizontal reference path.

Wavelength, the variable leg length `L`, and propagation-path lengths are
unit-independent Physlib quantities.  Real numbers are used only for selected
length readouts and for dimensionless phase measured in wavelength cycles.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0322

open Dimension

/-! ## Dimensionful quantities and figure labels -/

/-- A signed physical length, independent of the unit used to read it. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical length as a real scalar in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : AcousticLength) : ℝ :=
  (length ({UnitChoices.SI with length := unit} : UnitChoices)).val

/-- Metre readout of a physical length. -/
def lengthInMeters (length : AcousticLength) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Construct a physical length from its metre readout. -/
def lengthOfMeters (value : ℝ) : AcousticLength :=
  CarriesDimension.toDimensionful UnitChoices.SI ⟨value⟩

/-- The two sound-wave rays labelled in the primary image. -/
inductive WaveLabel where
  | A
  | B
  deriving DecidableEq, Repr

/-- Horizontal propagation directions used by the problem statement. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-!
The four blue reflecting surfaces, named in the order in which wave `A`
encounters them while descending through the staircase.
-/
inductive ReflectionSurface where
  | firstUpper
  | firstLower
  | secondUpper
  | secondLower
  deriving DecidableEq, Repr

/-!
The physical quantities, ray data, and phase observables of the diagram.

`totalPathLengthAtLegLength wave candidateL` describes the member of the
depicted family obtained by assigning `candidateL` to both vertical legs.
Thus the observable `wavesExactlyOutOfPhaseAtLegLength` is independent data
constrained by the general acoustic phase laws below; it is not defined to
select the recorded answer.
-/
structure FourReflectionSoundSetup where
  /-- Common wavelength `lambda` of waves `A` and `B`. -/
  wavelengthLambda : AcousticLength
  /-- The variable physical distance printed as `L` beside both vertical legs. -/
  depictedLegLengthL : AcousticLength
  /-- Number of vertical path segments carrying the label `L`. -/
  verticalLegCount : ℕ
  initialDirection : WaveLabel → HorizontalDirection
  finalDirection : WaveLabel → HorizontalDirection
  /-- Initial phase, measured in wavelength cycles. -/
  initialPhaseCycles : WaveLabel → ℝ
  /-- Ordered sequence of reflecting surfaces encountered by each ray. -/
  reflectionSequence : WaveLabel → List ReflectionSurface
  /-- Phase shift of one surface reflection, measured in wavelength cycles. -/
  reflectionPhaseShiftCycles : ReflectionSurface → ℝ
  /-- Accumulated reflection phase of each ray, in wavelength cycles. -/
  totalReflectionPhaseCycles : WaveLabel → ℝ
  /-- Total propagation-path length for a proposed common vertical-leg length. -/
  totalPathLengthAtLegLength : WaveLabel → AcousticLength → AcousticLength
  /-- Arrival phase of `A` relative to `B`, in wavelength cycles. -/
  arrivalPhaseDifferenceCyclesAtLegLength : AcousticLength → ℝ
  /-- Whether the two arriving waves are exactly in opposition. -/
  wavesExactlyOutOfPhaseAtLegLength : AcousticLength → Prop

/-! ## Scenario and primary-figure readouts -/

/-!
Qualitative and integer data stated in the problem and read from the image.
The two waves begin in phase and rightward, wave `A` meets the four displayed
surfaces in order, wave `B` meets none, and both outgoing rays point right.
The raster shows exactly two vertical legs labelled `L`.  No wavelength
multiple or answer choice occurs in these data.
-/
structure MatchesProblemAndFigure
    (setup : FourReflectionSoundSetup) : Prop where
  wavesInitiallyInPhase :
    setup.initialPhaseCycles .A = setup.initialPhaseCycles .B
  waveAInitiallyRightward : setup.initialDirection .A = .rightward
  waveBInitiallyRightward : setup.initialDirection .B = .rightward
  waveAFinallyRightward : setup.finalDirection .A = .rightward
  waveBFinallyRightward : setup.finalDirection .B = .rightward
  waveAEndsInOriginalDirection :
    setup.finalDirection .A = setup.initialDirection .A
  waveAReflectionSequence :
    setup.reflectionSequence .A =
      [.firstUpper, .firstLower, .secondUpper, .secondLower]
  waveBReflectionSequence : setup.reflectionSequence .B = []
  twoVerticalLegsMarkedL : setup.verticalLegCount = 2

/-!
Positivity of the common wavelength and of the representative `L` drawn in
the setup.  Positivity for alternative candidate leg lengths is imposed in
the least-positive predicate below.
-/
structure HasPhysicalAcousticParameters
    (setup : FourReflectionSoundSetup) : Prop where
  wavelengthPositive : ∀ unit : LengthUnit,
    0 < lengthReadout unit setup.wavelengthLambda
  depictedLegLengthPositive : ∀ unit : LengthUnit,
    0 < lengthReadout unit setup.depictedLegLengthL

/-! ## Governing geometry and acoustic laws -/

/-!
The horizontal pieces of the two rays have the same total horizontal extent.
Consequently wave `A` exceeds the straight path of wave `B` precisely by its
two vertical legs.  The relation is stated for every proposed `L` and every
length unit, and does not single out a numerical multiple of `lambda`.
-/
structure SatisfiesDepictedPathGeometry
    (setup : FourReflectionSoundSetup) : Prop where
  pathExcessComesFromVerticalLegs :
    ∀ (candidateL : AcousticLength) (unit : LengthUnit),
      0 ≤ lengthReadout unit candidateL →
      lengthReadout unit
          (setup.totalPathLengthAtLegLength .A candidateL) -
          lengthReadout unit
            (setup.totalPathLengthAtLegLength .B candidateL) =
        (setup.verticalLegCount : ℝ) * lengthReadout unit candidateL

/-!
A reflection from any one of the four like surfaces has the same conventional
phase response.  Depending on whether acoustic pressure or displacement is
tracked, that common response is either zero or one half-cycle.  The total
reflection contribution is the sum along the ray's displayed reflection
sequence.  In either convention, four identical reflections contribute a
whole number of cycles; this law contains no condition on `L`.
-/
structure SatisfiesUniformReflectionPhaseLaw
    (setup : FourReflectionSoundSetup) : Prop where
  uniformSurfaceResponse :
    (∀ surface : ReflectionSurface,
      setup.reflectionPhaseShiftCycles surface = 0) ∨
    (∀ surface : ReflectionSurface,
      setup.reflectionPhaseShiftCycles surface = (1 : ℝ) / 2)
  totalReflectionPhaseIsSequenceSum : ∀ wave : WaveLabel,
    setup.totalReflectionPhaseCycles wave =
      ((setup.reflectionSequence wave).map
        setup.reflectionPhaseShiftCycles).sum

/-!
Propagation over one extra wavelength delays a wave by one phase cycle.
Therefore the arrival phase of `A` relative to `B` is its initial relative
phase, minus its excess path divided by `lambda`, plus the difference of the
two accumulated reflection phases.  Exact opposition means an odd half-cycle
modulo an integral number of cycles.

These are general phase laws quantified over arbitrary proposed leg lengths;
they do not assert which proposed length is the least solution.
-/
structure SatisfiesAcousticPhaseAccumulationLaw
    (setup : FourReflectionSoundSetup) : Prop where
  phaseFromPathAndReflections :
    ∀ (candidateL : AcousticLength) (unit : LengthUnit),
      0 < lengthReadout unit setup.wavelengthLambda →
      setup.arrivalPhaseDifferenceCyclesAtLegLength candidateL =
        setup.initialPhaseCycles .A - setup.initialPhaseCycles .B -
          (lengthReadout unit
                (setup.totalPathLengthAtLegLength .A candidateL) -
              lengthReadout unit
                (setup.totalPathLengthAtLegLength .B candidateL)) /
            lengthReadout unit setup.wavelengthLambda +
          (setup.totalReflectionPhaseCycles .A -
            setup.totalReflectionPhaseCycles .B)
  exactlyOutOfPhaseIffOddHalfCycle : ∀ candidateL : AcousticLength,
    setup.wavesExactlyOutOfPhaseAtLegLength candidateL ↔
      ∃ cycleOrder : ℤ,
        setup.arrivalPhaseDifferenceCyclesAtLegLength candidateL =
          (cycleOrder : ℝ) + (1 : ℝ) / 2

/-! ## Least positive distance and displayed answers -/

/-!
A physical leg length is the requested one when it is positive, puts the two
waves exactly out of phase, and has no larger metre readout than any other
positive leg length doing so.  Metre readout is used only to express the order
on physical lengths.
-/
def IsLeastPositiveOutOfPhaseLegLength
    (setup : FourReflectionSoundSetup) (candidateL : AcousticLength) : Prop :=
  0 < lengthInMeters candidateL ∧
    setup.wavesExactlyOutOfPhaseAtLegLength candidateL ∧
    ∀ otherL : AcousticLength,
      0 < lengthInMeters otherL →
      setup.wavesExactlyOutOfPhaseAtLegLength otherL →
      lengthInMeters candidateL ≤ lengthInMeters otherL

/-- Labels of the four printed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The multiple of the common wavelength printed beside each answer label. -/
def displayedWavelengthMultiple : AnswerChoice → ℝ
  | .A => 1
  | .B => 3 / 4
  | .C => 1 / 2
  | .D => 1 / 4

/-!
A displayed multiple matches the physical model when some least positive
out-of-phase leg length has that ratio to the wavelength in every unit.
-/
def MatchesDisplayedWavelengthMultiple
    (setup : FourReflectionSoundSetup) (choice : AnswerChoice) : Prop :=
  ∃ candidateL : AcousticLength,
    IsLeastPositiveOutOfPhaseLegLength setup candidateL ∧
      ∀ unit : LengthUnit,
        lengthReadout unit candidateL =
          displayedWavelengthMultiple choice *
            lengthReadout unit setup.wavelengthLambda

/-- Exactly one printed choice agrees with the least positive physical length. -/
def IsUniqueMatchingAnswer
    (setup : FourReflectionSoundSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedWavelengthMultiple setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedWavelengthMultiple setup other → other = choice

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
The least positive out-of-phase leg length is one quarter of the common
wavelength.  This relation is unit independent and identifies the displayed
answer D.  It is a derived conclusion, not a field of the setup or of any law.
-/
lemma leastPositiveOutOfPhaseLegLength_is_quarterWavelength
    (setup : FourReflectionSoundSetup)
    (hFigure : MatchesProblemAndFigure setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hGeometry : SatisfiesDepictedPathGeometry setup)
    (hReflection : SatisfiesUniformReflectionPhaseLaw setup)
    (hPhase : SatisfiesAcousticPhaseAccumulationLaw setup) :
    IsLeastPositiveOutOfPhaseLegLength setup setup.depictedLegLengthL ↔
      ∀ unit : LengthUnit,
        lengthReadout unit setup.depictedLegLengthL =
          (1 : ℝ) / 4 * lengthReadout unit setup.wavelengthLambda := by
  have hWavelengthMeters :
      0 < lengthInMeters setup.wavelengthLambda := by
    simpa [lengthInMeters] using
      hPhysical.wavelengthPositive LengthUnit.meters
  have hReflectionDifference :
      setup.totalReflectionPhaseCycles .A -
          setup.totalReflectionPhaseCycles .B = 0 ∨
        setup.totalReflectionPhaseCycles .A -
          setup.totalReflectionPhaseCycles .B = 2 := by
    rcases hReflection.uniformSurfaceResponse with hZero | hHalf
    · left
      simp [hReflection.totalReflectionPhaseIsSequenceSum,
        hFigure.waveAReflectionSequence, hFigure.waveBReflectionSequence,
        hZero]
    · right
      simp [hReflection.totalReflectionPhaseIsSequenceSum,
        hFigure.waveAReflectionSequence, hFigure.waveBReflectionSequence,
        hHalf]
      norm_num
  have hPhaseFormula (candidateL : AcousticLength)
      (hCandidateNonnegative : 0 ≤ lengthInMeters candidateL) :
      setup.arrivalPhaseDifferenceCyclesAtLegLength candidateL =
        -2 * (lengthInMeters candidateL /
          lengthInMeters setup.wavelengthLambda) +
        (setup.totalReflectionPhaseCycles .A -
          setup.totalReflectionPhaseCycles .B) := by
    have hPathExcess :=
      hGeometry.pathExcessComesFromVerticalLegs candidateL
        LengthUnit.meters (by
          simpa [lengthInMeters] using hCandidateNonnegative)
    have hPhaseAtMeters :=
      hPhase.phaseFromPathAndReflections candidateL LengthUnit.meters
        (by simpa [lengthInMeters] using hWavelengthMeters)
    rw [hPathExcess] at hPhaseAtMeters
    rw [hFigure.wavesInitiallyInPhase] at hPhaseAtMeters
    norm_num [hFigure.twoVerticalLegsMarkedL, lengthInMeters] at hPhaseAtMeters ⊢
    rw [hPhaseAtMeters]
    ring
  have hQuarterLowerBound (candidateL : AcousticLength)
      (hCandidatePositive : 0 < lengthInMeters candidateL)
      (hCandidateOutOfPhase :
        setup.wavesExactlyOutOfPhaseAtLegLength candidateL) :
      (1 : ℝ) / 4 * lengthInMeters setup.wavelengthLambda ≤
        lengthInMeters candidateL := by
    obtain ⟨cycleOrder, hOddHalfCycle⟩ :=
      (hPhase.exactlyOutOfPhaseIffOddHalfCycle candidateL).mp
        hCandidateOutOfPhase
    have hFormula :=
      hPhaseFormula candidateL (le_of_lt hCandidatePositive)
    have hRatioPositive :
        0 < lengthInMeters candidateL /
          lengthInMeters setup.wavelengthLambda :=
      div_pos hCandidatePositive hWavelengthMeters
    have hRatioLower :
        (1 : ℝ) / 4 ≤
          lengthInMeters candidateL /
            lengthInMeters setup.wavelengthLambda := by
      by_contra hNotLower
      have hRatioUpper :
          lengthInMeters candidateL /
              lengthInMeters setup.wavelengthLambda <
            (1 : ℝ) / 4 :=
        lt_of_not_ge hNotLower
      rcases hReflectionDifference with hReflectionZero | hReflectionTwo
      · have hCycleEquation :
            -2 * (lengthInMeters candidateL /
                lengthInMeters setup.wavelengthLambda) =
              (cycleOrder : ℝ) + (1 : ℝ) / 2 := by
          calc
            -2 * (lengthInMeters candidateL /
                lengthInMeters setup.wavelengthLambda) =
                setup.arrivalPhaseDifferenceCyclesAtLegLength candidateL := by
                  rw [hFormula, hReflectionZero]
                  ring
            _ = (cycleOrder : ℝ) + (1 : ℝ) / 2 := hOddHalfCycle
        have hCycleLowerReal : (-1 : ℝ) < (cycleOrder : ℝ) := by
          nlinarith
        have hCycleUpperReal : (cycleOrder : ℝ) < 0 := by
          nlinarith
        have hCycleLower : (-1 : ℤ) < cycleOrder := by
          exact_mod_cast hCycleLowerReal
        have hCycleUpper : cycleOrder < (0 : ℤ) := by
          exact_mod_cast hCycleUpperReal
        omega
      · have hCycleEquation :
            -2 * (lengthInMeters candidateL /
                lengthInMeters setup.wavelengthLambda) + 2 =
              (cycleOrder : ℝ) + (1 : ℝ) / 2 := by
          calc
            -2 * (lengthInMeters candidateL /
                lengthInMeters setup.wavelengthLambda) + 2 =
                setup.arrivalPhaseDifferenceCyclesAtLegLength candidateL := by
                  rw [hFormula, hReflectionTwo]
            _ = (cycleOrder : ℝ) + (1 : ℝ) / 2 := hOddHalfCycle
        have hCycleLowerReal : (1 : ℝ) < (cycleOrder : ℝ) := by
          nlinarith
        have hCycleUpperReal : (cycleOrder : ℝ) < 2 := by
          nlinarith
        have hCycleLower : (1 : ℤ) < cycleOrder := by
          exact_mod_cast hCycleLowerReal
        have hCycleUpper : cycleOrder < (2 : ℤ) := by
          exact_mod_cast hCycleUpperReal
        omega
    have hScaledLower :=
      (le_div_iff₀ hWavelengthMeters).mp hRatioLower
    nlinarith
  let quarterWavelength : AcousticLength :=
    (4⁻¹ : NNReal) • setup.wavelengthLambda
  have hQuarterReadout (unit : LengthUnit) :
      lengthReadout unit quarterWavelength =
        (1 : ℝ) / 4 * lengthReadout unit setup.wavelengthLambda := by
    norm_num [quarterWavelength, lengthReadout, NNReal.smul_def]
  have hQuarterMeters :
      lengthInMeters quarterWavelength =
        (1 : ℝ) / 4 * lengthInMeters setup.wavelengthLambda := by
    simpa [lengthInMeters] using hQuarterReadout LengthUnit.meters
  have hQuarterPositive :
      0 < lengthInMeters quarterWavelength := by
    rw [hQuarterMeters]
    nlinarith
  have hQuarterOutOfPhase :
      setup.wavesExactlyOutOfPhaseAtLegLength quarterWavelength := by
    apply
      (hPhase.exactlyOutOfPhaseIffOddHalfCycle quarterWavelength).mpr
    have hFormula :=
      hPhaseFormula quarterWavelength
        (le_of_lt hQuarterPositive)
    rcases hReflectionDifference with hReflectionZero | hReflectionTwo
    · refine ⟨-1, ?_⟩
      rw [hFormula, hReflectionZero, hQuarterMeters]
      field_simp [ne_of_gt hWavelengthMeters]
      norm_num
    · refine ⟨1, ?_⟩
      rw [hFormula, hReflectionTwo, hQuarterMeters]
      field_simp [ne_of_gt hWavelengthMeters]
      norm_num
  have hAcousticLengthExt (x y : AcousticLength)
      (hMeters : lengthInMeters x = lengthInMeters y) :
      x = y := by
    apply Dimensionful.ext
    funext unitChoices
    rw [x.2 UnitChoices.SI unitChoices,
      y.2 UnitChoices.SI unitChoices]
    congr 1
    apply WithDim.ext
    simpa [lengthInMeters, lengthReadout, UnitChoices.SI] using hMeters
  constructor
  · intro hLeast
    have hDepictedLeQuarter :
        lengthInMeters setup.depictedLegLengthL ≤
          lengthInMeters quarterWavelength :=
      hLeast.2.2 quarterWavelength hQuarterPositive hQuarterOutOfPhase
    have hQuarterLeDepicted :=
      hQuarterLowerBound setup.depictedLegLengthL hLeast.1 hLeast.2.1
    have hMeters :
        lengthInMeters setup.depictedLegLengthL =
          lengthInMeters quarterWavelength := by
      rw [hQuarterMeters] at hDepictedLeQuarter
      rw [hQuarterMeters]
      exact le_antisymm hDepictedLeQuarter hQuarterLeDepicted
    have hPhysicalLength :
        setup.depictedLegLengthL = quarterWavelength := by
      exact hAcousticLengthExt _ _ hMeters
    intro unit
    rw [hPhysicalLength, hQuarterReadout]
  · intro hQuarterRelation
    have hDepictedMeters :
        lengthInMeters setup.depictedLegLengthL =
          lengthInMeters quarterWavelength := by
      simpa [lengthInMeters] using
        (hQuarterRelation LengthUnit.meters).trans
          (hQuarterReadout LengthUnit.meters).symm
    have hDepictedPhysical :
        setup.depictedLegLengthL = quarterWavelength :=
      hAcousticLengthExt _ _ hDepictedMeters
    rw [hDepictedPhysical]
    refine ⟨hQuarterPositive, hQuarterOutOfPhase, ?_⟩
    intro otherL hOtherPositive hOtherOutOfPhase
    rw [hQuarterMeters]
    exact hQuarterLowerBound otherL hOtherPositive hOtherOutOfPhase

/-!
For the two initially in-phase rightward sound waves, the two extra legs give
path excess `2 L`, while the four like reflections contribute an integral
number of phase cycles.  The smallest positive odd-half-cycle path delay is
therefore obtained at `L = lambda / 4`, uniquely selecting answer D.

This formalizes blueprint label `thm:physics:phyx_mini_0322:target`.
-/
theorem problem_phyx_mini_0322
    (setup : FourReflectionSoundSetup)
    (hFigure : MatchesProblemAndFigure setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hGeometry : SatisfiesDepictedPathGeometry setup)
    (hReflection : SatisfiesUniformReflectionPhaseLaw setup)
    (hPhase : SatisfiesAcousticPhaseAccumulationLaw setup) :
    IsLeastPositiveOutOfPhaseLegLength setup setup.depictedLegLengthL ↔
      (∀ unit : LengthUnit,
        lengthReadout unit setup.depictedLegLengthL =
          displayedWavelengthMultiple recordedDatasetAnswer *
            lengthReadout unit setup.wavelengthLambda) ∧
        IsUniqueMatchingAnswer setup recordedDatasetAnswer := by
  have hQuarterCharacterization :=
    leastPositiveOutOfPhaseLegLength_is_quarterWavelength setup hFigure
      hPhysical hGeometry hReflection hPhase
  constructor
  · intro hLeast
    have hQuarter := hQuarterCharacterization.mp hLeast
    constructor
    · simpa [recordedDatasetAnswer, displayedWavelengthMultiple] using hQuarter
    · constructor
      · refine ⟨setup.depictedLegLengthL, hLeast, ?_⟩
        simpa [recordedDatasetAnswer, displayedWavelengthMultiple] using hQuarter
      · intro other hOtherMatches
        obtain ⟨otherL, hOtherLeast, hOtherReadout⟩ := hOtherMatches
        have hDepictedLeOther :
            lengthInMeters setup.depictedLegLengthL ≤
              lengthInMeters otherL :=
          hLeast.2.2 otherL hOtherLeast.1 hOtherLeast.2.1
        have hOtherLeDepicted :
            lengthInMeters otherL ≤
              lengthInMeters setup.depictedLegLengthL :=
          hOtherLeast.2.2 setup.depictedLegLengthL hLeast.1 hLeast.2.1
        have hMeters :
            lengthInMeters otherL =
              lengthInMeters setup.depictedLegLengthL :=
          le_antisymm hOtherLeDepicted hDepictedLeOther
        have hOtherMultiple := hOtherReadout LengthUnit.meters
        have hQuarterMeters := hQuarter LengthUnit.meters
        have hWavelengthPositive :=
          hPhysical.wavelengthPositive LengthUnit.meters
        cases other
        · simp [displayedWavelengthMultiple, lengthInMeters] at hOtherMultiple hMeters
          simp [recordedDatasetAnswer]
          nlinarith
        · simp [displayedWavelengthMultiple, lengthInMeters] at hOtherMultiple hMeters
          simp [recordedDatasetAnswer]
          nlinarith
        · simp [displayedWavelengthMultiple, lengthInMeters] at hOtherMultiple hMeters
          simp [recordedDatasetAnswer]
          nlinarith
        · rfl
  · rintro ⟨hDisplayed, _hUnique⟩
    apply hQuarterCharacterization.mpr
    simpa [recordedDatasetAnswer, displayedWavelengthMultiple] using hDisplayed

end PhyXMiniProblems.ProblemPhyXMini0322
