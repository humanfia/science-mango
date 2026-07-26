import Mathlib
import Physlib.SpaceAndTime.Space.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0312

open Dimension

/-!
# Out-of-phase points around two coherent sound sources

The figure places the two sound sources `S₁` and `S₂` on one horizontal line
and labels their separation by `D`.  The prose specifies isotropic point
sources which emit in phase, wavelength `0.50 m`, and separation `1.75 m`.
A detector travels along a large circle centered at the sources' midpoint.

Physical lengths use Physlib's unit-independent dimensionful quantities.
`Space 2` supplies the planar Euclidean geometry; its scalar coordinates and
metric are interpreted in an explicitly selected spatial length unit.
-/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Read a physical length as a real number in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- The two source labels printed in the supplied figure. -/
inductive SourceLabel where
  | S₁
  | S₂
  deriving DecidableEq, Repr

/-- The idealized acoustic-source kind stipulated by the problem. -/
inductive AcousticSourceKind where
  | isotropicPointSoundSource
  | other
  deriving DecidableEq, Repr

/-- Literal symbolic labels visible in the supplied raster. -/
inductive FigureLabel where
  | S₁
  | S₂
  | separationD
  deriving DecidableEq, Repr

/-!
Qualitative evidence read from the image: two red source dots and their labels
lie on a common horizontal baseline, with vertical projections down to a
double-headed separation indicator labelled `D`.  The raster itself contains
no numerical length.
-/
structure SourceSeparationFigure where
  showsRedSourceDot : SourceLabel → Bool
  showsLabel : FigureLabel → Bool
  sourceDotsLieOnHorizontalBaseline : Bool
  sourceOneIsLeftOfSourceTwo : Bool
  verticalProjectionsDropFromSources : Bool
  separationIndicatorRunsBetweenSources : Bool
  separationIndicatorIsDoubleHeaded : Bool
  separationIndicatorIsBelowBaseline : Bool
  containsNumericalDistanceText : Bool

/-!
The independent quantities, positions, emission phases, and arrival-phase
observable of the experiment.  The arrival observable is not defined from the
requested count; it is constrained only by the governing interference law.
-/
structure TwoPointSourceInterferenceSetup where
  spatialCoordinateUnit : LengthUnit
  sourcePosition : SourceLabel → Space 2
  midpoint : Space 2
  sourceSeparationD : LengthQuantity
  soundWavelength : LengthQuantity
  detectorCircleRadius : LengthQuantity
  sourceKind : SourceLabel → AcousticSourceKind
  emissionPhase : SourceLabel → Real.Angle
  wavesArriveExactlyOutOfPhaseAt : Space 2 → Prop
  figure : SourceSeparationFigure

/-- Numerical physical readouts stated in the problem prose. -/
structure MatchesProblemReadouts
    (setup : TwoPointSourceInterferenceSetup) : Prop where
  coordinatesAreInMeters :
    setup.spatialCoordinateUnit = LengthUnit.meters
  sourceSeparationMeters :
    lengthInMeters setup.sourceSeparationD = 7 / 4
  wavelengthMeters :
    lengthInMeters setup.soundWavelength = 1 / 2

/-!
Both labelled objects are isotropic point sources of sound and have equal
initial emission phase.
-/
structure MatchesCoherentIsotropicSourceScenario
    (setup : TwoPointSourceInterferenceSetup) : Prop where
  everySourceIsIsotropicPointSound : ∀ source : SourceLabel,
    setup.sourceKind source = .isotropicPointSoundSource
  sourcesEmitInPhase :
    setup.emissionPhase .S₁ = setup.emissionPhase .S₂

/-- Labels, colors, and incidences transcribed from the primary image. -/
structure MatchesSuppliedFigure
    (setup : TwoPointSourceInterferenceSetup) : Prop where
  everyRedSourceDotShown : ∀ source : SourceLabel,
    setup.figure.showsRedSourceDot source = true
  everyFigureLabelShown : ∀ label : FigureLabel,
    setup.figure.showsLabel label = true
  commonHorizontalBaseline :
    setup.figure.sourceDotsLieOnHorizontalBaseline = true
  sourceOneLeftInRaster :
    setup.figure.sourceOneIsLeftOfSourceTwo = true
  verticalSourceProjections :
    setup.figure.verticalProjectionsDropFromSources = true
  separationIndicatorBetweenSources :
    setup.figure.separationIndicatorRunsBetweenSources = true
  doubleHeadedSeparationIndicator :
    setup.figure.separationIndicatorIsDoubleHeaded = true
  separationIndicatorBelowBaseline :
    setup.figure.separationIndicatorIsBelowBaseline = true
  noNumericalDistanceInRaster :
    setup.figure.containsNumericalDistanceText = false

/-!
Planar geometry corresponding to the figure and the phrase "midpoint between
the sources."  Coordinate `0` is horizontal and coordinate `1` is vertical.
The metric and dimensionful separation use the same selected length unit.
-/
structure MatchesSourceGeometry
    (setup : TwoPointSourceInterferenceSetup) : Prop where
  sourceOneLeftOfSourceTwo :
    setup.sourcePosition .S₁ 0 < setup.sourcePosition .S₂ 0
  sourcesAreHorizontallyAligned :
    setup.sourcePosition .S₁ 1 = setup.sourcePosition .S₂ 1
  midpointCoordinates : ∀ coordinate : Fin 2,
    setup.midpoint coordinate =
      (setup.sourcePosition .S₁ coordinate +
        setup.sourcePosition .S₂ coordinate) / 2
  sourceDistanceIsD :
    dist (setup.sourcePosition .S₁) (setup.sourcePosition .S₂) =
      lengthReadout setup.spatialCoordinateUnit setup.sourceSeparationD

/-!
Strictly positive lengths and a precise form of "large circle": the radius is
greater than half the source separation, so both sources lie strictly inside
the circle once the midpoint geometry is imposed.  No requested point count is
included here.
-/
structure HasPhysicalLargeCircleParameters
    (setup : TwoPointSourceInterferenceSetup) : Prop where
  sourceSeparationPositive : ∀ unit : LengthUnit,
    0 < lengthReadout unit setup.sourceSeparationD
  wavelengthPositive : ∀ unit : LengthUnit,
    0 < lengthReadout unit setup.soundWavelength
  detectorRadiusPositive : ∀ unit : LengthUnit,
    0 < lengthReadout unit setup.detectorCircleRadius
  detectorCircleEnclosesBothSources :
    lengthReadout setup.spatialCoordinateUnit setup.sourceSeparationD / 2 <
      lengthReadout setup.spatialCoordinateUnit setup.detectorCircleRadius

/-- The large circular path along which the detector is moved. -/
def detectorCircle
    (setup : TwoPointSourceInterferenceSetup) : Set (Space 2) :=
  Metric.sphere setup.midpoint
    (lengthReadout setup.spatialCoordinateUnit setup.detectorCircleRadius)

/-- Absolute difference between the two source-to-detector path lengths. -/
def pathDifference
    (setup : TwoPointSourceInterferenceSetup) (detector : Space 2) : ℝ :=
  |dist detector (setup.sourcePosition .S₁) -
    dist detector (setup.sourcePosition .S₂)|

/-!
For coherent in-phase sources, destructive arrival occurs at an odd
half-integral multiple `(2 n + 1) λ / 2` of the common wavelength.  Natural
orders index the nonnegative absolute path differences.
-/
def IsOddHalfWavelengthPathDifference
    (setup : TwoPointSourceInterferenceSetup) (detector : Space 2) : Prop :=
  ∃ order : ℕ,
    pathDifference setup detector =
      ((2 * order + 1 : ℕ) : ℝ) *
        lengthReadout setup.spatialCoordinateUnit setup.soundWavelength / 2

/-!
The governing two-point-source phase law.  It relates the independent arrival
observable to path difference and wavelength at every planar detector point;
it contains neither a cardinality nor an answer label.
-/
structure SatisfiesTwoPointSourceInterferenceLaw
    (setup : TwoPointSourceInterferenceSetup) : Prop where
  outOfPhaseIffOddHalfWavelengthPathDifference : ∀ detector : Space 2,
    setup.wavesArriveExactlyOutOfPhaseAt detector ↔
      IsOddHalfWavelengthPathDifference setup detector

/-- Points on the detector circle where the two waves arrive in opposition. -/
def outOfPhaseDetectorPoints
    (setup : TwoPointSourceInterferenceSetup) : Set (Space 2) :=
  {detector |
    detector ∈ detectorCircle setup ∧
      setup.wavesArriveExactlyOutOfPhaseAt detector}

/-- Labels of the four printed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Detector-point counts printed beside the answer labels. -/
def displayedPointCount : AnswerChoice → ℕ
  | .A => 11
  | .B => 12
  | .C => 13
  | .D => 14

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A choice agrees with the cardinality derived from the physical model. -/
def MatchesDisplayedPointCount
    (setup : TwoPointSourceInterferenceSetup) (choice : AnswerChoice) : Prop :=
  (outOfPhaseDetectorPoints setup).ncard = displayedPointCount choice

/-- Exactly one printed choice agrees with the physical detector count. -/
def IsUniqueMatchingAnswer
    (setup : TwoPointSourceInterferenceSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedPointCount setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedPointCount setup other → other = choice

/-!
The geometry, readouts, large-circle condition, and odd-half-wavelength phase
law give exactly fourteen out-of-phase points.  The target count occurs only
in this conclusion, not in the setup or governing-law predicates.
-/
lemma outOfPhaseDetectorPointCount_exact
    (setup : TwoPointSourceInterferenceSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hScenario : MatchesCoherentIsotropicSourceScenario setup)
    (hGeometry : MatchesSourceGeometry setup)
    (hPhysical : HasPhysicalLargeCircleParameters setup)
    (hLaw : SatisfiesTwoPointSourceInterferenceLaw setup) :
    (outOfPhaseDetectorPoints setup).ncard = 14 := by
  exact by
      have hSourceDistance :
          dist (setup.sourcePosition .S₁) (setup.sourcePosition .S₂) = 7 / 4 := by
        rw [hGeometry.sourceDistanceIsD, hReadouts.coordinatesAreInMeters]
        exact hReadouts.sourceSeparationMeters
      have hHorizontalSeparation :
          setup.sourcePosition .S₂ 0 - setup.sourcePosition .S₁ 0 = 7 / 4 := by
        rw [Space.dist_eq, Fin.sum_univ_two] at hSourceDistance
        rw [hGeometry.sourcesAreHorizontallyAligned] at hSourceDistance
        norm_num [Real.sqrt_sq_eq_abs] at hSourceDistance
        rw [abs_of_neg (sub_neg.mpr hGeometry.sourceOneLeftOfSourceTwo)] at hSourceDistance
        linarith only [hSourceDistance]
      have hSourceOneHorizontal :
          setup.sourcePosition .S₁ 0 = setup.midpoint 0 - 7 / 8 := by
        have hMidpoint := hGeometry.midpointCoordinates (0 : Fin 2)
        linarith only [hMidpoint, hHorizontalSeparation]
      have hSourceTwoHorizontal :
          setup.sourcePosition .S₂ 0 = setup.midpoint 0 + 7 / 8 := by
        have hMidpoint := hGeometry.midpointCoordinates (0 : Fin 2)
        linarith only [hMidpoint, hHorizontalSeparation]
      have hSourceOneVertical :
          setup.sourcePosition .S₁ 1 = setup.midpoint 1 := by
        have hMidpoint := hGeometry.midpointCoordinates (1 : Fin 2)
        linarith only [hMidpoint, hGeometry.sourcesAreHorizontallyAligned]
      have hSourceTwoVertical :
          setup.sourcePosition .S₂ 1 = setup.midpoint 1 := by
        linarith only [hGeometry.sourcesAreHorizontallyAligned, hSourceOneVertical]
      let R : ℝ := lengthInMeters setup.detectorCircleRadius
      have hRadius : 7 / 8 < R := by
        have hEncloses := hPhysical.detectorCircleEnclosesBothSources
        rw [hReadouts.coordinatesAreInMeters] at hEncloses
        change lengthInMeters setup.sourceSeparationD / 2 < R at hEncloses
        rw [hReadouts.sourceSeparationMeters] at hEncloses
        norm_num at hEncloses
        exact hEncloses
      have hCircleEquation (detector : Space 2)
          (hDetectorCircle : detector ∈ detectorCircle setup) :
          (detector 0 - setup.midpoint 0) ^ 2 +
              (detector 1 - setup.midpoint 1) ^ 2 = R ^ 2 := by
        change dist detector setup.midpoint =
          lengthReadout setup.spatialCoordinateUnit setup.detectorCircleRadius at hDetectorCircle
        rw [hReadouts.coordinatesAreInMeters] at hDetectorCircle
        change dist detector setup.midpoint = R at hDetectorCircle
        rw [Space.dist_eq, Fin.sum_univ_two] at hDetectorCircle
        have hSquares : 0 ≤
            (detector 0 - setup.midpoint 0) ^ 2 +
              (detector 1 - setup.midpoint 1) ^ 2 := by positivity
        have hDetectorCircleSquared :=
          congrArg (fun distance : ℝ ↦ distance ^ 2) hDetectorCircle
        nlinarith only [hDetectorCircleSquared, Real.sq_sqrt hSquares]
      have hDistanceOneSquare (detector : Space 2)
          (hDetectorCircle : detector ∈ detectorCircle setup) :
          dist detector (setup.sourcePosition .S₁) ^ 2 =
            R ^ 2 + (7 / 8) ^ 2 +
              2 * (7 / 8) * (detector 0 - setup.midpoint 0) := by
        rw [Space.dist_eq, Fin.sum_univ_two]
        rw [Real.sq_sqrt (by positivity)]
        rw [hSourceOneHorizontal, hSourceOneVertical]
        nlinarith only [hCircleEquation detector hDetectorCircle]
      have hDistanceTwoSquare (detector : Space 2)
          (hDetectorCircle : detector ∈ detectorCircle setup) :
          dist detector (setup.sourcePosition .S₂) ^ 2 =
            R ^ 2 + (7 / 8) ^ 2 -
              2 * (7 / 8) * (detector 0 - setup.midpoint 0) := by
        rw [Space.dist_eq, Fin.sum_univ_two]
        rw [Real.sq_sqrt (by positivity)]
        rw [hSourceTwoHorizontal, hSourceTwoVertical]
        nlinarith only [hCircleEquation detector hDetectorCircle]
      have hPathDifferenceBounds (detector : Space 2) :
          0 ≤ pathDifference setup detector ∧
            pathDifference setup detector ≤ 7 / 4 := by
        constructor
        · exact abs_nonneg _
        · rw [pathDifference]
          calc
            |dist detector (setup.sourcePosition .S₁) -
                dist detector (setup.sourcePosition .S₂)| ≤
                dist (setup.sourcePosition .S₁) (setup.sourcePosition .S₂) := by
                  simpa [dist_comm] using
                    abs_dist_sub_le (setup.sourcePosition .S₁)
                      (setup.sourcePosition .S₂) detector
            _ = 7 / 4 := hSourceDistance
      have hPathDifferenceEquation (detector : Space 2)
          (hDetectorCircle : detector ∈ detectorCircle setup) :
          4 * (7 / 4) ^ 2 * (detector 0 - setup.midpoint 0) ^ 2 =
            pathDifference setup detector ^ 2 *
              (4 * R ^ 2 + (7 / 4) ^ 2 - pathDifference setup detector ^ 2) := by
        have hOne := hDistanceOneSquare detector hDetectorCircle
        have hTwo := hDistanceTwoSquare detector hDetectorCircle
        have hDifferenceSquares :
            dist detector (setup.sourcePosition .S₁) ^ 2 -
                dist detector (setup.sourcePosition .S₂) ^ 2 =
              2 * (7 / 4) * (detector 0 - setup.midpoint 0) := by
          nlinarith only [hOne, hTwo]
        have hSumSquare :
            (dist detector (setup.sourcePosition .S₁) +
                dist detector (setup.sourcePosition .S₂)) ^ 2 =
              4 * R ^ 2 + (7 / 4) ^ 2 - pathDifference setup detector ^ 2 := by
          rw [pathDifference, sq_abs]
          nlinarith only [hOne, hTwo]
        calc
          4 * (7 / 4) ^ 2 * (detector 0 - setup.midpoint 0) ^ 2 =
              (dist detector (setup.sourcePosition .S₁) ^ 2 -
                dist detector (setup.sourcePosition .S₂) ^ 2) ^ 2 := by
                  rw [hDifferenceSquares]
                  ring
          _ = ((dist detector (setup.sourcePosition .S₁) -
                  dist detector (setup.sourcePosition .S₂)) *
                (dist detector (setup.sourcePosition .S₁) +
                  dist detector (setup.sourcePosition .S₂))) ^ 2 := by ring
          _ = pathDifference setup detector ^ 2 *
                (dist detector (setup.sourcePosition .S₁) +
                  dist detector (setup.sourcePosition .S₂)) ^ 2 := by
                  rw [pathDifference, sq_abs]
                  ring
          _ = pathDifference setup detector ^ 2 *
                (4 * R ^ 2 + (7 / 4) ^ 2 -
                  pathDifference setup detector ^ 2) := by rw [hSumSquare]
      have hRadiusPositive : 0 < R := by linarith only [hRadius]
      have hRadiusSquare : (7 / 8 : ℝ) ^ 2 < R ^ 2 := by
        nlinarith only [hRadius]
      let A : ℝ → ℝ := fun delta ↦
        delta ^ 2 * (4 * R ^ 2 + (7 / 4) ^ 2 - delta ^ 2) /
          (4 * (7 / 4) ^ 2)
      let B : ℝ → ℝ := fun delta ↦ R ^ 2 - A delta
      let delta : Fin 3 → ℝ := fun order ↦
        ((2 * (order : ℕ) + 1 : ℕ) : ℝ) / 4
      have hAPositive (order : Fin 3) : 0 < A (delta order) := by
        fin_cases order <;> norm_num [A, delta] <;>
          nlinarith only [sq_nonneg R]
      have hBPositive (order : Fin 3) : 0 < B (delta order) := by
        fin_cases order <;> norm_num [A, B, delta] <;>
          nlinarith only [hRadiusSquare]
      let sign : Bool → ℝ := fun positive ↦ if positive then 1 else -1
      let point : ℝ → ℝ → Space 2 := fun x y ↦
        ⟨![setup.midpoint 0 + x, setup.midpoint 1 + y]⟩
      let candidate : (Fin 3 × Bool × Bool) ⊕ Bool → Space 2
        | .inl index =>
            point
              (sign index.2.1 * Real.sqrt (A (delta index.1)))
              (sign index.2.2 * Real.sqrt (B (delta index.1)))
        | .inr horizontalSign => point (sign horizontalSign * R) 0
      have hCandidateCircle (index : (Fin 3 × Bool × Bool) ⊕ Bool) :
          candidate index ∈ detectorCircle setup := by
        change dist (candidate index) setup.midpoint =
          lengthReadout setup.spatialCoordinateUnit setup.detectorCircleRadius
        rw [hReadouts.coordinatesAreInMeters]
        change dist (candidate index) setup.midpoint = R
        rw [Space.dist_eq, Fin.sum_univ_two]
        rcases index with index | horizontalSign
        · rcases index with ⟨order, verticalSign, horizontalSign⟩
          have hA := hAPositive order
          have hB := hBPositive order
          fin_cases verticalSign <;> fin_cases horizontalSign <;>
            simp [candidate, point, sign, Real.sq_sqrt (le_of_lt hA),
              Real.sq_sqrt (le_of_lt hB), B, Real.sqrt_sq_eq_abs,
              abs_of_pos hRadiusPositive]
        · fin_cases horizontalSign <;>
            simp [candidate, point, sign, Real.sqrt_sq_eq_abs,
              abs_of_pos hRadiusPositive]
      have hPathDifferenceUnique (detector : Space 2)
          (hDetectorCircle : detector ∈ detectorCircle setup)
          (target : ℝ) (hTargetNonnegative : 0 ≤ target)
          (hTargetBound : target ≤ 7 / 4)
          (hHorizontalSquare :
            (detector 0 - setup.midpoint 0) ^ 2 = A target) :
          pathDifference setup detector = target := by
        have hEquation := hPathDifferenceEquation detector hDetectorCircle
        have hBounds := hPathDifferenceBounds detector
        have hPolynomial :
            target ^ 2 * (4 * R ^ 2 + (7 / 4) ^ 2 - target ^ 2) =
              pathDifference setup detector ^ 2 *
                (4 * R ^ 2 + (7 / 4) ^ 2 -
                  pathDifference setup detector ^ 2) := by
          rw [hHorizontalSquare] at hEquation
          norm_num [A] at hEquation ⊢
          nlinarith only [hEquation]
        have hPathSquareBound :
            pathDifference setup detector ^ 2 ≤ (7 / 4 : ℝ) ^ 2 := by
          nlinarith only [hBounds.1, hBounds.2]
        have hTargetSquareBound : target ^ 2 ≤ (7 / 4 : ℝ) ^ 2 := by
          nlinarith only [hTargetNonnegative, hTargetBound]
        have hRemainingFactorPositive :
            0 < 4 * R ^ 2 + (7 / 4) ^ 2 - target ^ 2 -
              pathDifference setup detector ^ 2 := by
          nlinarith only [hRadiusSquare, hPathSquareBound, hTargetSquareBound]
        have hEqualSquares :
            pathDifference setup detector ^ 2 = target ^ 2 := by
          nlinarith only [hPolynomial, hRemainingFactorPositive]
        nlinarith only [hEqualSquares, hBounds.1, hTargetNonnegative]
      let candidateDelta : (Fin 3 × Bool × Bool) ⊕ Bool → ℝ
        | .inl index => delta index.1
        | .inr _ => 7 / 4
      have hCandidateDeltaNonnegative
          (index : (Fin 3 × Bool × Bool) ⊕ Bool) :
          0 ≤ candidateDelta index := by
        rcases index with index | horizontalSign
        · rcases index with ⟨order, xSign, ySign⟩
          change 0 ≤ (((2 * (order : ℕ) + 1 : ℕ) : ℝ) / 4)
          positivity
        · change 0 ≤ (7 / 4 : ℝ)
          norm_num
      have hCandidateDeltaBound
          (index : (Fin 3 × Bool × Bool) ⊕ Bool) :
          candidateDelta index ≤ 7 / 4 := by
        rcases index with index | horizontalSign
        · rcases index with ⟨order, xSign, ySign⟩
          change (((2 * (order : ℕ) + 1 : ℕ) : ℝ) / 4) ≤ 7 / 4
          have hOrderNat : (order : ℕ) ≤ 2 := by omega
          have hOrder : ((order : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hOrderNat
          norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
          nlinarith only [hOrder]
        · change (7 / 4 : ℝ) ≤ 7 / 4
          norm_num
      have hCandidateHorizontalSquare
          (index : (Fin 3 × Bool × Bool) ⊕ Bool) :
          (candidate index 0 - setup.midpoint 0) ^ 2 =
            A (candidateDelta index) := by
        rcases index with index | horizontalSign
        · rcases index with ⟨order, verticalSign, horizontalSign⟩
          have hA := hAPositive order
          fin_cases verticalSign <;> fin_cases horizontalSign <;>
            simp [candidate, candidateDelta, point, sign,
              Real.sq_sqrt (le_of_lt hA)]
        · fin_cases horizontalSign <;>
            simp [candidate, candidateDelta, point, sign, A] <;> ring
      have hCandidatePathDifference
          (index : (Fin 3 × Bool × Bool) ⊕ Bool) :
          pathDifference setup (candidate index) = candidateDelta index :=
        hPathDifferenceUnique (candidate index) (hCandidateCircle index)
          (candidateDelta index) (hCandidateDeltaNonnegative index)
          (hCandidateDeltaBound index) (hCandidateHorizontalSquare index)
      have hSignInjective : Function.Injective sign := by
        intro first second hEqual
        fin_cases first
        all_goals fin_cases second
        all_goals try rfl
        all_goals norm_num [sign] at hEqual
      have hDeltaInjective : Function.Injective delta := by
        intro first second hEqual
        fin_cases first
        all_goals fin_cases second
        all_goals try rfl
        all_goals norm_num [delta] at hEqual
      have hCandidateInjective : Function.Injective candidate := by
        intro first second hEqual
        have hPathEqual := congrArg (fun detector ↦ pathDifference setup detector) hEqual
        rw [hCandidatePathDifference first, hCandidatePathDifference second] at hPathEqual
        rcases first with first | first
        · rcases second with second | second
          · rcases first with ⟨firstOrder, firstXSign, firstYSign⟩
            rcases second with ⟨secondOrder, secondXSign, secondYSign⟩
            have hOrder : firstOrder = secondOrder := by
              apply hDeltaInjective
              simpa [candidateDelta] using hPathEqual
            subst secondOrder
            have hXCoordinate := congrArg (fun detector : Space 2 ↦ detector 0) hEqual
            have hYCoordinate := congrArg (fun detector : Space 2 ↦ detector 1) hEqual
            have hSqrtA : 0 < Real.sqrt (A (delta firstOrder)) :=
              Real.sqrt_pos.2 (hAPositive firstOrder)
            have hSqrtB : 0 < Real.sqrt (B (delta firstOrder)) :=
              Real.sqrt_pos.2 (hBPositive firstOrder)
            have hXSign : firstXSign = secondXSign := by
              apply hSignInjective
              simp [candidate, point] at hXCoordinate
              rcases hXCoordinate with hSigns | hZero
              · exact hSigns
              · nlinarith only [hSqrtA, hZero]
            have hYSign : firstYSign = secondYSign := by
              apply hSignInjective
              simp [candidate, point] at hYCoordinate
              rcases hYCoordinate with hSigns | hZero
              · exact hSigns
              · nlinarith only [hSqrtB, hZero]
            subst secondXSign
            subst secondYSign
            rfl
          · rcases first with ⟨firstOrder, firstXSign, firstYSign⟩
            fin_cases firstOrder <;> norm_num [candidateDelta, delta] at hPathEqual
        · rcases second with second | second
          · rcases second with ⟨secondOrder, secondXSign, secondYSign⟩
            fin_cases secondOrder <;> norm_num [candidateDelta, delta] at hPathEqual
          · have hXCoordinate := congrArg (fun detector : Space 2 ↦ detector 0) hEqual
            have hSigns : first = second := by
              apply hSignInjective
              simp [candidate, point] at hXCoordinate
              rcases hXCoordinate with hSigns | hZero
              · exact hSigns
              · nlinarith only [hRadiusPositive, hZero]
            subst second
            rfl
      have hHorizontalSquareFromPath (detector : Space 2)
          (hDetectorCircle : detector ∈ detectorCircle setup) :
          (detector 0 - setup.midpoint 0) ^ 2 =
            A (pathDifference setup detector) := by
        have hEquation := hPathDifferenceEquation detector hDetectorCircle
        norm_num [A] at hEquation ⊢
        nlinarith only [hEquation]
      have hWavelengthInCoordinateUnit :
          lengthReadout setup.spatialCoordinateUnit setup.soundWavelength = 1 / 2 := by
        rw [hReadouts.coordinatesAreInMeters]
        exact hReadouts.wavelengthMeters
      have hInteriorRepresentation (detector : Space 2)
          (hDetectorCircle : detector ∈ detectorCircle setup)
          (order : Fin 3)
          (hPath : pathDifference setup detector = delta order) :
          detector ∈ Set.range candidate := by
        have hHorizontalSquare :=
          hHorizontalSquareFromPath detector hDetectorCircle
        rw [hPath] at hHorizontalSquare
        have hVerticalSquare :
            (detector 1 - setup.midpoint 1) ^ 2 = B (delta order) := by
          have hCircle := hCircleEquation detector hDetectorCircle
          simp only [B]
          nlinarith only [hCircle, hHorizontalSquare]
        have hSqrtASquare :
            Real.sqrt (A (delta order)) ^ 2 = A (delta order) :=
          Real.sq_sqrt (le_of_lt (hAPositive order))
        have hSqrtBSquare :
            Real.sqrt (B (delta order)) ^ 2 = B (delta order) :=
          Real.sq_sqrt (le_of_lt (hBPositive order))
        have hHorizontalCases :
            detector 0 - setup.midpoint 0 = Real.sqrt (A (delta order)) ∨
              detector 0 - setup.midpoint 0 = -Real.sqrt (A (delta order)) := by
          rw [← sq_eq_sq_iff_eq_or_eq_neg, hSqrtASquare]
          exact hHorizontalSquare
        have hVerticalCases :
            detector 1 - setup.midpoint 1 = Real.sqrt (B (delta order)) ∨
              detector 1 - setup.midpoint 1 = -Real.sqrt (B (delta order)) := by
          rw [← sq_eq_sq_iff_eq_or_eq_neg, hSqrtBSquare]
          exact hVerticalSquare
        rcases hHorizontalCases with hHorizontal | hHorizontal <;>
          rcases hVerticalCases with hVertical | hVertical
        · refine ⟨Sum.inl (order, true, true), ?_⟩
          apply Space.eq_of_apply
          intro coordinate
          fin_cases coordinate <;> simp [candidate, point, sign] <;>
            linarith only [hHorizontal, hVertical]
        · refine ⟨Sum.inl (order, true, false), ?_⟩
          apply Space.eq_of_apply
          intro coordinate
          fin_cases coordinate <;> simp [candidate, point, sign] <;>
            linarith only [hHorizontal, hVertical]
        · refine ⟨Sum.inl (order, false, true), ?_⟩
          apply Space.eq_of_apply
          intro coordinate
          fin_cases coordinate <;> simp [candidate, point, sign] <;>
            linarith only [hHorizontal, hVertical]
        · refine ⟨Sum.inl (order, false, false), ?_⟩
          apply Space.eq_of_apply
          intro coordinate
          fin_cases coordinate <;> simp [candidate, point, sign] <;>
            linarith only [hHorizontal, hVertical]
      have hTerminalRepresentation (detector : Space 2)
          (hDetectorCircle : detector ∈ detectorCircle setup)
          (hPath : pathDifference setup detector = 7 / 4) :
          detector ∈ Set.range candidate := by
        have hHorizontalSquare :=
          hHorizontalSquareFromPath detector hDetectorCircle
        rw [hPath] at hHorizontalSquare
        have hHorizontalSquareRadius :
            (detector 0 - setup.midpoint 0) ^ 2 = R ^ 2 := by
          norm_num [A] at hHorizontalSquare ⊢
          nlinarith only [hHorizontalSquare]
        have hVerticalZero : detector 1 - setup.midpoint 1 = 0 := by
          have hCircle := hCircleEquation detector hDetectorCircle
          nlinarith only [hCircle, hHorizontalSquareRadius]
        have hHorizontalCases :
            detector 0 - setup.midpoint 0 = R ∨
              detector 0 - setup.midpoint 0 = -R := by
          rwa [sq_eq_sq_iff_eq_or_eq_neg] at hHorizontalSquareRadius
        rcases hHorizontalCases with hHorizontal | hHorizontal
        · refine ⟨Sum.inr true, ?_⟩
          apply Space.eq_of_apply
          intro coordinate
          fin_cases coordinate <;> simp [candidate, point, sign] <;>
            linarith only [hHorizontal, hVerticalZero]
        · refine ⟨Sum.inr false, ?_⟩
          apply Space.eq_of_apply
          intro coordinate
          fin_cases coordinate <;> simp [candidate, point, sign] <;>
            linarith only [hHorizontal, hVerticalZero]
      have hDetectorSet :
          outOfPhaseDetectorPoints setup = Set.range candidate := by
        ext detector
        constructor
        · rintro ⟨hDetectorCircle, hOutOfPhase⟩
          rw [hLaw.outOfPhaseIffOddHalfWavelengthPathDifference] at hOutOfPhase
          rcases hOutOfPhase with ⟨order, hOrder⟩
          have hOrder' :
              pathDifference setup detector =
                (((2 * order + 1 : ℕ) : ℝ) / 4) := by
            rw [hWavelengthInCoordinateUnit] at hOrder
            norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
              Nat.cast_ofNat] at hOrder ⊢
            convert hOrder using 1 <;> ring
          have hOrderBound : order ≤ 3 := by
            have hBound := (hPathDifferenceBounds detector).2
            rw [hOrder'] at hBound
            push_cast at hBound
            have hOrderCast : (order : ℝ) ≤ 3 := by
              nlinarith only [hBound]
            exact_mod_cast hOrderCast
          by_cases hInteriorOrder : order < 3
          · apply hInteriorRepresentation detector hDetectorCircle
              ⟨order, hInteriorOrder⟩
            simpa [delta] using hOrder'
          · have hTerminalOrder : order = 3 := by omega
            subst order
            apply hTerminalRepresentation detector hDetectorCircle
            norm_num at hOrder' ⊢
            exact hOrder'
        · rintro ⟨index, rfl⟩
          refine ⟨hCandidateCircle index, ?_⟩
          rw [hLaw.outOfPhaseIffOddHalfWavelengthPathDifference]
          rcases index with index | horizontalSign
          · refine ⟨index.1, ?_⟩
            rw [hCandidatePathDifference (Sum.inl index)]
            simp [candidateDelta, delta, hWavelengthInCoordinateUnit]
            ring
          · refine ⟨3, ?_⟩
            rw [hCandidatePathDifference (Sum.inr horizontalSign)]
            norm_num [candidateDelta, hWavelengthInCoordinateUnit]
      rw [hDetectorSet, Set.ncard_range_of_injective hCandidateInjective]
      norm_num

/-!
For the two in-phase isotropic point sources in the raster, `D = 1.75 m` and
`λ = 0.50 m` yield fourteen out-of-phase detector positions, uniquely
selecting answer D.

This formalizes `thm:physics:phyx_mini_0312:target`.  The answer catalogue
records the printed options, but the requested point count and selected answer
are absent from every physical premise and must be established here.
-/
theorem problem_phyx_mini_0312
    (setup : TwoPointSourceInterferenceSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hScenario : MatchesCoherentIsotropicSourceScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hGeometry : MatchesSourceGeometry setup)
    (hPhysical : HasPhysicalLargeCircleParameters setup)
    (hLaw : SatisfiesTwoPointSourceInterferenceLaw setup) :
    (outOfPhaseDetectorPoints setup).ncard = 14 ∧
      IsUniqueMatchingAnswer setup .D := by
  have hCount := outOfPhaseDetectorPointCount_exact setup hReadouts hScenario
    hGeometry hPhysical hLaw
  refine ⟨hCount, ?_⟩
  constructor
  · simpa [MatchesDisplayedPointCount, displayedPointCount]
  · intro other hOther
    cases other <;>
      simp_all [MatchesDisplayedPointCount, displayedPointCount]

end PhyXMiniProblems.ProblemPhyXMini0312
