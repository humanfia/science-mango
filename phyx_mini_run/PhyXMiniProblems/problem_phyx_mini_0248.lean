import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Basic

/-!
# Separation of the two order-two dark fringes

A `633 nm` helium-neon laser illuminates two narrow slits separated by
`0.40 mm`, with a viewing screen `2.0 m` beyond the slit plane.  The supplied
figure depicts a normally incident plane wave, spreading waves from the two
slits, their overlap, and a symmetric bright/dark screen pattern.

The propagation law below uses the exact Euclidean path lengths from two
point-like coherent apertures to a finite-distance screen.  In particular, it
does not turn the usual paraxial relation `y = L sin θ` into a global exact
equality.  The resulting separation is slightly larger than `15.825 mm`, but
still rounds to the displayed `15.8 mm`.

Physical lengths are represented by unit-independent Physlib quantities.
Real numbers are used only for signed coordinate readouts and numerical
readouts in explicitly selected units.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0248

open Dimension

/-! ## Dimensionful optical quantities and unit readouts -/

/-- A nonnegative physical length, independent of a chosen readout unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical length used for transverse screen coordinates. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a nonnegative physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed transverse coordinate in the selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (length : SignedLengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Millimeter readout of a physical length. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- Nanometer readout of a physical length. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-! ## Apparatus, figure labels, and fringe observables -/

/-- The two openings in the barrier, viewed from the top as in the figure. -/
inductive SlitLabel where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- The signed transverse location of a slit relative to the optical axis. -/
def SlitLabel.sign : SlitLabel → ℝ
  | .upper => 1
  | .lower => -1

/-- The two sides of the symmetric interference pattern. -/
inductive FringeSide where
  | above
  | below
  deriving DecidableEq, Repr

/-- Sign of a transverse screen coordinate on either side of the center. -/
def FringeSide.sign : FringeSide → ℝ
  | .above => 1
  | .below => -1

/-- Bright maxima and dark minima in the screen pattern. -/
inductive FringeKind where
  | bright
  | dark
  deriving DecidableEq, Repr

/-!
Offset from an integral path-difference multiple: a bright order `m` uses
`m`, while a dark order `m` uses `m + 1/2`.  Thus the question's order-two
dark fringes have path-difference magnitude `(2 + 1/2) λ`.
-/
def FringeKind.orderShift : FringeKind → ℝ
  | .bright => 0
  | .dark => 1 / 2

/-- The source technology named in the question. -/
inductive LightSourceKind where
  | heliumNeonLaser
  | other
  deriving DecidableEq, Repr

/-- Wavefront shape incident on the double slit. -/
inductive IncidentWavefront where
  | plane
  | other
  deriving DecidableEq, Repr

/-- Each sufficiently narrow opening is modeled as a point-like wave source. -/
inductive ApertureModel where
  | pointLikeNarrow
  | finiteWidth
  deriving DecidableEq, Repr

/-- The four explanatory stages explicitly shown in the supplied diagram. -/
inductive FigureStage where
  | incidentPlaneWave
  | wavesSpreadBehindSlits
  | wavesOverlapAndInterfere
  | brightFringesAtAntinodalScreenIntersections
  deriving DecidableEq, Repr

/-!
Physical data and observables of the double-slit experiment.

`fringeCoordinate kind side m` is the signed transverse screen position of a
labeled fringe.  No field assigns the requested order-two separation or an
answer-choice value.
-/
structure DoubleSlitInterferenceSetup where
  sourceKind : LightSourceKind
  incidentWavefront : IncidentWavefront
  apertureModel : SlitLabel → ApertureModel
  wavelength : LengthQuantity
  slitSeparation : LengthQuantity
  screenDistance : LengthQuantity
  slitOutputsMutuallyCoherent : Prop
  slitOutputPhaseCycles : SlitLabel → ℝ
  fringeCoordinate : FringeKind → FringeSide → ℕ → SignedLengthQuantity
  figureDepicts : FigureStage → Prop
  figureMarksCentralMaximum : Prop
  figureShowsBrightOrder : FringeSide → ℕ → Prop

/-!
Qualitative information supplied by the prose and primary figure.  The same
normally incident plane wave illuminates two point-like narrow coherent
apertures in phase.  The figure labels the central maximum as `m = 0` and the
subsequent bright maxima on both sides by `m = 1, 2, 3, 4`.

This predicate contains no numerical dark-fringe separation.
-/
def MatchesScenarioAndFigure
    (setup : DoubleSlitInterferenceSetup) : Prop :=
  setup.sourceKind = .heliumNeonLaser ∧
    setup.incidentWavefront = .plane ∧
    (∀ slit : SlitLabel, setup.apertureModel slit = .pointLikeNarrow) ∧
    setup.slitOutputsMutuallyCoherent ∧
    (∀ slit : SlitLabel, setup.slitOutputPhaseCycles slit = 0) ∧
    (∀ stage : FigureStage, setup.figureDepicts stage) ∧
    setup.figureMarksCentralMaximum ∧
    (∀ side : FringeSide,
      signedLengthReadout LengthUnit.millimeters
          (setup.fringeCoordinate .bright side 0) = 0) ∧
    ∀ (side : FringeSide) (order : ℕ),
      setup.figureShowsBrightOrder side order ↔ 1 ≤ order ∧ order ≤ 4

/-!
Numerical readouts stated in the question: wavelength `633 nm`, slit spacing
`0.40 mm`, and slit-to-screen distance `2.0 m`.
-/
def MatchesProblemReadouts
    (setup : DoubleSlitInterferenceSetup) : Prop :=
  lengthInNanometers setup.wavelength = 633 ∧
    lengthInMillimeters setup.slitSeparation = 2 / 5 ∧
    lengthInMeters setup.screenDistance = 2

/-- Positive, nondegenerate optical and geometric parameters. -/
def HasPhysicalParameters
    (setup : DoubleSlitInterferenceSetup) : Prop :=
  0 < lengthInMeters setup.wavelength ∧
    0 < lengthInMeters setup.slitSeparation ∧
    0 < lengthInMeters setup.screenDistance

/-! ## Exact finite-screen two-source laws -/

/-!
Euclidean path length from one slit to a screen coordinate, read in one common
length unit.  The slit plane is at axial coordinate zero, the screen is at
`screenDistance`, and the slit coordinates are `± slitSeparation / 2`.
-/
def pathLengthFromSlitReadout
    (unit : LengthUnit) (setup : DoubleSlitInterferenceSetup)
    (slit : SlitLabel) (screenCoordinate : SignedLengthQuantity) : ℝ :=
  Real.sqrt
    ((lengthReadout unit setup.screenDistance) ^ 2 +
      (signedLengthReadout unit screenCoordinate -
        slit.sign * lengthReadout unit setup.slitSeparation / 2) ^ 2)

/-!
Only path differences smaller than the slit spacing correspond to a fringe at
a finite screen coordinate in the exact two-point-source geometry.  The
condition is stated in meters, but is independent of the selected unit.
-/
def IsFiniteFringeOrder
    (setup : DoubleSlitInterferenceSetup)
    (kind : FringeKind) (order : ℕ) : Prop :=
  ((order : ℝ) + kind.orderShift) * lengthInMeters setup.wavelength <
    lengthInMeters setup.slitSeparation

/-!
Exact scalar-wave interference laws for two in-phase point-like sources and a
finite-distance planar screen.

For every physically finite fringe, the difference between the Euclidean path
lengths from the lower and upper slits is the appropriate integer or
half-integer multiple of the wavelength.  The second field records which side
of the optical axis the named coordinate lies on.  Neither field mentions the
distance between the two order-two dark fringes or any answer choice.
-/
structure SatisfiesExactTwoPointSourceLaws
    (setup : DoubleSlitInterferenceSetup) : Prop where
  pathDifferenceCondition :
    ∀ (kind : FringeKind) (side : FringeSide) (order : ℕ)
        (unit : LengthUnit),
      IsFiniteFringeOrder setup kind order →
        pathLengthFromSlitReadout unit setup .lower
            (setup.fringeCoordinate kind side order) -
          pathLengthFromSlitReadout unit setup .upper
            (setup.fringeCoordinate kind side order) =
          side.sign * ((order : ℝ) + kind.orderShift) *
            lengthReadout unit setup.wavelength
  fringeLiesOnNamedSide :
    ∀ (kind : FringeKind) (side : FringeSide) (order : ℕ)
        (unit : LengthUnit),
      IsFiniteFringeOrder setup kind order →
        0 ≤ side.sign * signedLengthReadout unit
          (setup.fringeCoordinate kind side order)

/-! ## Requested separation and displayed answer choices -/

/--
Distance between the two symmetric dark fringes of a given order, read in
millimeters.  This is a generic observable derived from their signed screen
coordinates, not a definition of the numerical answer.
-/
def darkFringeSeparationInMillimeters
    (setup : DoubleSlitInterferenceSetup) (order : ℕ) : ℝ :=
  |signedLengthReadout LengthUnit.millimeters
        (setup.fringeCoordinate .dark .above order) -
    signedLengthReadout LengthUnit.millimeters
        (setup.fringeCoordinate .dark .below order)|

/-!
Exact separation of the symmetric solutions for axial distance `L`, slit
spacing `d`, and positive path-difference magnitude `δ` in a common unit.
This generic geometric expression is not specialized to the problem data.
-/
def finiteScreenSymmetricSeparation
    (axialDistance slitSpacing pathDifference : ℝ) : ℝ :=
  pathDifference * Real.sqrt
    ((4 * axialDistance ^ 2 + slitSpacing ^ 2 - pathDifference ^ 2) /
      (slitSpacing ^ 2 - pathDifference ^ 2))

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The distance in millimeters printed next to each answer label. -/
def displayedDistanceInMillimeters : AnswerChoice → ℝ
  | .A => 79 / 5
  | .B => 76 / 5
  | .C => 84 / 5
  | .D => 81 / 5

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-- Round a millimeter readout to the nearest tenth of a millimeter. -/
def roundedToNearestTenthMillimeter (value : ℝ) : ℝ :=
  (round (10 * value) : ℝ) / 10

/-!
A displayed choice matches the physical result when the exact finite-screen
separation, rounded to the precision used by all four choices, equals its
printed value.
-/
def MatchesDisplayedDistance
    (setup : DoubleSlitInterferenceSetup) (choice : AnswerChoice) : Prop :=
  roundedToNearestTenthMillimeter
      (darkFringeSeparationInMillimeters setup 2) =
    displayedDistanceInMillimeters choice

/-- A choice is the unique displayed value matching the physical result. -/
def IsUniqueMatchingDisplayedDistance
    (setup : DoubleSlitInterferenceSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedDistance setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedDistance setup other → other = choice

/-!
The exact finite-screen geometry gives the radical expression below.  Here
`633 / 400000 mm` is the order-two dark path difference
`(2 + 1/2) · 633 nm`.  This is approximately `15.8251239 mm`, rather than
identically the paraxial value `633 / 40 mm = 15.825 mm`.
-/
lemma orderTwoDarkFringeSeparation_exactFiniteScreen
    (setup : DoubleSlitInterferenceSetup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesExactTwoPointSourceLaws setup) :
    darkFringeSeparationInMillimeters setup 2 =
      finiteScreenSymmetricSeparation 2000 (2 / 5) (633 / 400000) := by
  have nanometers_to_millimeters (length : LengthQuantity) :
      lengthInMillimeters length =
        (1 / 1000000 : ℝ) * lengthInNanometers length := by
    let u_nm : UnitChoices :=
      { UnitChoices.SI with length := LengthUnit.nanometers }
    let u_mm : UnitChoices :=
      { UnitChoices.SI with length := LengthUnit.millimeters }
    let scaleFactor : NNReal := ⟨1 / 1000000, by norm_num⟩
    have hscale : u_nm.dimScale u_mm L𝓭 = scaleFactor := by
      norm_num [u_nm, u_mm, scaleFactor, UnitChoices.dimScale,
        LengthUnit.nanometers, LengthUnit.millimeters, LengthUnit.scale,
        LengthUnit.meters, LengthUnit.div_eq_val]
    have hchange := congrArg WithDim.val (length.2 u_nm u_mm)
    have hcoe : (scaleFactor : ℝ) = 1 / 1000000 :=
      NNReal.coe_mk _ _
    change (length u_mm).val =
      (1 / 1000000 : ℝ) * (length u_nm).val
    rw [hchange]
    simp only [WithDim.smul_val, WithDim.dim_apply, hscale,
      smul_eq_mul]
    change (scaleFactor : ℝ) * ((length u_nm).val : ℝ) =
      (1 / 1000000 : ℝ) * ((length u_nm).val : ℝ)
    rw [hcoe]
  have meters_to_millimeters (length : LengthQuantity) :
      lengthInMillimeters length = 1000 * lengthInMeters length := by
    let u_m : UnitChoices :=
      { UnitChoices.SI with length := LengthUnit.meters }
    let u_mm : UnitChoices :=
      { UnitChoices.SI with length := LengthUnit.millimeters }
    let scaleFactor : NNReal := ⟨1000, by norm_num⟩
    have hscale : u_m.dimScale u_mm L𝓭 = scaleFactor := by
      norm_num [u_m, u_mm, scaleFactor, UnitChoices.dimScale,
        LengthUnit.millimeters, LengthUnit.scale, LengthUnit.meters,
        LengthUnit.div_eq_val]
    have hchange := congrArg WithDim.val (length.2 u_m u_mm)
    have hcoe : (scaleFactor : ℝ) = 1000 := NNReal.coe_mk _ _
    change (length u_mm).val = (1000 : ℝ) * (length u_m).val
    rw [hchange]
    simp only [WithDim.smul_val, WithDim.dim_apply, hscale,
      smul_eq_mul]
    change (scaleFactor : ℝ) * ((length u_m).val : ℝ) =
      (1000 : ℝ) * ((length u_m).val : ℝ)
    rw [hcoe]
  rcases h_readouts with ⟨hwavelength_nm, hslit_mm, hscreen_m⟩
  have hwavelength_mm :
      lengthInMillimeters setup.wavelength = (633 / 1000000 : ℝ) := by
    rw [nanometers_to_millimeters, hwavelength_nm]
    norm_num
  have hscreen_mm :
      lengthInMillimeters setup.screenDistance = (2000 : ℝ) := by
    rw [meters_to_millimeters, hscreen_m]
    norm_num
  have hwavelength_m :
      lengthInMeters setup.wavelength = (633 / 1000000000 : ℝ) := by
    nlinarith [meters_to_millimeters setup.wavelength, hwavelength_mm]
  have hslit_m :
      lengthInMeters setup.slitSeparation = (1 / 2500 : ℝ) := by
    nlinarith [meters_to_millimeters setup.slitSeparation, hslit_mm]
  have hfinite : IsFiniteFringeOrder setup .dark 2 := by
    unfold IsFiniteFringeOrder
    rw [hwavelength_m, hslit_m]
    norm_num [FringeKind.orderShift]
  let yAbove : ℝ :=
    signedLengthReadout LengthUnit.millimeters
      (setup.fringeCoordinate .dark .above 2)
  let yBelow : ℝ :=
    signedLengthReadout LengthUnit.millimeters
      (setup.fringeCoordinate .dark .below 2)
  have hAbovePath :=
    h_laws.pathDifferenceCondition .dark .above 2
      LengthUnit.millimeters hfinite
  have hBelowPath :=
    h_laws.pathDifferenceCondition .dark .below 2
      LengthUnit.millimeters hfinite
  simp [pathLengthFromSlitReadout, SlitLabel.sign, FringeSide.sign,
    FringeKind.orderShift] at hAbovePath hBelowPath
  dsimp [lengthInMillimeters] at hscreen_mm hslit_mm hwavelength_mm
  rw [hscreen_mm, hslit_mm, hwavelength_mm] at hAbovePath hBelowPath
  norm_num at hAbovePath hBelowPath
  have hAbovePath' :
    Real.sqrt
          ((2000 : ℝ) ^ 2 + (yAbove + (2 / 5 : ℝ) / 2) ^ 2) -
        Real.sqrt
          ((2000 : ℝ) ^ 2 + (yAbove - (2 / 5 : ℝ) / 2) ^ 2) =
      (633 / 400000 : ℝ) := by
    norm_num [yAbove] at hAbovePath ⊢
    exact hAbovePath
  have hBelowPath' :
    Real.sqrt
          ((2000 : ℝ) ^ 2 + (yBelow + (2 / 5 : ℝ) / 2) ^ 2) -
        Real.sqrt
          ((2000 : ℝ) ^ 2 + (yBelow - (2 / 5 : ℝ) / 2) ^ 2) =
      -(633 / 400000 : ℝ) := by
    norm_num [yBelow] at hBelowPath ⊢
    exact hBelowPath
  have hAboveSide :=
    h_laws.fringeLiesOnNamedSide .dark .above 2
      LengthUnit.millimeters hfinite
  have hBelowSide :=
    h_laws.fringeLiesOnNamedSide .dark .below 2
      LengthUnit.millimeters hfinite
  have hAboveSide' : 0 ≤ yAbove := by
    simpa [FringeSide.sign, yAbove] using hAboveSide
  have hBelowSide' : 0 ≤ -yBelow := by
    simpa [FringeSide.sign, yBelow] using hBelowSide
  have coordinate_square
      (y sign axialDistance slitSpacing pathDifference : ℝ)
      (hsign : sign ^ 2 = 1)
      (hpath :
        Real.sqrt
              (axialDistance ^ 2 + (y + slitSpacing / 2) ^ 2) -
            Real.sqrt
              (axialDistance ^ 2 + (y - slitSpacing / 2) ^ 2) =
          sign * pathDifference) :
      4 * (slitSpacing ^ 2 - pathDifference ^ 2) * y ^ 2 =
        pathDifference ^ 2 *
          (4 * axialDistance ^ 2 + slitSpacing ^ 2 -
            pathDifference ^ 2) := by
    let a :=
      Real.sqrt (axialDistance ^ 2 + (y + slitSpacing / 2) ^ 2)
    let b :=
      Real.sqrt (axialDistance ^ 2 + (y - slitSpacing / 2) ^ 2)
    have ha_sq :
        a ^ 2 = axialDistance ^ 2 + (y + slitSpacing / 2) ^ 2 := by
      dsimp [a]
      rw [Real.sq_sqrt]
      positivity
    have hb_sq :
        b ^ 2 = axialDistance ^ 2 + (y - slitSpacing / 2) ^ 2 := by
      dsimp [b]
      rw [Real.sq_sqrt]
      positivity
    change a - b = sign * pathDifference at hpath
    have hpath_sq := congrArg (fun value : ℝ => value ^ 2) hpath
    rw [mul_pow, hsign, one_mul] at hpath_sq
    have hab :
        2 * a * b = a ^ 2 + b ^ 2 - pathDifference ^ 2 := by
      calc
        2 * a * b = a ^ 2 + b ^ 2 - (a - b) ^ 2 := by ring
        _ = a ^ 2 + b ^ 2 - pathDifference ^ 2 := by rw [hpath_sq]
    have hpoly :
        4 * (a ^ 2 * b ^ 2) =
          (a ^ 2 + b ^ 2 - pathDifference ^ 2) ^ 2 := by
      calc
        4 * (a ^ 2 * b ^ 2) = (2 * a * b) ^ 2 := by ring
        _ = (a ^ 2 + b ^ 2 - pathDifference ^ 2) ^ 2 := by rw [hab]
    rw [ha_sq, hb_sq] at hpoly
    linear_combination -hpoly
  have hAboveSquare :
      4 * (((2 / 5 : ℝ) ^ 2) - (633 / 400000 : ℝ) ^ 2) *
          yAbove ^ 2 =
        (633 / 400000 : ℝ) ^ 2 *
          (4 * (2000 : ℝ) ^ 2 + (2 / 5 : ℝ) ^ 2 -
            (633 / 400000 : ℝ) ^ 2) := by
    refine coordinate_square yAbove 1 2000 (2 / 5) (633 / 400000)
      (by norm_num) ?_
    convert hAbovePath' using 1 <;> norm_num
  have hBelowSquare :
      4 * (((2 / 5 : ℝ) ^ 2) - (633 / 400000 : ℝ) ^ 2) *
          yBelow ^ 2 =
        (633 / 400000 : ℝ) ^ 2 *
          (4 * (2000 : ℝ) ^ 2 + (2 / 5 : ℝ) ^ 2 -
            (633 / 400000 : ℝ) ^ 2) := by
    refine coordinate_square yBelow (-1) 2000 (2 / 5) (633 / 400000)
      (by norm_num) ?_
    convert hBelowPath' using 1 <;> norm_num
  have hden_pos :
      0 < (2 / 5 : ℝ) ^ 2 - (633 / 400000 : ℝ) ^ 2 := by
    norm_num
  have hcoordinates_sq : yAbove ^ 2 = yBelow ^ 2 := by
    nlinarith [hAboveSquare, hBelowSquare]
  have hcoordinates_symm : yBelow = -yAbove := by
    nlinarith [hcoordinates_sq, hAboveSide', hBelowSide']
  let radicand : ℝ :=
    (4 * (2000 : ℝ) ^ 2 + (2 / 5 : ℝ) ^ 2 -
        (633 / 400000 : ℝ) ^ 2) /
      ((2 / 5 : ℝ) ^ 2 - (633 / 400000 : ℝ) ^ 2)
  have hradicand_pos : 0 < radicand := by
    dsimp [radicand]
    positivity
  have hsqrt_sq :
      (Real.sqrt radicand) ^ 2 = radicand :=
    Real.sq_sqrt hradicand_pos.le
  have hseparation_sq :
      (2 * yAbove) ^ 2 =
        ((633 / 400000 : ℝ) * Real.sqrt radicand) ^ 2 := by
    rw [mul_pow, mul_pow, hsqrt_sq]
    dsimp [radicand]
    norm_num at hAboveSquare ⊢
    linarith [hAboveSquare]
  have hseparation_nonneg : 0 ≤ 2 * yAbove := by
    positivity
  have hformula_pos :
      0 < (633 / 400000 : ℝ) * Real.sqrt radicand := by
    exact mul_pos (by norm_num) (Real.sqrt_pos.2 hradicand_pos)
  have hseparation :
      2 * yAbove =
        (633 / 400000 : ℝ) * Real.sqrt radicand := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hseparation_sq with h | h
    · exact h
    · nlinarith only [h, hseparation_nonneg, hformula_pos]
  unfold darkFringeSeparationInMillimeters
  change |yAbove - yBelow| =
    finiteScreenSymmetricSeparation 2000 (2 / 5) (633 / 400000)
  rw [hcoordinates_symm, abs_of_nonneg]
  · simpa [finiteScreenSymmetricSeparation, radicand, two_mul] using hseparation
  · nlinarith [hAboveSide']

/-!
The exact separation rounds to `15.8 mm`, uniquely selecting the recorded
answer A.

This formalizes `thm:physics:phyx_mini_0248:target`.  Neither the exact
separation, its rounded value, nor answer A is assumed by any apparatus,
readout, figure, positivity, or governing-law premise.
-/
theorem problem_phyx_mini_0248
    (setup : DoubleSlitInterferenceSetup)
    (h_scenario : MatchesScenarioAndFigure setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesExactTwoPointSourceLaws setup) :
    darkFringeSeparationInMillimeters setup 2 =
        finiteScreenSymmetricSeparation 2000 (2 / 5) (633 / 400000) ∧
      IsUniqueMatchingDisplayedDistance setup recordedDatasetAnswer := by
  have h_exact :=
    orderTwoDarkFringeSeparation_exactFiniteScreen setup h_readouts
      h_physical h_laws
  let radicand : ℝ :=
    (4 * (2000 : ℝ) ^ 2 + (2 / 5 : ℝ) ^ 2 -
        (633 / 400000 : ℝ) ^ 2) /
      ((2 / 5 : ℝ) ^ 2 - (633 / 400000 : ℝ) ^ 2)
  have hradicand_pos : 0 < radicand := by
    dsimp [radicand]
    positivity
  have hvalue_nonneg :
      0 ≤ finiteScreenSymmetricSeparation 2000 (2 / 5) (633 / 400000) := by
    unfold finiteScreenSymmetricSeparation
    positivity
  have hvalue_sq :
      (finiteScreenSymmetricSeparation 2000 (2 / 5) (633 / 400000)) ^ 2 =
        (633 / 400000 : ℝ) ^ 2 * radicand := by
    unfold finiteScreenSymmetricSeparation
    rw [mul_pow, Real.sq_sqrt hradicand_pos.le]
  have hlower_sq :
      (63 / 4 : ℝ) ^ 2 ≤
        (finiteScreenSymmetricSeparation 2000 (2 / 5) (633 / 400000)) ^ 2 := by
    rw [hvalue_sq]
    dsimp [radicand]
    norm_num
  have hupper_sq :
      (finiteScreenSymmetricSeparation 2000 (2 / 5) (633 / 400000)) ^ 2 <
        (317 / 20 : ℝ) ^ 2 := by
    rw [hvalue_sq]
    dsimp [radicand]
    norm_num
  have hlower :
      (63 / 4 : ℝ) ≤
        finiteScreenSymmetricSeparation 2000 (2 / 5) (633 / 400000) := by
    nlinarith only [hvalue_nonneg, hlower_sq]
  have hupper :
      finiteScreenSymmetricSeparation 2000 (2 / 5) (633 / 400000) <
        (317 / 20 : ℝ) := by
    nlinarith only [hvalue_nonneg, hupper_sq]
  have hround :
      round
          (10 *
            finiteScreenSymmetricSeparation 2000 (2 / 5) (633 / 400000)) =
        158 := by
    apply round_eq_iff.mpr
    constructor
    · norm_num
      linarith only [hlower]
    · norm_num
      linarith only [hupper]
  constructor
  · exact h_exact
  · unfold IsUniqueMatchingDisplayedDistance recordedDatasetAnswer
    constructor
    · unfold MatchesDisplayedDistance roundedToNearestTenthMillimeter
      rw [h_exact, hround]
      norm_num [displayedDistanceInMillimeters]
    · intro other hother
      unfold MatchesDisplayedDistance roundedToNearestTenthMillimeter at hother
      rw [h_exact, hround] at hother
      cases other with
      | A => rfl
      | B => norm_num [displayedDistanceInMillimeters] at hother
      | C => norm_num [displayedDistanceInMillimeters] at hother
      | D => norm_num [displayedDistanceInMillimeters] at hother

end PhyXMiniProblems.ProblemPhyXMini0248
