import Mathlib
import Physlib.Units.WithDim.Basic

/-!
# Relative image size for two separated converging lenses

The primary figure places a candle `36 cm` to the left of a converging lens
with focal length `f₁ = 13 cm`.  A second converging lens, with focal length
`f₂ = 16 cm`, is `56 cm` to the right of the first lens.

All focal lengths, axial distances, and transverse height magnitudes below are
Physlib dimensionful lengths.  Real numbers are used only for readouts in
centimeters and for the final dimensionless height ratio.  The intermediate
image made by the first lens is the real object for the second lens.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0144

open Dimension

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Unit choices in which physical lengths are read in centimeters. -/
def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The nonnegative real-valued centimeter readout of a physical length. -/
def centimetersValue (length : LengthMagnitude) : ℝ :=
  ((length centimeterUnitChoices).val : ℝ)

/-- The two lenses, in the left-to-right order shown in the figure. -/
inductive LensLabel where
  | first
  | second
  deriving DecidableEq, Repr

/-- Qualitative optical kind of a thin lens. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- A labeled thin lens with a physical focal-length magnitude. -/
structure ThinLens where
  label : LensLabel
  kind : ThinLensKind
  focalLength : LengthMagnitude

/-!
The dimensionful data for the two-stage image formation.

`firstImageFromFirstLens` and `firstImageToSecondLens` are the two positive
segments into which the intermediate real image divides the lens separation.
The three height fields are magnitudes, since the question asks for relative
size rather than signed orientation.
-/
structure TwoLensCandleSetup where
  lens : LensLabel → ThinLens
  candleToFirstLens : LengthMagnitude
  lensSeparation : LengthMagnitude
  firstImageFromFirstLens : LengthMagnitude
  firstImageToSecondLens : LengthMagnitude
  finalImageFromSecondLens : LengthMagnitude
  candleHeight : LengthMagnitude
  intermediateImageHeight : LengthMagnitude
  finalImageHeight : LengthMagnitude

/-- The real-object distance used at either imaging stage. -/
def stageObjectDistance
    (setup : TwoLensCandleSetup) : LensLabel → LengthMagnitude
  | .first => setup.candleToFirstLens
  | .second => setup.firstImageToSecondLens

/-- The real-image distance used at either imaging stage. -/
def stageImageDistance
    (setup : TwoLensCandleSetup) : LensLabel → LengthMagnitude
  | .first => setup.firstImageFromFirstLens
  | .second => setup.finalImageFromSecondLens

/-- The transverse object-height magnitude used at either imaging stage. -/
def stageObjectHeight
    (setup : TwoLensCandleSetup) : LensLabel → LengthMagnitude
  | .first => setup.candleHeight
  | .second => setup.intermediateImageHeight

/-- The transverse image-height magnitude produced at either imaging stage. -/
def stageImageHeight
    (setup : TwoLensCandleSetup) : LensLabel → LengthMagnitude
  | .first => setup.intermediateImageHeight
  | .second => setup.finalImageHeight

/-- Both convex lenses in the primary figure are labeled as converging lenses. -/
def HasDepictedLensArrangement (setup : TwoLensCandleSetup) : Prop :=
  (setup.lens .first).label = .first ∧
    (setup.lens .second).label = .second ∧
    (setup.lens .first).kind = .converging ∧
    (setup.lens .second).kind = .converging

/-!
Numerical readouts printed in the primary figure: the candle is `36 cm` from
the first lens, the lenses are `56 cm` apart, and their focal lengths are
`13 cm` and `16 cm`.  No image distance or image-size answer is assumed here.
-/
def HasStatedFigureReadouts (setup : TwoLensCandleSetup) : Prop :=
  centimetersValue setup.candleToFirstLens = 36 ∧
    centimetersValue setup.lensSeparation = 56 ∧
    centimetersValue (setup.lens .first).focalLength = 13 ∧
    centimetersValue (setup.lens .second).focalLength = 16

/-!
Sequential-image geometry: the first real image lies between the lenses and
therefore its distance from lens 1 plus its distance from lens 2 is the stated
lens separation.  This relation does not prescribe either segment numerically.
-/
def HasSequentialImageGeometry (setup : TwoLensCandleSetup) : Prop :=
  centimetersValue setup.firstImageFromFirstLens +
      centimetersValue setup.firstImageToSecondLens =
    centimetersValue setup.lensSeparation

/-!
Nondegeneracy and real-image conditions.  At each stage the positive real
object distance exceeds the positive focal length, and the image and height
magnitudes are nonzero.
-/
def HasPhysicalRealImageConfiguration (setup : TwoLensCandleSetup) : Prop :=
  (∀ lens,
      0 < centimetersValue (setup.lens lens).focalLength ∧
        centimetersValue (setup.lens lens).focalLength <
          centimetersValue (stageObjectDistance setup lens) ∧
        0 < centimetersValue (stageImageDistance setup lens)) ∧
    0 < centimetersValue setup.candleHeight ∧
    0 < centimetersValue setup.intermediateImageHeight ∧
    0 < centimetersValue setup.finalImageHeight

/-!
The Gaussian thin-lens equation at either lens.  The division-free form
`f (p + q) = p q` is dimensionally homogeneous and is equivalent to
`1/f = 1/p + 1/q` for the positive distances required above.
-/
def SatisfiesThinLensEquationAt
    (setup : TwoLensCandleSetup) (lens : LensLabel) : Prop :=
  let f := centimetersValue (setup.lens lens).focalLength
  let p := centimetersValue (stageObjectDistance setup lens)
  let q := centimetersValue (stageImageDistance setup lens)
  f * (p + q) = p * q

/-!
The magnitude form of the transverse-magnification law at either stage:
`hᵢ / hₒ = q / p`.  It is written without division so it also preserves the
physical dimensions of height times distance.
-/
def SatisfiesTransverseSizeLawAt
    (setup : TwoLensCandleSetup) (lens : LensLabel) : Prop :=
  centimetersValue (stageImageHeight setup lens) *
      centimetersValue (stageObjectDistance setup lens) =
    centimetersValue (stageObjectHeight setup lens) *
      centimetersValue (stageImageDistance setup lens)

/-- The dimensionless magnitude of the final image height relative to the candle. -/
def finalRelativeSize (setup : TwoLensCandleSetup) : ℝ :=
  centimetersValue setup.finalImageHeight /
    centimetersValue setup.candleHeight

/-- Labels of the four answer choices displayed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The dimensionless relative size printed beside each answer choice. -/
def displayedRelativeSize : AnswerChoice → ℝ
  | .A => 56 / 100
  | .B => 36 / 100
  | .C => 46 / 100
  | .D => 40 / 100

/-- Dataset metadata only: the source records answer choice C. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with a displayed relative size rounded to the nearest hundredth. -/
def MatchesDisplayedRelativeSize
    (setup : TwoLensCandleSetup) (choice : AnswerChoice) : Prop :=
  |finalRelativeSize setup - displayedRelativeSize choice| ≤ 1 / 200

/-- A choice is correct when its displayed value is nearest to the physical ratio. -/
def IsNearestDisplayedChoice
    (setup : TwoLensCandleSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |finalRelativeSize setup - displayedRelativeSize choice| ≤
      |finalRelativeSize setup - displayedRelativeSize other|

/-!
The figure readouts, intermediate-image geometry, and two thin-lens equations
determine the successive real-image distances.
-/
lemma stageDistancesInCentimeters_eq
    (setup : TwoLensCandleSetup)
    (h_readouts : HasStatedFigureReadouts setup)
    (h_geometry : HasSequentialImageGeometry setup)
    (h_physical : HasPhysicalRealImageConfiguration setup)
    (h_lens : ∀ lens, SatisfiesThinLensEquationAt setup lens) :
    centimetersValue setup.firstImageFromFirstLens = 468 / 23 ∧
      centimetersValue setup.firstImageToSecondLens = 820 / 23 ∧
      centimetersValue setup.finalImageFromSecondLens = 3280 / 113 := by
  rcases h_readouts with ⟨hp1, hs, hf1, hf2⟩
  have hgeom := h_geometry
  have hl1 := h_lens .first
  have hl2 := h_lens .second
  simp only [HasSequentialImageGeometry] at hgeom
  simp only [SatisfiesThinLensEquationAt, stageObjectDistance,
    stageImageDistance] at hl1 hl2
  have hq1 : centimetersValue setup.firstImageFromFirstLens = 468 / 23 := by
    nlinarith [hl1]
  have hp2 : centimetersValue setup.firstImageToSecondLens = 820 / 23 := by
    nlinarith [hgeom, hq1]
  have hq2 :
      centimetersValue setup.finalImageFromSecondLens = 3280 / 113 := by
    nlinarith [hl2, hp2]
  constructor
  · exact hq1
  constructor
  · exact hp2
  · exact hq2

/-!
The magnitude laws give stage height ratios `13/23` and `92/113`.
Their product is the final-to-candle height ratio.
-/
lemma stageRelativeSizes_eq
    (setup : TwoLensCandleSetup)
    (h_readouts : HasStatedFigureReadouts setup)
    (h_geometry : HasSequentialImageGeometry setup)
    (h_physical : HasPhysicalRealImageConfiguration setup)
    (h_lens : ∀ lens, SatisfiesThinLensEquationAt setup lens)
    (h_size : ∀ lens, SatisfiesTransverseSizeLawAt setup lens) :
    centimetersValue setup.intermediateImageHeight /
          centimetersValue setup.candleHeight = 13 / 23 ∧
      centimetersValue setup.finalImageHeight /
          centimetersValue setup.intermediateImageHeight = 92 / 113 := by
  obtain ⟨hq1, hp2, hq2⟩ :=
    stageDistancesInCentimeters_eq setup h_readouts h_geometry h_physical h_lens
  rcases h_readouts with ⟨hp1, hs, hf1, hf2⟩
  rcases h_physical with ⟨hphys, hcandle, hintermediate, hfinal⟩
  have hsize1 := h_size .first
  have hsize2 := h_size .second
  simp only [SatisfiesTransverseSizeLawAt, stageImageHeight,
    stageObjectDistance, stageObjectHeight, stageImageDistance] at hsize1 hsize2
  rw [hp1, hq1] at hsize1
  rw [hp2, hq2] at hsize2
  constructor
  · apply (div_eq_iff (ne_of_gt hcandle)).2
    nlinarith [hsize1]
  · apply (div_eq_iff (ne_of_gt hintermediate)).2
    nlinarith [hsize2]

/-!
The exact relative size is `1196/2599 ≈ 0.46018`.  Thus the final image is
`0.46 ×` the candle's size to the precision displayed in the choices, and C
is the nearest displayed answer.

This formalizes blueprint label `thm:physics:phyx_mini_0144:target`.
-/
theorem problem_phyx_mini_0144
    (setup : TwoLensCandleSetup)
    (h_arrangement : HasDepictedLensArrangement setup)
    (h_readouts : HasStatedFigureReadouts setup)
    (h_geometry : HasSequentialImageGeometry setup)
    (h_physical : HasPhysicalRealImageConfiguration setup)
    (h_lens : ∀ lens, SatisfiesThinLensEquationAt setup lens)
    (h_size : ∀ lens, SatisfiesTransverseSizeLawAt setup lens) :
    finalRelativeSize setup = 1196 / 2599 ∧
      MatchesDisplayedRelativeSize setup .C ∧
      IsNearestDisplayedChoice setup .C := by
  obtain ⟨hratio1, hratio2⟩ :=
    stageRelativeSizes_eq setup h_readouts h_geometry h_physical h_lens h_size
  rcases h_physical with ⟨hphys, hcandle, hintermediate, hfinal⟩
  have hintermediate_eq :=
    (div_eq_iff (ne_of_gt hcandle)).mp hratio1
  have hfinal_eq :=
    (div_eq_iff (ne_of_gt hintermediate)).mp hratio2
  have hratio : finalRelativeSize setup = 1196 / 2599 := by
    unfold finalRelativeSize
    apply (div_eq_iff (ne_of_gt hcandle)).2
    nlinarith [hintermediate_eq, hfinal_eq]
  constructor
  · exact hratio
  constructor
  · unfold MatchesDisplayedRelativeSize
    rw [hratio]
    norm_num [displayedRelativeSize]
  · unfold IsNearestDisplayedChoice
    intro other
    rw [hratio]
    cases other <;> norm_num [displayedRelativeSize]

end PhyXMiniProblems.ProblemPhyXMini0144
