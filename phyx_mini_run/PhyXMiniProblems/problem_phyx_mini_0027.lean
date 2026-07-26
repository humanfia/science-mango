import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0027

open Dimension

/-!
# Image height of an axially extended square under a thin converging lens

The square lies in a plane containing the principal axis. Its far vertical
edge `ab` is 30 cm from the lens, its near vertical edge `dc` is 20 cm from
the lens, and its upper corners `b` and `c` are 10 cm above the axis. Heights
are signed: a negative image height records inversion below the principal
axis.
-/

/-- A signed physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The scalar centimeter readout of a signed physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length { UnitChoices.SI with length := LengthUnit.centimeters }).val

/-- The four object corners labeled in the figure. -/
inductive ObjectCorner where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Repr

/-- The four corresponding image corners labeled with primes in the problem. -/
inductive ImageCorner where
  | aPrime
  | bPrime
  | cPrime
  | dPrime
  deriving DecidableEq, Repr

/-- The correspondence between each object corner and its geometrical image. -/
def correspondingImage : ObjectCorner → ImageCorner
  | .a => .aPrime
  | .b => .bPrime
  | .c => .cPrime
  | .d => .dPrime

/--
The dimensionful quantities in the thin-lens ray diagram.

`objectDistance` and `imageDistance` are positive distances measured away
from the lens on their respective sides. `objectHeight` and `imageHeight`
are signed transverse coordinates measured from the principal axis.
-/
structure ThinLensSquareSetup where
  focalLength : LengthQuantity
  objectDistance : ObjectCorner → LengthQuantity
  objectHeight : ObjectCorner → LengthQuantity
  imageDistance : ImageCorner → LengthQuantity
  imageHeight : ImageCorner → LengthQuantity

/--
The lens is converging and each pictured object point lies beyond its focal
plane, producing a real image on the opposite side of the lens.
-/
def HasPhysicalRealImageConfiguration (setup : ThinLensSquareSetup) : Prop :=
  0 < lengthInCentimeters setup.focalLength ∧
    ∀ corner,
      lengthInCentimeters setup.focalLength <
          lengthInCentimeters (setup.objectDistance corner) ∧
        0 < lengthInCentimeters
          (setup.imageDistance (correspondingImage corner))

/--
Numerical and geometrical readouts supplied by the problem and figure:
`f = 14 cm`, the far edge `ab` is at `30 cm`, the near edge `dc` is at
`20 cm`, and the square extends from the axis to height `10 cm`.
-/
def MatchesFigureReadouts (setup : ThinLensSquareSetup) : Prop :=
  lengthInCentimeters setup.focalLength = 14 ∧
    lengthInCentimeters (setup.objectDistance .a) = 30 ∧
    lengthInCentimeters (setup.objectDistance .b) = 30 ∧
    lengthInCentimeters (setup.objectDistance .c) = 20 ∧
    lengthInCentimeters (setup.objectDistance .d) = 20 ∧
    lengthInCentimeters (setup.objectHeight .a) = 0 ∧
    lengthInCentimeters (setup.objectHeight .b) = 10 ∧
    lengthInCentimeters (setup.objectHeight .c) = 10 ∧
    lengthInCentimeters (setup.objectHeight .d) = 0

/--
The names `q_a` and `q_d` in the statement each denote one image plane:
`a'`, `b'` share `q_a`, while `c'`, `d'` share `q_d`.
-/
def RespectsLabeledImagePlanes (setup : ThinLensSquareSetup) : Prop :=
  setup.imageDistance .aPrime = setup.imageDistance .bPrime ∧
    setup.imageDistance .cPrime = setup.imageDistance .dPrime

/--
The governing thin-lens equation `1/f = 1/p + 1/q`, applied to every corner.
Writing it in one fixed length unit preserves the physical relation.
-/
def SatisfiesThinLensEquation (setup : ThinLensSquareSetup) : Prop :=
  ∀ corner,
    1 / lengthInCentimeters setup.focalLength =
      1 / lengthInCentimeters (setup.objectDistance corner) +
        1 / lengthInCentimeters
          (setup.imageDistance (correspondingImage corner))

/--
The signed transverse-magnification law `h_i / h_o = -q / p`, written in a
division-free form that also applies to the two corners on the axis.
-/
def SatisfiesTransverseMagnification (setup : ThinLensSquareSetup) : Prop :=
  ∀ corner,
    lengthInCentimeters
          (setup.imageHeight (correspondingImage corner)) *
        lengthInCentimeters (setup.objectDistance corner) =
      -(lengthInCentimeters (setup.objectHeight corner) *
        lengthInCentimeters
          (setup.imageDistance (correspondingImage corner)))

/-- The four signed image-height choices printed in centimeters. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The scalar centimeter readout displayed beside each answer choice. -/
def answerHeightInCentimeters : AnswerChoice → ℝ
  | .A => -27.1
  | .B => -19.6
  | .C => -18.5
  | .D => -23.3

/-- Agreement with an answer height displayed to the nearest tenth centimeter. -/
def MatchesAnswerToNearestTenth
    (height : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInCentimeters height - answerHeightInCentimeters choice| ≤ 0.05

/--
The thin-lens equation determines the two named image distances
`q_a = 105/4 cm` and `q_d = 140/3 cm`.
-/
lemma namedImageDistances_eq
    (setup : ThinLensSquareSetup)
    (h_physical : HasPhysicalRealImageConfiguration setup)
    (h_figure : MatchesFigureReadouts setup)
    (h_planes : RespectsLabeledImagePlanes setup)
    (h_lens : SatisfiesThinLensEquation setup) :
    lengthInCentimeters (setup.imageDistance .aPrime) = 105 / 4 ∧
      lengthInCentimeters (setup.imageDistance .bPrime) = 105 / 4 ∧
      lengthInCentimeters (setup.imageDistance .cPrime) = 140 / 3 ∧
      lengthInCentimeters (setup.imageDistance .dPrime) = 140 / 3 := by
  rcases h_figure with
    ⟨hf, hpa, hpb, hpc, hpd, _ha, _hb, _hc, _hd⟩
  have hqa_pos := (h_physical.2 .a).2
  have hqb_pos := (h_physical.2 .b).2
  have hqc_pos := (h_physical.2 .c).2
  have hqd_pos := (h_physical.2 .d).2
  have ha_lens := h_lens .a
  have hb_lens := h_lens .b
  have hc_lens := h_lens .c
  have hd_lens := h_lens .d
  rw [hf, hpa] at ha_lens
  rw [hf, hpb] at hb_lens
  rw [hf, hpc] at hc_lens
  rw [hf, hpd] at hd_lens
  field_simp [ne_of_gt hqa_pos] at ha_lens
  field_simp [ne_of_gt hqb_pos] at hb_lens
  field_simp [ne_of_gt hqc_pos] at hc_lens
  field_simp [ne_of_gt hqd_pos] at hd_lens
  simp [correspondingImage] at hqa_pos hqb_pos hqc_pos hqd_pos ha_lens hb_lens hc_lens hd_lens
  norm_num at ha_lens hb_lens hc_lens hd_lens ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The far upper corner has signed image height `h_b' = -35/4 cm`. -/
lemma imageHeight_bPrime_eq
    (setup : ThinLensSquareSetup)
    (h_physical : HasPhysicalRealImageConfiguration setup)
    (h_figure : MatchesFigureReadouts setup)
    (h_planes : RespectsLabeledImagePlanes setup)
    (h_lens : SatisfiesThinLensEquation setup)
    (h_magnification : SatisfiesTransverseMagnification setup) :
    lengthInCentimeters (setup.imageHeight .bPrime) = -(35 / 4) := by
  have hqb :=
    (namedImageDistances_eq setup h_physical h_figure h_planes h_lens).2.1
  rcases h_figure with
    ⟨_hf, _hpa, hpb, _hpc, _hpd, _ha, hhb, _hc, _hd⟩
  have hb_magnification := h_magnification .b
  simp [correspondingImage] at hb_magnification
  rw [hpb, hhb, hqb] at hb_magnification
  norm_num at hb_magnification ⊢
  linarith

/--
For the near upper corner, the governing laws give the exact signed height
`h_c' = -70/3 cm`.
-/
lemma imageHeight_cPrime_eq
    (setup : ThinLensSquareSetup)
    (h_physical : HasPhysicalRealImageConfiguration setup)
    (h_figure : MatchesFigureReadouts setup)
    (h_planes : RespectsLabeledImagePlanes setup)
    (h_lens : SatisfiesThinLensEquation setup)
    (h_magnification : SatisfiesTransverseMagnification setup) :
    lengthInCentimeters (setup.imageHeight .cPrime) = -(70 / 3) := by
  have hqc :=
    (namedImageDistances_eq setup h_physical h_figure h_planes h_lens).2.2.1
  rcases h_figure with
    ⟨_hf, _hpa, _hpb, hpc, _hpd, _ha, _hb, hhc, _hd⟩
  have hc_magnification := h_magnification .c
  simp [correspondingImage] at hc_magnification
  rw [hpc, hhc, hqc] at hc_magnification
  norm_num at hc_magnification ⊢
  linarith

/--
The image corner `c'` is at the exact signed height `-70/3 cm`, which rounds
to `-23.3 cm`, answer choice D.

This formalizes `thm:physics:phyx_mini_0027:target`.
-/
theorem problem_phyx_mini_0027
    (setup : ThinLensSquareSetup)
    (h_physical : HasPhysicalRealImageConfiguration setup)
    (h_figure : MatchesFigureReadouts setup)
    (h_planes : RespectsLabeledImagePlanes setup)
    (h_lens : SatisfiesThinLensEquation setup)
    (h_magnification : SatisfiesTransverseMagnification setup) :
    lengthInCentimeters (setup.imageHeight .cPrime) = -(70 / 3) ∧
      MatchesAnswerToNearestTenth (setup.imageHeight .cPrime) .D := by
  have hc := imageHeight_cPrime_eq setup h_physical h_figure h_planes h_lens
    h_magnification
  constructor
  · exact hc
  · unfold MatchesAnswerToNearestTenth answerHeightInCentimeters
    rw [hc]
    norm_num [abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0027
