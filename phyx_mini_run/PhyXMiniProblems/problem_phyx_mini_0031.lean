import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0031

open Dimension

/-!
# Object position for a two-converging-lens system

Lens 1 and lens 2 lie on a common optical axis, with lens 2 to the right of
lens 1.  The figure labels the positive object distance to the left of lens 1
by `p`, the lens separation by `d`, and the position of the requested final
image relative to lens 1 by `x`.  Since `x < d`, that final image is a virtual
image for lens 2 and has a negative signed image distance from lens 2.

All optical distances below are physical, dimension-carrying quantities.
Signed centimeter readouts are used only to state the one-dimensional lens
equations and the numerical information printed in the problem.
-/

/-- A signed physical length, independent of the unit chosen to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The scalar centimeter readout of a signed physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length { UnitChoices.SI with length := LengthUnit.centimeters }).val

/-- A thin lens, represented by its dimensionful focal length. -/
structure ThinLens where
  focalLength : LengthQuantity

/--
The physical quantities in the two-lens ray construction.

`objectDistance` is the figure label `p`. `lensSeparation` is `d`, while
`finalImagePositionFromFirst` is `x`. The remaining three signed lengths are
the quantities needed to apply the thin-lens equation successively: the first
lens's intermediate image distance, and the object and image distances for
the second lens.
-/
structure TwoLensSetup where
  firstLens : ThinLens
  secondLens : ThinLens
  objectDistance : LengthQuantity
  lensSeparation : LengthQuantity
  finalImagePositionFromFirst : LengthQuantity
  intermediateImageDistanceFromFirst : LengthQuantity
  secondLensObjectDistance : LengthQuantity
  secondLensSignedImageDistance : LengthQuantity

/--
The numerical readouts supplied by the problem: `f₁ = 10 cm`, `f₂ = 20 cm`,
`d = 50 cm`, and `x = 31 cm` measured rightward from lens 1.
-/
def HasStatedReadouts (setup : TwoLensSetup) : Prop :=
  lengthInCentimeters setup.firstLens.focalLength = 10 ∧
    lengthInCentimeters setup.secondLens.focalLength = 20 ∧
    lengthInCentimeters setup.lensSeparation = 50 ∧
    lengthInCentimeters setup.finalImagePositionFromFirst = 31

/--
The placement and sign branch depicted in the figure: both focal lengths are
positive, the object is a positive distance to the left of lens 1, the final
image lies strictly between the lenses, and the intermediate real image lies
between the lenses and acts as a real object for lens 2.
-/
def HasPhysicalAxialPlacement (setup : TwoLensSetup) : Prop :=
  0 < lengthInCentimeters setup.firstLens.focalLength ∧
    0 < lengthInCentimeters setup.secondLens.focalLength ∧
    0 < lengthInCentimeters setup.objectDistance ∧
    0 < lengthInCentimeters setup.finalImagePositionFromFirst ∧
    lengthInCentimeters setup.finalImagePositionFromFirst <
      lengthInCentimeters setup.lensSeparation ∧
    0 < lengthInCentimeters setup.intermediateImageDistanceFromFirst ∧
    lengthInCentimeters setup.intermediateImageDistanceFromFirst <
      lengthInCentimeters setup.lensSeparation ∧
    0 < lengthInCentimeters setup.secondLensObjectDistance

/--
Axial geometry relating the distances used at lens 2 to positions measured
from lens 1. In particular, the image distance for lens 2 is signed and equals
`x - d`, hence is negative for the pictured placement `x < d`.
-/
def SatisfiesTwoLensAxialGeometry (setup : TwoLensSetup) : Prop :=
  lengthInCentimeters setup.secondLensObjectDistance =
      lengthInCentimeters setup.lensSeparation -
        lengthInCentimeters setup.intermediateImageDistanceFromFirst ∧
    lengthInCentimeters setup.secondLensSignedImageDistance =
      lengthInCentimeters setup.finalImagePositionFromFirst -
        lengthInCentimeters setup.lensSeparation

/--
The signed thin-lens equation `1/f = 1/p + 1/q`, evaluated using a common
centimeter unit. A virtual image is represented by a negative `q` readout.
-/
def SatisfiesThinLensEquation
    (lens : ThinLens)
    (objectDistance signedImageDistance : LengthQuantity) : Prop :=
  1 / lengthInCentimeters lens.focalLength =
    1 / lengthInCentimeters objectDistance +
      1 / lengthInCentimeters signedImageDistance

/-- The governing thin-lens law applied successively to both lenses. -/
def SatisfiesBothThinLensEquations (setup : TwoLensSetup) : Prop :=
  SatisfiesThinLensEquation setup.firstLens setup.objectDistance
      setup.intermediateImageDistanceFromFirst ∧
    SatisfiesThinLensEquation setup.secondLens setup.secondLensObjectDistance
      setup.secondLensSignedImageDistance

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The positive centimeter readout displayed beside each answer choice. -/
def answerDistanceInCentimeters : AnswerChoice → ℝ
  | .A => 106 / 10
  | .B => 128 / 10
  | .C => 115 / 10
  | .D => 133 / 10

/-- Agreement with a displayed distance rounded to the nearest tenth centimeter. -/
def MatchesAnswerToNearestTenth
    (distance : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInCentimeters distance - answerDistanceInCentimeters choice| ≤ 1 / 20

/--
The second lens sees a real object at `380/39 cm` and forms the requested
virtual image at signed distance `-19 cm`; consequently the intermediate image
of lens 1 is at `1570/39 cm` from lens 1.
-/
lemma derived_intermediate_and_second_lens_distances
    (setup : TwoLensSetup)
    (h_readouts : HasStatedReadouts setup)
    (h_placement : HasPhysicalAxialPlacement setup)
    (h_geometry : SatisfiesTwoLensAxialGeometry setup)
    (h_lenses : SatisfiesBothThinLensEquations setup) :
    lengthInCentimeters setup.secondLensSignedImageDistance = -19 ∧
      lengthInCentimeters setup.secondLensObjectDistance = 380 / 39 ∧
      lengthInCentimeters setup.intermediateImageDistanceFromFirst = 1570 / 39 := by
  rcases h_readouts with ⟨hf1, hf2, hd, hx⟩
  rcases h_placement with
    ⟨hf1pos, hf2pos, hppos, hxpos, hxd, hq1pos, hq1d, hp2pos⟩
  rcases h_geometry with ⟨hp2geom, hq2geom⟩
  rcases h_lenses with ⟨hlens1, hlens2⟩
  unfold SatisfiesThinLensEquation at hlens1 hlens2
  have hq2 :
      lengthInCentimeters setup.secondLensSignedImageDistance = -19 := by
    linarith
  have hp2ne :
      lengthInCentimeters setup.secondLensObjectDistance ≠ 0 :=
    ne_of_gt hp2pos
  rw [hf2, hq2] at hlens2
  field_simp [hp2ne] at hlens2
  have hp2 :
      lengthInCentimeters setup.secondLensObjectDistance = 380 / 39 := by
    norm_num at hlens2 ⊢
    linarith
  refine ⟨hq2, hp2, ?_⟩
  norm_num at hp2 ⊢
  linarith

/--
The two thin-lens equations determine the figure label `p` exactly as
`785/59 cm`, approximately `13.305 cm`.
-/
lemma object_distance_exact
    (setup : TwoLensSetup)
    (h_readouts : HasStatedReadouts setup)
    (h_placement : HasPhysicalAxialPlacement setup)
    (h_geometry : SatisfiesTwoLensAxialGeometry setup)
    (h_lenses : SatisfiesBothThinLensEquations setup) :
    lengthInCentimeters setup.objectDistance = 785 / 59 := by
  obtain ⟨hq2, hp2, hq1⟩ :=
    derived_intermediate_and_second_lens_distances
      setup h_readouts h_placement h_geometry h_lenses
  rcases h_readouts with ⟨hf1, hf2, hd, hx⟩
  rcases h_placement with
    ⟨hf1pos, hf2pos, hppos, hxpos, hxd, hq1pos, hq1d, hp2pos⟩
  rcases h_lenses with ⟨hlens1, hlens2⟩
  unfold SatisfiesThinLensEquation at hlens1
  rw [hf1, hq1] at hlens1
  field_simp [ne_of_gt hppos] at hlens1
  norm_num at hlens1 ⊢
  nlinarith

/--
The object must be positioned at the exact positive distance `785/59 cm` to
the left of lens 1. This rounds to `+13.3 cm`, answer choice D.

This formalizes `thm:physics:phyx_mini_0031:target`.
-/
theorem problem_phyx_mini_0031
    (setup : TwoLensSetup)
    (h_readouts : HasStatedReadouts setup)
    (h_placement : HasPhysicalAxialPlacement setup)
    (h_geometry : SatisfiesTwoLensAxialGeometry setup)
    (h_lenses : SatisfiesBothThinLensEquations setup) :
    lengthInCentimeters setup.objectDistance = 785 / 59 ∧
      MatchesAnswerToNearestTenth setup.objectDistance .D := by
  have hp :=
    object_distance_exact setup h_readouts h_placement h_geometry h_lenses
  refine ⟨hp, ?_⟩
  unfold MatchesAnswerToNearestTenth answerDistanceInCentimeters
  rw [hp]
  norm_num [abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0031
