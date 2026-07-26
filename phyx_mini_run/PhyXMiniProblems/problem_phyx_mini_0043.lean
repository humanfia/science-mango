import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0043

open Dimension

/-!
# Magnification of two converging lenses

The optical axis is directed from the upright object `O` through lens `A` and
then lens `B`. The first real image `I` is the real object for lens `B`, whose
final real image is `I'`. The source figure labels the near and far focal points
of the two lenses by `F₁`, `F₂`, `F₁'`, and `F₂'`.

All axial coordinates, focal lengths, distances, and height magnitudes are
Physlib dimensionful lengths. Real numbers occur only as centimeter readouts
and as signed, dimensionless transverse magnifications.
-/

/-- A signed physical length, used for coordinates on the optical axis. -/
abbrev SignedLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical length, used for distances and height magnitudes. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- The scalar centimeter readout of a signed physical length. -/
def signedLengthInCentimeters (length : SignedLength) : ℝ :=
  (length { UnitChoices.SI with length := LengthUnit.centimeters }).val

/-- The scalar centimeter readout of a nonnegative physical length. -/
def lengthMagnitudeInCentimeters (length : LengthMagnitude) : ℝ :=
  ((length { UnitChoices.SI with length := LengthUnit.centimeters }).val : ℝ)

/-- The labels of the two lenses, in propagation order. -/
inductive LensLabel where
  | A
  | B
  deriving DecidableEq, Repr

/-- The optical kind stated for each lens. -/
inductive LensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- The three object/image arrows in the ray diagram. -/
inductive ImagePointLabel where
  | O
  | I
  | IPrime
  deriving DecidableEq, Repr

/-- The nine labeled axial points, ordered from left to right in the figure. -/
inductive FigurePointLabel where
  | O
  | F1
  | lensACenter
  | F2
  | I
  | F1Prime
  | lensBCenter
  | F2Prime
  | IPrime
  deriving DecidableEq, Repr

/-- The six principal rays, with primed labels reserved for lens `B`. -/
inductive PrincipalRayLabel where
  | ray1
  | ray2
  | ray3
  | ray1Prime
  | ray2Prime
  | ray3Prime
  deriving DecidableEq, Repr

/-- The three standard paraxial constructions shown at each converging lens. -/
inductive PrincipalRayRole where
  | parallelThenThroughFarFocus
  | undeviatedThroughCenter
  | throughNearFocusThenParallel
  deriving DecidableEq, Repr

/-- Orientation of a transverse arrow relative to the principal axis. -/
inductive ImageOrientation where
  | upright
  | inverted
  deriving DecidableEq, Repr

/-- The lens traversed by a labeled principal ray. -/
def PrincipalRayLabel.lens : PrincipalRayLabel → LensLabel
  | .ray1 | .ray2 | .ray3 => .A
  | .ray1Prime | .ray2Prime | .ray3Prime => .B

/-- The optical construction represented by each numbered ray. -/
def PrincipalRayLabel.role : PrincipalRayLabel → PrincipalRayRole
  | .ray1 | .ray1Prime => .parallelThenThroughFarFocus
  | .ray2 | .ray2Prime => .undeviatedThroughCenter
  | .ray3 | .ray3Prime => .throughNearFocusThenParallel

/-- The object point for each of the two imaging stages. -/
def stageObject : LensLabel → ImagePointLabel
  | .A => .O
  | .B => .I

/-- The image point for each of the two imaging stages. -/
def stageImage : LensLabel → ImagePointLabel
  | .A => .I
  | .B => .IPrime

/-- The axial point carrying each object/image-arrow label. -/
def ImagePointLabel.figurePoint : ImagePointLabel → FigurePointLabel
  | .O => .O
  | .I => .I
  | .IPrime => .IPrime

/-- The center point labeled for each lens. -/
def lensCenterPoint : LensLabel → FigurePointLabel
  | .A => .lensACenter
  | .B => .lensBCenter

/-- The incident-side focal point labeled for each lens. -/
def nearFocalPoint : LensLabel → FigurePointLabel
  | .A => .F1
  | .B => .F1Prime

/-- The outgoing-side focal point labeled for each lens. -/
def farFocalPoint : LensLabel → FigurePointLabel
  | .A => .F2
  | .B => .F2Prime

/-- A thin lens with its figure label, optical kind, and focal-length magnitude. -/
structure ThinLens where
  label : LensLabel
  kind : LensKind
  focalLength : LengthMagnitude

/-
Dimensionful data and dimensionless magnifications for the two-stage ray trace.
The ray-origin and ray-intersection fields retain the convergence information
drawn in the figure without attempting to model a full geometric-optics ray API.
-/
structure TwoConvergingLensSetup where
  lens : LensLabel → ThinLens
  lensSeparation : LengthMagnitude
  axisPosition : FigurePointLabel → SignedLength
  objectDistance : LensLabel → LengthMagnitude
  imageDistance : LensLabel → LengthMagnitude
  heightMagnitude : ImagePointLabel → LengthMagnitude
  orientation : ImagePointLabel → ImageOrientation
  transverseMagnification : LensLabel → ℝ
  rayOrigin : PrincipalRayLabel → ImagePointLabel
  rayIntersection : PrincipalRayLabel → ImagePointLabel

/-- Convert an orientation and a height magnitude to a signed height readout. -/
def signedHeightInCentimeters
    (setup : TwoConvergingLensSetup) (point : ImagePointLabel) : ℝ :=
  match setup.orientation point with
  | .upright => lengthMagnitudeInCentimeters (setup.heightMagnitude point)
  | .inverted => -lengthMagnitudeInCentimeters (setup.heightMagnitude point)

/-
The explicitly stated numerical data: two converging lenses with focal lengths
`8 cm` and `6 cm`, separated by `36 cm`, and an upright `8 cm` object `12 cm`
to the incident side of lens `A`.
-/
def MatchesSourceReadouts (setup : TwoConvergingLensSetup) : Prop :=
  (setup.lens .A).label = .A ∧
    (setup.lens .B).label = .B ∧
    (setup.lens .A).kind = .converging ∧
    (setup.lens .B).kind = .converging ∧
    lengthMagnitudeInCentimeters (setup.lens .A).focalLength = 8 ∧
    lengthMagnitudeInCentimeters (setup.lens .B).focalLength = 6 ∧
    lengthMagnitudeInCentimeters setup.lensSeparation = 36 ∧
    lengthMagnitudeInCentimeters (setup.objectDistance .A) = 12 ∧
    lengthMagnitudeInCentimeters (setup.heightMagnitude .O) = 8 ∧
    setup.orientation .O = .upright

/-
Axial geometry of the labeled figure. Besides the four focal-point relations,
it states that the two stage distances are measured between the corresponding
object, lens center, and image, and records the pictured left-to-right order.
No intermediate or final image distance is assigned a numerical value here.
-/
def MatchesFigureGeometry (setup : TwoConvergingLensSetup) : Prop :=
  let x := fun point => signedLengthInCentimeters (setup.axisPosition point)
  let p := fun lens => lengthMagnitudeInCentimeters (setup.objectDistance lens)
  let q := fun lens => lengthMagnitudeInCentimeters (setup.imageDistance lens)
  let f := fun lens => lengthMagnitudeInCentimeters (setup.lens lens).focalLength
  x .lensACenter - x .O = p .A ∧
    x .I - x .lensACenter = q .A ∧
    x .lensBCenter - x .I = p .B ∧
    x .IPrime - x .lensBCenter = q .B ∧
    x .lensBCenter - x .lensACenter =
      lengthMagnitudeInCentimeters setup.lensSeparation ∧
    x .lensACenter - x .F1 = f .A ∧
    x .F2 - x .lensACenter = f .A ∧
    x .lensBCenter - x .F1Prime = f .B ∧
    x .F2Prime - x .lensBCenter = f .B ∧
    x .O < x .F1 ∧
    x .F1 < x .lensACenter ∧
    x .lensACenter < x .F2 ∧
    x .F2 < x .I ∧
    x .I < x .F1Prime ∧
    x .F1Prime < x .lensBCenter ∧
    x .lensBCenter < x .F2Prime ∧
    x .F2Prime < x .IPrime

/-
The numbered rays from `O` meet at `I`; the primed rays from `I` meet at
`I'`. The arrow orientations are the ones visibly drawn in the source figure.
-/
def MatchesRayDiagram (setup : TwoConvergingLensSetup) : Prop :=
  (∀ ray,
      setup.rayOrigin ray = stageObject ray.lens ∧
        setup.rayIntersection ray = stageImage ray.lens) ∧
    setup.orientation .I = .inverted ∧
    setup.orientation .IPrime = .upright

/-- Nondegeneracy conditions for the real-object, real-image configuration. -/
def HasPhysicalConfiguration (setup : TwoConvergingLensSetup) : Prop :=
  ∀ lens,
    0 < lengthMagnitudeInCentimeters (setup.lens lens).focalLength ∧
      0 < lengthMagnitudeInCentimeters (setup.objectDistance lens) ∧
      0 < lengthMagnitudeInCentimeters (setup.imageDistance lens)

/-
The Gaussian thin-lens equation `1/f = 1/p + 1/q` for a real object and real
image at either converging lens.
-/
def SatisfiesThinLensEquationAt
    (setup : TwoConvergingLensSetup) (lens : LensLabel) : Prop :=
  1 / lengthMagnitudeInCentimeters (setup.lens lens).focalLength =
    1 / lengthMagnitudeInCentimeters (setup.objectDistance lens) +
      1 / lengthMagnitudeInCentimeters (setup.imageDistance lens)

/-
The signed transverse-magnification laws `m = -q/p` and `hᵢ = m hₒ` at
either stage. These are governing laws and do not assign the requested overall
magnification a numerical value.
-/
def SatisfiesTransverseMagnificationAt
    (setup : TwoConvergingLensSetup) (lens : LensLabel) : Prop :=
  setup.transverseMagnification lens =
      -(lengthMagnitudeInCentimeters (setup.imageDistance lens) /
        lengthMagnitudeInCentimeters (setup.objectDistance lens)) ∧
    signedHeightInCentimeters setup (stageImage lens) =
      setup.transverseMagnification lens *
        signedHeightInCentimeters setup (stageObject lens)

/-- Sequential transverse magnifications multiply for the two-lens system. -/
def overallMagnification (setup : TwoConvergingLensSetup) : ℝ :=
  setup.transverseMagnification .A * setup.transverseMagnification .B

/-- The labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The dimensionless magnification printed beside each answer choice. -/
def displayedMagnification : AnswerChoice → ℝ
  | .A => -(107 / 125)
  | .B => -1
  | .C => 199 / 200
  | .D => -(407 / 500)

/-- The answer label recorded by the dataset. -/
def recordedAnswerChoice : AnswerChoice := .B

/-
The source data, axial geometry, and Gaussian laws determine the successive
real image distances `q_A = 24 cm`, `p_B = 12 cm`, and `q_B = 12 cm`.
-/
lemma stageDistancesInCentimeters_eq
    (setup : TwoConvergingLensSetup)
    (h_readouts : MatchesSourceReadouts setup)
    (h_geometry : MatchesFigureGeometry setup)
    (h_physical : HasPhysicalConfiguration setup)
    (h_lens : ∀ lens, SatisfiesThinLensEquationAt setup lens) :
    lengthMagnitudeInCentimeters (setup.imageDistance .A) = 24 ∧
      lengthMagnitudeInCentimeters (setup.objectDistance .B) = 12 ∧
      lengthMagnitudeInCentimeters (setup.imageDistance .B) = 12 := by
  rcases h_readouts with
    ⟨_, _, _, _, hfA, hfB, hseparation, hpA, _, _⟩
  dsimp only [MatchesFigureGeometry] at h_geometry
  rcases h_geometry with
    ⟨_, hqA_geometry, hpB_geometry, _, hseparation_geometry, _⟩
  have hqA_pos :=
    (h_physical .A).2.2
  have hqA_ne :
      lengthMagnitudeInCentimeters (setup.imageDistance .A) ≠ 0 :=
    ne_of_gt hqA_pos
  have hqA_lens := h_lens .A
  dsimp only [SatisfiesThinLensEquationAt] at hqA_lens
  rw [hfA, hpA] at hqA_lens
  field_simp [hqA_ne] at hqA_lens
  have hqA :
      lengthMagnitudeInCentimeters (setup.imageDistance .A) = 24 := by
    nlinarith
  have hpB :
      lengthMagnitudeInCentimeters (setup.objectDistance .B) = 12 := by
    rw [hseparation] at hseparation_geometry
    linarith
  have hqB_pos :=
    (h_physical .B).2.2
  have hqB_ne :
      lengthMagnitudeInCentimeters (setup.imageDistance .B) ≠ 0 :=
    ne_of_gt hqB_pos
  have hqB_lens := h_lens .B
  dsimp only [SatisfiesThinLensEquationAt] at hqB_lens
  rw [hfB, hpB] at hqB_lens
  field_simp [hqB_ne] at hqB_lens
  have hqB :
      lengthMagnitudeInCentimeters (setup.imageDistance .B) = 12 := by
    nlinarith
  exact ⟨hqA, hpB, hqB⟩

/-
The first lens inverts and doubles the image; the second lens has unit-magnitude
inverting magnification. Their two sign reversals give an upright final image.
-/
lemma stageMagnifications_eq
    (setup : TwoConvergingLensSetup)
    (h_readouts : MatchesSourceReadouts setup)
    (h_geometry : MatchesFigureGeometry setup)
    (h_physical : HasPhysicalConfiguration setup)
    (h_lens : ∀ lens, SatisfiesThinLensEquationAt setup lens)
    (h_magnification :
      ∀ lens, SatisfiesTransverseMagnificationAt setup lens) :
    setup.transverseMagnification .A = -2 ∧
      setup.transverseMagnification .B = -1 := by
  obtain ⟨hqA, hpB, hqB⟩ :=
    stageDistancesInCentimeters_eq setup h_readouts h_geometry h_physical h_lens
  rcases h_readouts with
    ⟨_, _, _, _, _, _, _, hpA, _, _⟩
  have hmA := (h_magnification .A).1
  have hmB := (h_magnification .B).1
  rw [hqA, hpA] at hmA
  rw [hqB, hpB] at hmB
  norm_num at hmA hmB
  exact ⟨hmA, hmB⟩

/-
For the stated `8 cm` and `6 cm` converging lenses, the final image has signed
height `+16 cm` and the combination's dimensionless magnification is `+2`.

Blueprint label: `thm:physics:phyx_mini_0043:target`.
-/
theorem problem_phyx_mini_0043
    (setup : TwoConvergingLensSetup)
    (h_readouts : MatchesSourceReadouts setup)
    (h_geometry : MatchesFigureGeometry setup)
    (h_rays : MatchesRayDiagram setup)
    (h_physical : HasPhysicalConfiguration setup)
    (h_lens : ∀ lens, SatisfiesThinLensEquationAt setup lens)
    (h_magnification :
      ∀ lens, SatisfiesTransverseMagnificationAt setup lens) :
    overallMagnification setup = 2 ∧
      signedHeightInCentimeters setup .IPrime = 16 := by
  obtain ⟨hmA, hmB⟩ :=
    stageMagnifications_eq setup h_readouts h_geometry h_physical h_lens
      h_magnification
  rcases h_readouts with
    ⟨_, _, _, _, _, _, _, _, hO_height, hO_orientation⟩
  have hO : signedHeightInCentimeters setup .O = 8 := by
    simp [signedHeightInCentimeters, hO_orientation, hO_height]
  have hheightA := (h_magnification .A).2
  have hheightB := (h_magnification .B).2
  dsimp only [stageImage, stageObject] at hheightA hheightB
  rw [hmA, hO] at hheightA
  rw [hmB, hheightA] at hheightB
  constructor
  · simp [overallMagnification, hmA, hmB]
  · norm_num at hheightB
    exact hheightB

/-
Consequently the dataset's recorded choice `B = -1.00` is the second lens's
stage magnification, not the magnification of the two lenses in combination.
-/
theorem recordedAnswerChoice_ne_overallMagnification
    (setup : TwoConvergingLensSetup)
    (h_readouts : MatchesSourceReadouts setup)
    (h_geometry : MatchesFigureGeometry setup)
    (h_rays : MatchesRayDiagram setup)
    (h_physical : HasPhysicalConfiguration setup)
    (h_lens : ∀ lens, SatisfiesThinLensEquationAt setup lens)
    (h_magnification :
      ∀ lens, SatisfiesTransverseMagnificationAt setup lens) :
    displayedMagnification recordedAnswerChoice ≠
      overallMagnification setup := by
  have hoverall :=
    (problem_phyx_mini_0043 setup h_readouts h_geometry h_rays h_physical h_lens
      h_magnification).1
  rw [hoverall]
  norm_num [displayedMagnification, recordedAnswerChoice]

end PhyXMiniProblems.ProblemPhyXMini0043
