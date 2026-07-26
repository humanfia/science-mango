import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0134

open Dimension

/-!
# Final magnification of two converging lenses

The primary figure places converging lens A and converging lens B on a common
principal axis.  The original object `O` is left of A; A forms the intermediate
real image `I_A`, which is the object `O_B` for B; B then forms `I_B` to its
right.  Focal lengths, axial positions, and object/image distances are genuine
dimensionful Physlib quantities.  Their scalar readouts are used only after a
length unit has been chosen.  Transverse magnifications are dimensionless.

The source metadata records choice C, `-0.50`.  With the displayed data and
the standard signed thin-lens and magnification laws, however, the two stage
magnifications are `-1/2` and `-1`, whose product is `+1/2`.  The target below
states this physically supported result; the incompatible recorded answer is
retained only as source metadata.
-/

/-! ## Dimensionful quantities and figure labels -/

/-- A signed physical optical length, independent of the unit used to read it. -/
abbrev OpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices obtained from SI by replacing only the length unit. -/
def unitChoicesForLength (unit : LengthUnit) : UnitChoices :=
  { UnitChoices.SI with length := unit }

/-- Scalar readout of a physical optical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : OpticalLength) : ℝ :=
  (length (unitChoicesForLength unit)).val

/-- The two lenses in the order traversed by the light. -/
inductive LensLabel where
  | A
  | B
  deriving DecidableEq, Repr

/-- Qualitative focal-length sign role of a thin lens. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- Optical approximation used by the ray diagram. -/
inductive OpticalApproximation where
  | thinParaxial
  | exactRayTracing
  deriving DecidableEq, Repr

/-- Labeled points on the principal axis in the primary figure. -/
inductive AxisPoint where
  | objectO
  | focalPrimeA
  | lensACenter
  | focalA
  | imageIA
  | objectOB
  | focalPrimeB
  | lensBCenter
  | focalB
  | finalImageIB
  deriving DecidableEq, Repr

/-- Object and image arrows whose transverse orientations are shown. -/
inductive ArrowLabel where
  | objectO
  | imageIA
  | finalImageIB
  deriving DecidableEq, Repr

/-- Transverse orientation relative to the upright source arrow. -/
inductive ImageOrientation where
  | upright
  | inverted
  deriving DecidableEq, Repr

/-- Whether the outgoing rays themselves meet at the image point. -/
inductive ImageNature where
  | real
  | virtual
  deriving DecidableEq, Repr

/-- Principal-ray labels printed in the lower diagram. -/
inductive RayLabel where
  | ray1
  | ray2
  | ray3
  | ray4
  | ray1Prime
  | ray2Prime
  | ray3Prime
  deriving DecidableEq, Repr

/-- Qualitative construction rule represented by a principal ray. -/
inductive PrincipalRayRole where
  | parallelThenThroughFarFocus
  | throughOpticalCenter
  | throughNearFocusThenParallel
  | alongPrincipalAxis
  deriving DecidableEq, Repr

/-- A thin lens carrying its physical kind and signed focal length. -/
structure ThinLens where
  kind : ThinLensKind
  signedFocalLength : OpticalLength

/--
Physical quantities and labels of the two-lens construction.

`signedImageDistance` uses the Cartesian convention: it is positive for the
two real images drawn to the right of their respective lenses.  The stage and
net transverse magnifications retain their signs and are dimensionless.
-/
structure TwoLensDiagram where
  lens : LensLabel → ThinLens
  axisPosition : AxisPoint → OpticalLength
  objectDistance : LensLabel → OpticalLength
  signedImageDistance : LensLabel → OpticalLength
  stageMagnification : LensLabel → ℝ
  netTransverseMagnification : ℝ
  imageNature : LensLabel → ImageNature
  arrowOrientation : ArrowLabel → ImageOrientation
  rayRole : RayLabel → PrincipalRayRole
  approximation : OpticalApproximation

/-- Focal-length readout for one lens. -/
def focalLengthReadout
    (diagram : TwoLensDiagram) (unit : LengthUnit) (lens : LensLabel) : ℝ :=
  lengthReadout unit (diagram.lens lens).signedFocalLength

/-- Object-distance readout for one lens. -/
def objectDistanceReadout
    (diagram : TwoLensDiagram) (unit : LengthUnit) (lens : LensLabel) : ℝ :=
  lengthReadout unit (diagram.objectDistance lens)

/-- Signed image-distance readout for one lens. -/
def imageDistanceReadout
    (diagram : TwoLensDiagram) (unit : LengthUnit) (lens : LensLabel) : ℝ :=
  lengthReadout unit (diagram.signedImageDistance lens)

/-- Coordinate readout of a labeled point on the principal axis. -/
def axisPositionReadout
    (diagram : TwoLensDiagram) (unit : LengthUnit) (point : AxisPoint) : ℝ :=
  lengthReadout unit (diagram.axisPosition point)

/-- Directed axial separation from `start` to `finish`. -/
def axialSeparationReadout
    (diagram : TwoLensDiagram) (unit : LengthUnit)
    (start finish : AxisPoint) : ℝ :=
  axisPositionReadout diagram unit finish - axisPositionReadout diagram unit start

/-- Separation from lens A to lens B. -/
def lensSeparationReadout (diagram : TwoLensDiagram) (unit : LengthUnit) : ℝ :=
  axialSeparationReadout diagram unit .lensACenter .lensBCenter

/-! ## Problem data, figure readouts, and physical branch -/

/--
Numerical data stated in the problem: `f_A = 20 cm`, `f_B = 25 cm`, lens
separation `80 cm`, and original object distance `d_oA = 60 cm`.
-/
structure MatchesProblemData (diagram : TwoLensDiagram) : Prop where
  focal_length_A_cm :
    focalLengthReadout diagram LengthUnit.centimeters .A = 20
  focal_length_B_cm :
    focalLengthReadout diagram LengthUnit.centimeters .B = 25
  lens_separation_cm :
    lensSeparationReadout diagram LengthUnit.centimeters = 80
  object_distance_A_cm :
    objectDistanceReadout diagram LengthUnit.centimeters .A = 60

/--
Literal qualitative labels and axial identifications read from the figure.
No numerical image distance or magnification is asserted here.
-/
structure MatchesTwoLensFigure (diagram : TwoLensDiagram) : Prop where
  lens_A_is_converging : (diagram.lens .A).kind = .converging
  lens_B_is_converging : (diagram.lens .B).kind = .converging
  intermediate_image_is_real : diagram.imageNature .A = .real
  final_image_is_real : diagram.imageNature .B = .real
  source_arrow_is_upright : diagram.arrowOrientation .objectO = .upright
  intermediate_arrow_is_inverted : diagram.arrowOrientation .imageIA = .inverted
  final_arrow_is_upright : diagram.arrowOrientation .finalImageIB = .upright
  image_A_is_object_B :
    ∀ unit : LengthUnit,
      axisPositionReadout diagram unit .imageIA =
        axisPositionReadout diagram unit .objectOB
  object_distance_labels :
    ∀ unit : LengthUnit,
      objectDistanceReadout diagram unit .A =
          axialSeparationReadout diagram unit .objectO .lensACenter ∧
        objectDistanceReadout diagram unit .B =
          axialSeparationReadout diagram unit .objectOB .lensBCenter
  image_distance_labels :
    ∀ unit : LengthUnit,
      imageDistanceReadout diagram unit .A =
          axialSeparationReadout diagram unit .lensACenter .imageIA ∧
        imageDistanceReadout diagram unit .B =
          axialSeparationReadout diagram unit .lensBCenter .finalImageIB
  focal_point_labels :
    ∀ unit : LengthUnit,
      focalLengthReadout diagram unit .A =
          axialSeparationReadout diagram unit .focalPrimeA .lensACenter ∧
        focalLengthReadout diagram unit .A =
          axialSeparationReadout diagram unit .lensACenter .focalA ∧
        focalLengthReadout diagram unit .B =
          axialSeparationReadout diagram unit .focalPrimeB .lensBCenter ∧
        focalLengthReadout diagram unit .B =
          axialSeparationReadout diagram unit .lensBCenter .focalB
  ray_1_role : diagram.rayRole .ray1 = .parallelThenThroughFarFocus
  ray_2_role : diagram.rayRole .ray2 = .throughOpticalCenter
  ray_3_role : diagram.rayRole .ray3 = .throughNearFocusThenParallel
  ray_4_role : diagram.rayRole .ray4 = .alongPrincipalAxis
  ray_1_prime_role : diagram.rayRole .ray1Prime = .parallelThenThroughFarFocus
  ray_2_prime_role : diagram.rayRole .ray2Prime = .throughOpticalCenter
  ray_3_prime_role : diagram.rayRole .ray3Prime = .throughNearFocusThenParallel

/-- Positivity and left-to-right ordering for the physical branch shown. -/
structure HasPhysicalTwoLensConfiguration (diagram : TwoLensDiagram) : Prop where
  focal_lengths_positive :
    ∀ lens : LensLabel,
      0 < focalLengthReadout diagram LengthUnit.centimeters lens
  object_distances_positive :
    ∀ lens : LensLabel,
      0 < objectDistanceReadout diagram LengthUnit.centimeters lens
  real_image_distances_positive :
    ∀ lens : LensLabel,
      0 < imageDistanceReadout diagram LengthUnit.centimeters lens
  object_before_focal_prime_A :
    axisPositionReadout diagram LengthUnit.centimeters .objectO <
      axisPositionReadout diagram LengthUnit.centimeters .focalPrimeA
  focal_prime_A_before_lens_A :
    axisPositionReadout diagram LengthUnit.centimeters .focalPrimeA <
      axisPositionReadout diagram LengthUnit.centimeters .lensACenter
  lens_A_before_focal_A :
    axisPositionReadout diagram LengthUnit.centimeters .lensACenter <
      axisPositionReadout diagram LengthUnit.centimeters .focalA
  focal_A_before_image_A :
    axisPositionReadout diagram LengthUnit.centimeters .focalA <
      axisPositionReadout diagram LengthUnit.centimeters .imageIA
  object_B_before_focal_prime_B :
    axisPositionReadout diagram LengthUnit.centimeters .objectOB <
      axisPositionReadout diagram LengthUnit.centimeters .focalPrimeB
  focal_prime_B_before_lens_B :
    axisPositionReadout diagram LengthUnit.centimeters .focalPrimeB <
      axisPositionReadout diagram LengthUnit.centimeters .lensBCenter
  lens_B_before_focal_B :
    axisPositionReadout diagram LengthUnit.centimeters .lensBCenter <
      axisPositionReadout diagram LengthUnit.centimeters .focalB
  focal_B_before_final_image :
    axisPositionReadout diagram LengthUnit.centimeters .focalB <
      axisPositionReadout diagram LengthUnit.centimeters .finalImageIB

/-! ## Governing paraxial laws -/

/--
Standard thin-lens, signed transverse-magnification, and composition laws.

The Gaussian equation is written without division as `f (d_o + d_i) =
d_o d_i`.  The stage law is `m d_o = -d_i`, and the net magnification is the
product of the two stage magnifications.  All dimensionful factors in an
equation are read in the same arbitrary length unit.
-/
structure SatisfiesTwoLensParaxialLaws (diagram : TwoLensDiagram) : Prop where
  uses_thin_paraxial_approximation : diagram.approximation = .thinParaxial
  gaussian_thin_lens_equation :
    ∀ (unit : LengthUnit) (lens : LensLabel),
      focalLengthReadout diagram unit lens *
          (objectDistanceReadout diagram unit lens +
            imageDistanceReadout diagram unit lens) =
        objectDistanceReadout diagram unit lens *
          imageDistanceReadout diagram unit lens
  signed_stage_magnification :
    ∀ (unit : LengthUnit) (lens : LensLabel),
      diagram.stageMagnification lens *
          objectDistanceReadout diagram unit lens =
        -imageDistanceReadout diagram unit lens
  net_magnification_composition :
    diagram.netTransverseMagnification =
      diagram.stageMagnification .A * diagram.stageMagnification .B

/-! ## Derived values, source metadata, and physical target -/

/--
The two imaging stages determine the unprinted intermediate quantities:
`d_iA = 30 cm`, `d_oB = 50 cm`, `d_iB = 50 cm`, `m_A = -1/2`, and `m_B = -1`.
-/
lemma derived_stage_distances_and_magnifications
    (diagram : TwoLensDiagram)
    (h_data : MatchesProblemData diagram)
    (h_figure : MatchesTwoLensFigure diagram)
    (h_physical : HasPhysicalTwoLensConfiguration diagram)
    (h_laws : SatisfiesTwoLensParaxialLaws diagram) :
    imageDistanceReadout diagram LengthUnit.centimeters .A = 30 ∧
      objectDistanceReadout diagram LengthUnit.centimeters .B = 50 ∧
      imageDistanceReadout diagram LengthUnit.centimeters .B = 50 ∧
      diagram.stageMagnification .A = (-1 : ℝ) / 2 ∧
      diagram.stageMagnification .B = -1 := by
  have h_diA_equation :=
    h_laws.gaussian_thin_lens_equation LengthUnit.centimeters LensLabel.A
  rw [h_data.focal_length_A_cm, h_data.object_distance_A_cm] at h_diA_equation
  have h_diA :
      imageDistanceReadout diagram LengthUnit.centimeters .A = 30 := by
    nlinarith [h_diA_equation]

  have h_lens_separation := h_data.lens_separation_cm
  have h_image_A_label :=
    (h_figure.image_distance_labels LengthUnit.centimeters).1
  have h_object_B_label :=
    (h_figure.object_distance_labels LengthUnit.centimeters).2
  have h_image_A_is_object_B :=
    h_figure.image_A_is_object_B LengthUnit.centimeters
  simp only [lensSeparationReadout, axialSeparationReadout] at h_lens_separation
  simp only [axialSeparationReadout] at h_image_A_label h_object_B_label
  have h_doB :
      objectDistanceReadout diagram LengthUnit.centimeters .B = 50 := by
    nlinarith [h_lens_separation, h_image_A_label, h_object_B_label,
      h_image_A_is_object_B, h_diA]

  have h_diB_equation :=
    h_laws.gaussian_thin_lens_equation LengthUnit.centimeters LensLabel.B
  rw [h_data.focal_length_B_cm, h_doB] at h_diB_equation
  have h_diB :
      imageDistanceReadout diagram LengthUnit.centimeters .B = 50 := by
    nlinarith [h_diB_equation]

  have h_mA_equation :=
    h_laws.signed_stage_magnification LengthUnit.centimeters LensLabel.A
  rw [h_data.object_distance_A_cm, h_diA] at h_mA_equation
  have h_mA : diagram.stageMagnification .A = (-1 : ℝ) / 2 := by
    nlinarith [h_mA_equation]

  have h_mB_equation :=
    h_laws.signed_stage_magnification LengthUnit.centimeters LensLabel.B
  rw [h_doB, h_diB] at h_mB_equation
  have h_mB : diagram.stageMagnification .B = -1 := by
    nlinarith [h_mB_equation]

  exact ⟨h_diA, h_doB, h_diB, h_mA, h_mB⟩

/-- Labels of the four displayed answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Signed dimensionless magnification printed beside each answer. -/
def AnswerChoice.magnificationReadout : AnswerChoice → ℝ
  | .A => (-3 : ℝ) / 10
  | .B => (-2 : ℝ) / 5
  | .C => (-1 : ℝ) / 2
  | .D => (-3 : ℝ) / 5

/-- Dataset metadata only: the source records choice C. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Exact agreement between the physical net magnification and a displayed choice. -/
def MatchesDisplayedAnswer
    (diagram : TwoLensDiagram) (choice : AnswerChoice) : Prop :=
  diagram.netTransverseMagnification = choice.magnificationReadout

/--
The physically supported net magnification is `+0.50`: lens A contributes
`-1/2` and lens B contributes `-1`, so two inversions give an upright final
image with magnification `+1/2`.  The dataset's recorded choice C remains
available above as metadata, but does not occur in this target or any premise.

This formalizes `thm:physics:phyx_mini_0134:target`.
-/
theorem problem_phyx_mini_0134
    (diagram : TwoLensDiagram)
    (h_data : MatchesProblemData diagram)
    (h_figure : MatchesTwoLensFigure diagram)
    (h_physical : HasPhysicalTwoLensConfiguration diagram)
    (h_laws : SatisfiesTwoLensParaxialLaws diagram) :
    diagram.netTransverseMagnification = (1 : ℝ) / 2 := by
  obtain ⟨_, _, _, h_mA, h_mB⟩ :=
    derived_stage_distances_and_magnifications
      diagram h_data h_figure h_physical h_laws
  rw [h_laws.net_magnification_composition, h_mA, h_mB]
  norm_num

end PhyXMiniProblems.ProblemPhyXMini0134
