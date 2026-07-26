import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/-!
# Effective focal length of a two-lens zoom system

This file formalizes `phyx_mini_0112`. A parallel paraxial ray bundle first
crosses a converging thin lens and then a diverging thin lens. The lenses have
signed focal lengths `f₁` and `f₂`, are separated by the adjustable distance
`d`, and together have effective focal length `f`.

All radii, positions, focal lengths, and distances are dimensionful Physlib
quantities. Scalar equations are stated for readouts in arbitrary length units
when they express governing laws, and in centimeters for the supplied data and
the requested multiple-choice result.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0112

open CarriesDimension Dimension

/-! ## Dimensionful quantities and figure roles -/

/-- A real-valued physical length, allowing signed optical distances. -/
abbrev OpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices obtained from SI by replacing only the length unit. -/
def unitChoicesForLength (unit : LengthUnit) : UnitChoices :=
  { UnitChoices.SI with length := unit }

/-- Scalar readout of a dimensionful optical length in the chosen length unit. -/
def lengthReadout (unit : LengthUnit) (length : OpticalLength) : ℝ :=
  (length (unitChoicesForLength unit)).val

/-- The two lenses in propagation order. -/
inductive LensLabel where
  | first
  | second
  deriving DecidableEq, Repr

/-- Qualitative sign role of a thin lens. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- Ray-bundle profile before entering the first lens. -/
inductive RayBundleProfile where
  | parallelToPrincipalAxis
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- Optical approximation under which the ray-transfer laws are asserted. -/
inductive OpticalApproximation where
  | thinParaxial
  | exactRayTracing
  deriving DecidableEq, Repr

/-- Named points on the optical axis in the supplied figure. -/
inductive AxisPoint where
  /-- The point labelled `Q`, from which the effective focal length is drawn. -/
  | q
  | firstLensCenter
  | secondLensCenter
  /-- The final image point labelled `I'`. -/
  | finalImageIPrime
  deriving DecidableEq, Repr

/-- The center label belonging to each lens in the figure. -/
def lensCenterPoint : LensLabel → AxisPoint
  | .first => .firstLensCenter
  | .second => .secondLensCenter

/-- A thin lens carrying its qualitative kind and signed focal length. -/
structure ThinLens where
  kind : ThinLensKind
  signedFocalLength : OpticalLength

/--
Physical quantities and labels in the zoom-lens diagram.

`incomingRayRadius` is the displayed `r₀`, `radiusAtSecondLens` is `r'₀`,
`secondLensImageDistance` is `s'₂`, and `effectiveFocalLength` is `f`.
-/
structure ZoomLensDiagram where
  lens : LensLabel → ThinLens
  axisPosition : AxisPoint → OpticalLength
  incomingRayRadius : OpticalLength
  radiusAtSecondLens : OpticalLength
  secondLensImageDistance : OpticalLength
  effectiveFocalLength : OpticalLength
  incomingBundleProfile : RayBundleProfile
  approximation : OpticalApproximation

/-- Signed focal-length readout for one lens. -/
def focalLengthReadout
    (diagram : ZoomLensDiagram) (unit : LengthUnit) (lens : LensLabel) : ℝ :=
  lengthReadout unit (diagram.lens lens).signedFocalLength

/-- Signed coordinate readout of a labelled point on the optical axis. -/
def axisPositionReadout
    (diagram : ZoomLensDiagram) (unit : LengthUnit) (point : AxisPoint) : ℝ :=
  lengthReadout unit (diagram.axisPosition point)

/-- Signed axial separation from `start` to `finish`. -/
def axialSeparationReadout
    (diagram : ZoomLensDiagram) (unit : LengthUnit)
    (start finish : AxisPoint) : ℝ :=
  axisPositionReadout diagram unit finish - axisPositionReadout diagram unit start

/-- The adjustable lens separation `d`. -/
def lensSeparationReadout (diagram : ZoomLensDiagram) (unit : LengthUnit) : ℝ :=
  axialSeparationReadout diagram unit .firstLensCenter .secondLensCenter

/-- Readout of the displayed ray radius `r₀`. -/
def incomingRayRadiusReadout (diagram : ZoomLensDiagram) (unit : LengthUnit) : ℝ :=
  lengthReadout unit diagram.incomingRayRadius

/-- Readout of the displayed ray radius `r'₀` at the second lens. -/
def radiusAtSecondLensReadout
    (diagram : ZoomLensDiagram) (unit : LengthUnit) : ℝ :=
  lengthReadout unit diagram.radiusAtSecondLens

/-- Readout of the second-lens image distance `s'₂`. -/
def secondLensImageDistanceReadout
    (diagram : ZoomLensDiagram) (unit : LengthUnit) : ℝ :=
  lengthReadout unit diagram.secondLensImageDistance

/-- Readout of the effective focal length `f` of the two-lens combination. -/
def effectiveFocalLengthReadout
    (diagram : ZoomLensDiagram) (unit : LengthUnit) : ℝ :=
  lengthReadout unit diagram.effectiveFocalLength

/-! ## Figure, data, and physical assumptions -/

/--
Qualitative labels and distance annotations read from the supplied figure.
The predicate identifies `s'₂` and `f` with their drawn axial spans but gives
no numerical value for the requested separation.
-/
structure MatchesZoomLensFigure (diagram : ZoomLensDiagram) : Prop where
  first_lens_is_converging : (diagram.lens .first).kind = .converging
  second_lens_is_diverging : (diagram.lens .second).kind = .diverging
  incident_bundle_is_parallel :
    diagram.incomingBundleProfile = .parallelToPrincipalAxis
  second_lens_image_distance_label :
    ∀ unit : LengthUnit,
      secondLensImageDistanceReadout diagram unit =
        axialSeparationReadout diagram unit .secondLensCenter .finalImageIPrime
  effective_focal_length_label :
    ∀ unit : LengthUnit,
      effectiveFocalLengthReadout diagram unit =
        axialSeparationReadout diagram unit .q .finalImageIPrime

/--
Numerical problem data in centimeters. The desired effective focal length is
an input condition of the question; the separation itself is constrained only
to the stated adjustable interval.
-/
structure MatchesZoomLensProblemData (diagram : ZoomLensDiagram) : Prop where
  first_focal_length_cm :
    focalLengthReadout diagram LengthUnit.centimeters .first = 12
  second_focal_length_cm :
    focalLengthReadout diagram LengthUnit.centimeters .second = -18
  separation_nonnegative :
    0 ≤ lensSeparationReadout diagram LengthUnit.centimeters
  separation_at_most_four_cm :
    lensSeparationReadout diagram LengthUnit.centimeters ≤ 4
  requested_effective_focal_length_cm :
    effectiveFocalLengthReadout diagram LengthUnit.centimeters = 30

/--
Sign, ordering, and nondegeneracy conditions for the physical branch shown in
the diagram. The final inequality is the source condition
`|f₂| > f₁ - d`.
-/
structure HasPhysicalZoomLensConfiguration (diagram : ZoomLensDiagram) : Prop where
  first_focal_length_positive :
    0 < focalLengthReadout diagram LengthUnit.centimeters .first
  second_focal_length_negative :
    focalLengthReadout diagram LengthUnit.centimeters .second < 0
  incoming_radius_positive :
    0 < incomingRayRadiusReadout diagram LengthUnit.centimeters
  second_lens_radius_positive :
    0 < radiusAtSecondLensReadout diagram LengthUnit.centimeters
  second_lens_image_distance_positive :
    0 < secondLensImageDistanceReadout diagram LengthUnit.centimeters
  effective_focal_length_positive :
    0 < effectiveFocalLengthReadout diagram LengthUnit.centimeters
  q_precedes_first_lens :
    axisPositionReadout diagram LengthUnit.centimeters .q <
      axisPositionReadout diagram LengthUnit.centimeters .firstLensCenter
  first_lens_precedes_second :
    axisPositionReadout diagram LengthUnit.centimeters .firstLensCenter <
      axisPositionReadout diagram LengthUnit.centimeters .secondLensCenter
  second_lens_precedes_image :
    axisPositionReadout diagram LengthUnit.centimeters .secondLensCenter <
      axisPositionReadout diagram LengthUnit.centimeters .finalImageIPrime
  separation_less_than_first_focal_length :
    lensSeparationReadout diagram LengthUnit.centimeters <
      focalLengthReadout diagram LengthUnit.centimeters .first
  diverging_focal_magnitude_condition :
    |focalLengthReadout diagram LengthUnit.centimeters .second| >
      focalLengthReadout diagram LengthUnit.centimeters .first -
        lensSeparationReadout diagram LengthUnit.centimeters

/-! ## Governing paraxial laws -/

/--
Paraxial ray-transfer and thin-lens laws for the separated lens pair.

For every length unit, the first equation transports the ray height from `r₀`
to `r'₀`; the second adds the angular deflections of the two thin lenses; the
third is the signed Gaussian equation for the diverging lens, whose virtual
object distance is `d - f₁`. All equations are division-free and homogeneous
in physical dimension.
-/
structure SatisfiesParaxialZoomLensLaws (diagram : ZoomLensDiagram) : Prop where
  uses_thin_paraxial_approximation : diagram.approximation = .thinParaxial
  ray_height_transport :
    ∀ unit : LengthUnit,
      radiusAtSecondLensReadout diagram unit *
          focalLengthReadout diagram unit .first =
        incomingRayRadiusReadout diagram unit *
          (focalLengthReadout diagram unit .first -
            lensSeparationReadout diagram unit)
  combined_thin_lens_refraction :
    ∀ unit : LengthUnit,
      incomingRayRadiusReadout diagram unit *
          focalLengthReadout diagram unit .first *
          focalLengthReadout diagram unit .second =
        effectiveFocalLengthReadout diagram unit *
          (incomingRayRadiusReadout diagram unit *
              focalLengthReadout diagram unit .second +
            radiusAtSecondLensReadout diagram unit *
              focalLengthReadout diagram unit .first)
  diverging_lens_gaussian_equation :
    ∀ unit : LengthUnit,
      focalLengthReadout diagram unit .second *
          ((lensSeparationReadout diagram unit -
                focalLengthReadout diagram unit .first) +
            secondLensImageDistanceReadout diagram unit) =
        (lensSeparationReadout diagram unit -
            focalLengthReadout diagram unit .first) *
          secondLensImageDistanceReadout diagram unit

/-! ## Derived relation and multiple-choice target -/

/--
The ray-height and refraction laws imply the standard effective-focal-length
relation for two separated thin lenses,
`f (f₁ + f₂ - d) = f₁ f₂`.
-/
lemma separated_lens_effective_focal_relation
    (diagram : ZoomLensDiagram)
    (_physical : HasPhysicalZoomLensConfiguration diagram)
    (_laws : SatisfiesParaxialZoomLensLaws diagram) :
    ∀ unit : LengthUnit,
      effectiveFocalLengthReadout diagram unit *
          (focalLengthReadout diagram unit .first +
            focalLengthReadout diagram unit .second -
            lensSeparationReadout diagram unit) =
        focalLengthReadout diagram unit .first *
          focalLengthReadout diagram unit .second := by
  intro unit
  have htransport := _laws.ray_height_transport unit
  have hrefraction := _laws.combined_thin_lens_refraction unit
  have hscale : incomingRayRadiusReadout diagram LengthUnit.centimeters =
      (UnitChoices.dimScale (unitChoicesForLength unit)
        (unitChoicesForLength LengthUnit.centimeters) L𝓭 : ℝ) *
        incomingRayRadiusReadout diagram unit := by
    simpa [incomingRayRadiusReadout, lengthReadout, NNReal.smul_def] using
      congrArg WithDim.val
        (diagram.incomingRayRadius.2
          (unitChoicesForLength unit)
          (unitChoicesForLength LengthUnit.centimeters))
  have hincoming_ne : incomingRayRadiusReadout diagram unit ≠ 0 := by
    intro hz
    have hcm_zero :
        incomingRayRadiusReadout diagram LengthUnit.centimeters = 0 := by
      rw [hscale, hz, mul_zero]
    exact (ne_of_gt _physical.incoming_radius_positive) hcm_zero
  apply mul_left_cancel₀ hincoming_ne
  calc
    incomingRayRadiusReadout diagram unit *
        (effectiveFocalLengthReadout diagram unit *
          (focalLengthReadout diagram unit .first +
            focalLengthReadout diagram unit .second -
            lensSeparationReadout diagram unit)) =
        effectiveFocalLengthReadout diagram unit *
          (incomingRayRadiusReadout diagram unit *
              focalLengthReadout diagram unit .second +
            incomingRayRadiusReadout diagram unit *
              (focalLengthReadout diagram unit .first -
                lensSeparationReadout diagram unit)) := by ring
    _ = effectiveFocalLengthReadout diagram unit *
          (incomingRayRadiusReadout diagram unit *
              focalLengthReadout diagram unit .second +
            radiusAtSecondLensReadout diagram unit *
              focalLengthReadout diagram unit .first) := by rw [htransport]
    _ = incomingRayRadiusReadout diagram unit *
          focalLengthReadout diagram unit .first *
            focalLengthReadout diagram unit .second := hrefraction.symm
    _ = incomingRayRadiusReadout diagram unit *
          (focalLengthReadout diagram unit .first *
            focalLengthReadout diagram unit .second) := by ring

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Separation in centimeters printed beside each answer choice. -/
def AnswerChoice.separationInCentimeters : AnswerChoice → ℝ
  | .A => 6 / 5
  | .B => 12 / 5
  | .C => 18 / 5
  | .D => 9 / 10

/-- Dataset metadata: the recorded answer label, not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .A

/-- Exact agreement between the modeled lens separation and an answer choice. -/
def MatchesAnswer (diagram : ZoomLensDiagram) (choice : AnswerChoice) : Prop :=
  lensSeparationReadout diagram LengthUnit.centimeters =
    choice.separationInCentimeters

/--
For `f₁ = 12 cm`, `f₂ = -18 cm`, and effective focal length `f = 30 cm`,
the separated-thin-lens law determines `d = 6/5 cm = 1.2 cm`, answer A.

This formalizes `thm:physics:phyx_mini_0112:target`.
-/
theorem problem_phyx_mini_0112
    (diagram : ZoomLensDiagram)
    (_figure : MatchesZoomLensFigure diagram)
    (_data : MatchesZoomLensProblemData diagram)
    (_physical : HasPhysicalZoomLensConfiguration diagram)
    (_laws : SatisfiesParaxialZoomLensLaws diagram) :
    lensSeparationReadout diagram LengthUnit.centimeters = 6 / 5 ∧
      MatchesAnswer diagram .A := by
  have hrelation :=
    separated_lens_effective_focal_relation diagram _physical _laws
      LengthUnit.centimeters
  rw [_data.requested_effective_focal_length_cm,
    _data.first_focal_length_cm, _data.second_focal_length_cm] at hrelation
  have hseparation :
      lensSeparationReadout diagram LengthUnit.centimeters = 6 / 5 := by
    norm_num at hrelation ⊢
    linarith
  exact ⟨hseparation, by
    simpa [MatchesAnswer, AnswerChoice.separationInCentimeters] using hseparation⟩

end PhyXMiniProblems.ProblemPhyXMini0112
