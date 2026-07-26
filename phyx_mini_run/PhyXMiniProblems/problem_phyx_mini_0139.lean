import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0139

open Dimension

/-!
# Magnification of an external convex rearview mirror

The spherical mirror's radius of curvature, focal length, object distance,
and image distance are represented as genuine dimensionful signed lengths.
Their numerical data are read in SI metres.  Transverse magnification and the
multiple-choice values are dimensionless real numbers.

The source photograph shows an external car mirror reflecting a truck and a
roadside scene.  It contains no optical-axis markings or numerical labels, so
the photograph's scene elements are recorded separately from the two numerical
problem-statement readouts.
-/

/-- A signed optical length whose scalar readout varies coherently with units. -/
abbrev OpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The signed scalar readout of an optical length in SI metres. -/
def lengthInMeters (length : OpticalLength) : ℝ :=
  (length UnitChoices.SI).val

/-- The two spherical-mirror kinds, viewed from the incident-light side. -/
inductive SphericalMirrorKind where
  | concave
  | convex
  deriving DecidableEq, Repr

/-- The use made of the mirror in the physical scenario. -/
inductive MirrorRole where
  | externalRearview
  deriving DecidableEq, Repr

/-- Distinct physical elements recognizable in the supplied photograph. -/
inductive FigureElement where
  | mirrorFrame
  | hostCarBody
  | approachingTruck
  | highway
  | trees
  | sky
  deriving DecidableEq, Repr

/-!
The physical mirror configuration.

`radiusOfCurvatureMagnitude` and `objectDistance` are positive magnitudes.
`signedFocalLength` and `signedImageDistance` use the Cartesian convention in
which a convex mirror has negative focal length and its virtual image lies
behind the mirror at negative image distance.  No value is assigned here to
the requested `transverseMagnification`.
-/
structure ConvexRearviewMirrorSetup where
  mirrorKind : SphericalMirrorKind
  mirrorRole : MirrorRole
  imagedObject : FigureElement
  radiusOfCurvatureMagnitude : OpticalLength
  signedFocalLength : OpticalLength
  objectDistance : OpticalLength
  signedImageDistance : OpticalLength
  transverseMagnification : ℝ
  directlyVisibleInFigure : FigureElement → Prop
  visibleInReflectedView : FigureElement → Prop
  figureHasText : Prop

/-!
The numerical and categorical data stated in the problem: an external convex
rearview mirror of curvature-radius magnitude `16.0 m`, imaging the truck at
an object distance of `10.0 m`.

Neither the signed image distance nor the magnification is fixed here.
-/
structure MatchesProblemStatement (setup : ConvexRearviewMirrorSetup) : Prop where
  mirror_is_convex : setup.mirrorKind = .convex
  mirror_is_external_rearview : setup.mirrorRole = .externalRearview
  imaged_object_is_truck : setup.imagedObject = .approachingTruck
  radius_readout_meters :
    lengthInMeters setup.radiusOfCurvatureMagnitude = 16
  object_distance_readout_meters : lengthInMeters setup.objectDistance = 10

/-!
Qualitative readouts from the primary photograph.  The truck, highway, trees,
and sky occur in the mirror's reflected view; the mirror frame and host car
body are directly visible.  The image contains no text or metric annotations.
-/
structure MatchesPrimaryFigure (setup : ConvexRearviewMirrorSetup) : Prop where
  mirror_frame_directly_visible : setup.directlyVisibleInFigure .mirrorFrame
  host_car_directly_visible : setup.directlyVisibleInFigure .hostCarBody
  truck_visible_in_mirror : setup.visibleInReflectedView .approachingTruck
  highway_visible_in_mirror : setup.visibleInReflectedView .highway
  trees_visible_in_mirror : setup.visibleInReflectedView .trees
  sky_visible_in_mirror : setup.visibleInReflectedView .sky
  no_text_in_figure : ¬setup.figureHasText

/-!
Physical signs for the chosen Cartesian mirror convention.  These are
qualitative branch conditions, not numerical values of the requested
magnification or of the derived image distance.
-/
structure UsesCartesianConvexMirrorConvention
    (setup : ConvexRearviewMirrorSetup) : Prop where
  radius_magnitude_positive :
    0 < lengthInMeters setup.radiusOfCurvatureMagnitude
  object_distance_positive : 0 < lengthInMeters setup.objectDistance
  convex_focal_length_negative : lengthInMeters setup.signedFocalLength < 0

/-!
For a paraxial convex spherical mirror, the signed focal length is minus half
the positive radius-of-curvature magnitude.  Requiring the equality in every
unit system makes it independent of the metre readout used for the data.
-/
def SatisfiesConvexMirrorFocalLaw
    (setup : ConvexRearviewMirrorSetup) : Prop :=
  ∀ units : UnitChoices,
    (setup.radiusOfCurvatureMagnitude units).val =
      -2 * (setup.signedFocalLength units).val

/-!
The signed Gaussian spherical-mirror equation `1/f = 1/dₒ + 1/dᵢ`, written in
the division-free, dimensionally homogeneous form
`f * (dₒ + dᵢ) = dₒ * dᵢ` in every unit system.
-/
def SatisfiesGaussianMirrorEquation
    (setup : ConvexRearviewMirrorSetup) : Prop :=
  ∀ units : UnitChoices,
    setup.signedFocalLength units *
        (setup.objectDistance units + setup.signedImageDistance units) =
      setup.objectDistance units * setup.signedImageDistance units

/-!
The signed transverse-magnification law `m = -dᵢ/dₒ`, written without
division.  The two distances are dimensionful while `m` is dimensionless.
-/
def SatisfiesTransverseMagnificationLaw
    (setup : ConvexRearviewMirrorSetup) : Prop :=
  ∀ units : UnitChoices,
    setup.transverseMagnification * (setup.objectDistance units).val =
      -(setup.signedImageDistance units).val

/-- Labels of the four multiple-choice answers in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The dimensionless decimal magnification printed beside each choice. -/
def AnswerChoice.magnificationReadout : AnswerChoice → ℝ
  | .A => 24 / 100
  | .B => 34 / 100
  | .C => 44 / 100
  | .D => 54 / 100

/-!
`reported` is a nearest-hundredth readout of `exact`: it is an integer number
of hundredths and differs from the exact value by at most half a hundredth.
-/
def IsNearestHundredthReadout (exact reported : ℝ) : Prop :=
  (∃ hundredths : ℤ, reported = (hundredths : ℝ) / 100) ∧
    |exact - reported| ≤ 1 / 200

/-!
The curvature law and `R = 16 m` give `f = -8 m`; the Gaussian mirror equation
with `dₒ = 10 m` then gives the virtual-image distance `dᵢ = -40/9 m`.
-/
lemma signedImageDistanceInMeters_eq_neg_forty_ninths
    (setup : ConvexRearviewMirrorSetup)
    (_data : MatchesProblemStatement setup)
    (_signs : UsesCartesianConvexMirrorConvention setup)
    (_focalLaw : SatisfiesConvexMirrorFocalLaw setup)
    (_mirrorEquation : SatisfiesGaussianMirrorEquation setup) :
    lengthInMeters setup.signedImageDistance = -(40 : ℝ) / 9 := by
  have hRadius := _data.radius_readout_meters
  have hObject := _data.object_distance_readout_meters
  have hFocal := _focalLaw UnitChoices.SI
  have hMirror :=
    congrArg WithDim.val (_mirrorEquation UnitChoices.SI)
  change
    (setup.radiusOfCurvatureMagnitude UnitChoices.SI).val = 16
      at hRadius
  change
    (setup.objectDistance UnitChoices.SI).val = 10
      at hObject
  change
    (setup.signedFocalLength UnitChoices.SI).val *
        ((setup.objectDistance UnitChoices.SI).val +
          (setup.signedImageDistance UnitChoices.SI).val) =
      (setup.objectDistance UnitChoices.SI).val *
        (setup.signedImageDistance UnitChoices.SI).val
      at hMirror
  change
    (setup.signedImageDistance UnitChoices.SI).val = -(40 : ℝ) / 9
  nlinarith

/-!
Substituting the derived virtual-image distance into `m = -dᵢ/dₒ` yields the
exact positive, upright, reduced magnification `m = 4/9`.
-/
lemma transverseMagnification_eq_four_ninths
    (setup : ConvexRearviewMirrorSetup)
    (_data : MatchesProblemStatement setup)
    (_signs : UsesCartesianConvexMirrorConvention setup)
    (_focalLaw : SatisfiesConvexMirrorFocalLaw setup)
    (_mirrorEquation : SatisfiesGaussianMirrorEquation setup)
    (_magnificationLaw : SatisfiesTransverseMagnificationLaw setup) :
    setup.transverseMagnification = (4 : ℝ) / 9 := by
  have hImage :=
    signedImageDistanceInMeters_eq_neg_forty_ninths
      setup _data _signs _focalLaw _mirrorEquation
  have hObject := _data.object_distance_readout_meters
  have hMagnification := _magnificationLaw UnitChoices.SI
  change
    (setup.signedImageDistance UnitChoices.SI).val = -(40 : ℝ) / 9
      at hImage
  change
    (setup.objectDistance UnitChoices.SI).val = 10
      at hObject
  nlinarith

/-!
The exact magnification is `4/9`.  Its nearest-hundredth readout is `+0.44`,
which is answer choice C.

This formalizes `thm:physics:phyx_mini_0139:target`.
-/
theorem problem_phyx_mini_0139
    (setup : ConvexRearviewMirrorSetup)
    (_data : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryFigure setup)
    (_signs : UsesCartesianConvexMirrorConvention setup)
    (_focalLaw : SatisfiesConvexMirrorFocalLaw setup)
    (_mirrorEquation : SatisfiesGaussianMirrorEquation setup)
    (_magnificationLaw : SatisfiesTransverseMagnificationLaw setup) :
    setup.transverseMagnification = (4 : ℝ) / 9 ∧
      IsNearestHundredthReadout setup.transverseMagnification
        AnswerChoice.C.magnificationReadout := by
  have hMagnification :=
    transverseMagnification_eq_four_ninths
      setup _data _signs _focalLaw _mirrorEquation _magnificationLaw
  refine ⟨hMagnification, ?_⟩
  rw [hMagnification]
  constructor
  · exact ⟨44, by norm_num [AnswerChoice.magnificationReadout]⟩
  · norm_num [AnswerChoice.magnificationReadout, abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0139
