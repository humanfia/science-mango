import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0109

open Dimension

/-!
# Focal length from a principal-ray grid diagram

The source figure shows one ray from the top of a plant to a thin lens.  Its
solid outgoing part is parallel to the horizontal optic axis, while the dashed
backward extension of its incident part meets that axis on the object side.
That intercept is nine horizontal grid squares from the optical center of the
lens, and each horizontal square represents `2.0 cm`.

All axial positions, the focal-length magnitude, the plant height, and the
horizontal grid spacing are genuine physical lengths.  Only their scalar
readouts in centimeters are real numbers.  The explicitly uncalibrated
vertical drawing scale is not used to infer a physical distance.
-/

/-- A signed physical length whose readout transforms coherently with units. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- SI units with centimeters selected for length readouts. -/
def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The signed scalar readout of a physical length in centimeters. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length centimeterUnitChoices).val

/-- The thin-lens approximation stated in the problem. -/
inductive LensApproximation where
  | thin
  | thick
  deriving DecidableEq, Repr

/-- Orientation of the labelled optic axis in the source figure. -/
inductive OpticAxisOrientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Whether vertical page distances share the calibrated horizontal scale. -/
inductive VerticalScaleStatus where
  | sameAsHorizontal
  | notSameAsHorizontal
  deriving DecidableEq, Repr

/-- Points whose horizontal locations or optical roles occur in the diagram. -/
inductive FigurePoint where
  /-- Where the dashed backward ray extension crosses the optic axis. -/
  | backwardAxisIntercept
  | plantBase
  | plantTip
  | lensOpticalCenter
  /-- The point above the axis at which the ray meets the lens. -/
  | lensRayHit
  deriving DecidableEq, Repr

/-- The three visually distinguished parts of the single depicted ray. -/
inductive FigureRayPart where
  | dashedBackwardExtension
  | solidIncident
  | solidOutgoing
  deriving DecidableEq, Repr

/-!
The physical quantities and incidence relations represented by the figure.

`axialPosition` is only a horizontal coordinate.  The plant height is retained
as a physical quantity even though the diagram supplies no calibrated
vertical readout.  The relational ray fields preserve the fact that the
dashed and solid incident pieces are one line without assigning page-picture
coordinates physical meaning.
-/
structure PrincipalRayLensDiagram where
  approximation : LensApproximation
  axisOrientation : OpticAxisOrientation
  verticalScaleStatus : VerticalScaleStatus
  focalLengthMagnitude : LengthQuantity
  plantHeight : LengthQuantity
  horizontalGridSquareWidth : LengthQuantity
  axialPosition : FigurePoint → LengthQuantity
  horizontalGridSquaresBetween : FigurePoint → FigurePoint → ℕ
  onVerticalGridLine : FigurePoint → Prop
  liesOnOpticAxis : FigurePoint → Prop
  rayPartPassesThrough : FigureRayPart → FigurePoint → Prop
  rayPartsCollinear : FigureRayPart → FigureRayPart → Prop
  rayPartParallelToOpticAxis : FigureRayPart → Prop
  /-- The problem statement identifies the combined drawn ray as principal. -/
  shownRayIsPrincipal : Prop

/-- Signed horizontal separation from `start` to `finish`, in centimeters. -/
def axialSeparationInCentimeters
    (diagram : PrincipalRayLensDiagram) (start finish : FigurePoint) : ℝ :=
  lengthInCentimeters (diagram.axialPosition finish) -
    lengthInCentimeters (diagram.axialPosition start)

/-!
Primary-image and problem-text readouts.  In particular, the backward-axis
intercept and lens center are nine calibrated horizontal squares apart.  This
does not identify that separation with the unknown focal length.
-/
structure MatchesPrimaryFigure (diagram : PrincipalRayLensDiagram) : Prop where
  lens_is_thin : diagram.approximation = .thin
  optic_axis_is_horizontal : diagram.axisOrientation = .horizontal
  vertical_scale_is_not_horizontal_scale :
    diagram.verticalScaleStatus = .notSameAsHorizontal
  horizontal_square_width_cm :
    lengthInCentimeters diagram.horizontalGridSquareWidth = 2
  intercept_on_grid_line : diagram.onVerticalGridLine .backwardAxisIntercept
  lens_center_on_grid_line : diagram.onVerticalGridLine .lensOpticalCenter
  nine_horizontal_squares_to_lens :
    diagram.horizontalGridSquaresBetween
      .backwardAxisIntercept .lensOpticalCenter = 9
  backward_intercept_on_axis :
    diagram.liesOnOpticAxis .backwardAxisIntercept
  plant_base_on_axis : diagram.liesOnOpticAxis .plantBase
  lens_center_on_axis : diagram.liesOnOpticAxis .lensOpticalCenter
  plant_tip_off_axis : ¬ diagram.liesOnOpticAxis .plantTip
  lens_ray_hit_off_axis : ¬ diagram.liesOnOpticAxis .lensRayHit
  intercept_left_of_plant :
    lengthInCentimeters (diagram.axialPosition .backwardAxisIntercept) <
      lengthInCentimeters (diagram.axialPosition .plantBase)
  plant_left_of_lens :
    lengthInCentimeters (diagram.axialPosition .plantBase) <
      lengthInCentimeters (diagram.axialPosition .lensOpticalCenter)
  ray_hit_at_lens_center_axial_position :
    diagram.axialPosition .lensRayHit = diagram.axialPosition .lensOpticalCenter
  dashed_extension_through_axis_intercept :
    diagram.rayPartPassesThrough
      .dashedBackwardExtension .backwardAxisIntercept
  dashed_extension_through_plant_tip :
    diagram.rayPartPassesThrough .dashedBackwardExtension .plantTip
  incident_ray_through_plant_tip :
    diagram.rayPartPassesThrough .solidIncident .plantTip
  incident_ray_through_lens :
    diagram.rayPartPassesThrough .solidIncident .lensRayHit
  outgoing_ray_through_lens :
    diagram.rayPartPassesThrough .solidOutgoing .lensRayHit
  dashed_and_incident_are_one_line :
    diagram.rayPartsCollinear .dashedBackwardExtension .solidIncident
  incident_ray_is_not_axis_parallel :
    ¬ diagram.rayPartParallelToOpticAxis .solidIncident
  outgoing_ray_is_axis_parallel :
    diagram.rayPartParallelToOpticAxis .solidOutgoing
  shown_ray_is_principal : diagram.shownRayIsPrincipal

/-!
The horizontal grid calibration: for two marked vertical grid lines, the
physical axial separation is the counted number of squares times the physical
width of one square.  This is a general measurement rule, not an optical law.
-/
def HasCalibratedHorizontalGrid (diagram : PrincipalRayLensDiagram) : Prop :=
  ∀ left right : FigurePoint,
    diagram.onVerticalGridLine left →
      diagram.onVerticalGridLine right →
        lengthInCentimeters (diagram.axialPosition left) ≤
            lengthInCentimeters (diagram.axialPosition right) →
          axialSeparationInCentimeters diagram left right =
            (diagram.horizontalGridSquaresBetween left right : ℝ) *
              lengthInCentimeters diagram.horizontalGridSquareWidth

/-- Positivity of the three physical length magnitudes in the setup. -/
def HasPhysicalLengthMagnitudes (diagram : PrincipalRayLensDiagram) : Prop :=
  0 < lengthInCentimeters diagram.focalLengthMagnitude ∧
    0 < lengthInCentimeters diagram.plantHeight ∧
    0 < lengthInCentimeters diagram.horizontalGridSquareWidth

/-!
The focal principal-ray law for a thin lens.  If a non-axis-parallel principal
incident ray has a backward extension meeting the optic axis and emerges
parallel to that axis, then the axis intercept is the object-side principal
focus.  Consequently its axial distance from the lens optical center equals
the focal-length magnitude.

The law is quantified over candidate axis-intersection and lens-hit points;
it contains neither the figure's grid count nor the requested numeric answer.
-/
def ObeysThinLensPrincipalRayLaw (diagram : PrincipalRayLensDiagram) : Prop :=
  ∀ axisIntersection lensHit : FigurePoint,
    diagram.approximation = .thin →
      diagram.shownRayIsPrincipal →
        diagram.liesOnOpticAxis axisIntersection →
          lengthInCentimeters (diagram.axialPosition axisIntersection) <
              lengthInCentimeters
                (diagram.axialPosition .lensOpticalCenter) →
            diagram.rayPartPassesThrough
                .dashedBackwardExtension axisIntersection →
              diagram.rayPartsCollinear
                  .dashedBackwardExtension .solidIncident →
                diagram.rayPartPassesThrough .solidIncident lensHit →
                  diagram.rayPartPassesThrough .solidOutgoing lensHit →
                    diagram.axialPosition lensHit =
                        diagram.axialPosition .lensOpticalCenter →
                      ¬ diagram.rayPartParallelToOpticAxis .solidIncident →
                        diagram.rayPartParallelToOpticAxis .solidOutgoing →
                          axialSeparationInCentimeters
                              diagram axisIntersection .lensOpticalCenter =
                            lengthInCentimeters diagram.focalLengthMagnitude

/-- The four displayed answer labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Focal-length readout printed beside each answer, in centimeters. -/
def answerFocalLengthInCentimeters : AnswerChoice → ℝ
  | .A => 18
  | .B => 234 / 10
  | .C => 192 / 10
  | .D => 169 / 10

/-- Dataset metadata: the recorded answer label, not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .A

/-- Exact agreement of a physical focal-length magnitude with one answer. -/
def MatchesAnswerExactly
    (focalLengthMagnitude : LengthQuantity) (choice : AnswerChoice) : Prop :=
  lengthInCentimeters focalLengthMagnitude =
    answerFocalLengthInCentimeters choice

/-!
The calibrated grid alone makes the horizontal separation between the
backward intercept and lens center `9 * 2 = 18 cm`.  No optical interpretation
of that separation is used in this intermediate statement.
-/
lemma backwardAxisInterceptSeparation_eq_eighteen
    (diagram : PrincipalRayLensDiagram)
    (hFigure : MatchesPrimaryFigure diagram)
    (hGrid : HasCalibratedHorizontalGrid diagram) :
    axialSeparationInCentimeters
      diagram .backwardAxisIntercept .lensOpticalCenter = 18 := by
  have hInterceptLeftOfLens :
      lengthInCentimeters
          (diagram.axialPosition .backwardAxisIntercept) ≤
        lengthInCentimeters
          (diagram.axialPosition .lensOpticalCenter) :=
    le_of_lt (hFigure.intercept_left_of_plant.trans hFigure.plant_left_of_lens)
  have hCalibrated := hGrid
    .backwardAxisIntercept
    .lensOpticalCenter
    hFigure.intercept_on_grid_line
    hFigure.lens_center_on_grid_line
    hInterceptLeftOfLens
  rw [hFigure.nine_horizontal_squares_to_lens,
    hFigure.horizontal_square_width_cm] at hCalibrated
  norm_num at hCalibrated
  exact hCalibrated

/-!
The non-axis-parallel principal ray emerges parallel to the optic axis, so its
dashed backward-axis intercept is the object-side focal point.  Nine squares
of `2.0 cm` give a focal-length magnitude of `18.0 cm`, answer choice A.

This formalizes `thm:physics:phyx_mini_0109:target`.
-/
theorem problem_phyx_mini_0109
    (diagram : PrincipalRayLensDiagram)
    (hFigure : MatchesPrimaryFigure diagram)
    (hPhysical : HasPhysicalLengthMagnitudes diagram)
    (hGrid : HasCalibratedHorizontalGrid diagram)
    (hPrincipalRay : ObeysThinLensPrincipalRayLaw diagram) :
    lengthInCentimeters diagram.focalLengthMagnitude = 18 ∧
      MatchesAnswerExactly diagram.focalLengthMagnitude .A := by
  have hInterceptLeftOfLens :
      lengthInCentimeters
          (diagram.axialPosition .backwardAxisIntercept) <
        lengthInCentimeters
          (diagram.axialPosition .lensOpticalCenter) :=
    hFigure.intercept_left_of_plant.trans hFigure.plant_left_of_lens
  have hPrincipalFocus := hPrincipalRay
    .backwardAxisIntercept
    .lensRayHit
    hFigure.lens_is_thin
    hFigure.shown_ray_is_principal
    hFigure.backward_intercept_on_axis
    hInterceptLeftOfLens
    hFigure.dashed_extension_through_axis_intercept
    hFigure.dashed_and_incident_are_one_line
    hFigure.incident_ray_through_lens
    hFigure.outgoing_ray_through_lens
    hFigure.ray_hit_at_lens_center_axial_position
    hFigure.incident_ray_is_not_axis_parallel
    hFigure.outgoing_ray_is_axis_parallel
  have hSeparation :=
    backwardAxisInterceptSeparation_eq_eighteen diagram hFigure hGrid
  have hFocalLength :
      lengthInCentimeters diagram.focalLengthMagnitude = 18 :=
    hPrincipalFocus.symm.trans hSeparation
  refine ⟨hFocalLength, ?_⟩
  simpa [MatchesAnswerExactly, answerFocalLengthInCentimeters] using hFocalLength

end PhyXMiniProblems.ProblemPhyXMini0109
