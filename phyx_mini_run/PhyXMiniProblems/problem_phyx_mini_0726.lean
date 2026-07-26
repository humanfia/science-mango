import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Sphere.Tangent
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0726

open Dimension

/-!
# Estimating Earth's radius from the horizon across a lake

The primary figure has four geometrically relevant points: Earth's center,
the water-surface point below the observer, the observer's eye, and the rocks
at water level on the opposite shore.  The two center-to-surface segments are
both labelled `R`; the radial eye height is labelled `h`; and the tangent
line of sight is labelled `d`.

Physical lengths are Physlib dimensionful quantities.  The Euclidean-plane
coordinates and numerical answer choices are scalar readouts in explicitly
named units.
-/

/-! ## Dimensionful lengths and unit readouts -/

/-- A genuine physical quantity with the dimension of length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical length as a scalar in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- SI-metre readout used for the Euclidean diagram and exact calculation. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Kilometre readout used by the map estimate and answer choices. -/
def lengthInKilometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.kilometers length

/-- Foot readout appearing in the prose as a rounded alternative to `3.0 m`. -/
def lengthInFeet (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.feet length

/-! ## Physical objects and labels transcribed from the primary figure -/

/-- The plane of the circular-Earth cross-section, in SI-metre coordinates. -/
abbrev DiagramPlane := EuclideanSpace ℝ (Fin 2)

/-- Named points needed by the horizon construction. -/
inductive FigurePoint where
  | earthCenter
  | nearWaterSurface
  | observerEye
  | oppositeShoreRock
  deriving DecidableEq, Repr

/-- The four length-bearing segments visible in the figure. -/
inductive FigureSegment where
  | nearRadius
  | farRadius
  | eyeHeight
  | lineOfSightDistance
  deriving DecidableEq, Repr

/-- Literal mathematical labels printed beside figure segments. -/
inductive FigureLengthLabel where
  | R
  | h
  | d
  deriving DecidableEq, Repr

/-- The diagram prints `R` twice, and prints `h` and `d` once each. -/
def figureSegmentLabel : FigureSegment → FigureLengthLabel
  | .nearRadius => .R
  | .farRadius => .R
  | .eyeHeight => .h
  | .lineOfSightDistance => .d

/-- Endpoints of each named segment in the cross-sectional figure. -/
def figureSegmentEndpoints : FigureSegment → FigurePoint × FigurePoint
  | .nearRadius => (.earthCenter, .nearWaterSurface)
  | .farRadius => (.earthCenter, .oppositeShoreRock)
  | .eyeHeight => (.nearWaterSurface, .observerEye)
  | .lineOfSightDistance => (.observerEye, .oppositeShoreRock)

/-- Semantic regions carrying the visible `Earth` and `Lake` information. -/
inductive FigureRegion where
  | earthInterior
  | lakeSurface
  | airAboveLake
  deriving DecidableEq, Repr

/-- The spherical cross-sectional model drawn in the source. -/
inductive EarthModel where
  | sphericalCrossSection
  deriving DecidableEq, Repr

/-- The raised support explicitly named in the prose and drawn at the left. -/
inductive ObserverSupport where
  | stepladder
  deriving DecidableEq, Repr

/-- The object that becomes visible at the far water-level point. -/
inductive SightTarget where
  | rocksAtOppositeShoreWaterLevel
  deriving DecidableEq, Repr

/-- The limiting observation described by “can just see”. -/
inductive VisibilityStatus where
  | justVisible
  deriving DecidableEq, Repr

/-- Provenance of the supplied value `d ≈ 6.1 km`. -/
inductive DistanceSource where
  | estimatedFromMap
  deriving DecidableEq, Repr

/-!
The physical and diagrammatic state of the horizon observation.

`earthRadius` is an independent unknown physical length.  In particular, it
is not defined from an answer choice or from the requested radius formula.
-/
structure EarthHorizonSetup where
  point : FigurePoint → DiagramPlane
  lineOfSightCarrier : AffineSubspace ℝ DiagramPlane
  depictedRegion : FigurePoint → FigureRegion
  earthModel : EarthModel
  earthRadius : LengthQuantity
  observerEyeHeight : LengthQuantity
  oppositeShoreDistance : LengthQuantity
  support : ObserverSupport
  sightTarget : SightTarget
  visibility : VisibilityStatus
  distanceSource : DistanceSource
  reportedEyeHeightFeet : ℝ
  reportedOppositeShoreKilometers : ℝ

/-- The circular Earth boundary with the independent physical radius read in metres. -/
def earthSphere
    (setup : EarthHorizonSetup) : EuclideanGeometry.Sphere DiagramPlane :=
  ⟨setup.point .earthCenter, lengthInMeters setup.earthRadius⟩

/-- Length of a displayed segment, computed from its metre-coordinate endpoints. -/
def diagramSegmentLengthMeters
    (setup : EarthHorizonSetup) (segmentName : FigureSegment) : ℝ :=
  let endpoints := figureSegmentEndpoints segmentName
  dist (setup.point endpoints.1) (setup.point endpoints.2)

/-- Horizontal coordinate in the orientation used by the supplied bitmap. -/
def figureX (setup : EarthHorizonSetup) (pointName : FigurePoint) : ℝ :=
  setup.point pointName 0

/-- Vertical coordinate in the orientation used by the supplied bitmap. -/
def figureY (setup : EarthHorizonSetup) (pointName : FigurePoint) : ℝ :=
  setup.point pointName 1

/-! ## Assumption/target split -/

/-!
The numerical and qualitative observations supplied by the prose.

The foot value is explicitly treated as a rounded report, while `h = 3.0 m`
is the metric value requested by the question.  The map value is retained as
an estimate whose displayed readout is `6.1 km`.
-/
structure HasStatedObservationData (setup : EarthHorizonSetup) : Prop where
  spherical_earth_model : setup.earthModel = .sphericalCrossSection
  observer_uses_stepladder : setup.support = .stepladder
  target_is_rocks_at_water_level :
    setup.sightTarget = .rocksAtOppositeShoreWaterLevel
  rocks_are_just_visible : setup.visibility = .justVisible
  distance_was_estimated_from_map : setup.distanceSource = .estimatedFromMap
  reported_height_feet : setup.reportedEyeHeightFeet = 10
  metric_height_meters : lengthInMeters setup.observerEyeHeight = 3
  foot_report_is_nearest_foot :
    |lengthInFeet setup.observerEyeHeight - setup.reportedEyeHeightFeet| ≤ 1 / 2
  reported_distance_kilometers :
    setup.reportedOppositeShoreKilometers = 61 / 10
  map_distance_kilometers :
    lengthInKilometers setup.oppositeShoreDistance =
      setup.reportedOppositeShoreKilometers

/-!
Transcription of the primary bitmap.  It records the two equal radial
segments, the radial eye-height segment, the eye-to-rock segment `d`, the
placement of the named points, and the visible orientation of the far radius
and dashed line of sight.  It does not assign a numerical value to `R`.
-/
structure MatchesPrimaryFigure (setup : EarthHorizonSetup) : Prop where
  center_is_in_earth : setup.depictedRegion .earthCenter = .earthInterior
  near_point_is_on_lake_surface :
    setup.depictedRegion .nearWaterSurface = .lakeSurface
  far_rock_is_on_lake_surface :
    setup.depictedRegion .oppositeShoreRock = .lakeSurface
  eye_is_above_lake : setup.depictedRegion .observerEye = .airAboveLake
  near_radius_is_R :
    diagramSegmentLengthMeters setup .nearRadius =
      lengthInMeters setup.earthRadius
  far_radius_is_R :
    diagramSegmentLengthMeters setup .farRadius =
      lengthInMeters setup.earthRadius
  radial_eye_height_is_h :
    diagramSegmentLengthMeters setup .eyeHeight =
      lengthInMeters setup.observerEyeHeight
  sightline_distance_is_d :
    diagramSegmentLengthMeters setup .lineOfSightDistance =
      lengthInMeters setup.oppositeShoreDistance
  eye_lies_on_sightline_carrier :
    setup.point .observerEye ∈ setup.lineOfSightCarrier
  near_surface_between_center_and_eye :
    setup.point .nearWaterSurface ∈
      segment ℝ (setup.point .earthCenter) (setup.point .observerEye)
  far_radius_is_drawn_vertical :
    figureX setup .earthCenter = figureX setup .oppositeShoreRock
  sightline_is_drawn_horizontal :
    figureY setup .observerEye = figureY setup .oppositeShoreRock
  eye_is_left_of_far_rock :
    figureX setup .observerEye < figureX setup .oppositeShoreRock
  center_is_below_far_rock :
    figureY setup .earthCenter < figureY setup .oppositeShoreRock

/-- Positivity conditions for the three independent physical lengths. -/
structure HasPhysicalLengths (setup : EarthHorizonSetup) : Prop where
  radius_positive : 0 < lengthInMeters setup.earthRadius
  eye_height_positive : 0 < lengthInMeters setup.observerEyeHeight
  shore_distance_positive : 0 < lengthInMeters setup.oppositeShoreDistance

/-!
The governing horizon law: a straight limiting line of sight to a surface
target is tangent to a spherical Earth, hence perpendicular to the radius at
the point of tangency.  This is a reusable geometric law, not the requested
formula or numerical radius.
-/
structure ObeysSphericalEarthHorizonLaw (setup : EarthHorizonSetup) : Prop where
  limiting_sightline_is_tangent :
    setup.visibility = .justVisible →
      (earthSphere setup).IsTangentAt
        (setup.point .oppositeShoreRock) setup.lineOfSightCarrier

/-! ## Derived radius and displayed answer -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Radius readout in kilometres printed beside an answer label. -/
def AnswerChoice.radiusKilometers : AnswerChoice → ℝ
  | .A => 6000
  | .B => 6100
  | .C => 6200
  | .D => 6380

/-!
A choice is selected by proximity to the radius obtained from the physical
model.  This definition does not privilege choice C and does not make any
choice correct by unfolding alone.
-/
def IsClosestDisplayedRadius
    (setup : EarthHorizonSetup) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice : AnswerChoice,
    |lengthInKilometers setup.earthRadius - choice.radiusKilometers| ≤
      |lengthInKilometers setup.earthRadius - otherChoice.radiusKilometers|

/-!
The right triangle with legs `R` and `d` and hypotenuse `R + h` gives

`R = (d^2 - h^2) / (2 h)`.

This is an intermediate derived conclusion, not a premise of the model.
-/
lemma earthRadius_from_tangent_geometry
    (setup : EarthHorizonSetup)
    (h_observation : HasStatedObservationData setup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_lengths : HasPhysicalLengths setup)
    (h_horizon : ObeysSphericalEarthHorizonLaw setup) :
    lengthInMeters setup.earthRadius =
      ((lengthInMeters setup.oppositeShoreDistance) ^ 2 -
          (lengthInMeters setup.observerEyeHeight) ^ 2) /
        (2 * lengthInMeters setup.observerEyeHeight) := by
  have h_tangent :=
    h_horizon.limiting_sightline_is_tangent
      h_observation.rocks_are_just_visible
  have h_center_eye :=
    dist_add_dist_of_mem_segment
      h_figure.near_surface_between_center_and_eye
  change
    diagramSegmentLengthMeters setup .nearRadius +
        diagramSegmentLengthMeters setup .eyeHeight =
      dist (setup.point .earthCenter) (setup.point .observerEye)
    at h_center_eye
  rw [h_figure.near_radius_is_R, h_figure.radial_eye_height_is_h] at h_center_eye
  have h_pythagorean :=
    h_tangent.dist_sq_eq_of_mem h_figure.eye_lies_on_sightline_carrier
  change
    dist (setup.point .observerEye) (setup.point .earthCenter) ^ 2 =
      lengthInMeters setup.earthRadius ^ 2 +
        diagramSegmentLengthMeters setup .lineOfSightDistance ^ 2
    at h_pythagorean
  rw [dist_comm (setup.point .observerEye) (setup.point .earthCenter),
    ← h_center_eye, h_figure.sightline_distance_is_d] at h_pythagorean
  have h_denominator :
      2 * lengthInMeters setup.observerEyeHeight ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt h_lengths.eye_height_positive)
  apply (eq_div_iff h_denominator).2
  nlinarith [h_pythagorean]

/-!
For `h = 3.0 m` and the map estimate `d = 6.1 km`, the tangent construction
gives `R = 37209991 / 6 m ≈ 6201.7 km`.  Therefore the nearest displayed
estimate is `6200 km`, answer choice C.

Blueprint: `thm:physics:phyx_mini_0726:target`.
-/
theorem problem_phyx_mini_0726
    (setup : EarthHorizonSetup)
    (h_observation : HasStatedObservationData setup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_lengths : HasPhysicalLengths setup)
    (h_horizon : ObeysSphericalEarthHorizonLaw setup) :
    lengthInMeters setup.earthRadius = (37209991 : ℝ) / 6 ∧
      IsClosestDisplayedRadius setup .C := by
  have meters_eq_thousand_kilometers (length : LengthQuantity) :
      lengthInMeters length = 1000 * lengthInKilometers length := by
    let kilometerUnits : UnitChoices :=
      { UnitChoices.SI with length := LengthUnit.kilometers }
    let meterUnits : UnitChoices :=
      { UnitChoices.SI with length := LengthUnit.meters }
    let scale : NNReal := kilometerUnits.dimScale meterUnits L𝓭
    have h_scale :=
      congrArg WithDim.val (length.property kilometerUnits meterUnits)
    change
      lengthInMeters length = (scale : ℝ) * lengthInKilometers length
      at h_scale
    have scale_eq : (scale : ℝ) = 1000 := by
      norm_num [scale, kilometerUnits, meterUnits, UnitChoices.dimScale,
        LengthUnit.kilometers, LengthUnit.meters, LengthUnit.scale,
        LengthUnit.div_eq_val]
      rfl
    rw [scale_eq] at h_scale
    exact h_scale
  have h_shore_kilometers :
      lengthInKilometers setup.oppositeShoreDistance = 61 / 10 := by
    rw [h_observation.map_distance_kilometers,
      h_observation.reported_distance_kilometers]
  have h_shore_meters :
      lengthInMeters setup.oppositeShoreDistance = 6100 := by
    rw [meters_eq_thousand_kilometers, h_shore_kilometers]
    norm_num
  have h_radius_meters :=
    earthRadius_from_tangent_geometry setup h_observation h_figure h_lengths h_horizon
  rw [h_shore_meters, h_observation.metric_height_meters] at h_radius_meters
  norm_num at h_radius_meters
  have h_radius_kilometers :
      lengthInKilometers setup.earthRadius = (37209991 : ℝ) / 6000 := by
    have h_conversion := meters_eq_thousand_kilometers setup.earthRadius
    rw [h_radius_meters] at h_conversion
    linarith
  refine ⟨h_radius_meters, ?_⟩
  intro otherChoice
  rw [h_radius_kilometers]
  cases otherChoice <;>
    norm_num [AnswerChoice.radiusKilometers, abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0726
