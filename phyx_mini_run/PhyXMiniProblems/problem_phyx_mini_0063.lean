import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0063

/-!
# A laser reflected by a mirrored ceiling

The figure shows a rectangular room of width `5.0 m` and height `3.0 m`.
A laser starts at the lower-left corner, reflects specularly from the
horizontal mirrored ceiling, and is required to hit the midpoint of the far
(right-hand) wall.  Lengths below are genuine dimensionful quantities;
coordinate calculations use explicitly named SI-metre readouts.
-/

/-- A physical length, represented coherently in every choice of units. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim Dimension.L𝓭 ℝ)

/-- The numerical SI readout of a physical length, in metres. -/
def metersValue (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- A point in the vertical cross-section of the room.
Both coordinates are physical lengths measured from the lower-left corner. -/
structure Point2D where
  x : LengthQuantity
  y : LengthQuantity

/-- The horizontal coordinate of a point, read in metres. -/
def Point2D.xMeters (point : Point2D) : ℝ :=
  metersValue point.x

/-- The vertical coordinate of a point, read in metres. -/
def Point2D.yMeters (point : Point2D) : ℝ :=
  metersValue point.y

/-- The two physical dimensions of the rectangular room. -/
structure RectangularRoom where
  width : LengthQuantity
  height : LengthQuantity

/-- The room width, read in metres. -/
def RectangularRoom.widthMeters (room : RectangularRoom) : ℝ :=
  metersValue room.width

/-- The room height, read in metres. -/
def RectangularRoom.heightMeters (room : RectangularRoom) : ℝ :=
  metersValue room.height

/-- Labels for the four sides of the rectangular cross-section. -/
inductive RoomBoundary where
  | floor
  | nearWall
  | mirroredCeiling
  | farWall
  deriving DecidableEq, Repr

/-- Coordinate characterization of each labelled room boundary.
In particular, `mirroredCeiling` is the entire top side and `farWall` is the
right-hand side marked "Wall" in the figure. -/
def LiesOnBoundary
    (room : RectangularRoom) (boundary : RoomBoundary) (point : Point2D) : Prop :=
  match boundary with
  | .floor =>
      point.yMeters = 0 ∧
        0 ≤ point.xMeters ∧ point.xMeters ≤ room.widthMeters
  | .nearWall =>
      point.xMeters = 0 ∧
        0 ≤ point.yMeters ∧ point.yMeters ≤ room.heightMeters
  | .mirroredCeiling =>
      point.yMeters = room.heightMeters ∧
        0 ≤ point.xMeters ∧ point.xMeters ≤ room.widthMeters
  | .farWall =>
      point.xMeters = room.widthMeters ∧
        0 ≤ point.yMeters ∧ point.yMeters ≤ room.heightMeters

/-- The point is the lower-left corner from which the depicted laser starts. -/
def IsBottomLeftCorner (point : Point2D) : Prop :=
  point.xMeters = 0 ∧ point.yMeters = 0

/-- The point is the midpoint of the right-hand wall.
The equation is kept division-free and hence remains dimensionally clear. -/
def IsMidpointOfFarWall (room : RectangularRoom) (point : Point2D) : Prop :=
  LiesOnBoundary room .farWall point ∧
    2 * point.yMeters = room.heightMeters

/-- The physical objects and labelled points in the reflected laser path. -/
structure CeilingMirrorLaserSetup where
  room : RectangularRoom
  source : Point2D
  ceilingHit : Point2D
  wallHit : Point2D
  /-- The angle `φ`, measured counterclockwise from the horizontal floor. -/
  launchAngle : Real.Angle

/-- Figure-derived data: a `5.0 m` by `3.0 m` room, source at the lower-left
corner, reflection point on the mirrored ceiling, and target at the midpoint
of the far wall.  The unknown launch angle is deliberately not fixed here. -/
def MatchesFigureReadouts (setup : CeilingMirrorLaserSetup) : Prop :=
  setup.room.widthMeters = 5 ∧
    setup.room.heightMeters = 3 ∧
    IsBottomLeftCorner setup.source ∧
    LiesOnBoundary setup.room .mirroredCeiling setup.ceilingHit ∧
    IsMidpointOfFarWall setup.room setup.wallHit

/-- Positivity and left-to-right travel conditions for the two nondegenerate
ray segments shown in the room. -/
def HasPhysicalPathGeometry (setup : CeilingMirrorLaserSetup) : Prop :=
  0 < setup.room.widthMeters ∧
    0 < setup.room.heightMeters ∧
    setup.source.xMeters < setup.ceilingHit.xMeters ∧
    setup.ceilingHit.xMeters < setup.wallHit.xMeters

/-- The directed inclination of a straight ray segment from the horizontal,
in radians.  The quotient is dimensionless because both differences are SI
readouts of lengths. -/
noncomputable def rayInclinationRadians (startPoint endPoint : Point2D) : ℝ :=
  Real.arctan
    ((endPoint.yMeters - startPoint.yMeters) /
      (endPoint.xMeters - startPoint.xMeters))

/-- The labelled angle `φ` is the inclination of the incident ray segment. -/
def LaunchAngleDescribesIncidentRay (setup : CeilingMirrorLaserSetup) : Prop :=
  setup.launchAngle =
    ((rayInclinationRadians setup.source setup.ceilingHit : ℝ) : Real.Angle)

/-- The launch direction lies strictly between the horizontal and vertical
directions, as depicted. -/
def HasAcuteLaunchAngle (setup : CeilingMirrorLaserSetup) : Prop :=
  0 < setup.launchAngle.toReal ∧ setup.launchAngle.toReal < Real.pi / 2

/-- Specular reflection at a horizontal mirror reverses the sign of the ray's
vertical inclination while preserving its magnitude.  This is the law of
reflection specialized to the ceiling orientation in the figure. -/
def ObeysSpecularReflectionLaw (setup : CeilingMirrorLaserSetup) : Prop :=
  rayInclinationRadians setup.source setup.ceilingHit =
    -rayInclinationRadians setup.ceilingHit setup.wallHit

/-- Convert a degree value into a physical angle. -/
noncomputable def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-- Read the principal representative of a physical angle in degrees. -/
noncomputable def degreeReadout (angle : Real.Angle) : ℝ :=
  angle.toReal * 180 / Real.pi

/-- The four multiple-choice labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Numerical degree values printed beside the four answer choices. -/
def AnswerChoice.degreeValue : AnswerChoice → ℝ
  | .A => 35
  | .B => 90
  | .C => 42
  | .D => 123

/-- An integer-degree answer matches when it is the nearest-degree readout of
the exact physical angle. -/
def MatchesAnswerToNearestDegree
    (angle : Real.Angle) (choice : AnswerChoice) : Prop :=
  |degreeReadout angle - choice.degreeValue| ≤ (1 : ℝ) / 2

/--
Unfolding the reflected ray across the ceiling sends the wall midpoint from
height `1.5 m` to height `4.5 m`.  Thus the exact launch inclination has
tangent `4.5 / 5 = 9 / 10`, whose nearest whole-degree answer is `42°`,
choice C.

This formalizes `thm:physics:phyx_mini_0063:target`.
-/
theorem problem_phyx_mini_0063
    (setup : CeilingMirrorLaserSetup)
    (h_figure : MatchesFigureReadouts setup)
    (h_geometry : HasPhysicalPathGeometry setup)
    (h_launch : LaunchAngleDescribesIncidentRay setup)
    (h_acute : HasAcuteLaunchAngle setup)
    (h_reflection : ObeysSpecularReflectionLaw setup) :
    setup.launchAngle =
        ((Real.arctan ((9 : ℝ) / 10) : ℝ) : Real.Angle) ∧
      MatchesAnswerToNearestDegree setup.launchAngle .C := by
  rcases h_figure with ⟨h_width, h_height, h_source, h_ceiling, h_wall⟩
  rcases h_source with ⟨h_source_x, h_source_y⟩
  rcases h_ceiling with ⟨h_ceiling_y, -, -⟩
  rcases h_wall with ⟨⟨h_wall_x, -, -⟩, h_wall_y_eq⟩
  rcases h_geometry with ⟨-, -, h_source_ceiling, h_ceiling_wall⟩
  have h_ceiling_x_pos : 0 < setup.ceilingHit.xMeters := by
    simpa [h_source_x] using h_source_ceiling
  have h_ceiling_x_lt : setup.ceilingHit.xMeters < 5 := by
    simpa [h_wall_x, h_width] using h_ceiling_wall
  have h_wall_y : setup.wallHit.yMeters = 3 / 2 := by
    rw [h_height] at h_wall_y_eq
    linarith
  have h_incident_slope :
      (setup.ceilingHit.yMeters - setup.source.yMeters) /
          (setup.ceilingHit.xMeters - setup.source.xMeters) =
        -((setup.wallHit.yMeters - setup.ceilingHit.yMeters) /
          (setup.wallHit.xMeters - setup.ceilingHit.xMeters)) := by
    apply Real.arctan_injective
    simpa only [ObeysSpecularReflectionLaw, rayInclinationRadians,
      Real.arctan_neg] using h_reflection
  have h_ceiling_x : setup.ceilingHit.xMeters = 10 / 3 := by
    have h_left_ne : setup.ceilingHit.xMeters ≠ 0 :=
      ne_of_gt h_ceiling_x_pos
    have h_right_ne : 5 - setup.ceilingHit.xMeters ≠ 0 := by
      linarith
    rw [h_source_x, h_source_y, h_ceiling_y, h_height, h_wall_y,
      h_wall_x, h_width] at h_incident_slope
    field_simp [h_left_ne, h_right_ne] at h_incident_slope
    nlinarith
  have h_angle :
      setup.launchAngle =
        ((Real.arctan ((9 : ℝ) / 10) : ℝ) : Real.Angle) := by
    rw [h_launch]
    congr 1
    simp only [rayInclinationRadians]
    rw [h_source_x, h_source_y, h_ceiling_y, h_height, h_ceiling_x]
    norm_num
  refine ⟨h_angle, ?_⟩
  rw [h_angle]
  simp only [MatchesAnswerToNearestDegree, degreeReadout,
    AnswerChoice.degreeValue]
  have h_toReal :
      (((Real.arctan ((9 : ℝ) / 10) : ℝ) : Real.Angle).toReal) =
        Real.arctan ((9 : ℝ) / 10) := by
    rw [Real.Angle.toReal_coe_eq_self_iff]
    constructor
    · nlinarith [Real.neg_pi_div_two_lt_arctan ((9 : ℝ) / 10),
        Real.pi_pos]
    · nlinarith [Real.arctan_lt_pi_div_two ((9 : ℝ) / 10),
        Real.pi_pos]
  rw [h_toReal]
  let x : ℝ := 1 / 19
  let x2 : ℝ := 2 * x / (1 - x ^ 2)
  let x4 : ℝ := 2 * x2 / (1 - x2 ^ 2)
  let x8 : ℝ := 2 * x4 / (1 - x4 ^ 2)
  let x16 : ℝ := 2 * x8 / (1 - x8 ^ 2)
  let x12 : ℝ := (x8 + x4) / (1 - x8 * x4)
  let x14 : ℝ := (x12 + x2) / (1 - x12 * x2)
  let x18 : ℝ := (x16 + x2) / (1 - x16 * x2)
  have hx2 : 2 * Real.arctan x = Real.arctan x2 := by
    simpa [x2] using Real.two_mul_arctan (x := x)
      (by norm_num [x]) (by norm_num [x])
  have hx4 : 4 * Real.arctan x = Real.arctan x4 := by
    calc
      4 * Real.arctan x = 2 * (2 * Real.arctan x) := by ring
      _ = 2 * Real.arctan x2 := by rw [hx2]
      _ = Real.arctan x4 := by
        simpa [x4] using Real.two_mul_arctan (x := x2)
          (by norm_num [x, x2]) (by norm_num [x, x2])
  have hx8 : 8 * Real.arctan x = Real.arctan x8 := by
    calc
      8 * Real.arctan x = 2 * (4 * Real.arctan x) := by ring
      _ = 2 * Real.arctan x4 := by rw [hx4]
      _ = Real.arctan x8 := by
        simpa [x8] using Real.two_mul_arctan (x := x4)
          (by norm_num [x, x2, x4]) (by norm_num [x, x2, x4])
  have hx16 : 16 * Real.arctan x = Real.arctan x16 := by
    calc
      16 * Real.arctan x = 2 * (8 * Real.arctan x) := by ring
      _ = 2 * Real.arctan x8 := by rw [hx8]
      _ = Real.arctan x16 := by
        simpa [x16] using Real.two_mul_arctan (x := x8)
          (by norm_num [x, x2, x4, x8])
          (by norm_num [x, x2, x4, x8])
  have hx12 : 12 * Real.arctan x = Real.arctan x12 := by
    calc
      12 * Real.arctan x =
          8 * Real.arctan x + 4 * Real.arctan x := by ring
      _ = Real.arctan x8 + Real.arctan x4 := by rw [hx8, hx4]
      _ = Real.arctan x12 := by
        simpa [x12] using Real.arctan_add (x := x8) (y := x4)
          (by norm_num [x, x2, x4, x8])
  have hx14 : 14 * Real.arctan x = Real.arctan x14 := by
    calc
      14 * Real.arctan x =
          12 * Real.arctan x + 2 * Real.arctan x := by ring
      _ = Real.arctan x12 + Real.arctan x2 := by rw [hx12, hx2]
      _ = Real.arctan x14 := by
        simpa [x14] using Real.arctan_add (x := x12) (y := x2)
          (by norm_num [x, x2, x4, x8, x12])
  have hx18 : 18 * Real.arctan x = Real.arctan x18 := by
    calc
      18 * Real.arctan x =
          16 * Real.arctan x + 2 * Real.arctan x := by ring
      _ = Real.arctan x16 + Real.arctan x2 := by rw [hx16, hx2]
      _ = Real.arctan x18 := by
        simpa [x18] using Real.arctan_add (x := x16) (y := x2)
          (by norm_num [x, x2, x4, x8, x16])
  have h14 : 14 * Real.arctan x < Real.pi / 4 := by
    rw [hx14, ← Real.arctan_one]
    apply Real.arctan_strictMono
    norm_num [x, x2, x4, x8, x12, x14]
  have h18 : Real.pi / 4 < 18 * Real.arctan x := by
    rw [hx18, ← Real.arctan_one]
    apply Real.arctan_strictMono
    norm_num [x, x2, x4, x8, x16, x18]
  have h_decomposition :
      Real.arctan ((9 : ℝ) / 10) + Real.arctan x =
        Real.pi / 4 := by
    rw [← Real.arctan_one, Real.arctan_add]
    · congr 1
      norm_num [x]
    · norm_num [x]
  have h_correction_lower :
      (5 : ℝ) / 2 < 180 * Real.arctan x / Real.pi := by
    rw [lt_div_iff₀ Real.pi_pos]
    nlinarith [h18]
  have h_correction_upper :
      180 * Real.arctan x / Real.pi < (7 : ℝ) / 2 := by
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith [h14, Real.pi_pos]
  have h_readout :
      Real.arctan ((9 : ℝ) / 10) * 180 / Real.pi - 42 =
        3 - 180 * Real.arctan x / Real.pi := by
    have h_pi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp [h_pi_ne]
    nlinarith [h_decomposition]
  rw [h_readout, abs_le]
  constructor <;> linarith

end PhyXMiniProblems.ProblemPhyXMini0063
