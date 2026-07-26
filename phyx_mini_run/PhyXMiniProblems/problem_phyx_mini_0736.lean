import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0736

open Dimension

/-!
# Direction of a marked rim point after a rolling half-turn

A wheel of radius `45.0 cm` rolls without slipping along a horizontal floor.
At the first pictured time `t₁`, the painted point `P` is the contact point; at
the second pictured time `t₂`, after one half-revolution, `P` is at the top of
the wheel.  The requested observable is the angle of the displacement of `P`
above the floor.

Wheel radii and planar position coordinates are represented by dimensionful
Physlib quantities.  Real numbers occur only as scalar readouts in named unit
systems, dimensionless rotation angles, and displayed answer values.
-/

/-! ## Dimensionful lengths and coordinate readouts -/

/-- A nonnegative physical length, used for the wheel radius. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical length, used for a coordinate relative to a chosen origin. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Scalar readout of a nonnegative physical length in a coherent unit system. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  ((length units).val : ℝ)

/-- Scalar readout of a signed physical coordinate in a coherent unit system. -/
def signedLengthReadout
    (units : UnitChoices) (length : SignedLengthQuantity) : ℝ :=
  (length units).val

/-- SI base units with centimeters selected as the length unit. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- Read a physical radius in centimeters. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout centimeterUnitChoices length

/-! ## Plane, time, and primary-figure vocabulary -/

/-- The two coordinate directions in the plane of the wheel. -/
inductive PlaneAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- A planar physical position, represented by one signed length per axis. -/
abbrev PlanePosition : Type := PlaneAxis → SignedLengthQuantity

/-- The two observation times named in the figure. -/
inductive WheelInstant where
  | t₁
  | t₂
  deriving DecidableEq, Fintype, Repr

/-- Literal time labels printed beneath the two panels. -/
inductive FigureTimeLabel where
  | t₁
  | t₂
  deriving DecidableEq, Repr

/-- The label attached to the painted rim point. -/
inductive MarkedPointLabel where
  | P
  deriving DecidableEq, Repr

/-- Qualitative locations of the marked point in the two supplied panels. -/
inductive RimLocation where
  | bottomContact
  | topmost
  deriving DecidableEq, Repr

/-- Orientation of the supporting floor. -/
inductive FloorOrientation where
  | horizontal
  deriving DecidableEq, Repr

/-- Horizontal rolling direction indicated by the left-to-right panel layout. -/
inductive RollingDirection where
  | rightward
  deriving DecidableEq, Repr

/-- The physical observable requested in the question. -/
inductive RequestedObservable where
  | markedPointDisplacementAngleRelativeToFloor
  deriving DecidableEq, Repr

/-- Qualitative information transcribed from the two-panel primary image. -/
structure RollingWheelFigure where
  panelCount : ℕ
  panelLabel : WheelInstant → FigureTimeLabel
  wheelVisible : WheelInstant → Bool
  floorVisible : WheelInstant → Bool
  markedPointVisible : WheelInstant → Bool
  wheelContactsFloor : WheelInstant → Bool
  markedPointLabel : MarkedPointLabel
  markedPointLocation : WheelInstant → RimLocation
  sameWheelInBothPanels : Bool
  laterPanelDrawnToRight : Bool

/-!
The independent physical quantities and trajectories in the scenario.
Neither the displacement direction nor any answer choice is stored here.
-/
structure RollingWheelSetup where
  wheelRadius : LengthQuantity
  centerPosition : WheelInstant → PlanePosition
  markedPointPosition : WheelInstant → PlanePosition
  rotationMagnitudeRadians : ℝ
  floorOrientation : FloorOrientation
  rollingDirection : RollingDirection
  requestedObservable : RequestedObservable
  figure : RollingWheelFigure

/-! ## General scalar observables -/

/-- Read one coordinate of a dimensionful planar position. -/
def coordinateReadout
    (units : UnitChoices) (position : PlanePosition) (axis : PlaneAxis) : ℝ :=
  signedLengthReadout units (position axis)

/-- Coordinate displacement between two dimensionful planar positions. -/
def displacementCoordinateReadout
    (units : UnitChoices) (initialPosition finalPosition : PlanePosition)
    (axis : PlaneAxis) : ℝ :=
  coordinateReadout units finalPosition axis -
    coordinateReadout units initialPosition axis

/-- Displacement of the wheel center from `t₁` to `t₂`. -/
def centerDisplacementReadout
    (setup : RollingWheelSetup) (units : UnitChoices) (axis : PlaneAxis) : ℝ :=
  displacementCoordinateReadout units (setup.centerPosition .t₁)
    (setup.centerPosition .t₂) axis

/-- Displacement of the painted point `P` from `t₁` to `t₂`. -/
def markedPointDisplacementReadout
    (setup : RollingWheelSetup) (units : UnitChoices) (axis : PlaneAxis) : ℝ :=
  displacementCoordinateReadout units (setup.markedPointPosition .t₁)
    (setup.markedPointPosition .t₂) axis

/-!
Angle of the marked point's displacement above the positive horizontal floor
direction.  The physical assumptions below imply a positive horizontal
component, selecting the ordinary `Real.arctan` branch.
-/
def markedPointDisplacementAngleRadians (setup : RollingWheelSetup) : ℝ :=
  Real.arctan
    (markedPointDisplacementReadout setup UnitChoices.SI .vertical /
      markedPointDisplacementReadout setup UnitChoices.SI .horizontal)

/-- Convert a dimensionless radian readout to degrees. -/
def radiansToDegrees (angleRadians : ℝ) : ℝ :=
  angleRadians * 180 / Real.pi

/-! ## Stated measurements and figure-derived data -/

/-!
Problem-text data: a `45.0 cm` wheel on a horizontal floor completes a
half-revolution, and the question asks for the direction of `P`'s
displacement.  No displacement component or answer angle is included.
-/
structure MatchesProblemStatement (setup : RollingWheelSetup) : Prop where
  radiusInCentimeters : lengthInCentimeters setup.wheelRadius = 45
  floorIsHorizontal : setup.floorOrientation = .horizontal
  halfRevolution : setup.rotationMagnitudeRadians = Real.pi
  asksForMarkedPointDisplacementAngle :
    setup.requestedObservable = .markedPointDisplacementAngleRelativeToFloor

/-!
Primary-image evidence: two labeled panels show the same wheel and floor; `P`
is the bottom contact point at `t₁`, the topmost rim point at `t₂`, and the
later panel lies to the right.  These qualitative readouts contain no answer
angle or numerical displacement.
-/
structure MatchesPrimaryFigure (setup : RollingWheelSetup) : Prop where
  twoPanels : setup.figure.panelCount = 2
  firstPanelLabel : setup.figure.panelLabel .t₁ = .t₁
  secondPanelLabel : setup.figure.panelLabel .t₂ = .t₂
  wheelVisible : ∀ instant, setup.figure.wheelVisible instant = true
  floorVisible : ∀ instant, setup.figure.floorVisible instant = true
  markedPointVisible : ∀ instant, setup.figure.markedPointVisible instant = true
  wheelContactsFloor : ∀ instant, setup.figure.wheelContactsFloor instant = true
  labelIsP : setup.figure.markedPointLabel = .P
  pointAtBottomContactAtT₁ :
    setup.figure.markedPointLocation .t₁ = .bottomContact
  pointAtTopAtT₂ : setup.figure.markedPointLocation .t₂ = .topmost
  depictsSameWheel : setup.figure.sameWheelInBothPanels = true
  laterPanelIsToRight : setup.figure.laterPanelDrawnToRight = true
  rollingIsRightward : setup.rollingDirection = .rightward

/-- Positivity needed to cancel the physical radius and select the angle branch. -/
structure HasPhysicalWheelParameters (setup : RollingWheelSetup) : Prop where
  radiusPositive : 0 < lengthReadout UnitChoices.SI setup.wheelRadius

/-! ## Governing wheel geometry and no-slip law -/

/-!
Rigid-wheel geometry relative to the floor coordinate frame.  The center
stays one radius above the floor.  A qualitative bottom/top rim location
places `P` one radius below/above the center, respectively.  These laws are
stated in every coherent unit system and do not mention the requested angle.
-/
structure SatisfiesRigidWheelGeometry (setup : RollingWheelSetup) : Prop where
  centerHeightAboveFloor : ∀ instant units,
    coordinateReadout units (setup.centerPosition instant) .vertical =
      lengthReadout units setup.wheelRadius
  markedPointAtBottom : ∀ instant units,
    setup.figure.markedPointLocation instant = .bottomContact →
      coordinateReadout units (setup.markedPointPosition instant) .horizontal =
          coordinateReadout units (setup.centerPosition instant) .horizontal ∧
        coordinateReadout units (setup.markedPointPosition instant) .vertical =
          coordinateReadout units (setup.centerPosition instant) .vertical -
            lengthReadout units setup.wheelRadius
  markedPointAtTop : ∀ instant units,
    setup.figure.markedPointLocation instant = .topmost →
      coordinateReadout units (setup.markedPointPosition instant) .horizontal =
          coordinateReadout units (setup.centerPosition instant) .horizontal ∧
        coordinateReadout units (setup.markedPointPosition instant) .vertical =
          coordinateReadout units (setup.centerPosition instant) .vertical +
            lengthReadout units setup.wheelRadius

/-!
Rolling without slipping: for the rightward motion shown, the center's
horizontal travel is the wheel radius times the positive rotation magnitude.
This is the governing kinematic law, not a statement of `P`'s displacement or
its angle.
-/
structure SatisfiesRollingWithoutSlipping (setup : RollingWheelSetup) : Prop where
  noSlipCenterTravel : ∀ units,
    centerDisplacementReadout setup units .horizontal =
      lengthReadout units setup.wheelRadius * setup.rotationMagnitudeRadians

/-! ## Derived displacement and multiple-choice conclusion -/

/-- Labels of the four displayed answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Angle in degrees printed beside each answer label. -/
def AnswerChoice.degrees : AnswerChoice → ℝ
  | .A => 51 / 2
  | .B => 55 / 2
  | .C => 65 / 2
  | .D => 69 / 2

/-- Dataset metadata: the recorded answer is choice C; this is never a premise. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
Agreement with a degree value displayed to the nearest tenth.  The
half-tenth-degree tolerance models the precision of the answer list.
-/
def MatchesDisplayedPrecision (angleRadians : ℝ) (choice : AnswerChoice) : Prop :=
  |radiansToDegrees angleRadians - choice.degrees| ≤ 1 / 20

/-- A displayed answer is uniquely closest to the physical angle. -/
def IsUniqueClosestAnswer (angleRadians : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |radiansToDegrees angleRadians - choice.degrees| <
      |radiansToDegrees angleRadians - other.degrees|

/-!
The no-slip and rigid-wheel relations imply that, in any coherent length
unit, the displacement of `P` is `(π R, 2 R)`.  This is a derived kinematic
result rather than a premise.
-/
lemma markedPoint_displacement_components
    (setup : RollingWheelSetup)
    (_statement : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryFigure setup)
    (_geometry : SatisfiesRigidWheelGeometry setup)
    (_rolling : SatisfiesRollingWithoutSlipping setup)
    (units : UnitChoices) :
    markedPointDisplacementReadout setup units .horizontal =
        Real.pi * lengthReadout units setup.wheelRadius ∧
      markedPointDisplacementReadout setup units .vertical =
        2 * lengthReadout units setup.wheelRadius := by
  have hbottom :=
    _geometry.markedPointAtBottom .t₁ units
      _figure.pointAtBottomContactAtT₁
  have htop :=
    _geometry.markedPointAtTop .t₂ units _figure.pointAtTopAtT₂
  constructor
  · rw [markedPointDisplacementReadout, displacementCoordinateReadout,
      htop.1, hbottom.1]
    change centerDisplacementReadout setup units .horizontal =
      Real.pi * lengthReadout units setup.wheelRadius
    rw [_rolling.noSlipCenterTravel, _statement.halfRevolution, mul_comm]
  · rw [markedPointDisplacementReadout, displacementCoordinateReadout,
      htop.2, hbottom.2,
      _geometry.centerHeightAboveFloor .t₂ units,
      _geometry.centerHeightAboveFloor .t₁ units]
    ring

/-!
The exact ideal-model angle is `arctan (2 / π)` radians, approximately
`32.48°`.  It therefore agrees with the displayed `32.5°` precision and is
uniquely closest to choice C.

This formalizes blueprint label `thm:physics:phyx_mini_0736:target`.
-/
theorem problem_phyx_mini_0736
    (setup : RollingWheelSetup)
    (_statement : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalWheelParameters setup)
    (_geometry : SatisfiesRigidWheelGeometry setup)
    (_rolling : SatisfiesRollingWithoutSlipping setup) :
    markedPointDisplacementAngleRadians setup =
        Real.arctan (2 / Real.pi) ∧
      MatchesDisplayedPrecision
        (markedPointDisplacementAngleRadians setup) recordedAnswerChoice ∧
      IsUniqueClosestAnswer
        (markedPointDisplacementAngleRadians setup) recordedAnswerChoice := by
  have hcomponents :=
    markedPoint_displacement_components setup _statement _figure _geometry
      _rolling UnitChoices.SI
  have hradius_pos :
      0 < lengthReadout UnitChoices.SI setup.wheelRadius :=
    _physical.radiusPositive
  have hradius_ne :
      lengthReadout UnitChoices.SI setup.wheelRadius ≠ 0 :=
    ne_of_gt hradius_pos
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hangle :
      markedPointDisplacementAngleRadians setup =
        Real.arctan (2 / Real.pi) := by
    rw [markedPointDisplacementAngleRadians, hcomponents.1, hcomponents.2]
    congr 1
    field_simp [hradius_ne, hpi_ne]

  have r_lt_arctan_of_poly {r q : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
      (hq0 : 0 ≤ q)
      (hpoly :
        r - r ^ 3 / 6 + r ^ 4 * (5 / 96) <
          q * (1 - r ^ 2 / 2 - r ^ 4 * (5 / 96))) :
      r < Real.arctan q := by
    have habs : |r| ≤ 1 := by
      rw [abs_of_pos hr0]
      exact hr1.le
    have hs := Real.sin_bound habs
    have hc := Real.cos_bound habs
    rw [abs_of_pos hr0] at hs hc
    have hsin_upper :
        Real.sin r ≤ r - r ^ 3 / 6 + r ^ 4 * (5 / 96) := by
      linarith [abs_le.mp hs |>.2]
    have hcos_lower :
        1 - r ^ 2 / 2 - r ^ 4 * (5 / 96) ≤ Real.cos r := by
      linarith [abs_le.mp hc |>.1]
    have hrpi : r < Real.pi / 2 :=
      hr1.trans_le Real.one_le_pi_div_two
    have hcos_pos : 0 < Real.cos r :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], hrpi⟩
    have htan : Real.tan r < q := by
      rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcos_pos]
      calc
        Real.sin r ≤ r - r ^ 3 / 6 + r ^ 4 * (5 / 96) :=
          hsin_upper
        _ < q * (1 - r ^ 2 / 2 - r ^ 4 * (5 / 96)) := hpoly
        _ ≤ q * Real.cos r :=
          mul_le_mul_of_nonneg_left hcos_lower hq0
    rw [← Real.arctan_tan (by linarith [Real.pi_pos]) hrpi]
    exact Real.arctan_strictMono htan

  have arctan_lt_r_of_poly {q r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
      (hq0 : 0 ≤ q)
      (hpoly :
        q * (1 - r ^ 2 / 2 + r ^ 4 * (5 / 96)) <
          r - r ^ 3 / 6 - r ^ 4 * (5 / 96)) :
      Real.arctan q < r := by
    have habs : |r| ≤ 1 := by
      rw [abs_of_pos hr0]
      exact hr1.le
    have hs := Real.sin_bound habs
    have hc := Real.cos_bound habs
    rw [abs_of_pos hr0] at hs hc
    have hsin_lower :
        r - r ^ 3 / 6 - r ^ 4 * (5 / 96) ≤ Real.sin r := by
      linarith [abs_le.mp hs |>.1]
    have hcos_upper :
        Real.cos r ≤ 1 - r ^ 2 / 2 + r ^ 4 * (5 / 96) := by
      linarith [abs_le.mp hc |>.2]
    have hrpi : r < Real.pi / 2 :=
      hr1.trans_le Real.one_le_pi_div_two
    have hcos_pos : 0 < Real.cos r :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], hrpi⟩
    have htan : q < Real.tan r := by
      rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcos_pos]
      calc
        q * Real.cos r ≤ q * (1 - r ^ 2 / 2 + r ^ 4 * (5 / 96)) :=
          mul_le_mul_of_nonneg_left hcos_upper hq0
        _ < r - r ^ 3 / 6 - r ^ 4 * (5 / 96) := hpoly
        _ ≤ Real.sin r := hsin_lower
    rw [← Real.arctan_tan (by linarith [Real.pi_pos]) hrpi]
    exact Real.arctan_strictMono htan

  have harctan_sixth_lower :
      (1651 / 10000 : ℝ) < Real.arctan (1 / 6 : ℝ) := by
    apply r_lt_arctan_of_poly <;> norm_num
  have harctan_sixth_upper :
      Real.arctan (1 / 6 : ℝ) < (413 / 2500 : ℝ) := by
    apply arctan_lt_r_of_poly <;> norm_num
  have harctan_31_lower :
      (161 / 5000 : ℝ) < Real.arctan (1 / 31 : ℝ) := by
    apply r_lt_arctan_of_poly <;> norm_num
  have harctan_31_upper :
      Real.arctan (1 / 31 : ℝ) < (129 / 4000 : ℝ) := by
    apply arctan_lt_r_of_poly <;> norm_num
  have harctan_fifth_split :
      Real.arctan (1 / 6 : ℝ) + Real.arctan (1 / 31 : ℝ) =
        Real.arctan (1 / 5 : ℝ) := by
    rw [Real.arctan_add] <;> norm_num
  have harctan_fifth_lower :
      (1973 / 10000 : ℝ) < Real.arctan (1 / 5 : ℝ) := by
    nlinarith
  have harctan_fifth_upper :
      Real.arctan (1 / 5 : ℝ) < (3949 / 20000 : ℝ) := by
    nlinarith
  have harctan_239_lower :
      (1 / 240 : ℝ) < Real.arctan (1 / 239 : ℝ) := by
    apply r_lt_arctan_of_poly <;> norm_num
  have harctan_239_upper :
      Real.arctan (1 / 239 : ℝ) < (1 / 239 : ℝ) := by
    apply arctan_lt_r_of_poly <;> norm_num
  have hmachin := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  norm_num [inv_eq_one_div] at hmachin
  have hpi_lower : (157 / 50 : ℝ) < Real.pi := by
    nlinarith
  have hpi_upper : Real.pi < (22 / 7 : ℝ) := by
    nlinarith

  have hpi_add_two_pos : 0 < Real.pi + 2 := by
    linarith [Real.pi_pos]
  have hcorrection_lower :
      (57 / 257 : ℝ) <
        (Real.pi - 2) / (Real.pi + 2) := by
    rw [lt_div_iff₀ hpi_add_two_pos]
    nlinarith [hpi_lower]
  have hcorrection_upper :
      (Real.pi - 2) / (Real.pi + 2) < (2 / 9 : ℝ) := by
    rw [div_lt_iff₀ hpi_add_two_pos]
    nlinarith [hpi_upper]
  have hatan_correction_lower :
      (109 / 500 : ℝ) <
        Real.arctan ((Real.pi - 2) / (Real.pi + 2)) := by
    calc
      (109 / 500 : ℝ) < Real.arctan (57 / 257 : ℝ) := by
        apply r_lt_arctan_of_poly <;> norm_num
      _ < Real.arctan ((Real.pi - 2) / (Real.pi + 2)) :=
        Real.arctan_strictMono hcorrection_lower
  have hatan_correction_upper :
      Real.arctan ((Real.pi - 2) / (Real.pi + 2)) <
        (2189 / 10000 : ℝ) := by
    calc
      Real.arctan ((Real.pi - 2) / (Real.pi + 2)) <
          Real.arctan (2 / 9 : ℝ) :=
        Real.arctan_strictMono hcorrection_upper
      _ < (2189 / 10000 : ℝ) := by
        apply arctan_lt_r_of_poly <;> norm_num

  have hproduct_den_pos : 0 < Real.pi * (Real.pi + 2) :=
    mul_pos Real.pi_pos hpi_add_two_pos
  have hproduct_lt :
      (2 / Real.pi) * ((Real.pi - 2) / (Real.pi + 2)) < 1 := by
    calc
      (2 / Real.pi) * ((Real.pi - 2) / (Real.pi + 2)) =
          (2 * (Real.pi - 2)) / (Real.pi * (Real.pi + 2)) := by
        field_simp [hpi_ne, ne_of_gt hpi_add_two_pos]
      _ < 1 := by
        rw [div_lt_one hproduct_den_pos]
        nlinarith [sq_nonneg Real.pi]
  have hratio :
      ((2 / Real.pi) + ((Real.pi - 2) / (Real.pi + 2))) /
          (1 - (2 / Real.pi) * ((Real.pi - 2) / (Real.pi + 2))) =
        1 := by
    have hpi_add_two_ne : Real.pi + 2 ≠ 0 :=
      ne_of_gt hpi_add_two_pos
    have houter_ne :
        1 - (2 / Real.pi) * ((Real.pi - 2) / (Real.pi + 2)) ≠ 0 :=
      ne_of_gt (sub_pos.mpr hproduct_lt)
    rw [div_eq_one_iff_eq houter_ne]
    field_simp [hpi_ne, hpi_add_two_ne]
    ring
  have hcomplement :
      Real.arctan (2 / Real.pi) +
          Real.arctan ((Real.pi - 2) / (Real.pi + 2)) =
        Real.pi / 4 := by
    rw [Real.arctan_add]
    · rw [hratio, Real.arctan_one]
    · exact hproduct_lt

  have hcorrection_relative_lower :
      249 * Real.pi / 3600 <
        Real.arctan ((Real.pi - 2) / (Real.pi + 2)) := by
    nlinarith [hpi_upper, hatan_correction_lower]
  have hcorrection_relative_upper :
      Real.arctan ((Real.pi - 2) / (Real.pi + 2)) <
        251 * Real.pi / 3600 := by
    nlinarith [hpi_lower, hatan_correction_upper]
  have hangle_radians_lower :
      649 * Real.pi / 3600 < Real.arctan (2 / Real.pi) := by
    nlinarith [hcomplement, hcorrection_relative_upper]
  have hangle_radians_upper :
      Real.arctan (2 / Real.pi) < 651 * Real.pi / 3600 := by
    nlinarith [hcomplement, hcorrection_relative_lower]
  have hdegrees_lower :
      (649 / 20 : ℝ) <
        Real.arctan (2 / Real.pi) * 180 / Real.pi := by
    rw [lt_div_iff₀ Real.pi_pos]
    nlinarith only [hangle_radians_lower]
  have hdegrees_upper :
      Real.arctan (2 / Real.pi) * 180 / Real.pi <
        (651 / 20 : ℝ) := by
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith only [hangle_radians_upper]
  have hdistance_c :
      |Real.arctan (2 / Real.pi) * 180 / Real.pi - (65 / 2 : ℝ)| ≤
        (1 / 20 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith

  refine ⟨hangle, ?_, ?_⟩
  · rw [hangle]
    simpa [MatchesDisplayedPrecision, radiansToDegrees,
      recordedAnswerChoice, AnswerChoice.degrees] using hdistance_c
  · rw [hangle]
    unfold IsUniqueClosestAnswer
    intro other hother
    change
      |Real.arctan (2 / Real.pi) * 180 / Real.pi - (65 / 2 : ℝ)| <
        |Real.arctan (2 / Real.pi) * 180 / Real.pi -
          AnswerChoice.degrees other|
    apply lt_of_le_of_lt hdistance_c
    cases other with
    | A =>
        simp only [AnswerChoice.degrees]
        rw [abs_of_pos (by linarith only [hdegrees_lower])]
        linarith only [hdegrees_lower]
    | B =>
        simp only [AnswerChoice.degrees]
        rw [abs_of_pos (by linarith only [hdegrees_lower])]
        linarith only [hdegrees_lower]
    | C =>
        exact (hother rfl).elim
    | D =>
        simp only [AnswerChoice.degrees]
        rw [abs_of_neg (by linarith only [hdegrees_upper])]
        linarith only [hdegrees_upper]

end PhyXMiniProblems.ProblemPhyXMini0736
