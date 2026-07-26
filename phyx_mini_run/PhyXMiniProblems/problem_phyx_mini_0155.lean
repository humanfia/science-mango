import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0155

open Dimension

/-!
# Direction of a laser ray inside a parallel glass sheet

A laser ray meets a horizontal, `1.0 cm`-thick glass sheet at `30°` above the
surface.  The supplied diagram labels the normal-relative ray angles by
`θ₁`, `θ₂`, `θ₃`, and `θ₄`.  In particular, the printed `30°` arc is measured
from the horizontal surface, whereas all four theta labels are measured from
the vertical interface normals.  Thus the entry incidence angle is `60°`
from the normal.

Sheet thickness is a unit-independent Physlib quantity. Refractive indices
are dimensionless real readouts, and angles are real readouts in radians. The
direction requested by the problem is the in-glass angle `θ₂`, measured from
the entry-face normal.
-/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Read a physical length as a real scalar in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length { UnitChoices.SI with length := unit }).val : ℝ)

/-- The centimeter readout used for the sheet-thickness datum. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Convert an angle readout in degrees to radians. -/
def angleOfDegrees (value : ℝ) : ℝ :=
  value * Real.pi / 180

/-- Convert a radian angle readout to degrees. -/
def angleInDegrees (angleRadians : ℝ) : ℝ :=
  angleRadians * 180 / Real.pi

/-- The three homogeneous regions crossed by the ray in the figure. -/
inductive OpticalRegion where
  | upperAir
  | glassSheet
  | lowerAir
  deriving DecidableEq, Repr

/-- The physical materials occupying the three optical regions. -/
inductive OpticalMaterial where
  | ambientAir
  | glass
  | other
  deriving DecidableEq, Repr

/-- The two parallel faces of the sheet, in propagation order. -/
inductive SheetBoundary where
  | entryFace
  | exitFace
  deriving DecidableEq, Repr

/-- The three straight portions of the depicted laser ray. -/
inductive RaySegment where
  | incidentInUpperAir
  | travelingInGlass
  | emergentInLowerAir
  deriving DecidableEq, Repr

/-- The four normal-relative angle labels printed in the diagram. -/
inductive FigureAngleLabel where
  | thetaOne
  | thetaTwo
  | thetaThree
  | thetaFour
  deriving DecidableEq, Repr

/-- The three refractive-index labels printed in the diagram. -/
inductive FigureIndexLabel where
  | nOneAbove
  | nTwoInGlass
  | nOneBelow
  deriving DecidableEq, Repr

/-- Shapes and orientations needed to distinguish the pictured interfaces. -/
inductive InterfaceGeometry where
  | horizontalPlanar
  | other
  deriving DecidableEq, Repr

/-- Orientations of the dashed normal lines in the source diagram. -/
inductive NormalOrientation where
  | vertical
  | other
  deriving DecidableEq, Repr

/-- Kind of light source named by the problem statement. -/
inductive LightSourceKind where
  | laserBeam
  | other
  deriving DecidableEq, Repr

/-- The optical region containing each displayed ray segment. -/
def raySegmentRegion : RaySegment → OpticalRegion
  | .incidentInUpperAir => .upperAir
  | .travelingInGlass => .glassSheet
  | .emergentInLowerAir => .lowerAir

/-- The interface at which each theta label is drawn. -/
def angleLabelBoundary : FigureAngleLabel → SheetBoundary
  | .thetaOne => .entryFace
  | .thetaTwo => .entryFace
  | .thetaThree => .exitFace
  | .thetaFour => .exitFace

/-- The optical region in which each normal-relative theta angle lies. -/
def angleLabelRegion : FigureAngleLabel → OpticalRegion
  | .thetaOne => .upperAir
  | .thetaTwo => .glassSheet
  | .thetaThree => .glassSheet
  | .thetaFour => .lowerAir

/-- The region to which each displayed refractive-index label is attached. -/
def indexLabelRegion : FigureIndexLabel → OpticalRegion
  | .nOneAbove => .upperAir
  | .nTwoInGlass => .glassSheet
  | .nOneBelow => .lowerAir

/-!
The presence of the boundaries, normals, ray segments, and labels in the
primary image. Their physical roles are supplied by the mappings above.
-/
structure GlassSheetRayFigure where
  showsBoundary : SheetBoundary → Bool
  showsNormal : SheetBoundary → Bool
  showsRaySegment : RaySegment → Bool
  showsAngleLabel : FigureAngleLabel → Bool
  showsIndexLabel : FigureIndexLabel → Bool
  showsThirtyDegreeSurfaceAngle : Bool
  showsGlassRegionShading : Bool

/-!
All physical quantities and figure data for refraction through the sheet.

`incidentAngleAboveSurfaceRadians` is the separately printed `30°` angle from
the horizontal entry face. `angleInRadians` stores `θ₁` through `θ₄`, all
measured from the appropriate normal. No numerical value for `θ₂` is built
into this structure.
-/
structure GlassSheetRefractionSetup where
  sourceKind : LightSourceKind
  sheetThickness : LengthQuantity
  materialAt : OpticalRegion → OpticalMaterial
  refractiveIndex : OpticalRegion → ℝ
  interfaceGeometry : SheetBoundary → InterfaceGeometry
  normalOrientation : SheetBoundary → NormalOrientation
  incidentAngleAboveSurfaceRadians : ℝ
  angleInRadians : FigureAngleLabel → ℝ
  figure : GlassSheetRayFigure

/-- The requested direction in the glass, measured from the entry normal. -/
def travelDirectionInGlassRadians (setup : GlassSheetRefractionSetup) : ℝ :=
  setup.angleInRadians .thetaTwo

/-!
The qualitative scenario: a laser crosses a planar horizontal glass sheet
surrounded by air, with vertical normals to its two parallel faces.
-/
def MatchesProblemScenario (setup : GlassSheetRefractionSetup) : Prop :=
  setup.sourceKind = .laserBeam ∧
    setup.materialAt .upperAir = .ambientAir ∧
    setup.materialAt .glassSheet = .glass ∧
    setup.materialAt .lowerAir = .ambientAir ∧
    (∀ boundary, setup.interfaceGeometry boundary = .horizontalPlanar) ∧
    ∀ boundary, setup.normalOrientation boundary = .vertical

/-!
Primary-image evidence that both faces and normals, all three ray segments,
all four theta labels, all three index labels, and the separate `30°` surface
angle are displayed. It contains no numerical direction for `θ₂`.
-/
def MatchesSuppliedFigure (setup : GlassSheetRefractionSetup) : Prop :=
  (∀ boundary, setup.figure.showsBoundary boundary = true) ∧
    (∀ boundary, setup.figure.showsNormal boundary = true) ∧
    (∀ segment, setup.figure.showsRaySegment segment = true) ∧
    (∀ angle, setup.figure.showsAngleLabel angle = true) ∧
    (∀ index, setup.figure.showsIndexLabel index = true) ∧
    setup.figure.showsThirtyDegreeSurfaceAngle = true ∧
    setup.figure.showsGlassRegionShading = true

/-!
Numerical readouts supplied by the problem and figure: thickness `1.0 cm`,
surface-relative incidence `30°`, ambient-air index `n₁ = 1.00` above and
below, and glass index `n₂ = 1.50`. The requested in-glass angle is absent.
-/
def MatchesProblemAndFigureReadouts
    (setup : GlassSheetRefractionSetup) : Prop :=
  lengthInCentimeters setup.sheetThickness = 1 ∧
    setup.incidentAngleAboveSurfaceRadians = angleOfDegrees 30 ∧
    setup.refractiveIndex .upperAir = 1 ∧
    setup.refractiveIndex .glassSheet = (3 / 2 : ℝ) ∧
    setup.refractiveIndex .lowerAir = 1

/-- A normal-relative interface angle lies on the physical acute branch. -/
def IsPhysicalInterfaceAngle (angleRadians : ℝ) : Prop :=
  angleRadians ∈ Set.Ioo 0 (Real.pi / 2)

/-!
Positivity, optical ordering, and acute branches for the physical ray. These
conditions select the physical inverse-sine solution without assigning a
numerical value or answer choice to the in-glass direction.
-/
def HasPhysicalOpticalParameters
    (setup : GlassSheetRefractionSetup) : Prop :=
  0 < lengthInCentimeters setup.sheetThickness ∧
    (∀ region, 0 < setup.refractiveIndex region) ∧
    setup.refractiveIndex .upperAir < setup.refractiveIndex .glassSheet ∧
    setup.refractiveIndex .lowerAir < setup.refractiveIndex .glassSheet ∧
    IsPhysicalInterfaceAngle setup.incidentAngleAboveSurfaceRadians ∧
    ∀ label, IsPhysicalInterfaceAngle (setup.angleInRadians label)

/-!
Geometry of a ray crossing a parallel-sided sheet. The first relation converts
the printed angle above the horizontal face to the normal-relative angle `θ₁`.
The second says that one straight ray in the glass makes equal angles `θ₂` and
`θ₃` with the parallel vertical normals.
-/
structure SatisfiesParallelSheetRayGeometry
    (setup : GlassSheetRefractionSetup) : Prop where
  incidentAngleComplement :
    setup.angleInRadians .thetaOne =
      Real.pi / 2 - setup.incidentAngleAboveSurfaceRadians
  equalInternalNormalAngles :
    setup.angleInRadians .thetaTwo = setup.angleInRadians .thetaThree

/-!
Snell's law at the entry and exit faces. Every angle is measured from the
corresponding interface normal. These are governing laws, not a formula for
the requested numerical direction.
-/
structure SatisfiesSnellLawAtBothInterfaces
    (setup : GlassSheetRefractionSetup) : Prop where
  entryFaceLaw :
    setup.refractiveIndex .upperAir *
        Real.sin (setup.angleInRadians .thetaOne) =
      setup.refractiveIndex .glassSheet *
        Real.sin (setup.angleInRadians .thetaTwo)
  exitFaceLaw :
    setup.refractiveIndex .glassSheet *
        Real.sin (setup.angleInRadians .thetaThree) =
      setup.refractiveIndex .lowerAir *
        Real.sin (setup.angleInRadians .thetaFour)

/-- Labels of the four displayed multiple-choice directions. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The direction in degrees printed beside each answer label. -/
def displayedDirectionInDegrees : AnswerChoice → ℝ
  | .A => 353 / 10
  | .B => 323 / 10
  | .C => 333 / 10
  | .D => 172 / 10

/-- The source dataset's recorded answer label, retained only as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-!
A modeled direction matches a nearest-tenth-degree choice when its degree
readout is within half of one tenth of a degree of the displayed value.
-/
def MatchesDisplayedDirection
    (setup : GlassSheetRefractionSetup) (choice : AnswerChoice) : Prop :=
  |angleInDegrees (travelDirectionInGlassRadians setup) -
      displayedDirectionInDegrees choice| ≤ (1 / 20 : ℝ)

/-- A displayed direction is the unique nearest-tenth match to the model. -/
def IsUniqueMatchingDisplayedDirection
    (setup : GlassSheetRefractionSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedDirection setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedDirection setup other → other = choice

/-!
The `30°` angle drawn from the horizontal sheet surface is a `60°` incidence
angle from the vertical entry normal.
-/
lemma incidentAngleFromNormal_eq_sixtyDegrees
    (setup : GlassSheetRefractionSetup)
    (h_readouts : MatchesProblemAndFigureReadouts setup)
    (h_geometry : SatisfiesParallelSheetRayGeometry setup) :
    setup.angleInRadians .thetaOne = angleOfDegrees 60 := by
  have h_surface :
      setup.incidentAngleAboveSurfaceRadians = angleOfDegrees 30 :=
    h_readouts.2.1
  rw [h_geometry.incidentAngleComplement, h_surface]
  unfold angleOfDegrees
  ring

/-!
On the acute physical branch, entry-face Snell's law expresses the requested
in-glass direction as the inverse sine of the index-scaled incident sine.
-/
lemma travelDirectionInGlass_eq_arcsinSnell
    (setup : GlassSheetRefractionSetup)
    (h_physical : HasPhysicalOpticalParameters setup)
    (h_snell : SatisfiesSnellLawAtBothInterfaces setup) :
    travelDirectionInGlassRadians setup =
      Real.arcsin
        (setup.refractiveIndex .upperAir /
            setup.refractiveIndex .glassSheet *
          Real.sin (setup.angleInRadians .thetaOne)) := by
  have h_glass_pos : 0 < setup.refractiveIndex .glassSheet :=
    h_physical.2.1 .glassSheet
  have h_glass_ne : setup.refractiveIndex .glassSheet ≠ 0 :=
    ne_of_gt h_glass_pos
  have h_sin :
      setup.refractiveIndex .upperAir /
            setup.refractiveIndex .glassSheet *
          Real.sin (setup.angleInRadians .thetaOne) =
        Real.sin (setup.angleInRadians .thetaTwo) := by
    calc
      setup.refractiveIndex .upperAir /
              setup.refractiveIndex .glassSheet *
            Real.sin (setup.angleInRadians .thetaOne) =
          (setup.refractiveIndex .upperAir *
            Real.sin (setup.angleInRadians .thetaOne)) /
              setup.refractiveIndex .glassSheet := by ring
      _ = (setup.refractiveIndex .glassSheet *
            Real.sin (setup.angleInRadians .thetaTwo)) /
              setup.refractiveIndex .glassSheet := by
        rw [h_snell.entryFaceLaw]
      _ = Real.sin (setup.angleInRadians .thetaTwo) := by
        field_simp
  have h_theta_two :
      IsPhysicalInterfaceAngle (setup.angleInRadians .thetaTwo) :=
    h_physical.2.2.2.2.2 .thetaTwo
  rw [travelDirectionInGlassRadians, h_sin]
  symm
  exact Real.arcsin_sin
    (by
      unfold IsPhysicalInterfaceAngle at h_theta_two
      nlinarith [h_theta_two.1, Real.pi_pos])
    (by
      unfold IsPhysicalInterfaceAngle at h_theta_two
      exact h_theta_two.2.le)

/-!
Because glass has the larger refractive index, the refracted ray bends toward
the normal: its normal-relative direction is smaller than `θ₁`.
-/
lemma travelDirectionInGlass_lt_incidentAngle
    (setup : GlassSheetRefractionSetup)
    (h_physical : HasPhysicalOpticalParameters setup)
    (h_snell : SatisfiesSnellLawAtBothInterfaces setup) :
    travelDirectionInGlassRadians setup <
      setup.angleInRadians .thetaOne := by
  have h_air_pos : 0 < setup.refractiveIndex .upperAir :=
    h_physical.2.1 .upperAir
  have h_glass_pos : 0 < setup.refractiveIndex .glassSheet :=
    h_physical.2.1 .glassSheet
  have h_index_lt :
      setup.refractiveIndex .upperAir <
        setup.refractiveIndex .glassSheet :=
    h_physical.2.2.1
  have h_glass_ne : setup.refractiveIndex .glassSheet ≠ 0 :=
    ne_of_gt h_glass_pos
  have h_sin :
      setup.refractiveIndex .upperAir /
            setup.refractiveIndex .glassSheet *
          Real.sin (setup.angleInRadians .thetaOne) =
        Real.sin (setup.angleInRadians .thetaTwo) := by
    calc
      setup.refractiveIndex .upperAir /
              setup.refractiveIndex .glassSheet *
            Real.sin (setup.angleInRadians .thetaOne) =
          (setup.refractiveIndex .upperAir *
            Real.sin (setup.angleInRadians .thetaOne)) /
              setup.refractiveIndex .glassSheet := by ring
      _ = (setup.refractiveIndex .glassSheet *
            Real.sin (setup.angleInRadians .thetaTwo)) /
              setup.refractiveIndex .glassSheet := by
        rw [h_snell.entryFaceLaw]
      _ = Real.sin (setup.angleInRadians .thetaTwo) := by
        field_simp
  have h_theta_one :
      IsPhysicalInterfaceAngle (setup.angleInRadians .thetaOne) :=
    h_physical.2.2.2.2.2 .thetaOne
  have h_theta_two :
      IsPhysicalInterfaceAngle (setup.angleInRadians .thetaTwo) :=
    h_physical.2.2.2.2.2 .thetaTwo
  unfold IsPhysicalInterfaceAngle at h_theta_one h_theta_two
  have h_sin_theta_one_pos :
      0 < Real.sin (setup.angleInRadians .thetaOne) :=
    Real.sin_pos_of_pos_of_lt_pi h_theta_one.1
      (by nlinarith [h_theta_one.2, Real.pi_pos])
  have h_ratio_lt_one :
      setup.refractiveIndex .upperAir /
          setup.refractiveIndex .glassSheet < 1 :=
    (div_lt_one h_glass_pos).2 h_index_lt
  have h_sin_lt :
      Real.sin (setup.angleInRadians .thetaTwo) <
        Real.sin (setup.angleInRadians .thetaOne) := by
    calc
      Real.sin (setup.angleInRadians .thetaTwo) =
          setup.refractiveIndex .upperAir /
              setup.refractiveIndex .glassSheet *
            Real.sin (setup.angleInRadians .thetaOne) :=
        h_sin.symm
      _ < 1 * Real.sin (setup.angleInRadians .thetaOne) :=
        mul_lt_mul_of_pos_right h_ratio_lt_one h_sin_theta_one_pos
      _ = Real.sin (setup.angleInRadians .thetaOne) := one_mul _
  unfold travelDirectionInGlassRadians
  exact
    (Real.strictMonoOn_sin.lt_iff_lt
      ⟨by nlinarith [h_theta_two.1, Real.pi_pos], h_theta_two.2.le⟩
      ⟨by nlinarith [h_theta_one.1, Real.pi_pos], h_theta_one.2.le⟩).1
      h_sin_lt

/-!
With `θ₁ = 60°`, `n_air = 1`, and `n_glass = 3/2`, Snell's law gives the
exact unrounded in-glass direction `arcsin (√3 / 3)` from the normal.
-/
lemma travelDirectionInGlass_eq_exactValue
    (setup : GlassSheetRefractionSetup)
    (h_readouts : MatchesProblemAndFigureReadouts setup)
    (h_physical : HasPhysicalOpticalParameters setup)
    (h_geometry : SatisfiesParallelSheetRayGeometry setup)
    (h_snell : SatisfiesSnellLawAtBothInterfaces setup) :
    travelDirectionInGlassRadians setup =
      Real.arcsin (Real.sqrt 3 / 3) := by
  have h_theta_one :=
    incidentAngleFromNormal_eq_sixtyDegrees setup h_readouts h_geometry
  have h_direction :=
    travelDirectionInGlass_eq_arcsinSnell setup h_physical h_snell
  rw [h_direction]
  have h_air : setup.refractiveIndex .upperAir = 1 :=
    h_readouts.2.2.1
  have h_glass :
      setup.refractiveIndex .glassSheet = (3 / 2 : ℝ) :=
    h_readouts.2.2.2.1
  rw [h_air, h_glass, h_theta_one]
  congr 1
  rw [show angleOfDegrees 60 = Real.pi / 3 by
    unfold angleOfDegrees
    ring, Real.sin_pi_div_three]
  ring

/-!
The laser therefore travels through the glass at
`arcsin (√3 / 3) ≈ 35.264°` from the normal, which uniquely rounds to
`35.3°`, answer A. The `1.0 cm` thickness affects the lateral displacement
and second-interface location, but not this direction inside the homogeneous
glass.

This formalizes `thm:physics:phyx_mini_0155:target`.
-/
theorem problem_phyx_mini_0155
    (setup : GlassSheetRefractionSetup)
    (_h_scenario : MatchesProblemScenario setup)
    (_h_figure : MatchesSuppliedFigure setup)
    (h_readouts : MatchesProblemAndFigureReadouts setup)
    (h_physical : HasPhysicalOpticalParameters setup)
    (h_geometry : SatisfiesParallelSheetRayGeometry setup)
    (h_snell : SatisfiesSnellLawAtBothInterfaces setup) :
    travelDirectionInGlassRadians setup =
        Real.arcsin (Real.sqrt 3 / 3) ∧
      IsUniqueMatchingDisplayedDirection setup .A := by
  set_option maxHeartbeats 800000 in
    have h_exact :=
      travelDirectionInGlass_eq_exactValue setup h_readouts h_physical
        h_geometry h_snell
    refine ⟨h_exact, ?_⟩

    /-
    This local estimate is the imaginary-part consequence of the ninth-order
    remainder bound for the complex exponential.  It supplies enough
    precision for both the local bound on `π` and the nearest-tenth check.
    -/
    have sin_taylor_bound (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1) :
        |Real.sin x -
            (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040)| ≤
          x ^ 9 * (10 / ((Nat.factorial 9 : ℝ) * 9)) := by
      let z : ℂ := (x : ℂ) * Complex.I
      have hz : ‖z‖ ≤ 1 := by
        dsimp [z]
        simpa [abs_of_nonneg hx0] using hx
      have h_exp := Complex.exp_bound hz (n := 9) (by norm_num)
      have h_im := (Complex.abs_im_le_norm
        (Complex.exp z - ∑ m ∈ Finset.range 9,
          z ^ m / (m.factorial : ℂ))).trans h_exp
      dsimp [z] at h_im
      norm_num [Finset.sum_range_succ, Complex.exp_ofReal_mul_I_im,
        Complex.exp_mul_I, Complex.sin_ofReal_re, Nat.factorial, pow_succ,
        abs_of_nonneg hx0] at h_im
      calc
        |Real.sin x -
            (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040)| =
            |Real.sin x -
                (x + -(x * x * x) / 6 + x * x * x * x * x / 120 +
                -(x * x * x * x * x * x * x) / 5040)| := by
                  congr 1
                  ring
        _ ≤ x * x * x * x * x * x * x * x * x * (1 / 326592) :=
          h_im
        _ = x ^ 9 * (10 / ((Nat.factorial 9 : ℝ) * 9)) := by
          norm_num
          ring

    have h_sin_below_half :
        Real.sin (6283 / 12000 : ℝ) < (1 / 2 : ℝ) := by
      have hb :=
        sin_taylor_bound (6283 / 12000 : ℝ) (by norm_num) (by norm_num)
      rw [abs_le] at hb
      norm_num at hb ⊢
      linarith
    have h_half_below_sin :
        (1 / 2 : ℝ) < Real.sin (1309 / 2500 : ℝ) := by
      have hb :=
        sin_taylor_bound (1309 / 2500 : ℝ) (by norm_num) (by norm_num)
      rw [abs_le] at hb
      norm_num at hb ⊢
      linarith
    have h_pi_six_mem :
        Real.pi / 6 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith only [Real.pi_pos]
    have h_pi_lower_test_mem :
        (6283 / 12000 : ℝ) ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith only [Real.one_le_pi_div_two]
    have h_pi_upper_test_mem :
        (1309 / 2500 : ℝ) ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith only [Real.one_le_pi_div_two]
    have h_pi_lower : (6283 / 2000 : ℝ) < Real.pi := by
      by_contra h
      have h_angle :
          Real.pi / 6 ≤ (6283 / 12000 : ℝ) := by
        nlinarith only [le_of_not_gt h]
      have h_sine :=
        Real.strictMonoOn_sin.monotoneOn h_pi_six_mem
          h_pi_lower_test_mem h_angle
      rw [Real.sin_pi_div_six] at h_sine
      nlinarith
    have h_pi_upper : Real.pi < (3927 / 1250 : ℝ) := by
      by_contra h
      have h_angle :
          (1309 / 2500 : ℝ) ≤ Real.pi / 6 := by
        nlinarith only [le_of_not_gt h]
      have h_sine :=
        Real.strictMonoOn_sin.monotoneOn h_pi_upper_test_mem
          h_pi_six_mem h_angle
      rw [Real.sin_pi_div_six] at h_sine
      nlinarith

    have h_sqrt_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
    have h_sqrt_sq : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have h_sqrt_lower : (1732 / 1000 : ℝ) ≤ Real.sqrt 3 := by
      nlinarith
    have h_sqrt_upper : Real.sqrt 3 ≤ (1733 / 1000 : ℝ) := by
      nlinarith

    have h_sin_lower_endpoint :
        Real.sin (47 * Real.pi / 240) ≤ Real.sqrt 3 / 3 := by
      let x : ℝ := 47 * Real.pi / 240
      have hx_nonneg : 0 ≤ x := by
        dsimp [x]
        positivity
      have hx_le_one : x ≤ 1 := by
        dsimp [x]
        nlinarith only [Real.pi_le_four]
      have hx_lower : (61521 / 100000 : ℝ) ≤ x := by
        dsimp [x]
        nlinarith only [h_pi_lower]
      have hx_upper : x ≤ (61523 / 100000 : ℝ) := by
        dsimp [x]
        nlinarith only [h_pi_upper]
      have hx3_lower : (61521 / 100000 : ℝ) ^ 3 ≤ x ^ 3 :=
        pow_le_pow_left₀ (by norm_num) hx_lower 3
      have hx5_upper : x ^ 5 ≤ (61523 / 100000 : ℝ) ^ 5 :=
        pow_le_pow_left₀ hx_nonneg hx_upper 5
      have hx7_nonneg : 0 ≤ x ^ 7 := by positivity
      have hx9_upper : x ^ 9 ≤ (61523 / 100000 : ℝ) ^ 9 :=
        pow_le_pow_left₀ hx_nonneg hx_upper 9
      have hb := sin_taylor_bound x hx_nonneg hx_le_one
      rw [abs_le] at hb
      have h_sin_upper : Real.sin x ≤ (5772 / 10000 : ℝ) := by
        norm_num [Nat.factorial] at hb
        nlinarith only [hb.2, hx_upper, hx3_lower, hx5_upper,
          hx7_nonneg, hx9_upper]
      dsimp [x] at h_sin_upper
      nlinarith only [h_sin_upper, h_sqrt_lower]

    have h_sin_upper_endpoint :
        Real.sqrt 3 / 3 ≤ Real.sin (707 * Real.pi / 3600) := by
      let x : ℝ := 707 * Real.pi / 3600
      have hx_nonneg : 0 ≤ x := by
        dsimp [x]
        positivity
      have hx_le_one : x ≤ 1 := by
        dsimp [x]
        nlinarith only [Real.pi_le_four]
      have hx_lower : (61695 / 100000 : ℝ) ≤ x := by
        dsimp [x]
        nlinarith only [h_pi_lower]
      have hx_upper : x ≤ (61698 / 100000 : ℝ) := by
        dsimp [x]
        nlinarith only [h_pi_upper]
      have hx3_upper : x ^ 3 ≤ (61698 / 100000 : ℝ) ^ 3 :=
        pow_le_pow_left₀ hx_nonneg hx_upper 3
      have hx5_nonneg : 0 ≤ x ^ 5 := by positivity
      have hx7_upper : x ^ 7 ≤ (61698 / 100000 : ℝ) ^ 7 :=
        pow_le_pow_left₀ hx_nonneg hx_upper 7
      have hx9_upper : x ^ 9 ≤ (61698 / 100000 : ℝ) ^ 9 :=
        pow_le_pow_left₀ hx_nonneg hx_upper 9
      have hb := sin_taylor_bound x hx_nonneg hx_le_one
      rw [abs_le] at hb
      have h_sin_lower : (5777 / 10000 : ℝ) ≤ Real.sin x := by
        norm_num [Nat.factorial] at hb
        nlinarith only [hb.1, hx_lower, hx3_upper, hx5_nonneg,
          hx7_upper, hx9_upper]
      dsimp [x] at h_sin_lower
      nlinarith only [h_sin_lower, h_sqrt_upper]

    have h_lower_angle_mem :
        (47 * Real.pi / 240 : ℝ) ∈
          Set.Ioc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith only [Real.pi_pos]
    have h_upper_angle_mem :
        (707 * Real.pi / 3600 : ℝ) ∈
          Set.Ico (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith only [Real.pi_pos]
    have h_arcsin_lower :
        47 * Real.pi / 240 ≤ Real.arcsin (Real.sqrt 3 / 3) :=
      (Real.le_arcsin_iff_sin_le' h_lower_angle_mem).2
        h_sin_lower_endpoint
    have h_arcsin_upper :
        Real.arcsin (Real.sqrt 3 / 3) ≤ 707 * Real.pi / 3600 :=
      (Real.arcsin_le_iff_le_sin' h_upper_angle_mem).2
        h_sin_upper_endpoint
    have h_degree_lower :
        (141 / 4 : ℝ) ≤
          Real.arcsin (Real.sqrt 3 / 3) * 180 / Real.pi := by
      apply (le_div_iff₀ Real.pi_pos).2
      nlinarith only [h_arcsin_lower]
    have h_degree_upper :
        Real.arcsin (Real.sqrt 3 / 3) * 180 / Real.pi ≤
          (707 / 20 : ℝ) := by
      apply (div_le_iff₀ Real.pi_pos).2
      nlinarith only [h_arcsin_upper]

    have h_matches_a : MatchesDisplayedDirection setup .A := by
      unfold MatchesDisplayedDirection
      rw [h_exact]
      unfold angleInDegrees displayedDirectionInDegrees
      rw [abs_le]
      constructor <;> norm_num <;>
        nlinarith only [h_degree_lower, h_degree_upper]
    refine ⟨h_matches_a, ?_⟩
    intro other h_other
    unfold MatchesDisplayedDirection at h_other
    rw [h_exact] at h_other
    unfold angleInDegrees at h_other
    cases other with
    | A => rfl
    | B =>
        simp only [displayedDirectionInDegrees] at h_other
        rw [abs_le] at h_other
        norm_num at h_other
        exfalso
        nlinarith only [h_degree_lower, h_other.2]
    | C =>
        simp only [displayedDirectionInDegrees] at h_other
        rw [abs_le] at h_other
        norm_num at h_other
        exfalso
        nlinarith only [h_degree_lower, h_other.2]
    | D =>
        simp only [displayedDirectionInDegrees] at h_other
        rw [abs_le] at h_other
        norm_num at h_other
        exfalso
        nlinarith only [h_degree_lower, h_other.2]

end PhyXMiniProblems.ProblemPhyXMini0155
