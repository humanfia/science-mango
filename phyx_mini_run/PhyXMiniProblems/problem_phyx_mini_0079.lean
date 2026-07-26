import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0079

open Dimension

/-!
# Bragg diffraction from a rotated NaCl crystal

An X-ray beam meets the horizontal family of reflecting planes in an NaCl
crystal at an initial glancing angle of `45°`.  The plane spacing is
`0.252 nm`, while the wavelength is `0.125 nm`.  Counterclockwise rotation of
the crystal increases the glancing angle.  The problem asks for the larger
positive rotation at which Bragg diffraction occurs.

Lengths below use Physlib's dimension-carrying quantities.  Real numbers are
used only for dimensionless angle readouts (in radians), integer diffraction
orders, and scalar readings in a specified unit.
-/

/-- A physical length independent of the unit chosen to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices whose length unit is the nanometer used in the problem. -/
noncomputable def nanometerUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.nanometers }

/-- The scalar nanometer readout of a physical length. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  (length nanometerUnitChoices).val

/-- Convert a degree readout into the radian scalar expected by `Real.sin`. -/
def degreesToRadians (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/-- Convert a radian scalar into a degree readout. -/
def radiansToDegrees (radians : ℝ) : ℝ :=
  radians * 180 / Real.pi

/-- The kind of incident radiation distinguished in this problem. -/
inductive RadiationKind where
  | xRay
  deriving DecidableEq, Repr

/-- The crystal material named in the problem. -/
inductive CrystalMaterial where
  | sodiumChloride
  deriving DecidableEq, Repr

/-- The orientation of the axis about which the crystal is turned. -/
inductive RotationAxisOrientation where
  | perpendicularToPage
  deriving DecidableEq, Repr

/-- The three parallel horizontal lines explicitly drawn in the primary figure. -/
inductive CrystalPlaneLabel where
  | topFace
  | firstReflectingPlane
  | secondReflectingPlane
  deriving DecidableEq, Repr

/--
Physical quantities, labeled figure geometry, and the experimental maximum
predicate for the rotating-crystal setup.

`rotationRadians` is positive for counterclockwise rotation.  The function
`glancingAngleAfterCounterclockwiseRotation` records the acute angle between
the incident beam and the rotated reflecting planes; it is not defined here in
terms of the unknown answer.
-/
structure XRayCrystalDiffractionSetup where
  radiationKind : RadiationKind
  crystalMaterial : CrystalMaterial
  rotationAxisOrientation : RotationAxisOrientation
  wavelength : LengthQuantity
  reflectingPlaneSeparation : LengthQuantity
  planeOrientationRadians : CrystalPlaneLabel → ℝ
  initialGlancingAngleRadians : ℝ
  glancingAngleAfterCounterclockwiseRotation : ℝ → ℝ
  isDiffractionMaximum : ℝ → Prop

/--
The problem-statement and primary-figure readouts.  The primary image shows
`θ` between the incident ray and the horizontal top face, and all three drawn
planes are parallel.  No value of the requested rotation occurs here.
-/
structure MatchesProblemAndFigureReadouts
    (setup : XRayCrystalDiffractionSetup) : Prop where
  radiation_is_xray : setup.radiationKind = .xRay
  crystal_is_nacl : setup.crystalMaterial = .sodiumChloride
  rotation_axis_is_perpendicular_to_page :
    setup.rotationAxisOrientation = .perpendicularToPage
  wavelength_readout_nm : lengthInNanometers setup.wavelength = 0.125
  reflecting_plane_separation_readout_nm :
    lengthInNanometers setup.reflectingPlaneSeparation = 0.252
  initial_glancing_angle_readout :
    setup.initialGlancingAngleRadians = degreesToRadians 45
  top_and_first_plane_are_parallel :
    setup.planeOrientationRadians .topFace =
      setup.planeOrientationRadians .firstReflectingPlane
  first_and_second_plane_are_parallel :
    setup.planeOrientationRadians .firstReflectingPlane =
      setup.planeOrientationRadians .secondReflectingPlane

/--
Counterclockwise rotation through `φ` increases the glancing angle from `θ`
to `θ + φ`, as read from the primary figure.
-/
def SatisfiesCounterclockwiseRotationGeometry
    (setup : XRayCrystalDiffractionSetup) : Prop :=
  ∀ rotationRadians : ℝ,
    0 ≤ rotationRadians →
      setup.glancingAngleAfterCounterclockwiseRotation rotationRadians =
        setup.initialGlancingAngleRadians + rotationRadians

/--
The order-`n` Bragg relation `2 d sin(α) = n λ`, required in every unit system.
Both sides are scalar readouts of physical lengths in the same chosen unit.
-/
def IsBraggMaximumOfOrder
    (setup : XRayCrystalDiffractionSetup)
    (order : ℕ) (rotationRadians : ℝ) : Prop :=
  0 < order ∧
    ∀ units : UnitChoices,
      2 * (setup.reflectingPlaneSeparation units).val *
          Real.sin
            (setup.glancingAngleAfterCounterclockwiseRotation rotationRadians) =
        (order : ℝ) * (setup.wavelength units).val

/--
Ideal Bragg diffraction is the governing physical law: a rotation gives a
maximum exactly when the relation holds for some positive integer order.
-/
def SatisfiesIdealBraggDiffractionLaw
    (setup : XRayCrystalDiffractionSetup) : Prop :=
  ∀ rotationRadians : ℝ,
    setup.isDiffractionMaximum rotationRadians ↔
      ∃ order : ℕ, IsBraggMaximumOfOrder setup order rotationRadians

/--
A physically admissible counterclockwise solution on the acute glancing-angle
branch.  This branch contains the positive maxima reached from the pictured
`45°` starting configuration before the planes become perpendicular to the
incident beam.
-/
def IsAdmissibleCounterclockwiseMaximum
    (setup : XRayCrystalDiffractionSetup) (rotationRadians : ℝ) : Prop :=
  0 < rotationRadians ∧
    0 < setup.glancingAngleAfterCounterclockwiseRotation rotationRadians ∧
    setup.glancingAngleAfterCounterclockwiseRotation rotationRadians ≤
      Real.pi / 2 ∧
    setup.isDiffractionMaximum rotationRadians

/-- The selected rotation is the largest admissible counterclockwise maximum. -/
def IsLargerCounterclockwiseMaximum
    (setup : XRayCrystalDiffractionSetup) (rotationRadians : ℝ) : Prop :=
  IsAdmissibleCounterclockwiseMaximum setup rotationRadians ∧
    ∀ otherRotationRadians : ℝ,
      IsAdmissibleCounterclockwiseMaximum setup otherRotationRadians →
        otherRotationRadians ≤ rotationRadians

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The counterclockwise rotation in degrees printed beside each answer. -/
def AnswerChoice.rotationDegrees : AnswerChoice → ℝ
  | .A => 31.0
  | .B => 48.0
  | .C => 37.8
  | .D => 41.4

/-- Agreement with a one-decimal-place degree readout, to the nearest tenth. -/
def RoundsToNearestTenthDegree
    (rotationRadians displayedDegrees : ℝ) : Prop :=
  |radiansToDegrees rotationRadians - displayedDegrees| ≤ (1 : ℝ) / 20

/-- A physical rotation rounds to the degree readout of a displayed answer. -/
def MatchesAnswer (rotationRadians : ℝ) (choice : AnswerChoice) : Prop :=
  RoundsToNearestTenthDegree rotationRadians choice.rotationDegrees

/--
The larger admissible branch is the fourth-order Bragg maximum.  Its exact
rotation is the fourth-order Bragg angle minus the initial glancing angle.
This is a derived intermediate result, not a supplied readout.
-/
lemma larger_counterclockwise_rotation_formula
    (setup : XRayCrystalDiffractionSetup)
    (h_readouts : MatchesProblemAndFigureReadouts setup)
    (h_geometry : SatisfiesCounterclockwiseRotationGeometry setup)
    (h_bragg : SatisfiesIdealBraggDiffractionLaw setup) :
    ∃ rotationRadians : ℝ,
      IsLargerCounterclockwiseMaximum setup rotationRadians ∧
        rotationRadians =
          Real.arcsin
              ((4 : ℝ) * lengthInNanometers setup.wavelength /
                (2 * lengthInNanometers setup.reflectingPlaneSeparation)) -
            setup.initialGlancingAngleRadians := by
  let ratio : ℝ :=
    (4 : ℝ) * lengthInNanometers setup.wavelength /
      (2 * lengthInNanometers setup.reflectingPlaneSeparation)
  let rotationRadians : ℝ :=
    Real.arcsin ratio - setup.initialGlancingAngleRadians
  have hratio : ratio = (125 : ℝ) / 126 := by
    dsimp [ratio]
    rw [h_readouts.wavelength_readout_nm,
      h_readouts.reflecting_plane_separation_readout_nm]
    norm_num
  have hratio_mem : ratio ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [hratio]
    norm_num
  have hinitial_lt_arcsin :
      setup.initialGlancingAngleRadians < Real.arcsin ratio := by
    rw [h_readouts.initial_glancing_angle_readout, degreesToRadians]
    have hpi_four_mem :
        Real.pi / 4 ∈ Set.Ico (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith [Real.pi_pos]
    have hdegrees : 45 * Real.pi / 180 = Real.pi / 4 := by ring
    rw [hdegrees]
    apply (Real.lt_arcsin_iff_sin_lt' hpi_four_mem).2
    rw [Real.sin_pi_div_four, hratio]
    nlinarith [Real.sqrt_two_lt_three_halves]
  have hrotation_pos : 0 < rotationRadians := by
    dsimp [rotationRadians]
    exact sub_pos.mpr hinitial_lt_arcsin
  have hangle :
      setup.glancingAngleAfterCounterclockwiseRotation rotationRadians =
        Real.arcsin ratio := by
    rw [h_geometry rotationRadians hrotation_pos.le]
    dsimp [rotationRadians]
    ring
  have hscale (q : LengthQuantity) (units : UnitChoices) :
      (q units).val =
        (nanometerUnitChoices.dimScale units L𝓭 : ℝ) *
          (q nanometerUnitChoices).val := by
    have hq := congrArg WithDim.val (q.property nanometerUnitChoices units)
    simpa [WithDim.smul_val, NNReal.smul_def, smul_eq_mul] using hq
  refine ⟨rotationRadians, ?_, rfl⟩
  constructor
  · refine ⟨hrotation_pos, ?_, ?_, ?_⟩
    · rw [hangle]
      exact Real.arcsin_pos.mpr (by rw [hratio]; norm_num)
    · rw [hangle]
      exact Real.arcsin_le_pi_div_two ratio
    · apply (h_bragg rotationRadians).2
      refine ⟨4, ?_⟩
      constructor
      · norm_num
      · intro units
        rw [hangle, Real.sin_arcsin hratio_mem.1 hratio_mem.2]
        rw [hscale setup.reflectingPlaneSeparation units,
          hscale setup.wavelength units]
        change
          2 *
              ((nanometerUnitChoices.dimScale units L𝓭 : ℝ) *
                lengthInNanometers setup.reflectingPlaneSeparation) *
              ratio =
            (4 : ℝ) *
              ((nanometerUnitChoices.dimScale units L𝓭 : ℝ) *
                lengthInNanometers setup.wavelength)
        rw [h_readouts.reflecting_plane_separation_readout_nm,
          h_readouts.wavelength_readout_nm, hratio]
        ring
  · intro otherRotationRadians hother
    rcases hother with
      ⟨hother_pos, hother_angle_pos, hother_angle_le, hother_maximum⟩
    have hother_angle :
        setup.glancingAngleAfterCounterclockwiseRotation otherRotationRadians =
          setup.initialGlancingAngleRadians + otherRotationRadians :=
      h_geometry otherRotationRadians hother_pos.le
    rcases (h_bragg otherRotationRadians).1 hother_maximum with
      ⟨order, horder_pos, horder_relation⟩
    have hrelation_nm := horder_relation nanometerUnitChoices
    change
      2 * lengthInNanometers setup.reflectingPlaneSeparation *
          Real.sin
            (setup.glancingAngleAfterCounterclockwiseRotation
              otherRotationRadians) =
        (order : ℝ) * lengthInNanometers setup.wavelength at hrelation_nm
    rw [h_readouts.reflecting_plane_separation_readout_nm,
      h_readouts.wavelength_readout_nm] at hrelation_nm
    have horder_lt_five_real : (order : ℝ) < 5 := by
      nlinarith
        [Real.sin_le_one
          (setup.glancingAngleAfterCounterclockwiseRotation
            otherRotationRadians)]
    have horder_lt_five : order < 5 := by
      exact_mod_cast horder_lt_five_real
    have horder_le_four : order ≤ 4 := by omega
    have horder_le_four_real : (order : ℝ) ≤ 4 := by
      exact_mod_cast horder_le_four
    have hsin_le_ratio :
        Real.sin
            (setup.glancingAngleAfterCounterclockwiseRotation
              otherRotationRadians) ≤ ratio := by
      rw [hratio]
      nlinarith
    have hother_angle_mem :
        setup.glancingAngleAfterCounterclockwiseRotation otherRotationRadians ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · nlinarith [Real.pi_pos]
      · exact hother_angle_le
    have hangle_le_arcsin :
        setup.glancingAngleAfterCounterclockwiseRotation otherRotationRadians ≤
          Real.arcsin ratio :=
      (Real.le_arcsin_iff_sin_le hother_angle_mem hratio_mem).2 hsin_le_ratio
    dsimp [rotationRadians]
    linarith

/--
The larger counterclockwise Bragg rotation rounds to `37.8°`, which is answer
choice C.

This formalizes `thm:physics:phyx_mini_0079:target`.
-/
theorem problem_phyx_mini_0079
    (setup : XRayCrystalDiffractionSetup)
    (h_readouts : MatchesProblemAndFigureReadouts setup)
    (h_geometry : SatisfiesCounterclockwiseRotationGeometry setup)
    (h_bragg : SatisfiesIdealBraggDiffractionLaw setup) :
    ∃ rotationRadians : ℝ,
      IsLargerCounterclockwiseMaximum setup rotationRadians ∧
        RoundsToNearestTenthDegree rotationRadians 37.8 ∧
          MatchesAnswer rotationRadians .C := by
  rcases larger_counterclockwise_rotation_formula setup h_readouts h_geometry h_bragg with
    ⟨rotationRadians, hrotation_larger, hrotation_formula⟩
  let angle : ℝ := Real.arcsin ((125 : ℝ) / 126)
  have hangle_mem : angle ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    exact Real.arcsin_mem_Icc ((125 : ℝ) / 126)
  have hratio_mem : (125 : ℝ) / 126 ∈ Set.Icc (-1 : ℝ) 1 := by
    norm_num
  have hsqrt1_upper : Real.sqrt 2 ≤ (338 : ℝ) / 239 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hsqrt2_upper :
      Real.sqrt (2 + Real.sqrt 2) ≤ (704 : ℝ) / 381 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith
  have hsqrt3_upper :
      Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) ≤
        (1940 : ℝ) / 989 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith
  have hsqrt4_upper :
      Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) ≤
        (1447 : ℝ) / 727 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith
  have hsqrt1_lower : (41 : ℝ) / 29 ≤ Real.sqrt 2 := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hsqrt2_lower :
      (109 : ℝ) / 59 ≤ Real.sqrt (2 + Real.sqrt 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hsqrt3_lower :
      (865 : ℝ) / 441 ≤
        Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hsqrt4_lower :
      (412 : ℝ) / 207 ≤
        Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hseries_upper :
      Real.sqrtTwoAddSeries 0 4 ≤
        2 - (((157 : ℝ) / 50) / 32) ^ 2 := by
    have hseries :
        Real.sqrtTwoAddSeries 0 4 ≤ (1447 : ℝ) / 727 := by
      simpa [Real.sqrtTwoAddSeries] using hsqrt4_upper
    calc
      Real.sqrtTwoAddSeries 0 4 ≤ (1447 : ℝ) / 727 := hseries
      _ ≤ 2 - (((157 : ℝ) / 50) / 32) ^ 2 := by norm_num
  have hseries_lower :
      2 - ((((63 : ℝ) / 20 - 1 / 256) / 32) ^ 2) ≤
        Real.sqrtTwoAddSeries 0 4 := by
    have hseries :
        (412 : ℝ) / 207 ≤ Real.sqrtTwoAddSeries 0 4 := by
      simpa [Real.sqrtTwoAddSeries] using hsqrt4_lower
    calc
      2 - ((((63 : ℝ) / 20 - 1 / 256) / 32) ^ 2) ≤
          (412 : ℝ) / 207 := by norm_num
      _ ≤ Real.sqrtTwoAddSeries 0 4 := hseries
  let smallAngle : ℝ := Real.pi / 64
  have hsmall_pos : 0 < smallAngle := by
    dsimp [smallAngle]
    positivity
  have hsmall_le_one : smallAngle ≤ 1 := by
    dsimp [smallAngle]
    nlinarith [Real.pi_le_four]
  have hsmall_le_sixteenth : smallAngle ≤ (1 : ℝ) / 16 := by
    dsimp [smallAngle]
    nlinarith [Real.pi_le_four]
  have hsmall_four_le_three : smallAngle ^ 4 ≤ smallAngle ^ 3 := by
    calc
      smallAngle ^ 4 = smallAngle ^ 3 * smallAngle := by ring
      _ ≤ smallAngle ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left hsmall_le_one (by positivity)
      _ = smallAngle ^ 3 := by ring
  have hsmall_sin_bound :=
    Real.sin_bound
      (show |smallAngle| ≤ 1 by
        rw [abs_of_pos hsmall_pos]
        exact hsmall_le_one)
  rw [abs_of_pos hsmall_pos] at hsmall_sin_bound
  have hsin_small_lt : Real.sin smallAngle < smallAngle := by
    have hupper := (abs_sub_le_iff.mp hsmall_sin_bound).1
    nlinarith [pow_pos hsmall_pos 3]
  have hsin_small_gt :
      smallAngle - smallAngle ^ 3 / 4 < Real.sin smallAngle := by
    have hlower := (abs_sub_le_iff.mp hsmall_sin_bound).2
    nlinarith [pow_pos hsmall_pos 3]
  have hsin_small_exact :
      Real.sin smallAngle =
        Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) / 2 := by
    dsimp [smallAngle]
    convert Real.sin_pi_over_two_pow_succ 4 using 1 <;> norm_num
  have hradicand_nonneg :
      0 ≤ 2 - Real.sqrtTwoAddSeries 0 4 := by
    linarith [Real.sqrtTwoAddSeries_lt_two 4]
  have hsqrt_series_lower :
      ((157 : ℝ) / 50) / 32 ≤
        Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) := by
    apply (Real.le_sqrt (by norm_num) hradicand_nonneg).2
    nlinarith
  have hpi_lower : (157 : ℝ) / 50 < Real.pi := by
    have hroot_lt :
        Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) / 2 <
          Real.pi / 64 := by
      calc
        Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) / 2 =
            Real.sin smallAngle := hsin_small_exact.symm
        _ < smallAngle := hsin_small_lt
        _ = Real.pi / 64 := rfl
    nlinarith only [hsqrt_series_lower, hroot_lt]
  have hsqrt_series_upper :
      Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) ≤
        (((63 : ℝ) / 20 - 1 / 256) / 32) := by
    apply (Real.sqrt_le_left (by norm_num)).2
    nlinarith
  have hsmall_cube_le :
      smallAngle ^ 3 ≤ ((1 : ℝ) / 16) ^ 3 := by
    gcongr
  have hpi_upper : Real.pi < (63 : ℝ) / 20 := by
    have hsmall_estimate :
        smallAngle <
          Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) / 2 +
            (1 : ℝ) / 16384 := by
      rw [← hsin_small_exact]
      nlinarith only [hsin_small_gt, hsmall_cube_le]
    rw [show smallAngle = Real.pi / 64 from rfl] at hsmall_estimate
    nlinarith only [hsmall_estimate, hsqrt_series_upper]
  let lowerAngle : ℝ := 331 * Real.pi / 720
  let lowerComplement : ℝ := 29 * Real.pi / 720
  have hlower_complement_pos : 0 < lowerComplement := by
    dsimp [lowerComplement]
    positivity
  have hlower_complement_lower :
      29 * ((157 : ℝ) / 50) / 720 ≤ lowerComplement := by
    dsimp [lowerComplement]
    nlinarith
  have hlower_complement_upper :
      lowerComplement ≤ 29 * ((63 : ℝ) / 20) / 720 := by
    dsimp [lowerComplement]
    nlinarith
  have hlower_complement_sq_le :
      lowerComplement ^ 2 ≤ (1 : ℝ) / 60 := by
    have hsquare :
        lowerComplement ^ 2 ≤
          (29 * ((63 : ℝ) / 20) / 720) ^ 2 := by
      gcongr
    norm_num at hsquare ⊢
    exact hsquare.trans (by norm_num)
  have hlower_complement_four_le :
      lowerComplement ^ 4 ≤ lowerComplement ^ 2 * ((1 : ℝ) / 60) := by
    calc
      lowerComplement ^ 4 =
          lowerComplement ^ 2 * lowerComplement ^ 2 := by ring
      _ ≤ lowerComplement ^ 2 * ((1 : ℝ) / 60) :=
        mul_le_mul_of_nonneg_left hlower_complement_sq_le (sq_nonneg _)
  have hlower_complement_sq_lower :
      (29 * ((157 : ℝ) / 50) / 720) ^ 2 ≤
        lowerComplement ^ 2 := by
    gcongr
  have hcos_lower_complement_bound :=
    Real.cos_bound
      (show |lowerComplement| ≤ 1 by
        rw [abs_of_pos hlower_complement_pos]
        exact hlower_complement_upper.trans (by norm_num))
  rw [abs_of_pos hlower_complement_pos] at hcos_lower_complement_bound
  have hcos_lower_complement :
      Real.cos lowerComplement ≤ (125 : ℝ) / 126 := by
    have hupper := (abs_sub_le_iff.mp hcos_lower_complement_bound).1
    nlinarith only
      [hupper, hlower_complement_four_le, hlower_complement_sq_lower]
  have hlower_angle_mem :
      lowerAngle ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    dsimp [lowerAngle]
    constructor
    · nlinarith only [Real.pi_pos]
    · nlinarith only [Real.pi_pos]
  have hlower_angle_eq :
      lowerAngle = Real.pi / 2 - lowerComplement := by
    dsimp [lowerAngle, lowerComplement]
    ring
  have hangle_lower : lowerAngle ≤ angle := by
    dsimp [angle]
    apply (Real.le_arcsin_iff_sin_le hlower_angle_mem hratio_mem).2
    rw [hlower_angle_eq, Real.sin_pi_div_two_sub]
    exact hcos_lower_complement
  let upperAngle : ℝ := 1657 * Real.pi / 3600
  let upperComplement : ℝ := 143 * Real.pi / 3600
  have hupper_complement_pos : 0 < upperComplement := by
    dsimp [upperComplement]
    positivity
  have hupper_complement_upper :
      upperComplement ≤ 143 * ((63 : ℝ) / 20) / 3600 := by
    dsimp [upperComplement]
    nlinarith
  have hupper_complement_sq_le :
      upperComplement ^ 2 ≤ (1 : ℝ) / 60 := by
    have hsquare :
        upperComplement ^ 2 ≤
          (143 * ((63 : ℝ) / 20) / 3600) ^ 2 := by
      gcongr
    exact hsquare.trans (by norm_num)
  have hupper_complement_four_le :
      upperComplement ^ 4 ≤ upperComplement ^ 2 * ((1 : ℝ) / 60) := by
    calc
      upperComplement ^ 4 =
          upperComplement ^ 2 * upperComplement ^ 2 := by ring
      _ ≤ upperComplement ^ 2 * ((1 : ℝ) / 60) :=
        mul_le_mul_of_nonneg_left hupper_complement_sq_le (sq_nonneg _)
  have hcos_upper_complement_bound :=
    Real.cos_bound
      (show |upperComplement| ≤ 1 by
        rw [abs_of_pos hupper_complement_pos]
        exact hupper_complement_upper.trans (by norm_num))
  rw [abs_of_pos hupper_complement_pos] at hcos_upper_complement_bound
  have hcos_upper_complement :
      (125 : ℝ) / 126 ≤ Real.cos upperComplement := by
    have hlower := (abs_sub_le_iff.mp hcos_upper_complement_bound).2
    have hupper_complement_sq_upper :
        upperComplement ^ 2 ≤
          (143 * ((63 : ℝ) / 20) / 3600) ^ 2 := by
      gcongr
    nlinarith only
      [hlower, hupper_complement_four_le, hupper_complement_sq_upper]
  have hupper_angle_mem :
      upperAngle ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    dsimp [upperAngle]
    constructor
    · nlinarith only [Real.pi_pos]
    · nlinarith only [Real.pi_pos]
  have hupper_angle_eq :
      upperAngle = Real.pi / 2 - upperComplement := by
    dsimp [upperAngle, upperComplement]
    ring
  have hangle_upper : angle ≤ upperAngle := by
    dsimp [angle]
    apply (Real.arcsin_le_iff_le_sin hratio_mem hupper_angle_mem).2
    rw [hupper_angle_eq, Real.sin_pi_div_two_sub]
    exact hcos_upper_complement
  have hrotation_eq :
      rotationRadians = angle - Real.pi / 4 := by
    rw [hrotation_formula]
    dsimp [angle]
    rw [h_readouts.wavelength_readout_nm,
      h_readouts.reflecting_plane_separation_readout_nm,
      h_readouts.initial_glancing_angle_readout]
    unfold degreesToRadians
    congr 1 <;> ring
  have hdegree_scale_nonneg : 0 ≤ (180 : ℝ) / Real.pi := by positivity
  have hdegree_lower :
      (151 : ℝ) / 4 ≤ (angle - Real.pi / 4) * 180 / Real.pi := by
    have hsub := sub_le_sub_right hangle_lower (Real.pi / 4)
    have hmul :=
      mul_le_mul_of_nonneg_right hsub hdegree_scale_nonneg
    calc
      (151 : ℝ) / 4 =
          (lowerAngle - Real.pi / 4) * ((180 : ℝ) / Real.pi) := by
            dsimp [lowerAngle]
            field_simp [Real.pi_ne_zero]
            <;> ring
      _ ≤ (angle - Real.pi / 4) * ((180 : ℝ) / Real.pi) := hmul
      _ = (angle - Real.pi / 4) * 180 / Real.pi := by ring
  have hdegree_upper :
      (angle - Real.pi / 4) * 180 / Real.pi ≤ (757 : ℝ) / 20 := by
    have hsub := sub_le_sub_right hangle_upper (Real.pi / 4)
    have hmul :=
      mul_le_mul_of_nonneg_right hsub hdegree_scale_nonneg
    calc
      (angle - Real.pi / 4) * 180 / Real.pi =
          (angle - Real.pi / 4) * ((180 : ℝ) / Real.pi) := by ring
      _ ≤ (upperAngle - Real.pi / 4) * ((180 : ℝ) / Real.pi) := hmul
      _ = (757 : ℝ) / 20 := by
        dsimp [upperAngle]
        field_simp [Real.pi_ne_zero]
        <;> ring
  have hrounds :
      RoundsToNearestTenthDegree rotationRadians 37.8 := by
    rw [hrotation_eq]
    unfold RoundsToNearestTenthDegree radiansToDegrees
    rw [abs_le]
    constructor <;> norm_num at *
    · linarith
    · linarith
  refine ⟨rotationRadians, hrotation_larger, hrounds, ?_⟩
  simpa [MatchesAnswer, AnswerChoice.rotationDegrees] using hrounds

end PhyXMiniProblems.ProblemPhyXMini0079
