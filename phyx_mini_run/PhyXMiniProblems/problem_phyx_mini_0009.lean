import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.Optics.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0009

/-- Convert a real-valued angle readout in degrees to its radian readout. -/
def radiansOfDegrees (degreeMeasure : ℝ) : ℝ :=
  degreeMeasure * Real.pi / 180

/-- Convert a real-valued angle readout in radians to its degree readout. -/
def degreesOfRadians (radianMeasure : ℝ) : ℝ :=
  radianMeasure * 180 / Real.pi

/--
The material data and apex-angle label of the triangular prism. Angle fields
are real-valued radian readouts. Refractive indices use PhysLean's
dimension-tagged type at the dimensionless dimension `1`.
-/
structure TriangularGlassPrism where
  /-- Figure label `Φ`, the angle between the two refracting faces. -/
  apexAngleRadians : ℝ
  /-- Dimensionless refractive-index readout of the glass. -/
  glassRefractiveIndex : WithDim (1 : Dimension) ℝ
  /-- Dimensionless refractive-index readout of the medium outside the prism. -/
  ambientRefractiveIndex : WithDim (1 : Dimension) ℝ

/-- Physical range conditions for the prism data used in this problem. -/
def TriangularGlassPrism.PhysicallyValid (prism : TriangularGlassPrism) : Prop :=
  0 < prism.apexAngleRadians ∧
    prism.apexAngleRadians < Real.pi ∧
    0 < prism.ambientRefractiveIndex.val ∧
    prism.ambientRefractiveIndex.val < prism.glassRefractiveIndex.val

/--
Snell's law at one interface. The refractive indices are dimensionless
PhysLean quantities and the angles are radian magnitudes measured from the
local surface normal.
-/
def SnellLawAtInterface
    (incidentRefractiveIndex transmittedRefractiveIndex :
      WithDim (1 : Dimension) ℝ)
    (incidentAngleRadians transmittedAngleRadians : ℝ) : Prop :=
  incidentRefractiveIndex.val * Real.sin incidentAngleRadians =
    transmittedRefractiveIndex.val * Real.sin transmittedAngleRadians

/-- A nonnegative incidence or refraction angle on its closed principal branch. -/
def IsPrincipalOpticalAngle (angleRadians : ℝ) : Prop :=
  angleRadians ∈ Set.Icc 0 (Real.pi / 2)

/--
The four normal-referenced angles of a ray that enters the left face and exits
the right face of the prism in the figure. `entranceIncidenceRadians` is the
figure label `θ₁`.
-/
structure PrismRayPath where
  entranceIncidenceRadians : ℝ
  entranceRefractionRadians : ℝ
  exitIncidenceRadians : ℝ
  emergenceAngleRadians : ℝ

/--
The governing geometrical-optics relations for a ray crossing both prism
faces. The two internal normal-referenced angles add to the apex angle `Φ`,
and Snell's law holds at both interfaces. The allowed range of the emergence
angle is kept as an explicit parameter so that strict transmission and the
tangent-inclusive limiting convention cannot be conflated.
-/
def PrismRayPath.ObeysGeometricalOptics
    (path : PrismRayPath) (prism : TriangularGlassPrism)
    (allowedEmergenceAngles : Set ℝ) : Prop :=
  IsPrincipalOpticalAngle path.entranceIncidenceRadians ∧
    IsPrincipalOpticalAngle path.entranceRefractionRadians ∧
    IsPrincipalOpticalAngle path.exitIncidenceRadians ∧
    path.emergenceAngleRadians ∈ allowedEmergenceAngles ∧
    path.entranceRefractionRadians + path.exitIncidenceRadians =
      prism.apexAngleRadians ∧
    SnellLawAtInterface
      prism.ambientRefractiveIndex prism.glassRefractiveIndex
      path.entranceIncidenceRadians path.entranceRefractionRadians ∧
    SnellLawAtInterface
      prism.glassRefractiveIndex prism.ambientRefractiveIndex
      path.exitIncidenceRadians path.emergenceAngleRadians

/--
An incident angle permits emergence under a specified emergence-angle
convention when some ray path obeys the prism geometry and Snell's law.
-/
def CanEmerge
    (prism : TriangularGlassPrism) (allowedEmergenceAngles : Set ℝ)
    (θ₁Radians : ℝ) : Prop :=
  ∃ path : PrismRayPath,
    path.entranceIncidenceRadians = θ₁Radians ∧
      path.ObeysGeometricalOptics prism allowedEmergenceAngles

/-- The answer-choice labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq

/-- The degree readout printed next to each answer-choice label. -/
def answerChoiceDegrees : AnswerChoice → ℝ
  | .A => 246 / 10
  | .B => 291 / 10
  | .C => 279 / 10
  | .D => 215 / 10

/-- A radian angle rounds to the displayed degree value to the nearest tenth. -/
def RoundsToNearestTenthDegree
    (angleRadians displayedDegrees : ℝ) : Prop :=
  |degreesOfRadians angleRadians - displayedDegrees| < 1 / 20

/--
For the 60-degree glass prism of refractive index 1.50 in air, strict
transmission uses emergence angles in `[0, π/2)`, whereas the limiting
convention that counts a tangent ray uses `[0, π/2]`. Both conventions have
the same threshold: it is the greatest lower bound of the strict set and the
least member of the tangent-inclusive set. Its exact critical-angle formula
rounds to 27.9 degrees, answer choice C.

Blueprint: `thm:physics:phyx_mini_0009:target`.
-/
theorem smallestIncidenceAngle_is_choiceC
    (prism : TriangularGlassPrism)
    (hApexAngle : prism.apexAngleRadians = radiansOfDegrees 60)
    (hGlassIndex : prism.glassRefractiveIndex.val = 3 / 2)
    (hAmbientIndex : prism.ambientRefractiveIndex.val = 1)
    (hValid : prism.PhysicallyValid) :
    ∃ θ₁ThresholdRadians : ℝ,
      IsGLB
          {θ₁Radians : ℝ |
            CanEmerge prism (Set.Ico 0 (Real.pi / 2)) θ₁Radians}
          θ₁ThresholdRadians ∧
        IsLeast
          {θ₁Radians : ℝ |
            CanEmerge prism (Set.Icc 0 (Real.pi / 2)) θ₁Radians}
          θ₁ThresholdRadians ∧
        θ₁ThresholdRadians =
          Real.arcsin
            ((3 / 2 : ℝ) *
              Real.sin
                (radiansOfDegrees 60 - Real.arcsin (2 / 3 : ℝ))) ∧
        RoundsToNearestTenthDegree
          θ₁ThresholdRadians (answerChoiceDegrees .C) := by
  let A : ℝ := Real.pi / 3
  let c : ℝ := Real.arcsin (2 / 3 : ℝ)
  let r₀ : ℝ := A - c
  let x₀ : ℝ := (3 / 2 : ℝ) * Real.sin r₀
  let θ₀ : ℝ := Real.arcsin x₀

  have hDegrees : radiansOfDegrees 60 = A := by
    dsimp [radiansOfDegrees, A]
    ring
  have hApex : prism.apexAngleRadians = A :=
    hApexAngle.trans hDegrees
  have hsin_c : Real.sin c = (2 / 3 : ℝ) := by
    dsimp [c]
    exact Real.sin_arcsin (by norm_num) (by norm_num)
  have hc_pos : 0 < c := by
    dsimp [c]
    exact Real.arcsin_pos.2 (by norm_num)
  have hsin_A : Real.sin A = Real.sqrt 3 / 2 := by
    dsimp [A]
    exact Real.sin_pi_div_three
  have h_two_thirds_lt_sin_A : (2 / 3 : ℝ) < Real.sin A := by
    rw [hsin_A]
    have hsqrt : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hsqrt_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    nlinarith only [hsqrt, hsqrt_nonneg]
  have hc_lt_A : c < A := by
    have hA_mem : A ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      dsimp [A]
      constructor <;> linarith only [Real.pi_pos]
    calc
      c = Real.arcsin (2 / 3 : ℝ) := rfl
      _ < Real.arcsin (Real.sin A) :=
        Real.arcsin_lt_arcsin (by norm_num) h_two_thirds_lt_sin_A
          (Real.sin_le_one A)
      _ = A := Real.arcsin_sin' hA_mem
  have hA_half_lt_c : A / 2 < c := by
    have hhalf_mem :
        Real.pi / 6 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith only [Real.pi_pos]
    have harcsin_half :
        Real.arcsin (1 / 2 : ℝ) = Real.pi / 6 := by
      rw [← Real.sin_pi_div_six]
      exact Real.arcsin_sin' hhalf_mem
    have h :=
      Real.arcsin_lt_arcsin (x := (1 / 2 : ℝ)) (y := (2 / 3 : ℝ))
        (by norm_num) (by norm_num) (by norm_num)
    dsimp [A, c]
    rw [harcsin_half] at h
    convert h using 1 <;> ring
  have hr₀_pos : 0 < r₀ := by
    dsimp [r₀]
    linarith only [hc_lt_A]
  have hr₀_lt_c : r₀ < c := by
    dsimp [r₀]
    linarith only [hA_half_lt_c]
  have hc_lt_pi_div_two : c < Real.pi / 2 := by
    dsimp [A] at hc_lt_A
    linarith only [hc_lt_A, Real.pi_pos]
  have hr₀_lt_pi_div_two : r₀ < Real.pi / 2 :=
    hr₀_lt_c.trans hc_lt_pi_div_two
  have hr₀_mem :
      r₀ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith only [Real.pi_pos, hr₀_pos],
      hr₀_lt_pi_div_two.le⟩
  have hc_mem :
      c ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith only [Real.pi_pos, hc_pos],
      hc_lt_pi_div_two.le⟩
  have hsin_r₀_pos : 0 < Real.sin r₀ := by
    have hzero_mem :
        (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith only [Real.pi_pos]
    simpa using Real.strictMonoOn_sin hzero_mem hr₀_mem hr₀_pos
  have hsin_r₀_lt : Real.sin r₀ < (2 / 3 : ℝ) := by
    rw [← hsin_c]
    exact Real.strictMonoOn_sin hr₀_mem hc_mem hr₀_lt_c
  have hx₀_pos : 0 < x₀ := by
    dsimp [x₀]
    positivity
  have hx₀_lt_one : x₀ < 1 := by
    dsimp [x₀]
    nlinarith only [hsin_r₀_lt]
  have hθ₀_pos : 0 < θ₀ := by
    dsimp [θ₀]
    exact Real.arcsin_pos.2 hx₀_pos
  have hθ₀_lt_pi_div_two : θ₀ < Real.pi / 2 := by
    dsimp [θ₀]
    exact Real.arcsin_lt_pi_div_two.2 hx₀_lt_one
  have hθ₀_mem :
      θ₀ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith only [Real.pi_pos, hθ₀_pos],
      hθ₀_lt_pi_div_two.le⟩
  have hsin_θ₀ : Real.sin θ₀ = x₀ := by
    dsimp [θ₀]
    exact Real.sin_arcsin (by linarith only [hx₀_pos]) hx₀_lt_one.le

  have threshold_is_lower_bound
      (allowedEmergenceAngles : Set ℝ)
      (hAllowed :
        allowedEmergenceAngles ⊆ Set.Icc 0 (Real.pi / 2)) :
      θ₀ ∈
        lowerBounds
          {θ₁Radians : ℝ |
            CanEmerge prism allowedEmergenceAngles θ₁Radians} := by
    intro θ₁ hθ₁
    rcases hθ₁ with ⟨path, rfl, hpath⟩
    rcases hpath with
      ⟨hEntrance, hRefraction, hExit, hEmergence, hGeometry,
        hEntrySnell, hExitSnell⟩
    change path.entranceIncidenceRadians ∈
      Set.Icc 0 (Real.pi / 2) at hEntrance
    change path.entranceRefractionRadians ∈
      Set.Icc 0 (Real.pi / 2) at hRefraction
    change path.exitIncidenceRadians ∈
      Set.Icc 0 (Real.pi / 2) at hExit
    change
      prism.ambientRefractiveIndex.val *
          Real.sin path.entranceIncidenceRadians =
        prism.glassRefractiveIndex.val *
          Real.sin path.entranceRefractionRadians at hEntrySnell
    change
      prism.glassRefractiveIndex.val *
          Real.sin path.exitIncidenceRadians =
        prism.ambientRefractiveIndex.val *
          Real.sin path.emergenceAngleRadians at hExitSnell
    rw [hAmbientIndex, hGlassIndex] at hEntrySnell
    rw [hGlassIndex, hAmbientIndex] at hExitSnell
    have hsin_exit_le :
        Real.sin path.exitIncidenceRadians ≤ (2 / 3 : ℝ) := by
      nlinarith only [hExitSnell,
        Real.sin_le_one path.emergenceAngleRadians]
    have hexit_le_c : path.exitIncidenceRadians ≤ c := by
      calc
        path.exitIncidenceRadians =
            Real.arcsin (Real.sin path.exitIncidenceRadians) := by
              symm
              exact Real.arcsin_sin
                (by linarith only [Real.pi_pos, hExit.1]) hExit.2
        _ ≤ Real.arcsin (2 / 3 : ℝ) :=
          Real.arcsin_le_arcsin hsin_exit_le
        _ = c := rfl
    have hr₀_le_refraction :
        r₀ ≤ path.entranceRefractionRadians := by
      dsimp [r₀]
      linarith only [hGeometry, hApex, hexit_le_c]
    have hsin_r₀_le_refraction :
        Real.sin r₀ ≤ Real.sin path.entranceRefractionRadians :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith only [Real.pi_pos, hr₀_pos])
        hRefraction.2 hr₀_le_refraction
    have hsin_θ₀_le_entrance :
        Real.sin θ₀ ≤ Real.sin path.entranceIncidenceRadians := by
      rw [hsin_θ₀]
      dsimp [x₀]
      nlinarith only [hEntrySnell, hsin_r₀_le_refraction]
    exact
      (Real.strictMonoOn_sin.le_iff_le hθ₀_mem
          ⟨by linarith only [Real.pi_pos, hEntrance.1],
            hEntrance.2⟩).1
        hsin_θ₀_le_entrance

  have threshold_can_emerge_closed :
      CanEmerge prism (Set.Icc 0 (Real.pi / 2)) θ₀ := by
    let criticalPath : PrismRayPath :=
      { entranceIncidenceRadians := θ₀
        entranceRefractionRadians := r₀
        exitIncidenceRadians := c
        emergenceAngleRadians := Real.pi / 2 }
    refine ⟨criticalPath, rfl, ?_⟩
    refine
      ⟨⟨hθ₀_pos.le, hθ₀_lt_pi_div_two.le⟩,
        ⟨hr₀_pos.le, hr₀_lt_pi_div_two.le⟩,
        ⟨hc_pos.le, hc_lt_pi_div_two.le⟩,
        ⟨Real.pi_div_two_pos.le, le_rfl⟩, ?_, ?_, ?_⟩
    · dsimp [criticalPath, r₀]
      calc
        A - c + c = A := by ring
        _ = prism.apexAngleRadians := hApex.symm
    · change
        prism.ambientRefractiveIndex.val * Real.sin θ₀ =
          prism.glassRefractiveIndex.val * Real.sin r₀
      rw [hAmbientIndex, hGlassIndex, one_mul, hsin_θ₀]
    · change
        prism.glassRefractiveIndex.val * Real.sin c =
          prism.ambientRefractiveIndex.val * Real.sin (Real.pi / 2)
      rw [hGlassIndex, hAmbientIndex, hsin_c, Real.sin_pi_div_two]
      norm_num

  have open_interval_can_emerge :
      Set.Ioc θ₀ (Real.pi / 2) ⊆
        {θ₁Radians : ℝ |
          CanEmerge prism (Set.Ico 0 (Real.pi / 2)) θ₁Radians} := by
    intro θ₁ hθ₁
    let r : ℝ := Real.arcsin ((2 / 3 : ℝ) * Real.sin θ₁)
    let i : ℝ := A - r
    let e : ℝ := Real.arcsin ((3 / 2 : ℝ) * Real.sin i)
    have hθ₁_mem :
        θ₁ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith only [Real.pi_pos, hθ₀_pos, hθ₁.1], hθ₁.2⟩
    have hsin_θ₀_lt_θ₁ : Real.sin θ₀ < Real.sin θ₁ :=
      Real.strictMonoOn_sin hθ₀_mem hθ₁_mem hθ₁.1
    have hsin_θ₁_nonneg : 0 ≤ Real.sin θ₁ := by
      exact Real.sin_nonneg_of_nonneg_of_le_pi
        (by linarith only [hθ₀_pos, hθ₁.1])
        (by linarith only [hθ₁.2, Real.pi_pos])
    have hy_nonneg : 0 ≤ (2 / 3 : ℝ) * Real.sin θ₁ := by positivity
    have hy_le : (2 / 3 : ℝ) * Real.sin θ₁ ≤ 2 / 3 := by
      nlinarith only [Real.sin_le_one θ₁]
    have hsin_r :
        Real.sin r = (2 / 3 : ℝ) * Real.sin θ₁ := by
      dsimp [r]
      exact Real.sin_arcsin
        (by linarith only [hy_nonneg]) (by linarith only [hy_le])
    have hr_nonneg : 0 ≤ r := by
      dsimp [r]
      exact Real.arcsin_nonneg.2 hy_nonneg
    have hr_le_c : r ≤ c := by
      dsimp [r, c]
      exact Real.arcsin_le_arcsin hy_le
    have hsin_r₀_lt_y :
        Real.sin r₀ < (2 / 3 : ℝ) * Real.sin θ₁ := by
      rw [hsin_θ₀] at hsin_θ₀_lt_θ₁
      dsimp [x₀] at hsin_θ₀_lt_θ₁
      nlinarith only [hsin_θ₀_lt_θ₁]
    have hr₀_lt_r : r₀ < r := by
      calc
        r₀ = Real.arcsin (Real.sin r₀) := by
          symm
          exact Real.arcsin_sin' hr₀_mem
        _ < Real.arcsin ((2 / 3 : ℝ) * Real.sin θ₁) :=
          Real.arcsin_lt_arcsin (Real.neg_one_le_sin r₀)
            hsin_r₀_lt_y (by linarith only [hy_le])
        _ = r := rfl
    have hi_pos : 0 < i := by
      dsimp [i]
      exact sub_pos.2 (hr_le_c.trans_lt hc_lt_A)
    have hi_lt_c : i < c := by
      dsimp [i, r₀] at hr₀_lt_r ⊢
      linarith only [hr₀_lt_r]
    have hi_le_pi_div_two : i ≤ Real.pi / 2 := by
      dsimp [i, A]
      linarith only [hr_nonneg, Real.pi_pos]
    have hi_mem :
        i ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith only [Real.pi_pos, hi_pos], hi_le_pi_div_two⟩
    have hsin_i_pos : 0 < Real.sin i := by
      have hzero_mem :
          (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith only [Real.pi_pos]
      simpa using Real.strictMonoOn_sin hzero_mem hi_mem hi_pos
    have hsin_i_lt : Real.sin i < (2 / 3 : ℝ) := by
      rw [← hsin_c]
      exact Real.strictMonoOn_sin hi_mem hc_mem hi_lt_c
    have hz_nonneg : 0 ≤ (3 / 2 : ℝ) * Real.sin i := by positivity
    have hz_lt_one : (3 / 2 : ℝ) * Real.sin i < 1 := by
      nlinarith only [hsin_i_lt]
    have hsin_e :
        Real.sin e = (3 / 2 : ℝ) * Real.sin i := by
      dsimp [e]
      exact Real.sin_arcsin
        (by linarith only [hz_nonneg]) hz_lt_one.le
    have he_nonneg : 0 ≤ e := by
      dsimp [e]
      exact Real.arcsin_nonneg.2 hz_nonneg
    have he_lt_pi_div_two : e < Real.pi / 2 := by
      dsimp [e]
      exact Real.arcsin_lt_pi_div_two.2 hz_lt_one
    let path : PrismRayPath :=
      { entranceIncidenceRadians := θ₁
        entranceRefractionRadians := r
        exitIncidenceRadians := i
        emergenceAngleRadians := e }
    refine ⟨path, rfl, ?_⟩
    refine
      ⟨⟨by linarith [hθ₀_pos, hθ₁.1], hθ₁.2⟩,
        ⟨hr_nonneg, hr_le_c.trans hc_lt_pi_div_two.le⟩,
        ⟨hi_pos.le, hi_le_pi_div_two⟩,
        ⟨he_nonneg, he_lt_pi_div_two⟩, ?_, ?_, ?_⟩
    · dsimp [path, i]
      calc
        r + (A - r) = A := by ring
        _ = prism.apexAngleRadians := hApex.symm
    · change
        prism.ambientRefractiveIndex.val * Real.sin θ₁ =
          prism.glassRefractiveIndex.val * Real.sin r
      rw [hAmbientIndex, hGlassIndex, one_mul, hsin_r]
      ring
    · change
        prism.glassRefractiveIndex.val * Real.sin i =
          prism.ambientRefractiveIndex.val * Real.sin e
      rw [hGlassIndex, hAmbientIndex, one_mul, hsin_e]

  refine ⟨θ₀, ?_, ?_, ?_, ?_⟩
  · exact
      (isGLB_Ioc hθ₀_lt_pi_div_two).of_subset_of_superset
        (isGLB_Icc hθ₀_lt_pi_div_two.le)
        open_interval_can_emerge
        (by
          intro θ₁ hθ₁
          constructor
          · exact
              threshold_is_lower_bound (Set.Ico 0 (Real.pi / 2))
                Set.Ico_subset_Icc_self hθ₁
          · rcases hθ₁ with ⟨path, rfl, hpath⟩
            exact hpath.1.2)
  · exact
      ⟨threshold_can_emerge_closed,
        threshold_is_lower_bound (Set.Icc 0 (Real.pi / 2)) (fun _ h => h)⟩
  · dsimp [θ₀, x₀, r₀]
    rw [hDegrees]
  · clear threshold_is_lower_bound threshold_can_emerge_closed
      open_interval_can_emerge
    clear hApex hValid hApexAngle hGlassIndex hAmbientIndex prism
    clear hDegrees hsin_c hc_pos hsin_A h_two_thirds_lt_sin_A
      hc_lt_A hA_half_lt_c hr₀_pos hr₀_lt_c hc_lt_pi_div_two
      hr₀_lt_pi_div_two hr₀_mem hc_mem hsin_r₀_pos hsin_r₀_lt
      hx₀_pos hx₀_lt_one hθ₀_pos hθ₀_lt_pi_div_two
    have hx₀_formula :
        x₀ = Real.sqrt 3 * Real.sqrt 5 / 4 - 1 / 2 := by
      dsimp [x₀, r₀, A, c]
      rw [Real.sin_sub, Real.sin_pi_div_three,
        Real.cos_pi_div_three, Real.cos_arcsin,
        Real.sin_arcsin (by norm_num) (by norm_num)]
      have hcosCritical :
          Real.sqrt (1 - (2 / 3 : ℝ) ^ 2) = Real.sqrt 5 / 3 := by
        have hradicand :
            (1 - (2 / 3 : ℝ) ^ 2) = 5 / 9 := by norm_num
        rw [hradicand, Real.sqrt_div (by norm_num : 0 ≤ (5 : ℝ)),
          show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
        norm_num
      rw [hcosCritical]
      ring

    have hpi_six_mem :
        Real.pi / 6 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith only [Real.pi_pos]
    have hpi_lower : (31 / 10 : ℝ) < Real.pi := by
      let a : ℝ := 31 / 60
      have ha_mem :
          a ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        dsimp [a]
        constructor <;> nlinarith only [Real.two_le_pi]
      have hbound := Real.sin_bound (x := a) (by norm_num [a])
      rw [abs_le] at hbound
      have hsin_a : Real.sin a < (1 / 2 : ℝ) := by
        dsimp [a] at hbound ⊢
        norm_num at hbound ⊢
        linarith only [hbound.2]
      have ha_lt : a < Real.pi / 6 :=
        (Real.strictMonoOn_sin.lt_iff_lt ha_mem hpi_six_mem).1 (by
          rw [Real.sin_pi_div_six]
          exact hsin_a)
      dsimp [a] at ha_lt
      linarith only [ha_lt]
    have hpi_upper : Real.pi < (159 / 50 : ℝ) := by
      let b : ℝ := 53 / 100
      have hb_mem :
          b ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        dsimp [b]
        constructor <;> nlinarith only [Real.two_le_pi]
      have hbound := Real.sin_bound (x := b) (by norm_num [b])
      rw [abs_le] at hbound
      have hsin_b : (1 / 2 : ℝ) < Real.sin b := by
        dsimp [b] at hbound ⊢
        norm_num at hbound ⊢
        linarith only [hbound.1]
      have hlt : Real.pi / 6 < b :=
        (Real.strictMonoOn_sin.lt_iff_lt hpi_six_mem hb_mem).1 (by
          rw [Real.sin_pi_div_six]
          exact hsin_b)
      dsimp [b] at hlt
      linarith only [hlt]

    have hsin_lower_proxy :
          Real.sin
            (Real.pi / 6 - (43 * (31 / 10 : ℝ) / 3600)) <
          Real.sqrt 3 * Real.sqrt 5 / 4 - 1 / 2 := by
      let d : ℝ := 43 * (31 / 10 : ℝ) / 3600
      have hbound :
          |Real.sin d - (d - d ^ 3 / 6)| ≤
            |d| ^ 4 * (5 / 96) :=
        @Real.sin_bound d (by norm_num [d])
      rw [abs_le] at hbound
      have hsin_d_lower : (37 / 1000 : ℝ) < Real.sin d := by
        dsimp [d] at hbound ⊢
        norm_num at hbound ⊢
        linarith only [hbound.1]
      have hsqrt_three : (433 / 250 : ℝ) < Real.sqrt 3 := by
        exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
      have hsqrt_five : (559 / 250 : ℝ) < Real.sqrt 5 := by
        exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
      simp only [Real.sin_sub, Real.sin_pi_div_six, Real.cos_pi_div_six]
      dsimp [d] at hsin_d_lower ⊢
      nlinarith only [hsin_d_lower, hsqrt_three, hsqrt_five,
        Real.sqrt_nonneg 3, Real.sqrt_nonneg 5,
        Real.cos_le_one (43 * (31 / 10 : ℝ) / 3600)]

    have hsin_upper_proxy :
        Real.sqrt 3 * Real.sqrt 5 / 4 - 1 / 2 <
          Real.sin
            (Real.pi / 6 - (41 * (159 / 50 : ℝ) / 3600)) := by
      let d : ℝ := 41 * (159 / 50 : ℝ) / 3600
      have hbound :
          |Real.sin d - (d - d ^ 3 / 6)| ≤
            |d| ^ 4 * (5 / 96) :=
        @Real.sin_bound d (by norm_num [d])
      rw [abs_le] at hbound
      have hsin_d_upper : Real.sin d < (3621 / 100000 : ℝ) := by
        dsimp [d] at hbound ⊢
        norm_num at hbound ⊢
        linarith only [hbound.2]
      have hsin_d_pos : 0 < Real.sin d := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · norm_num [d]
        · dsimp [d]
          nlinarith only [Real.two_le_pi]
      have hsqrt_three : Real.sqrt 3 < (86603 / 50000 : ℝ) := by
        exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
      have hsqrt_five : Real.sqrt 5 < (223607 / 100000 : ℝ) := by
        exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
      have hd_mem :
          d ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        dsimp [d]
        constructor <;> nlinarith only [Real.two_le_pi]
      have hcos_nonneg : 0 ≤ Real.cos d :=
        Real.cos_nonneg_of_mem_Icc hd_mem
      have hsin_sq :
          Real.sin d ^ 2 < (3621 / 100000 : ℝ) ^ 2 :=
        (sq_lt_sq₀ hsin_d_pos.le (by norm_num)).2 hsin_d_upper
      have hcos_lower : (49967 / 50000 : ℝ) < Real.cos d := by
        have htrig := Real.sin_sq_add_cos_sq d
        have hsq :
            (49967 / 50000 : ℝ) ^ 2 < Real.cos d ^ 2 := by
          calc
            (49967 / 50000 : ℝ) ^ 2 <
                1 - (3621 / 100000 : ℝ) ^ 2 := by norm_num
            _ < 1 - Real.sin d ^ 2 := sub_lt_sub_left hsin_sq 1
            _ = Real.cos d ^ 2 := by linarith only [htrig]
        exact (sq_lt_sq₀ (by norm_num) hcos_nonneg).1 hsq
      simp only [Real.sin_sub, Real.sin_pi_div_six, Real.cos_pi_div_six]
      dsimp [d] at hsin_d_upper hsin_d_pos hcos_lower ⊢
      nlinarith only [hsin_d_upper, hsin_d_pos, hsqrt_three,
        hsqrt_five, hcos_lower, Real.sqrt_nonneg 3,
        Real.sqrt_nonneg 5]

    let α : ℝ := 557 * Real.pi / 3600
    let β : ℝ := 559 * Real.pi / 3600
    have hα_mem :
        α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      dsimp [α]
      constructor <;> nlinarith only [Real.pi_pos]
    have hβ_mem :
        β ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      dsimp [β]
      constructor <;> nlinarith only [Real.pi_pos]
    have hlower_proxy_mem :
        Real.pi / 6 - (43 * (31 / 10 : ℝ) / 3600) ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith only [Real.pi_pos, hpi_lower]
    have hupper_proxy_mem :
        Real.pi / 6 - (41 * (159 / 50 : ℝ) / 3600) ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith only [Real.pi_pos, hpi_lower]
    have hα_lt_proxy :
        α < Real.pi / 6 - (43 * (31 / 10 : ℝ) / 3600) := by
      dsimp [α]
      nlinarith only [hpi_lower]
    have hproxy_lt_β :
        Real.pi / 6 - (41 * (159 / 50 : ℝ) / 3600) < β := by
      dsimp [β]
      nlinarith only [hpi_upper]
    have hsin_α_lt_x₀ : Real.sin α < x₀ := by
      rw [hx₀_formula]
      exact
        (Real.strictMonoOn_sin hα_mem hlower_proxy_mem hα_lt_proxy).trans
          hsin_lower_proxy
    have hsin_x₀_lt_β : x₀ < Real.sin β := by
      rw [hx₀_formula]
      exact
        hsin_upper_proxy.trans
          (Real.strictMonoOn_sin hupper_proxy_mem hβ_mem hproxy_lt_β)
    have hα_lt_θ₀ : α < θ₀ :=
      (Real.strictMonoOn_sin.lt_iff_lt hα_mem hθ₀_mem).1 (by
        rw [hsin_θ₀]
        exact hsin_α_lt_x₀)
    have hθ₀_lt_β : θ₀ < β :=
      (Real.strictMonoOn_sin.lt_iff_lt hθ₀_mem hβ_mem).1 (by
        rw [hsin_θ₀]
        exact hsin_x₀_lt_β)

    change
      |θ₀ * 180 / Real.pi - (279 / 10 : ℝ)| < (1 / 20 : ℝ)
    rw [abs_lt]
    constructor
    · have hscaled :
          (557 / 20 : ℝ) * Real.pi < θ₀ * 180 := by
        dsimp [α] at hα_lt_θ₀
        nlinarith only [hα_lt_θ₀]
      have hquotient :
          (557 / 20 : ℝ) < θ₀ * 180 / Real.pi :=
        (lt_div_iff₀ Real.pi_pos).2 hscaled
      linarith only [hquotient]
    · have hscaled :
          θ₀ * 180 < (559 / 20 : ℝ) * Real.pi := by
        dsimp [β] at hθ₀_lt_β
        nlinarith only [hθ₀_lt_β]
      have hquotient :
          θ₀ * 180 / Real.pi < (559 / 20 : ℝ) :=
        (div_lt_iff₀ Real.pi_pos).2 hscaled
      linarith only [hquotient]

end PhyXMiniProblems.ProblemPhyXMini0009
