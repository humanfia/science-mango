import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.Optics.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0016

/-!
# Critical-angle ray in a triangular prism

The primary figure shows a light ray entering surface 1 of an isosceles
triangular prism, reaching surface 2 at the critical angle, and reflecting
there.  Plane angles are represented by `Real.Angle`.  Whenever an ordered
principal-branch value or a numerical degree value is needed, it is exposed
by an explicitly named scalar projection.

Refractive indices are dimensionless scalar readouts.  Physlib's `Dimension`
does not treat plane angle as an independent base dimension, so the file uses
Mathlib's angle carrier rather than manufacturing a dimension tag for it.
-/

/-- Convert a scalar degree readout into a physical plane angle. -/
def degreesToAngle (angleDegrees : ℝ) : Real.Angle :=
  ((angleDegrees * Real.pi / 180 : ℝ) : Real.Angle)

/-- The principal representative of a plane angle, measured in radians. -/
def angleInRadians (angle : Real.Angle) : ℝ :=
  angle.toReal

/-- Convert a scalar radian readout into its numerical value in degrees. -/
def radiansToDegrees (angleRadians : ℝ) : ℝ :=
  angleRadians * 180 / Real.pi

/-- The two homogeneous optical media traversed by the pictured beam. -/
inductive OpticalMedium where
  | ambientAir
  | prismMaterial
  deriving DecidableEq, Repr

/-- The two prism interfaces named in the primary figure. -/
inductive PrismSurface where
  | surfaceOne
  | surfaceTwo
  deriving DecidableEq, Repr

/-- The three directed physical ray segments visible in the primary figure. -/
inductive PrismRaySegment where
  | externalIncident
  | internalBetweenSurfaces
  | internalReflected
  deriving DecidableEq, Repr

/--
An angle between a typed ray segment and the normal to a typed prism surface.
The value is a plane angle; its ordered radian representative is obtained only
through `angleInRadians`.
-/
structure NormalReferencedAngle
    (surface : PrismSurface) (ray : PrismRaySegment) where
  angle : Real.Angle

/--
The physical prism and its dimensionless material readouts.  The interior
angle is the angle at which surface 1 and surface 2 meet in the triangular
cross-section.
-/
structure TriangularPrismSetup where
  refractiveIndexDimensionless : OpticalMedium → ℝ
  interiorAngle : Real.Angle
  isIsosceles : Prop

/-- The four normal-referenced angular quantities along the depicted path. -/
structure PrismRayPath where
  /-- Figure label `θ₁`, for the external ray incident on surface 1. -/
  incidenceAtSurfaceOne :
    NormalReferencedAngle .surfaceOne .externalIncident
  /-- The internal ray immediately after refraction at surface 1. -/
  refractionAtSurfaceOne :
    NormalReferencedAngle .surfaceOne .internalBetweenSurfaces
  /-- The same internal ray incident on surface 2. -/
  incidenceAtSurfaceTwo :
    NormalReferencedAngle .surfaceTwo .internalBetweenSurfaces
  /-- The ray after specular reflection at surface 2. -/
  reflectionAtSurfaceTwo :
    NormalReferencedAngle .surfaceTwo .internalReflected

/-- An interface angle is on the nonnegative principal branch up to grazing. -/
def IsInterfaceAngle (angle : Real.Angle) : Prop :=
  angleInRadians angle ∈ Set.Icc 0 (Real.pi / 2)

/--
Positivity, optical density ordering, and principal-branch conditions for the
pictured physical configuration.  These conditions do not determine the
requested incidence angle numerically.
-/
structure IsPhysicalPrismConfiguration
    (setup : TriangularPrismSetup) (path : PrismRayPath) : Prop where
  refractiveIndicesPositive :
    ∀ medium, 0 < setup.refractiveIndexDimensionless medium
  prismDenserThanAmbient :
    setup.refractiveIndexDimensionless .ambientAir <
      setup.refractiveIndexDimensionless .prismMaterial
  incidenceAtSurfaceOneValid :
    IsInterfaceAngle path.incidenceAtSurfaceOne.angle
  refractionAtSurfaceOneValid :
    IsInterfaceAngle path.refractionAtSurfaceOne.angle
  incidenceAtSurfaceTwoValid :
    IsInterfaceAngle path.incidenceAtSurfaceTwo.angle
  reflectionAtSurfaceTwoValid :
    IsInterfaceAngle path.reflectionAtSurfaceTwo.angle

/-- Snell's law where the ray passes from ambient air into the prism. -/
def SatisfiesSnellLawAtSurfaceOne
    (setup : TriangularPrismSetup) (path : PrismRayPath) : Prop :=
  setup.refractiveIndexDimensionless .ambientAir *
      Real.Angle.sin path.incidenceAtSurfaceOne.angle =
    setup.refractiveIndexDimensionless .prismMaterial *
      Real.Angle.sin path.refractionAtSurfaceOne.angle

/--
The incidence at surface 2 is critical: the limiting transmitted air ray is
at `90°` from the interface normal.
-/
def SatisfiesCriticalAngleLawAtSurfaceTwo
    (setup : TriangularPrismSetup) (path : PrismRayPath) : Prop :=
  setup.refractiveIndexDimensionless .prismMaterial *
      Real.Angle.sin path.incidenceAtSurfaceTwo.angle =
    setup.refractiveIndexDimensionless .ambientAir *
      Real.Angle.sin (degreesToAngle 90)

/-- Specular reflection gives equal incidence and reflection angles. -/
def SatisfiesReflectionLawAtSurfaceTwo (path : PrismRayPath) : Prop :=
  path.incidenceAtSurfaceTwo.angle = path.reflectionAtSurfaceTwo.angle

/--
The straight internal ray lies between the two inward normals; the two
normal-referenced internal angles sum to the prism's surface angle.
-/
def SatisfiesPrismRayGeometry
    (setup : TriangularPrismSetup) (path : PrismRayPath) : Prop :=
  path.refractionAtSurfaceOne.angle + path.incidenceAtSurfaceTwo.angle =
    setup.interiorAngle

/-- The governing geometrical-optics laws for the pictured ray. -/
structure PrismOpticsLaws
    (setup : TriangularPrismSetup) (path : PrismRayPath) : Prop where
  snellAtSurfaceOne : SatisfiesSnellLawAtSurfaceOne setup path
  criticalAtSurfaceTwo : SatisfiesCriticalAngleLawAtSurfaceTwo setup path
  reflectionAtSurfaceTwo : SatisfiesReflectionLawAtSurfaceTwo path
  internalRayGeometry : SatisfiesPrismRayGeometry setup path

/--
Categorical and numerical readouts taken from the primary image.  In
particular, neither `18°` nor the requested external incidence angle occurs
among these source readouts.
-/
structure PrismFigureReadouts
    (setup : TriangularPrismSetup) (path : PrismRayPath) : Prop where
  isoscelesPrism : setup.isIsosceles
  surfacesOneTwoAngle : setup.interiorAngle = degreesToAngle 60
  criticalIncidenceAngle :
    path.incidenceAtSurfaceTwo.angle = degreesToAngle 42
  reflectedAngle :
    path.reflectionAtSurfaceTwo.angle = degreesToAngle 42

/-- Labels of the four incidence-angle choices printed with the problem. -/
inductive IncidenceAnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The scalar degree readout printed beside each displayed answer choice. -/
def answerAngleDegrees : IncidenceAnswerChoice → ℝ
  | .A => 11.5
  | .B => 27.5
  | .C => 42.5
  | .D => 19.5

/-- The answer label supplied by the dataset, retained only as metadata. -/
def recordedDatasetAnswerChoice : IncidenceAnswerChoice :=
  .C

/--
`value` rounds to `rounded` to the nearest tenth: `rounded` is an integral
multiple of one tenth and differs from `value` by less than half a tenth.
-/
def RoundsToNearestTenth (value rounded : ℝ) : Prop :=
  ∃ tenth : ℤ,
    rounded = (tenth : ℝ) / 10 ∧
      |value - rounded| < (1 : ℝ) / 20

/--
For the pictured `60°` isosceles prism, surface-2 incidence is the displayed
critical angle `42°`.  The geometry therefore gives an internal surface-1
refraction angle of `18°`; eliminating the two refractive indices from the
two Snell equations gives the displayed exact principal-branch expression.
Its degree value rounds to `27.5°`, answer choice B.

The recorded dataset answer C is represented only by
`recordedDatasetAnswerChoice` and is not assumed here.

Blueprint: `thm:physics:phyx_mini_0016:target`.
-/
theorem incidenceAngleSurfaceOne_is_answerChoiceB
    (setup : TriangularPrismSetup)
    (path : PrismRayPath)
    (physical : IsPhysicalPrismConfiguration setup path)
    (laws : PrismOpticsLaws setup path)
    (figure : PrismFigureReadouts setup path) :
    angleInRadians path.incidenceAtSurfaceOne.angle =
        Real.arcsin
          (Real.Angle.sin (degreesToAngle 18) /
            Real.Angle.sin (degreesToAngle 42)) ∧
      RoundsToNearestTenth
        (radiansToDegrees
          (angleInRadians path.incidenceAtSurfaceOne.angle))
        (answerAngleDegrees .B) := by
  exact
    set_option maxHeartbeats 1000000 in
    by
      have hRefract :
          path.refractionAtSurfaceOne.angle = degreesToAngle 18 := by
        apply add_right_cancel (b := path.incidenceAtSurfaceTwo.angle)
        rw [laws.internalRayGeometry, figure.surfacesOneTwoAngle,
          figure.criticalIncidenceAngle]
        norm_num [degreesToAngle]
        rw [← Real.Angle.coe_add]
        congr 1
        ring
      have hSin42Pos : 0 < Real.Angle.sin (degreesToAngle 42) := by
        rw [degreesToAngle, Real.Angle.sin_coe]
        exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by
          have := Real.pi_pos
          nlinarith)
      have hSinIncidence :
          Real.Angle.sin path.incidenceAtSurfaceOne.angle =
            Real.Angle.sin (degreesToAngle 18) /
              Real.Angle.sin (degreesToAngle 42) := by
        have hSnell := laws.snellAtSurfaceOne
        have hCritical := laws.criticalAtSurfaceTwo
        dsimp [SatisfiesSnellLawAtSurfaceOne] at hSnell
        dsimp [SatisfiesCriticalAngleLawAtSurfaceTwo] at hCritical
        rw [hRefract] at hSnell
        rw [figure.criticalIncidenceAngle] at hCritical
        have hSin90 : Real.Angle.sin (degreesToAngle 90) = 1 := by
          rw [degreesToAngle, Real.Angle.sin_coe]
          rw [show (90 : ℝ) * Real.pi / 180 = Real.pi / 2 by ring_nf,
            Real.sin_pi_div_two]
        rw [hSin90, mul_one] at hCritical
        rw [← hCritical] at hSnell
        have hPrismPos :=
          physical.refractiveIndicesPositive OpticalMedium.prismMaterial
        apply (eq_div_iff hSin42Pos.ne').2
        apply (mul_left_cancel₀ hPrismPos.ne')
        calc
          setup.refractiveIndexDimensionless .prismMaterial *
              (Real.Angle.sin path.incidenceAtSurfaceOne.angle *
                Real.Angle.sin (degreesToAngle 42)) =
              (setup.refractiveIndexDimensionless .prismMaterial *
                Real.Angle.sin (degreesToAngle 42)) *
                  Real.Angle.sin path.incidenceAtSurfaceOne.angle := by ring
          _ = setup.refractiveIndexDimensionless .prismMaterial *
              Real.Angle.sin (degreesToAngle 18) := hSnell
      have hExact :
          angleInRadians path.incidenceAtSurfaceOne.angle =
            Real.arcsin
              (Real.Angle.sin (degreesToAngle 18) /
                Real.Angle.sin (degreesToAngle 42)) := by
        symm
        apply Real.arcsin_eq_of_sin_eq
        · simpa [angleInRadians, Real.Angle.sin_toReal] using hSinIncidence
        · rcases physical.incidenceAtSurfaceOneValid with ⟨hNonneg, hLe⟩
          exact ⟨by
            have := Real.pi_pos
            linarith, hLe⟩
      refine ⟨hExact, ?_⟩
      rw [hExact]
      refine ⟨275, by norm_num [answerAngleDegrees], ?_⟩
      have hAngleSin18 :
          Real.Angle.sin (degreesToAngle 18) = Real.sin (Real.pi / 10) := by
        rw [degreesToAngle, Real.Angle.sin_coe]
        congr 1
        ring
      have hAngleSin42 :
          Real.Angle.sin (degreesToAngle 42) =
            Real.sin (7 * Real.pi / 30) := by
        rw [degreesToAngle, Real.Angle.sin_coe]
        congr 1
        ring
      rw [hAngleSin18, hAngleSin42]
    
      -- Elementary rational bounds on `π`, proved from the local cosine
      -- remainder estimate and repeated use of the double-angle formula.
      have hPiLower : (3.14 : ℝ) < Real.pi := by
        have h0 :
            (9987961 : ℝ) / 10000000 <
              Real.cos ((157 : ℝ) / 3200) := by
          have hb := Real.cos_bound (x := (157 : ℝ) / 3200)
            (by norm_num [abs_of_nonneg])
          rw [abs_le] at hb
          norm_num [abs_of_nonneg] at hb ⊢
          linarith
        have h1 :
            (9951872 : ℝ) / 10000000 <
              Real.cos ((157 : ℝ) / 1600) := by
          rw [show (157 : ℝ) / 1600 = 2 * (157 / 3200) by norm_num,
            Real.cos_two_mul]
          nlinarith only [h0]
        have h2 :
            (980795 : ℝ) / 1000000 <
              Real.cos ((157 : ℝ) / 800) := by
          rw [show (157 : ℝ) / 800 = 2 * (157 / 1600) by norm_num,
            Real.cos_two_mul]
          nlinarith only [h1]
        have h3 :
            (923917 : ℝ) / 1000000 <
              Real.cos ((157 : ℝ) / 400) := by
          rw [show (157 : ℝ) / 400 = 2 * (157 / 800) by norm_num,
            Real.cos_two_mul]
          nlinarith only [h2]
        have h4 :
            (70724 : ℝ) / 100000 <
              Real.cos ((157 : ℝ) / 200) := by
          rw [show (157 : ℝ) / 200 = 2 * (157 / 400) by norm_num,
            Real.cos_two_mul]
          nlinarith only [h3]
        have h5 : 0 < Real.cos ((157 : ℝ) / 100) := by
          rw [show (157 : ℝ) / 100 = 2 * (157 / 200) by norm_num,
            Real.cos_two_mul]
          nlinarith only [h4]
        by_contra h
        have hpi : Real.pi / 2 ≤ (157 : ℝ) / 100 := by
          norm_num at h ⊢
          linarith
        have hnonpos :=
          Real.cos_nonpos_of_pi_div_two_le_of_le hpi (by
            have htwo := Real.two_le_pi
            norm_num at htwo ⊢
            linarith)
        linarith only [h5, hnonpos]
      have hPiUpper : Real.pi < (3.15 : ℝ) := by
        have h0 :
            Real.cos ((315 : ℝ) / 6400) <
              (9987891 : ℝ) / 10000000 := by
          have hb := Real.cos_bound (x := (315 : ℝ) / 6400)
            (by norm_num [abs_of_nonneg])
          rw [abs_le] at hb
          norm_num [abs_of_nonneg] at hb ⊢
          linarith
        have h1 :
            Real.cos ((315 : ℝ) / 3200) <
              (9951594 : ℝ) / 10000000 := by
          rw [show (315 : ℝ) / 3200 = 2 * (315 / 6400) by norm_num,
            Real.cos_two_mul]
          have hcos : 0 ≤ Real.cos ((315 : ℝ) / 6400) :=
            Real.cos_nonneg_of_mem_Icc (by
              constructor <;> nlinarith [Real.one_le_pi_div_two])
          nlinarith only [h0, hcos]
        have h2 :
            Real.cos ((315 : ℝ) / 1600) <
              (9806845 : ℝ) / 10000000 := by
          rw [show (315 : ℝ) / 1600 = 2 * (315 / 3200) by norm_num,
            Real.cos_two_mul]
          have hcos : 0 ≤ Real.cos ((315 : ℝ) / 3200) :=
            Real.cos_nonneg_of_mem_Icc (by
              constructor <;> nlinarith [Real.one_le_pi_div_two])
          nlinarith only [h1, hcos]
        have h3 :
            Real.cos ((315 : ℝ) / 800) <
              (923485 : ℝ) / 1000000 := by
          rw [show (315 : ℝ) / 800 = 2 * (315 / 1600) by norm_num,
            Real.cos_two_mul]
          have hcos : 0 ≤ Real.cos ((315 : ℝ) / 1600) :=
            Real.cos_nonneg_of_mem_Icc (by
              constructor <;> nlinarith [Real.one_le_pi_div_two])
          nlinarith only [h2, hcos]
        have h4 :
            Real.cos ((315 : ℝ) / 400) <
              (70565 : ℝ) / 100000 := by
          rw [show (315 : ℝ) / 400 = 2 * (315 / 800) by norm_num,
            Real.cos_two_mul]
          have hcos : 0 ≤ Real.cos ((315 : ℝ) / 800) :=
            Real.cos_nonneg_of_mem_Icc (by
              constructor <;> nlinarith [Real.one_le_pi_div_two])
          nlinarith only [h3, hcos]
        have h5 : Real.cos ((315 : ℝ) / 200) < 0 := by
          rw [show (315 : ℝ) / 200 = 2 * (315 / 400) by norm_num,
            Real.cos_two_mul]
          have hcos : 0 ≤ Real.cos ((315 : ℝ) / 400) :=
            Real.cos_nonneg_of_mem_Icc (by
              constructor <;> nlinarith [Real.one_le_pi_div_two])
          nlinarith only [h4, hcos]
        by_contra h
        have hpi : (315 : ℝ) / 200 ≤ Real.pi / 2 := by
          norm_num at h ⊢
          linarith
        have hnonneg :=
          Real.cos_nonneg_of_mem_Icc (show
            (315 : ℝ) / 200 ∈
              Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
            constructor <;> nlinarith [Real.pi_pos])
        linarith only [h5, hnonneg]
    
      -- The library's certified fourth-order remainder estimate gives useful
      -- simultaneous bounds for sine and cosine on each small correction angle.
      have smallTrigEnclosure :
          ∀ (x lo hi : ℝ), 0 ≤ lo → lo < x → x < hi → hi ≤ 1 →
            lo - hi ^ 3 / 6 - hi ^ 4 * (5 / 96) < Real.sin x ∧
            Real.sin x < hi - lo ^ 3 / 6 + hi ^ 4 * (5 / 96) ∧
            1 - hi ^ 2 / 2 - hi ^ 4 * (5 / 96) < Real.cos x ∧
            Real.cos x < 1 - lo ^ 2 / 2 + hi ^ 4 * (5 / 96) := by
        intro x lo hi hlo hloX hxHi hhi
        have hxPos : 0 < x := lt_of_le_of_lt hlo hloX
        have hx3Lower : lo ^ 3 < x ^ 3 :=
          pow_lt_pow_left₀ hloX hlo (by norm_num)
        have hx3Upper : x ^ 3 < hi ^ 3 :=
          pow_lt_pow_left₀ hxHi hxPos.le (by norm_num)
        have hx2Lower : lo ^ 2 < x ^ 2 :=
          pow_lt_pow_left₀ hloX hlo (by norm_num)
        have hx2Upper : x ^ 2 < hi ^ 2 :=
          pow_lt_pow_left₀ hxHi hxPos.le (by norm_num)
        have hx4Upper : x ^ 4 < hi ^ 4 :=
          pow_lt_pow_left₀ hxHi hxPos.le (by norm_num)
        have hsin := Real.sin_bound (x := x) (by
          rw [abs_of_pos hxPos]
          exact hxHi.le.trans hhi)
        have hcos := Real.cos_bound (x := x) (by
          rw [abs_of_pos hxPos]
          exact hxHi.le.trans hhi)
        rw [abs_of_pos hxPos, abs_le] at hsin hcos
        constructor
        · linarith only [hsin.1, hloX, hx3Upper, hx4Upper]
        constructor
        · linarith only [hsin.2, hxHi, hx3Lower, hx4Upper]
        constructor
        · linarith only [hcos.1, hx2Upper, hx4Upper]
        · linarith only [hcos.2, hx2Lower, hx4Upper]
      have ht := smallTrigEnclosure (Real.pi / 60)
        ((157 : ℝ) / 3000) ((21 : ℝ) / 400) (by norm_num)
        (by nlinarith only [hPiLower]) (by nlinarith only [hPiUpper])
        (by norm_num)
      have hu := smallTrigEnclosure (17 * Real.pi / 1200)
        ((2669 : ℝ) / 60000) ((357 : ℝ) / 8000) (by norm_num)
        (by nlinarith only [hPiLower]) (by nlinarith only [hPiUpper])
        (by norm_num)
      have hv := smallTrigEnclosure (49 * Real.pi / 3600)
        ((7693 : ℝ) / 180000) ((343 : ℝ) / 8000) (by norm_num)
        (by nlinarith only [hPiLower]) (by nlinarith only [hPiUpper])
        (by norm_num)
      norm_num at ht hu hv
      have htSinLower :
          (523088 : ℝ) / 10000000 < Real.sin (Real.pi / 60) := by
        linarith only [ht.1]
      have htSinUpper :
          Real.sin (Real.pi / 60) < (524766 : ℝ) / 10000000 := by
        linarith only [ht.2.1]
      have htCosLower :
          (9986214 : ℝ) / 10000000 < Real.cos (Real.pi / 60) := by
        linarith only [ht.2.2.1]
      have htCosUpper :
          Real.cos (Real.pi / 60) < (9986311 : ℝ) / 10000000 := by
        linarith only [ht.2.2.2]
      have huSinLower :
          (444683 : ℝ) / 10000000 <
            Real.sin (17 * Real.pi / 1200) := by
        linarith only [hu.1]
      have huCosUpper :
          Real.cos (17 * Real.pi / 1200) <
            (9990109 : ℝ) / 10000000 := by
        linarith only [hu.2.2.2]
      have hvSinUpper :
          Real.sin (49 * Real.pi / 3600) <
            (428622 : ℝ) / 10000000 := by
        linarith only [hv.2.1]
      have hvSinLower :
          (427255 : ℝ) / 10000000 <
            Real.sin (49 * Real.pi / 3600) := by
        linarith only [hv.1]
      have hvCosLower :
          (9990806 : ℝ) / 10000000 <
            Real.cos (49 * Real.pi / 3600) := by
        linarith only [hv.2.2.1]
    
      have hsqrt2 :
          (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hsqrt3 :
          (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have hsqrt5 :
          (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      have hsqrt2Nonneg := Real.sqrt_nonneg 2
      have hsqrt3Nonneg := Real.sqrt_nonneg 3
      have hsqrt5Nonneg := Real.sqrt_nonneg 5
      have hsqrt2Lower :
          (1414213 : ℝ) / 1000000 < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have hsqrt2Upper :
          Real.sqrt 2 < (1414214 : ℝ) / 1000000 := by
        rw [Real.sqrt_lt (by norm_num) (by norm_num)]
        norm_num
      have hsqrt3Lower :
          (1732050 : ℝ) / 1000000 < Real.sqrt 3 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have hsqrt3Upper :
          Real.sqrt 3 < (1732051 : ℝ) / 1000000 := by
        rw [Real.sqrt_lt (by norm_num) (by norm_num)]
        norm_num
      have hsqrt5Lower :
          (2236067 : ℝ) / 1000000 < Real.sqrt 5 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have hsqrt5Upper :
          Real.sqrt 5 < (2236068 : ℝ) / 1000000 := by
        rw [Real.sqrt_lt (by norm_num) (by norm_num)]
        norm_num
    
      have hSin18Exact :
          Real.sin (Real.pi / 10) = (Real.sqrt 5 - 1) / 4 := by
        rw [← Real.cos_pi_div_two_sub]
        rw [show Real.pi / 2 - Real.pi / 10 =
            2 * (Real.pi / 5) by ring,
          Real.cos_two_mul, Real.cos_pi_div_five]
        nlinarith only [hsqrt5]
      have hSin42Exact :
          Real.sin (7 * Real.pi / 30) =
            Real.sqrt 2 / 2 *
              (Real.cos (Real.pi / 60) - Real.sin (Real.pi / 60)) := by
        rw [show 7 * Real.pi / 30 =
            Real.pi / 4 - Real.pi / 60 by ring,
          Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
        ring
      have hSinLowerEndpointExact :
          Real.sin (61 * Real.pi / 400) =
            1 / 2 * Real.cos (17 * Real.pi / 1200) -
              Real.sqrt 3 / 2 * Real.sin (17 * Real.pi / 1200) := by
        rw [show 61 * Real.pi / 400 =
            Real.pi / 6 - 17 * Real.pi / 1200 by ring,
          Real.sin_sub, Real.sin_pi_div_six, Real.cos_pi_div_six]
      have hSinUpperEndpointExact :
          Real.sin (551 * Real.pi / 3600) =
            1 / 2 * Real.cos (49 * Real.pi / 3600) -
              Real.sqrt 3 / 2 * Real.sin (49 * Real.pi / 3600) := by
        rw [show 551 * Real.pi / 3600 =
            Real.pi / 6 - 49 * Real.pi / 3600 by ring,
          Real.sin_sub, Real.sin_pi_div_six, Real.cos_pi_div_six]
    
      have hSin18Lower :
          (3090167 : ℝ) / 10000000 < Real.sin (Real.pi / 10) := by
        rw [hSin18Exact]
        linarith only [hsqrt5Lower]
      have hSin18Upper :
          Real.sin (Real.pi / 10) < (309017 : ℝ) / 1000000 := by
        rw [hSin18Exact]
        linarith only [hsqrt5Upper]
      have hSin42Lower :
          (669024 : ℝ) / 1000000 < Real.sin (7 * Real.pi / 30) := by
        rw [hSin42Exact]
        have hdiff :
            (9461448 : ℝ) / 10000000 <
              Real.cos (Real.pi / 60) - Real.sin (Real.pi / 60) := by
          linarith only [htCosLower, htSinUpper]
        have hp := mul_lt_mul'' hsqrt2Lower hdiff
          (by norm_num) (by norm_num)
        calc
          (669024 : ℝ) / 1000000 <
              ((1414213 : ℝ) / 1000000) *
                ((9461448 : ℝ) / 10000000) / 2 := by norm_num
          _ < Real.sqrt 2 *
              (Real.cos (Real.pi / 60) - Real.sin (Real.pi / 60)) /
                2 := by linarith only [hp]
          _ = Real.sqrt 2 / 2 *
              (Real.cos (Real.pi / 60) - Real.sin (Real.pi / 60)) := by
            ring
      have hSin42Upper :
          Real.sin (7 * Real.pi / 30) < (669152 : ℝ) / 1000000 := by
        rw [hSin42Exact]
        have hdiff :
            Real.cos (Real.pi / 60) - Real.sin (Real.pi / 60) <
              (9463223 : ℝ) / 10000000 := by
          linarith only [htCosUpper, htSinLower]
        have hp := mul_lt_mul'' hsqrt2Upper hdiff hsqrt2Nonneg (by
          linarith only [htCosLower, htSinUpper])
        calc
          Real.sqrt 2 / 2 *
                (Real.cos (Real.pi / 60) - Real.sin (Real.pi / 60)) =
              Real.sqrt 2 *
                (Real.cos (Real.pi / 60) - Real.sin (Real.pi / 60)) /
              2 := by ring
          _ <
              ((1414214 : ℝ) / 1000000) *
                ((9463223 : ℝ) / 10000000) / 2 := by
            linarith only [hp]
          _ < (669152 : ℝ) / 1000000 := by norm_num
      have hSinLowerEndpointUpper :
          Real.sin (61 * Real.pi / 400) < (461 : ℝ) / 1000 := by
        rw [hSinLowerEndpointExact]
        have hp := mul_lt_mul'' hsqrt3Lower huSinLower
          (by norm_num) (by norm_num)
        linarith only [hp, huCosUpper]
      have hSinUpperEndpointLower :
          (4624 : ℝ) / 10000 < Real.sin (551 * Real.pi / 3600) := by
        rw [hSinUpperEndpointExact]
        have hp := mul_lt_mul'' hsqrt3Upper hvSinUpper hsqrt3Nonneg
          (by linarith only [hvSinLower])
        linarith only [hp, hvCosLower]
    
      have hSin42RealPos : 0 < Real.sin (7 * Real.pi / 30) := by
        linarith
      have hSinLowerEndpointPos :
          0 < Real.sin (61 * Real.pi / 400) :=
        Real.sin_pos_of_pos_of_lt_pi (by positivity) (by
          nlinarith only [Real.pi_pos])
      have hSinUpperEndpointPos :
          0 < Real.sin (551 * Real.pi / 3600) :=
        Real.sin_pos_of_pos_of_lt_pi (by positivity) (by
          nlinarith only [Real.pi_pos])
      have hRatioLower :
          Real.sin (61 * Real.pi / 400) <
            Real.sin (Real.pi / 10) / Real.sin (7 * Real.pi / 30) := by
        apply (lt_div_iff₀ hSin42RealPos).2
        calc
          Real.sin (61 * Real.pi / 400) * Real.sin (7 * Real.pi / 30) <
              ((461 : ℝ) / 1000) * Real.sin (7 * Real.pi / 30) :=
            mul_lt_mul_of_pos_right hSinLowerEndpointUpper hSin42RealPos
          _ < ((461 : ℝ) / 1000) * ((669152 : ℝ) / 1000000) :=
            mul_lt_mul_of_pos_left hSin42Upper (by norm_num)
          _ < Real.sin (Real.pi / 10) := by
            linarith only [hSin18Lower]
      have hRatioUpper :
          Real.sin (Real.pi / 10) / Real.sin (7 * Real.pi / 30) <
            Real.sin (551 * Real.pi / 3600) := by
        apply (div_lt_iff₀ hSin42RealPos).2
        calc
          Real.sin (Real.pi / 10) < (309017 : ℝ) / 1000000 :=
            hSin18Upper
          _ < ((4624 : ℝ) / 10000) * ((669024 : ℝ) / 1000000) := by
            norm_num
          _ < Real.sin (551 * Real.pi / 3600) *
              ((669024 : ℝ) / 1000000) :=
            mul_lt_mul_of_pos_right hSinUpperEndpointLower (by norm_num)
          _ < Real.sin (551 * Real.pi / 3600) *
              Real.sin (7 * Real.pi / 30) :=
            mul_lt_mul_of_pos_left hSin42Lower hSinUpperEndpointPos
      have hArcLower :
          61 * Real.pi / 400 <
            Real.arcsin
              (Real.sin (Real.pi / 10) / Real.sin (7 * Real.pi / 30)) := by
        apply (Real.lt_arcsin_iff_sin_lt' (by
          constructor <;> nlinarith only [Real.pi_pos])).2
        exact hRatioLower
      have hArcUpper :
          Real.arcsin
              (Real.sin (Real.pi / 10) / Real.sin (7 * Real.pi / 30)) <
            551 * Real.pi / 3600 := by
        apply (Real.arcsin_lt_iff_lt_sin' (by
          constructor <;> nlinarith only [Real.pi_pos])).2
        exact hRatioUpper
      have hDegreesLower :
          (27.45 : ℝ) <
            Real.arcsin
                (Real.sin (Real.pi / 10) / Real.sin (7 * Real.pi / 30)) *
              180 / Real.pi := by
        calc
          (27.45 : ℝ) = (61 * Real.pi / 400) * 180 / Real.pi := by
            field_simp
            ring
          _ < Real.arcsin
                (Real.sin (Real.pi / 10) / Real.sin (7 * Real.pi / 30)) *
              180 / Real.pi := by
            exact div_lt_div_of_pos_right
              (mul_lt_mul_of_pos_right hArcLower (by norm_num)) Real.pi_pos
      have hDegreesUpper :
          Real.arcsin
                (Real.sin (Real.pi / 10) / Real.sin (7 * Real.pi / 30)) *
              180 / Real.pi < (27.55 : ℝ) := by
        calc
          Real.arcsin
                (Real.sin (Real.pi / 10) / Real.sin (7 * Real.pi / 30)) *
              180 / Real.pi <
              (551 * Real.pi / 3600) * 180 / Real.pi := by
            exact div_lt_div_of_pos_right
              (mul_lt_mul_of_pos_right hArcUpper (by norm_num)) Real.pi_pos
          _ = (27.55 : ℝ) := by
            field_simp
            ring
      change
        |Real.arcsin
              (Real.sin (Real.pi / 10) / Real.sin (7 * Real.pi / 30)) *
            180 / Real.pi - 27.5| < (1 : ℝ) / 20
      set_option maxHeartbeats 1000000 in
        rw [abs_lt]
        constructor <;> nlinarith only [hDegreesLower, hDegreesUpper]
    
end PhyXMiniProblems.ProblemPhyXMini0016
