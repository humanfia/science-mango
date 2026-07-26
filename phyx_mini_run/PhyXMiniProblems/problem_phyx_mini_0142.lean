import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Physlib.Optics.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0142

/-!
# Two successive reflections from perpendicular plane mirrors

The supplied figure shows a horizontal first mirror meeting a vertical second
mirror at a right angle. A light ray arrives at the first mirror at `15°` to
its surface, reflects toward the second mirror, and reflects once more.

The ambient optical plane is genuine two-dimensional Euclidean space. Point
coordinates are scalar readouts in meters, ray-travel parameters carry
Physlib's length dimension, and propagation, tangent, and normal vectors are
dimensionless directions. Every angular readout below is a real number measured
in radians; `degreesInRadians` converts the degree labels printed in the figure.
-/

/-- The two-dimensional Euclidean laboratory plane used by the ray diagram. -/
abbrev OpticalPlane := EuclideanSpace ℝ (Fin 2)

/-- Convert a degree readout to its real-valued radian measure. -/
def degreesInRadians (value : ℝ) : ℝ :=
  value * Real.pi / 180

/-- The two flat mirrors, named in the order in which the beam meets them. -/
inductive MirrorLabel where
  | first
  | second
  deriving DecidableEq, Repr

/-- The three directed portions of the light path visible in the figure. -/
inductive RaySegment where
  | incoming
  | betweenMirrors
  | outgoing
  deriving DecidableEq, Repr

/-- The two physical reflection events. -/
inductive ReflectionSite where
  | atFirstMirror
  | atSecondMirror
  deriving DecidableEq, Repr

/-!
Literal angular labels in the supplied diagram. The first two constructors
retain the printed `15°` and `90°`; the remaining constructors retain
`theta_1` through `theta_5`.
-/
inductive FigureAngleLabel where
  | incidentFifteen
  | mirrorRightAngle
  | thetaOne
  | thetaTwo
  | thetaThree
  | thetaFour
  | thetaFive
  deriving DecidableEq, Repr

/-!
A flat mirror in the optical plane. Its reflective surface is an affine
subspace. The selected tangent and normal directions let the diagram's
surface-relative and normal-relative angle labels be interpreted without
identifying a physical mirror with a bare scalar.
-/
structure PlaneMirror where
  surface : AffineSubspace ℝ OpticalPlane
  tangentDirection : OpticalPlane
  normalDirection : OpticalPlane

/-!
An oriented light ray. `originMeters` is a point whose coordinates are meter
readouts and `propagationDirection` is a dimensionless direction vector.
-/
structure DirectedLightRay where
  originMeters : OpticalPlane
  propagationDirection : OpticalPlane

/--
Advance a ray by a Physlib length whose underlying scalar is read in meters in
the laboratory coordinate system.
-/
def DirectedLightRay.pointAtMeters
    (ray : DirectedLightRay)
    (distanceMeters : WithDim Dimension.L𝓭 ℝ) : OpticalPlane :=
  ray.originMeters + distanceMeters.val • ray.propagationDirection

/-!
The acute angle between the unoriented lines represented by two nonzero
vectors. Taking the smaller Mathlib angle to `w` or `-w` makes the result
independent of the selected orientation of the physical line.
-/
def lineAngleRadians (v w : OpticalPlane) : ℝ :=
  min (InnerProductGeometry.angle v w)
    (InnerProductGeometry.angle v (-w))

/-!
All physical objects and figure annotations for the experiment. Neither the
outgoing angle nor an answer choice is fixed by a field of this structure.
-/
structure PerpendicularMirrorExperiment where
  mirror : MirrorLabel → PlaneMirror
  ray : RaySegment → DirectedLightRay
  cornerMeters : OpticalPlane
  incidencePointMeters : ReflectionSite → OpticalPlane
  figureAngleRadians : FigureAngleLabel → ℝ

/-- The angle made by a ray with a selected mirror surface. -/
def rayMirrorAngleRadians
    (setup : PerpendicularMirrorExperiment)
    (ray : RaySegment) (mirror : MirrorLabel) : ℝ :=
  lineAngleRadians
    (setup.ray ray).propagationDirection
    (setup.mirror mirror).tangentDirection

/-- The angle made by a ray with a selected mirror normal. -/
def rayNormalAngleRadians
    (setup : PerpendicularMirrorExperiment)
    (ray : RaySegment) (mirror : MirrorLabel) : ℝ :=
  lineAngleRadians
    (setup.ray ray).propagationDirection
    (setup.mirror mirror).normalDirection

/-- The angle asked for in the problem: outgoing ray versus second mirror. -/
def requestedOutgoingAngleRadians
    (setup : PerpendicularMirrorExperiment) : ℝ :=
  rayMirrorAngleRadians setup .outgoing .second

/-!
A mirror surface is a genuine affine line with compatible unit tangent and
unit normal directions. Orthogonality makes the selected normal meaningful;
no outgoing-ray information appears here.
-/
def IsFlatPlaneMirror (mirror : PlaneMirror) : Prop :=
  Module.finrank ℝ mirror.surface.direction = 1 ∧
    mirror.tangentDirection ∈ mirror.surface.direction ∧
    ‖mirror.tangentDirection‖ = 1 ∧
    ‖mirror.normalDirection‖ = 1 ∧
    inner ℝ mirror.tangentDirection mirror.normalDirection = 0

/-!
Physical nondegeneracy conditions. Both mirrors are affine lines, all ray
directions are unit vectors, and the two reflection points are distinct.
-/
def HasPhysicalGeometry (setup : PerpendicularMirrorExperiment) : Prop :=
  (∀ label, IsFlatPlaneMirror (setup.mirror label)) ∧
    (∀ segment, ‖(setup.ray segment).propagationDirection‖ = 1) ∧
    setup.incidencePointMeters .atFirstMirror ≠
      setup.incidencePointMeters .atSecondMirror

/-!
The perpendicular-mirror geometry shown in the image. The mirrors meet at the
recorded corner, their tangent lines are perpendicular, and the incidence
points lie on the corresponding reflecting surfaces.
-/
def SatisfiesPerpendicularMirrorGeometry
    (setup : PerpendicularMirrorExperiment) : Prop :=
  setup.cornerMeters ∈ (setup.mirror .first).surface ∧
    setup.cornerMeters ∈ (setup.mirror .second).surface ∧
    inner ℝ (setup.mirror .first).tangentDirection
      (setup.mirror .second).tangentDirection = 0 ∧
    setup.incidencePointMeters .atFirstMirror ∈
      (setup.mirror .first).surface ∧
    setup.incidencePointMeters .atSecondMirror ∈
      (setup.mirror .second).surface

/-!
Straight, forward propagation between the labeled events. The incoming ray
reaches the first incidence point, the middle ray starts there and reaches the
second incidence point, and the outgoing ray starts at the latter point.
-/
def SatisfiesRayPathGeometry
    (setup : PerpendicularMirrorExperiment) : Prop :=
  (∃ distanceMeters : WithDim Dimension.L𝓭 ℝ,
      0 < distanceMeters.val ∧
        (setup.ray .incoming).pointAtMeters distanceMeters =
          setup.incidencePointMeters .atFirstMirror) ∧
    (setup.ray .betweenMirrors).originMeters =
      setup.incidencePointMeters .atFirstMirror ∧
    (∃ distanceMeters : WithDim Dimension.L𝓭 ℝ,
      0 < distanceMeters.val ∧
        (setup.ray .betweenMirrors).pointAtMeters distanceMeters =
          setup.incidencePointMeters .atSecondMirror) ∧
    (setup.ray .outgoing).originMeters =
      setup.incidencePointMeters .atSecondMirror

/-!
Mathlib's subspace reflection reverses the normal component of a direction
and preserves its component tangent to the mirror. This is the vector form of
the law of specular reflection for a flat mirror.
-/
def IsSpecularReflectionAt
    (incident reflected : DirectedLightRay) (mirror : PlaneMirror) : Prop :=
  reflected.propagationDirection =
    mirror.surface.direction.reflection incident.propagationDirection

/-- The law of reflection is imposed independently at each physical mirror. -/
def SatisfiesSpecularReflectionLaws
    (setup : PerpendicularMirrorExperiment) : Prop :=
  IsSpecularReflectionAt
      (setup.ray .incoming) (setup.ray .betweenMirrors)
      (setup.mirror .first) ∧
    IsSpecularReflectionAt
      (setup.ray .betweenMirrors) (setup.ray .outgoing)
      (setup.mirror .second)

/-!
Figure-derived readouts and label identifications. Only the printed incident
angle and right-angle marker receive numerical values. In particular,
`thetaFive` is identified with the requested physical angle but is not set to
`75°` here.
-/
def MatchesSuppliedFigure
    (setup : PerpendicularMirrorExperiment) : Prop :=
  setup.figureAngleRadians .incidentFifteen = degreesInRadians 15 ∧
    setup.figureAngleRadians .mirrorRightAngle = degreesInRadians 90 ∧
    setup.figureAngleRadians .mirrorRightAngle =
      lineAngleRadians
        (setup.mirror .first).tangentDirection
        (setup.mirror .second).tangentDirection ∧
    setup.figureAngleRadians .incidentFifteen =
      rayMirrorAngleRadians setup .incoming .first ∧
    setup.figureAngleRadians .thetaOne =
      rayNormalAngleRadians setup .incoming .first ∧
    setup.figureAngleRadians .thetaTwo =
      rayNormalAngleRadians setup .betweenMirrors .first ∧
    setup.figureAngleRadians .thetaThree =
      rayNormalAngleRadians setup .betweenMirrors .second ∧
    setup.figureAngleRadians .thetaFour =
      rayNormalAngleRadians setup .outgoing .second ∧
    setup.figureAngleRadians .thetaFive =
      requestedOutgoingAngleRadians setup

/-- The four displayed multiple-choice labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Degree readout printed beside each multiple-choice label. -/
def answerAngleDegrees : AnswerChoice → ℝ
  | .A => 55
  | .B => 65
  | .C => 75
  | .D => 45

/-!
Reflection at the first flat mirror preserves the acute angle with that
mirror, so the between-mirrors ray also makes `15°` with the first surface.
-/
lemma betweenMirrors_angleWithFirst_eq_fifteen
    (setup : PerpendicularMirrorExperiment)
    (h_physical : HasPhysicalGeometry setup)
    (h_figure : MatchesSuppliedFigure setup)
    (h_reflection : SatisfiesSpecularReflectionLaws setup) :
    rayMirrorAngleRadians setup .betweenMirrors .first =
      degreesInRadians 15 := by
  have reflection_preserves_lineAngle
      (K : Submodule ℝ OpticalPlane) (v t : OpticalPlane) (ht : t ∈ K) :
      lineAngleRadians (K.reflection v) t = lineAngleRadians v t := by
    have hfix : K.reflection t = t :=
      Submodule.reflection_mem_subspace_eq_self ht
    unfold lineAngleRadians
    calc
      min (InnerProductGeometry.angle (K.reflection v) t)
          (InnerProductGeometry.angle (K.reflection v) (-t)) =
        min (InnerProductGeometry.angle (K.reflection v) (K.reflection t))
          (InnerProductGeometry.angle (K.reflection v) (K.reflection (-t))) := by
            rw [hfix, map_neg, hfix]
      _ = _ := congrArg₂ min
        (K.reflection.toLinearIsometry.angle_map v t)
        (K.reflection.toLinearIsometry.angle_map v (-t))
  have h_firstReflection := h_reflection.1
  unfold IsSpecularReflectionAt at h_firstReflection
  rcases h_figure with
    ⟨h_fifteen, _, _, h_incident, _, _, _, _, _⟩
  calc
    rayMirrorAngleRadians setup .betweenMirrors .first =
        rayMirrorAngleRadians setup .incoming .first := by
      unfold rayMirrorAngleRadians
      rw [h_firstReflection]
      exact reflection_preserves_lineAngle
        (setup.mirror .first).surface.direction
        (setup.ray .incoming).propagationDirection
        (setup.mirror .first).tangentDirection
        (h_physical.1 .first).2.1
    _ = setup.figureAngleRadians .incidentFifteen := h_incident.symm
    _ = degreesInRadians 15 := h_fifteen

/-!
Because the second mirror is perpendicular to the first, the incoming ray at
that mirror makes the complementary angle `75°` with its surface.
-/
lemma betweenMirrors_angleWithSecond_eq_seventyFive
    (setup : PerpendicularMirrorExperiment)
    (h_physical : HasPhysicalGeometry setup)
    (h_geometry : SatisfiesPerpendicularMirrorGeometry setup)
    (h_figure : MatchesSuppliedFigure setup)
    (h_reflection : SatisfiesSpecularReflectionLaws setup) :
    rayMirrorAngleRadians setup .betweenMirrors .second =
      degreesInRadians 75 := by
  have lineAngle_eq_arccos_abs
      (u w : OpticalPlane) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
      lineAngleRadians u w = Real.arccos |inner ℝ u w| := by
    unfold lineAngleRadians InnerProductGeometry.angle
    simp only [hu, hw, norm_neg, one_mul, div_one, inner_neg_right]
    by_cases h : 0 ≤ inner ℝ u w
    · rw [abs_of_nonneg h, min_eq_left]
      exact Real.arccos_le_arccos (by linarith)
    · have h' : inner ℝ u w < 0 := lt_of_not_ge h
      rw [abs_of_neg h', min_eq_right]
      exact Real.arccos_le_arccos (by linarith)
  have perpendicular_lineAngles_complementary
      (v x y : OpticalPlane)
      (hv : ‖v‖ = 1) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
      (hxy : inner ℝ x y = 0) :
      lineAngleRadians v y = Real.pi / 2 - lineAngleRadians v x := by
    have hsquares :
        (inner ℝ v x) ^ 2 + (inner ℝ v y) ^ 2 = 1 := by
      let e : Fin 2 → OpticalPlane := ![x, y]
      have heorth : Orthonormal ℝ e := (orthonormal_iff_ite).2 (by
        intro i j
        fin_cases i <;> fin_cases j
        · simp [e, hx]
        · simp [e, hxy]
        · simp [e, real_inner_comm, hxy]
        · simp [e, hy])
      have hcard :
          Fintype.card (Fin 2) = Module.finrank ℝ OpticalPlane := by
        simp [finrank_euclideanSpace]
      let basis : Module.Basis (Fin 2) ℝ OpticalPlane :=
        basisOfOrthonormalOfCardEqFinrank heorth hcard
      have hbasis : (basis : Fin 2 → OpticalPlane) = e :=
        coe_basisOfOrthonormalOfCardEqFinrank heorth hcard
      have hborth : Orthonormal ℝ basis := by
        simpa [hbasis] using heorth
      let b : OrthonormalBasis (Fin 2) ℝ OpticalPlane :=
        basis.toOrthonormalBasis hborth
      have hb : (b : Fin 2 → OpticalPlane) = e := by
        simpa [b, hbasis] using
          Module.Basis.coe_toOrthonormalBasis basis hborth
      have hparseval := b.sum_inner_mul_inner v v
      simp only [Fin.sum_univ_two] at hparseval
      rw [show b 0 = x by simpa [hb, e],
        show b 1 = y by simpa [hb, e]] at hparseval
      rw [real_inner_self_eq_norm_sq, hv] at hparseval
      simpa only [pow_two, real_inner_comm v x, real_inner_comm v y, one_mul]
        using hparseval
    rw [lineAngle_eq_arccos_abs v y hv hy,
      lineAngle_eq_arccos_abs v x hv hx]
    apply Real.arccos_eq_of_eq_cos
    · exact sub_nonneg.mpr
        ((Real.arccos_le_pi_div_two).2 (abs_nonneg _))
    · linarith [Real.pi_nonneg, Real.arccos_nonneg |inner ℝ v x|]
    · rw [Real.cos_pi_div_two_sub, Real.sin_arccos]
      have habsSquares :
          |inner ℝ v y| ^ 2 = 1 - |inner ℝ v x| ^ 2 := by
        rw [sq_abs, sq_abs]
        linarith
      calc
        |inner ℝ v y| = Real.sqrt (|inner ℝ v y| ^ 2) :=
          (Real.sqrt_sq (abs_nonneg _)).symm
        _ = Real.sqrt (1 - |inner ℝ v x| ^ 2) :=
          congrArg Real.sqrt habsSquares
  have h_first :=
    betweenMirrors_angleWithFirst_eq_fifteen
      setup h_physical h_figure h_reflection
  calc
    rayMirrorAngleRadians setup .betweenMirrors .second =
        Real.pi / 2 -
          rayMirrorAngleRadians setup .betweenMirrors .first := by
      exact perpendicular_lineAngles_complementary
        (setup.ray .betweenMirrors).propagationDirection
        (setup.mirror .first).tangentDirection
        (setup.mirror .second).tangentDirection
        (h_physical.2.1 .betweenMirrors)
        ((h_physical.1 .first).2.2.1)
        ((h_physical.1 .second).2.2.1)
        h_geometry.2.2.1
    _ = degreesInRadians 75 := by
      rw [h_first]
      unfold degreesInRadians
      ring

/-!
Specular reflection at the second mirror preserves the acute surface-relative
angle. Thus the outgoing ray and the figure label `theta_5` both have the
requested value `75°`.
-/
lemma outgoing_angle_and_thetaFive_eq_seventyFive
    (setup : PerpendicularMirrorExperiment)
    (h_physical : HasPhysicalGeometry setup)
    (h_geometry : SatisfiesPerpendicularMirrorGeometry setup)
    (h_figure : MatchesSuppliedFigure setup)
    (h_reflection : SatisfiesSpecularReflectionLaws setup) :
    requestedOutgoingAngleRadians setup = degreesInRadians 75 ∧
      setup.figureAngleRadians .thetaFive = degreesInRadians 75 := by
  have h_between :=
    betweenMirrors_angleWithSecond_eq_seventyFive
      setup h_physical h_geometry h_figure h_reflection
  have reflection_preserves_lineAngle
      (K : Submodule ℝ OpticalPlane) (v t : OpticalPlane) (ht : t ∈ K) :
      lineAngleRadians (K.reflection v) t = lineAngleRadians v t := by
    have hfix : K.reflection t = t :=
      Submodule.reflection_mem_subspace_eq_self ht
    unfold lineAngleRadians
    calc
      min (InnerProductGeometry.angle (K.reflection v) t)
          (InnerProductGeometry.angle (K.reflection v) (-t)) =
        min (InnerProductGeometry.angle (K.reflection v) (K.reflection t))
          (InnerProductGeometry.angle (K.reflection v) (K.reflection (-t))) := by
            rw [hfix, map_neg, hfix]
      _ = _ := congrArg₂ min
        (K.reflection.toLinearIsometry.angle_map v t)
        (K.reflection.toLinearIsometry.angle_map v (-t))
  have h_secondReflection := h_reflection.2
  unfold IsSpecularReflectionAt at h_secondReflection
  have h_outgoing :
      requestedOutgoingAngleRadians setup = degreesInRadians 75 := by
    unfold requestedOutgoingAngleRadians rayMirrorAngleRadians
    rw [h_secondReflection]
    exact (reflection_preserves_lineAngle
      (setup.mirror .second).surface.direction
      (setup.ray .betweenMirrors).propagationDirection
      (setup.mirror .second).tangentDirection
      (h_physical.1 .second).2.1).trans h_between
  constructor
  · exact h_outgoing
  · exact h_figure.2.2.2.2.2.2.2.2.trans h_outgoing

/-!
For the complete ray path shown between the two perpendicular flat mirrors,
the outgoing beam makes `75°` with the second mirror. This is exactly answer
choice C.

This formalizes `thm:physics:phyx_mini_0142:target`. The target value `75°`
and choice C occur only in derived conclusions and in the answer-choice table,
never in the experiment data, figure readouts, or governing-law premises.
-/
theorem problem_phyx_mini_0142
    (setup : PerpendicularMirrorExperiment)
    (h_physical : HasPhysicalGeometry setup)
    (h_geometry : SatisfiesPerpendicularMirrorGeometry setup)
    (h_path : SatisfiesRayPathGeometry setup)
    (h_figure : MatchesSuppliedFigure setup)
    (h_reflection : SatisfiesSpecularReflectionLaws setup) :
    requestedOutgoingAngleRadians setup =
        degreesInRadians (answerAngleDegrees .C) ∧
      setup.figureAngleRadians .thetaFive =
        degreesInRadians (answerAngleDegrees .C) := by
  simpa [answerAngleDegrees] using
    outgoing_angle_and_thetaFive_eq_seventyFive
      setup h_physical h_geometry h_figure h_reflection

end PhyXMiniProblems.ProblemPhyXMini0142
