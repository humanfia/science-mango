import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Physlib.SpaceAndTime.Space.LengthUnit

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0061

/-!
# A ray reflected by a vertical mirror

Points are represented by two scalar coordinate readouts: the first is
horizontal position, and the second is downward position.  The setup carries
the physical `LengthUnit` used for these readouts; the primary figure fixes it
to Physlib's `LengthUnit.centimeters`.
-/

/-- A two-dimensional point represented by scalar coordinate readouts. -/
abbrev FigurePoint := EuclideanSpace ℝ (Fin 2)

/-- Construct a figure point from horizontal and downward coordinate readouts. -/
def pointFromReadouts (horizontal downward : ℝ) : FigurePoint :=
  !₂[horizontal, downward]

/-- The horizontal scalar readout of a figure point. -/
def horizontalReadout (point : FigurePoint) : ℝ :=
  point 0

/-- The downward scalar readout of a figure point. -/
def downwardReadout (point : FigurePoint) : ℝ :=
  point 1

/-- The vertical mirror, including its distinguished top edge. -/
structure VerticalMirror where
  topEdge : FigurePoint
  surface : Set FigurePoint

/--
The geometrical-optics ray path from the labelled source `A`, through its
single point of reflection on the mirror, to the labelled receiver `B`.
-/
structure ReflectedLightRay where
  sourceA : FigurePoint
  mirrorStrike : FigurePoint
  receiverB : FigurePoint

/-- The coordinate unit, mirror, and reflected light ray depicted in the problem. -/
structure MirrorRaySetup where
  coordinateLengthUnit : LengthUnit
  mirror : VerticalMirror
  ray : ReflectedLightRay

/--
The point one centimeter to the left of the strike point on the horizontal
normal to the vertical mirror.  It is used only to specify the direction of
the normal in Mathlib's angle API.
-/
private def leftNormalReferencePoint (strike : FigurePoint) : FigurePoint :=
  pointFromReadouts
    (horizontalReadout strike - 1)
    (downwardReadout strike)

/--
Primary-image readouts, in a coordinate gauge whose origin is the mirror's top
edge.  The image places `A` 10 cm from the mirror and 5 cm below its top, and
places `B` 15 cm from the mirror and 15 cm below its top.  The strike point is
required only to lie on the vertical mirror; its unknown depth is not assigned
here.
-/
structure MatchesMirrorRayFigure (setup : MirrorRaySetup) : Prop where
  coordinateUnitIsCentimeters :
    setup.coordinateLengthUnit = LengthUnit.centimeters
  mirrorTopCoordinates :
    setup.mirror.topEdge = pointFromReadouts 0 0
  sourceACoordinates :
    setup.ray.sourceA = pointFromReadouts (-10) 5
  receiverBCoordinates :
    setup.ray.receiverB = pointFromReadouts (-15) 15
  topEdgeOnMirror :
    setup.mirror.topEdge ∈ setup.mirror.surface
  mirrorVertical :
    ∀ point ∈ setup.mirror.surface,
      horizontalReadout point = horizontalReadout setup.mirror.topEdge
  topEdgeIsTopmost :
    ∀ point ∈ setup.mirror.surface,
      downwardReadout setup.mirror.topEdge ≤ downwardReadout point
  strikeOnMirror :
    setup.ray.mirrorStrike ∈ setup.mirror.surface

/--
The physical single-bounce branch selected by a ray travelling from `A` to
`B`: its mirror strike lies strictly between the two endpoint levels.  This
qualitative branch condition excludes the equal-angle continuation on the
wrong side of both endpoints without assigning the requested depth.
-/
def FollowsSingleReflectionBranch (setup : MirrorRaySetup) : Prop :=
  downwardReadout setup.ray.sourceA <
      downwardReadout setup.ray.mirrorStrike ∧
    downwardReadout setup.ray.mirrorStrike <
      downwardReadout setup.ray.receiverB

/--
The law of specular reflection: the incident and reflected ray segments make
equal undirected angles with the horizontal normal to the vertical mirror.
-/
def SatisfiesLawOfReflection (setup : MirrorRaySetup) : Prop :=
  EuclideanGeometry.angle
      setup.ray.sourceA
      setup.ray.mirrorStrike
      (leftNormalReferencePoint setup.ray.mirrorStrike) =
    EuclideanGeometry.angle
      (leftNormalReferencePoint setup.ray.mirrorStrike)
      setup.ray.mirrorStrike
      setup.ray.receiverB

/-- The strike point's depth below the mirror's actual top edge. -/
def strikeDepthBelowTopEdgeCentimeters (setup : MirrorRaySetup) : ℝ :=
  downwardReadout setup.ray.mirrorStrike -
    downwardReadout setup.mirror.topEdge

/-- The four printed multiple-choice labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The centimeter readout printed beside each answer choice. -/
def AnswerChoice.distanceCentimeters : AnswerChoice → ℝ
  | .A => 1.4
  | .B => 5.6
  | .C => 4.0
  | .D => 2.4

/-- Dataset metadata: the recorded multiple-choice answer is choice C. -/
def recordedAnswerChoice : AnswerChoice := .C

/--
Equal reflection angles make the strike point 4 cm below the level of `A`.
The primary image puts `A` itself 5 cm below the mirror's actual top edge, so
the strike point is 9 cm below that edge.  The source's recorded choice C is
retained above only as metadata: its printed `4.0 cm` is the drop from `A`, not
the top-edge distance asked for, and therefore is not asserted as the answer.

This formalizes `thm:physics:phyx_mini_0061:target`.
-/
theorem problem_phyx_mini_0061
    (setup : MirrorRaySetup)
    (hFigure : MatchesMirrorRayFigure setup)
    (hBranch : FollowsSingleReflectionBranch setup)
    (hReflection : SatisfiesLawOfReflection setup) :
    strikeDepthBelowTopEdgeCentimeters setup = 9 := by
  have hStrikeHorizontal :
      horizontalReadout setup.ray.mirrorStrike = 0 := by
    calc
      horizontalReadout setup.ray.mirrorStrike =
          horizontalReadout setup.mirror.topEdge :=
        hFigure.mirrorVertical setup.ray.mirrorStrike hFigure.strikeOnMirror
      _ = 0 := by
        rw [hFigure.mirrorTopCoordinates]
        rfl
  have hStrikeCoordinates :
      setup.ray.mirrorStrike =
        pointFromReadouts 0 (downwardReadout setup.ray.mirrorStrike) := by
    ext i
    fin_cases i
    · exact hStrikeHorizontal
    · rfl
  let y := downwardReadout setup.ray.mirrorStrike
  have hBranch' : 5 < y ∧ y < 15 := by
    simpa [FollowsSingleReflectionBranch, y, hFigure.sourceACoordinates,
      hFigure.receiverBCoordinates, pointFromReadouts, downwardReadout] using hBranch
  have hAngle :
      InnerProductGeometry.angle
          (!₂[(-10 : ℝ), 5 - y] : FigurePoint)
          (!₂[(-1 : ℝ), 0] : FigurePoint) =
        InnerProductGeometry.angle
          (!₂[(-1 : ℝ), 0] : FigurePoint)
          (!₂[(-15 : ℝ), 15 - y] : FigurePoint) := by
    unfold SatisfiesLawOfReflection at hReflection
    rw [hFigure.sourceACoordinates, hFigure.receiverBCoordinates,
      hStrikeCoordinates] at hReflection
    simp only [EuclideanGeometry.angle] at hReflection
    change
      InnerProductGeometry.angle
          (pointFromReadouts (-10) 5 - pointFromReadouts 0 y)
          (leftNormalReferencePoint (pointFromReadouts 0 y) -
            pointFromReadouts 0 y) =
        InnerProductGeometry.angle
          (leftNormalReferencePoint (pointFromReadouts 0 y) -
            pointFromReadouts 0 y)
          (pointFromReadouts (-15) 15 - pointFromReadouts 0 y) at hReflection
    have hIncident :
        (pointFromReadouts (-10) 5 - pointFromReadouts 0 y : FigurePoint) =
          !₂[(-10 : ℝ), 5 - y] := by
      ext i
      fin_cases i <;> simp [pointFromReadouts]
    have hNormal :
        (leftNormalReferencePoint (pointFromReadouts 0 y) -
            pointFromReadouts 0 y : FigurePoint) =
          !₂[(-1 : ℝ), 0] := by
      ext i
      fin_cases i <;>
        simp [pointFromReadouts, leftNormalReferencePoint, horizontalReadout,
          downwardReadout]
    have hReflected :
        (pointFromReadouts (-15) 15 - pointFromReadouts 0 y : FigurePoint) =
          !₂[(-15 : ℝ), 15 - y] := by
      ext i
      fin_cases i <;> simp [pointFromReadouts]
    rw [hIncident, hNormal, hReflected] at hReflection
    exact hReflection
  have hCos := congrArg Real.cos hAngle
  rw [InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle] at hCos
  have hIncidentNe :
      (!₂[(-10 : ℝ), 5 - y] : FigurePoint) ≠ 0 := by
    intro h
    have h0 := congrArg (fun p : FigurePoint => p 0) h
    norm_num at h0
  have hReflectedNe :
      (!₂[(-15 : ℝ), 15 - y] : FigurePoint) ≠ 0 := by
    intro h
    have h0 := congrArg (fun p : FigurePoint => p 0) h
    norm_num at h0
  have hNormalNorm :
      ‖(!₂[(-1 : ℝ), 0] : FigurePoint)‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    norm_num
  have hIncidentNormSq :
      ‖(!₂[(-10 : ℝ), 5 - y] : FigurePoint)‖ ^ 2 =
        100 + (5 - y) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num
  have hReflectedNormSq :
      ‖(!₂[(-15 : ℝ), 15 - y] : FigurePoint)‖ ^ 2 =
        225 + (15 - y) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num
  have hNormRatio :
      10 / ‖(!₂[(-10 : ℝ), 5 - y] : FigurePoint)‖ =
        15 / ‖(!₂[(-15 : ℝ), 15 - y] : FigurePoint)‖ := by
    simpa [PiLp.inner_apply, hNormalNorm] using hCos
  have hNormCross :
      10 * ‖(!₂[(-15 : ℝ), 15 - y] : FigurePoint)‖ =
        15 * ‖(!₂[(-10 : ℝ), 5 - y] : FigurePoint)‖ := by
    field_simp [norm_ne_zero_iff.mpr hIncidentNe,
      norm_ne_zero_iff.mpr hReflectedNe] at hNormRatio
    linarith
  have hPolynomial :
      100 * (225 + (15 - y) ^ 2) =
        225 * (100 + (5 - y) ^ 2) := by
    calc
      100 * (225 + (15 - y) ^ 2) =
          (10 * ‖(!₂[(-15 : ℝ), 15 - y] : FigurePoint)‖) ^ 2 := by
            rw [mul_pow, hReflectedNormSq]
            ring
      _ = (15 * ‖(!₂[(-10 : ℝ), 5 - y] : FigurePoint)‖) ^ 2 := by
            rw [hNormCross]
      _ = 225 * (100 + (5 - y) ^ 2) := by
            rw [mul_pow, hIncidentNormSq]
            ring
  have hy : y = 9 := by
    rcases hBranch' with ⟨hyLower, hyUpper⟩
    nlinarith [sq_nonneg (y - 5), sq_nonneg (15 - y)]
  change
    downwardReadout setup.ray.mirrorStrike -
      downwardReadout setup.mirror.topEdge = 9
  rw [hFigure.mirrorTopCoordinates]
  change y - 0 = 9
  norm_num [hy]

end PhyXMiniProblems.ProblemPhyXMini0061
