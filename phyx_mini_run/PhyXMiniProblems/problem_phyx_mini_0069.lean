import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Physlib.SpaceAndTime.Space.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0069

/-!
# A laser reflected successively by two plane mirrors

The primary image shows two plane mirrors meeting in an inverted `V` with an
interior apex angle of `80°`.  The incident laser travels upward, antiparallel
to the downward-pointing interior angle bisector.  It strikes the left mirror,
then the right mirror, and leaves downward.  The figure label `φ` is the acute
angle from the downward bisector to that final outgoing direction.

Physical points live in Physlib's two-dimensional `Space`, while propagation
directions and displacements are vectors in its associated real Euclidean
space.  Angle readouts below are real numbers in radians; the numbers printed
in the problem and figure are degree readouts.  Positive path-distance
parameters are scalar coordinate readouts in the arbitrary length unit carried
by `Space`.
-/

/-- Convert a scalar degree readout to its radian value. -/
def degreesToRadians (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/--
The one-dimensional direction subspace of a plane mirror in the diagram.
Only the tangent direction is needed to reflect a propagation direction; the
mirror's affine position is recorded separately by the path geometry.
-/
def mirrorDirectionSubspace
    (mirrorTangent : EuclideanSpace ℝ (Fin 2)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin 2)) :=
  Submodule.span ℝ {mirrorTangent}

/--
Specular reflection of a propagation direction in a plane mirror.  Mathlib's
`Submodule.reflection` fixes the mirror-tangent subspace and reverses its
orthogonal complement, which is precisely the vector form of the law of
reflection.
-/
def SatisfiesSpecularReflection
    (mirrorTangent incomingDirection outgoingDirection :
      EuclideanSpace ℝ (Fin 2)) : Prop :=
  outgoingDirection =
    (mirrorDirectionSubspace mirrorTangent).reflection incomingDirection

/--
The physical objects and ray data in the two-mirror laser setup.  Mirror
directions point from the common apex down their respective mirror faces.
The three laser directions refer, in order, to the segment before the left
reflection, the segment between the mirrors, and the final outgoing segment.
-/
structure TwoMirrorLaserSetup where
  apexPoint : Space 2
  laserSourcePoint : Space 2
  leftReflectionPoint : Space 2
  rightReflectionPoint : Space 2
  leftMirrorDirection : EuclideanSpace ℝ (Fin 2)
  rightMirrorDirection : EuclideanSpace ℝ (Fin 2)
  interiorBisectorDirection : EuclideanSpace ℝ (Fin 2)
  incidentDirection : EuclideanSpace ℝ (Fin 2)
  betweenMirrorsDirection : EuclideanSpace ℝ (Fin 2)
  outgoingDirection : EuclideanSpace ℝ (Fin 2)

/--
Problem-statement and primary-image readouts.  The positive-distance
conditions say that the displayed encounters occur on the downward mirror
rays and in the stated propagation order.  The incident direction is opposite
the downward unit bisector, matching the upward arrow in the figure.  No field
specifies `φ` or the requested `20°` conclusion.
-/
structure MatchesTwoMirrorFigure (setup : TwoMirrorLaserSetup) : Prop where
  leftMirrorDirectionUnit : ‖setup.leftMirrorDirection‖ = 1
  rightMirrorDirectionUnit : ‖setup.rightMirrorDirection‖ = 1
  interiorBisectorDirectionUnit : ‖setup.interiorBisectorDirection‖ = 1
  incidentDirectionUnit : ‖setup.incidentDirection‖ = 1
  betweenMirrorsDirectionUnit : ‖setup.betweenMirrorsDirection‖ = 1
  outgoingDirectionUnit : ‖setup.outgoingDirection‖ = 1
  apexAngleReadout :
    InnerProductGeometry.angle
        setup.leftMirrorDirection setup.rightMirrorDirection =
      degreesToRadians 80
  bisectsLeftHalfAngle :
    InnerProductGeometry.angle
        setup.leftMirrorDirection setup.interiorBisectorDirection =
      degreesToRadians 40
  bisectsRightHalfAngle :
    InnerProductGeometry.angle
        setup.interiorBisectorDirection setup.rightMirrorDirection =
      degreesToRadians 40
  incidentAntiparallelToBisector :
    setup.incidentDirection = -setup.interiorBisectorDirection
  leftEncounterOnMirrorRay :
    ∃ distanceFromApex : ℝ,
      0 < distanceFromApex ∧
        setup.leftReflectionPoint =
          distanceFromApex • setup.leftMirrorDirection +ᵥ setup.apexPoint
  rightEncounterOnMirrorRay :
    ∃ distanceFromApex : ℝ,
      0 < distanceFromApex ∧
        setup.rightReflectionPoint =
          distanceFromApex • setup.rightMirrorDirection +ᵥ setup.apexPoint
  sourceToLeftEncounter :
    ∃ travelDistance : ℝ,
      0 < travelDistance ∧
        setup.leftReflectionPoint =
          travelDistance • setup.incidentDirection +ᵥ setup.laserSourcePoint
  leftToRightEncounter :
    ∃ travelDistance : ℝ,
      0 < travelDistance ∧
        setup.rightReflectionPoint =
          travelDistance • setup.betweenMirrorsDirection +ᵥ
            setup.leftReflectionPoint

/-- The two successive applications of the governing law of reflection. -/
structure SatisfiesTwoMirrorReflectionLaws
    (setup : TwoMirrorLaserSetup) : Prop where
  reflectionAtLeftMirror :
    SatisfiesSpecularReflection setup.leftMirrorDirection
      setup.incidentDirection setup.betweenMirrorsDirection
  reflectionAtRightMirror :
    SatisfiesSpecularReflection setup.rightMirrorDirection
      setup.betweenMirrorsDirection setup.outgoingDirection

/--
The figure label `φ`: the undirected acute angle between the final outgoing
laser direction and the downward interior bisector, measured in radians.
-/
def phiRadians (setup : TwoMirrorLaserSetup) : ℝ :=
  InnerProductGeometry.angle
    setup.outgoingDirection setup.interiorBisectorDirection

/-- Labels of the four numerical answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Degree readout printed beside each answer-choice label. -/
def AnswerChoice.angleDegrees : AnswerChoice → ℝ
  | .A => 35
  | .B => 90
  | .C => 20
  | .D => 23

/-- Dataset metadata: the recorded answer is choice C. -/
def recordedAnswerChoice : AnswerChoice := .C

/--
After specular reflection first at the left mirror and then at the right
mirror, the final laser beam makes an angle `φ = 20°` with the downward
bisector of the `80°` mirror opening, so the numerical answer is choice C.

This formalizes `thm:physics:phyx_mini_0069:target`.
-/
theorem reflectedLaserAngle_eq_twenty_degrees
    (setup : TwoMirrorLaserSetup)
    (_figure : MatchesTwoMirrorFigure setup)
    (_reflectionLaws : SatisfiesTwoMirrorReflectionLaws setup) :
    phiRadians setup = degreesToRadians 20 := by
  let L := setup.leftMirrorDirection
  let R := setup.rightMirrorDirection
  let B := setup.interiorBisectorDirection
  let I := setup.incidentDirection
  let M := setup.betweenMirrorsDirection
  let O := setup.outgoingDirection
  have hL : ‖L‖ = 1 := by
    simpa [L] using _figure.leftMirrorDirectionUnit
  have hR : ‖R‖ = 1 := by
    simpa [R] using _figure.rightMirrorDirectionUnit
  have hB : ‖B‖ = 1 := by
    simpa [B] using _figure.interiorBisectorDirectionUnit
  have hO : ‖O‖ = 1 := by
    simpa [O] using _figure.outgoingDirectionUnit
  have hI : I = -B := by
    simpa [I, B] using _figure.incidentAntiparallelToBisector
  have h40 : degreesToRadians 40 = 2 * Real.pi / 9 := by
    unfold degreesToRadians
    ring
  have h80 : degreesToRadians 80 = 4 * Real.pi / 9 := by
    unfold degreesToRadians
    ring
  have h20 : degreesToRadians 20 = Real.pi / 9 := by
    unfold degreesToRadians
    ring
  have hLB : inner ℝ L B = Real.cos (2 * Real.pi / 9) := by
    rw [InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hL hB]
    rw [show InnerProductGeometry.angle L B = degreesToRadians 40 by
      simpa [L, B] using _figure.bisectsLeftHalfAngle]
    rw [h40]
  have hBR : inner ℝ B R = Real.cos (2 * Real.pi / 9) := by
    rw [InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hB hR]
    rw [show InnerProductGeometry.angle B R = degreesToRadians 40 by
      simpa [B, R] using _figure.bisectsRightHalfAngle]
    rw [h40]
  have hLR : inner ℝ L R = Real.cos (4 * Real.pi / 9) := by
    rw [InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hL hR]
    rw [show InnerProductGeometry.angle L R = degreesToRadians 80 by
      simpa [L, R] using _figure.apexAngleReadout]
    rw [h80]
  have hRB : inner ℝ R B = Real.cos (2 * Real.pi / 9) := by
    rw [real_inner_comm]
    exact hBR
  have hRL : inner ℝ R L = Real.cos (4 * Real.pi / 9) := by
    rw [real_inner_comm]
    exact hLR
  have hleftRaw :
      M = 2 • (inner ℝ L I / ‖L‖ ^ 2) • L - I := by
    have h := _reflectionLaws.reflectionAtLeftMirror
    change M = (mirrorDirectionSubspace L).reflection I at h
    simpa [mirrorDirectionSubspace, Submodule.reflection_singleton_apply] using h
  have hrightRaw :
      O = 2 • (inner ℝ R M / ‖R‖ ^ 2) • R - M := by
    have h := _reflectionLaws.reflectionAtRightMirror
    change O = (mirrorDirectionSubspace R).reflection M at h
    simpa [mirrorDirectionSubspace, Submodule.reflection_singleton_apply] using h
  have hleft :
      M = (2 * (inner ℝ L I / ‖L‖ ^ 2)) • L - I := by
    rw [hleftRaw]
    module
  have hright :
      O = (2 * (inner ℝ R M / ‖R‖ ^ 2)) • R - M := by
    rw [hrightRaw]
    module
  have hfinalInner :
      inner ℝ O B =
        4 * (Real.cos (2 * Real.pi / 9)) ^ 2 *
            (1 - Real.cos (4 * Real.pi / 9)) - 1 := by
    rw [hright, hleft, hI]
    simp only [hL, hR, hB, one_pow, div_one, inner_sub_left, inner_sub_right,
      inner_neg_left, inner_neg_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hLB, hRB, hRL]
    ring
  rw [h20]
  change InnerProductGeometry.angle O B = Real.pi / 9
  apply Real.injOn_cos
  · exact ⟨InnerProductGeometry.angle_nonneg O B,
      InnerProductGeometry.angle_le_pi O B⟩
  · constructor
    · positivity
    · nlinarith [Real.pi_pos]
  · rw [InnerProductGeometry.cos_angle, hO, hB]
    simp only [one_mul, div_one, hfinalInner]
    have htrig1 := Real.cos_two_mul (2 * Real.pi / 9)
    have htrig2 := Real.cos_two_mul (4 * Real.pi / 9)
    have hpi := Real.cos_pi_sub (Real.pi / 9)
    rw [show (2 : ℝ) * (2 * Real.pi / 9) = 4 * Real.pi / 9 by ring] at htrig1
    rw [show (2 : ℝ) * (4 * Real.pi / 9) =
        Real.pi - Real.pi / 9 by ring] at htrig2
    nlinarith

end PhyXMiniProblems.ProblemPhyXMini0069
