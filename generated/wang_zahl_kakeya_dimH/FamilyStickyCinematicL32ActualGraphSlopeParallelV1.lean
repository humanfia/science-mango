import FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
import Family4GlobalExtremalUpstream
import Submission.Kakeya.ConvexFactoring.TransverseUnit

set_option autoImplicit false

open Set
open scoped NNReal Matrix InnerProductSpace

namespace FamilyStickyCinematicL32ActualGraphSlopeParallelV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32LocalTangencyV1

noncomputable section

/-!
# Clean graph-slope producer for half-scale coefficient parallelity

For a nonvertical actual tube, its unit direction is its vertical component
times `(c,d,1)`.  The projective sine angle is bounded by the Euclidean
distance of the two graph slopes.  Consequently a half-radius c-bucket and
a half-radius reduced-coefficient ball give the exact angle bound required
by a same-scale cover.
-/

/-- Three-dimensional point notation local to the clean actual API. -/
def actualPoint3 (x y z : Real) : Space := WithLp.toLp 2 ![x, y, z]

/-- Unnormalized graph direction of an actual tube. -/
def actualTubeGraphDirection {delta : NNReal} (T : Tube delta) : Space :=
  actualPoint3 (projectedTubeGraphC T) (projectedTubeGraphD T) 1

theorem direction_eq_vertical_smul_actualTubeGraphDirection
    {delta : NNReal} (T : Tube delta)
    (hvertical : T.axis.direction 2 ≠ 0) :
    T.axis.direction =
      T.axis.direction 2 • actualTubeGraphDirection T := by
  ext i
  fin_cases i <;>
    simp [actualTubeGraphDirection, actualPoint3, projectedTubeGraphC,
      projectedTubeGraphD] <;>
    field_simp

theorem transverseVector_smul_smul_actual
    (a b : Real) (u v : Space) :
    transverseVector (a • u) (b • v) =
      (a * b) • transverseVector u v := by
  ext i
  fin_cases i <;>
    simp [transverseVector, cross_apply] <;>
    ring

theorem abs_actual_direction_apply_le_one
    {delta : NNReal} (T : Tube delta) (i : Fin 3) :
    |T.axis.direction i| ≤ 1 := by
  have hi := PiLp.norm_apply_le T.axis.direction i
  simpa only [Real.norm_eq_abs, T.axis.norm_direction] using hi

theorem norm_actualPoint3_sq (x y z : Real) :
    ‖actualPoint3 x y z‖ ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (by positivity)]
  norm_num [actualPoint3, Fin.sum_univ_succ]
  ring_nf

theorem actualGraphDeterminant_sq_le (c d x y : Real) :
    (d * x - c * y) ^ 2 ≤
      (c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (c * x + d * y)]

theorem vertical_sq_mul_actualGraphFactor_eq_one
    {delta : NNReal} (T : Tube delta)
    (hvertical : T.axis.direction 2 ≠ 0) :
    T.axis.direction 2 ^ 2 *
        (1 + projectedTubeGraphC T ^ 2 + projectedTubeGraphD T ^ 2) = 1 := by
  have hnorm := congrArg (fun x : Real => x ^ 2) T.axis.norm_direction
  rw [direction_eq_vertical_smul_actualTubeGraphDirection T hvertical,
    norm_smul, Real.norm_eq_abs] at hnorm
  have hgraph :
      ‖actualTubeGraphDirection T‖ ^ 2 =
        1 + projectedTubeGraphC T ^ 2 + projectedTubeGraphD T ^ 2 := by
    rw [actualTubeGraphDirection, norm_actualPoint3_sq]
    ring
  rw [mul_pow, sq_abs, hgraph] at hnorm
  norm_num at hnorm
  nlinarith

theorem transverseVector_actualTubeGraphDirection_eq_actualPoint3
    {delta : NNReal} (T U : Tube delta) :
    transverseVector (actualTubeGraphDirection T)
        (actualTubeGraphDirection U) =
      actualPoint3
        (projectedTubeGraphD T - projectedTubeGraphD U)
        (projectedTubeGraphC U - projectedTubeGraphC T)
        (projectedTubeGraphC T * projectedTubeGraphD U -
          projectedTubeGraphD T * projectedTubeGraphC U) := by
  ext i
  fin_cases i <;>
    simp [actualTubeGraphDirection, actualPoint3,
      transverseVector, cross_apply]

theorem actualGraphDirection_crossNorm_sq_le_slopeGapSq
    {delta : NNReal} (T U : Tube delta) :
    ‖transverseVector (actualTubeGraphDirection T)
        (actualTubeGraphDirection U)‖ ^ 2 ≤
      (1 + projectedTubeGraphC T ^ 2 + projectedTubeGraphD T ^ 2) *
        ((projectedTubeGraphC T - projectedTubeGraphC U) ^ 2 +
          (projectedTubeGraphD T - projectedTubeGraphD U) ^ 2) := by
  rw [transverseVector_actualTubeGraphDirection_eq_actualPoint3,
    norm_actualPoint3_sq]
  have hdet := actualGraphDeterminant_sq_le
    (projectedTubeGraphC T) (projectedTubeGraphD T)
    (projectedTubeGraphC T - projectedTubeGraphC U)
    (projectedTubeGraphD T - projectedTubeGraphD U)
  nlinarith

/-- Sharp squared projective sine bound by the actual graph-slope gap. -/
theorem sin_angle_direction_sq_le_actualSlopeGapSq
    {delta : NNReal} (T U : Tube delta)
    (hverticalT : T.axis.direction 2 ≠ 0)
    (hverticalU : U.axis.direction 2 ≠ 0) :
    Real.sin (InnerProductGeometry.angle
        T.axis.direction U.axis.direction) ^ 2 ≤
      (projectedTubeGraphC T - projectedTubeGraphC U) ^ 2 +
        (projectedTubeGraphD T - projectedTubeGraphD U) ^ 2 := by
  let gap : Real :=
    (projectedTubeGraphC T - projectedTubeGraphC U) ^ 2 +
      (projectedTubeGraphD T - projectedTubeGraphD U) ^ 2
  have hgap : 0 ≤ gap := by
    dsimp only [gap]
    positivity
  have hcross :
      ‖transverseVector T.axis.direction U.axis.direction‖ =
        Real.sin (InnerProductGeometry.angle
          T.axis.direction U.axis.direction) := by
    rw [norm_transverseVector, T.axis.norm_direction,
      U.axis.norm_direction]
    norm_num
  have hgraph := actualGraphDirection_crossNorm_sq_le_slopeGapSq T U
  have hTnorm := vertical_sq_mul_actualGraphFactor_eq_one T hverticalT
  have hbAbs := abs_actual_direction_apply_le_one U (2 : Fin 3)
  have hbSq : U.axis.direction 2 ^ 2 ≤ 1 := by
    have hsquare :=
      (sq_le_sq₀ (abs_nonneg (U.axis.direction 2)) (by norm_num)).2 hbAbs
    simpa only [sq_abs, one_pow] using hsquare
  have hscale :
      transverseVector T.axis.direction U.axis.direction =
        (T.axis.direction 2 * U.axis.direction 2) •
          transverseVector (actualTubeGraphDirection T)
            (actualTubeGraphDirection U) := by
    calc
      transverseVector T.axis.direction U.axis.direction =
          transverseVector
            (T.axis.direction 2 • actualTubeGraphDirection T)
            (U.axis.direction 2 • actualTubeGraphDirection U) :=
        congrArg₂ transverseVector
          (direction_eq_vertical_smul_actualTubeGraphDirection T hverticalT)
          (direction_eq_vertical_smul_actualTubeGraphDirection U hverticalU)
      _ = _ := transverseVector_smul_smul_actual _ _ _ _
  calc
    Real.sin (InnerProductGeometry.angle
        T.axis.direction U.axis.direction) ^ 2 =
        ‖transverseVector T.axis.direction U.axis.direction‖ ^ 2 := by
      rw [hcross]
    _ = ‖(T.axis.direction 2 * U.axis.direction 2) •
        transverseVector (actualTubeGraphDirection T)
          (actualTubeGraphDirection U)‖ ^ 2 := by
      rw [hscale]
    _ = (T.axis.direction 2 * U.axis.direction 2) ^ 2 *
        ‖transverseVector (actualTubeGraphDirection T)
          (actualTubeGraphDirection U)‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    _ ≤ (T.axis.direction 2 * U.axis.direction 2) ^ 2 *
        ((1 + projectedTubeGraphC T ^ 2 + projectedTubeGraphD T ^ 2) *
          gap) := by
      gcongr
    _ = U.axis.direction 2 ^ 2 * gap := by
      rw [mul_pow]
      calc
        (T.axis.direction 2 ^ 2 * U.axis.direction 2 ^ 2) *
            ((1 + projectedTubeGraphC T ^ 2 +
              projectedTubeGraphD T ^ 2) * gap) =
          U.axis.direction 2 ^ 2 *
            (T.axis.direction 2 ^ 2 *
              (1 + projectedTubeGraphC T ^ 2 +
                projectedTubeGraphD T ^ 2)) * gap := by ring
        _ = U.axis.direction 2 ^ 2 * gap := by rw [hTnorm]; ring
    _ ≤ gap := by
      calc
        U.axis.direction 2 ^ 2 * gap ≤ 1 * gap :=
          mul_le_mul_of_nonneg_right hbSq hgap
        _ = gap := one_mul gap
    _ = (projectedTubeGraphC T - projectedTubeGraphC U) ^ 2 +
        (projectedTubeGraphD T - projectedTubeGraphD U) ^ 2 := rfl

/-- A half-radius c-bucket and a half-radius reduced-coefficient ball give
actual projective parallelity at tube scale delta. -/
theorem essentiallyParallelAtScale_of_halfCBucket_halfCoefficient
    {delta : NNReal} (T U : Tube delta)
    (hverticalT : T.axis.direction 2 ≠ 0)
    (hverticalU : U.axis.direction 2 ≠ 0)
    (hC : |projectedTubeGraphC T - projectedTubeGraphC U| ≤
      (delta : Real) / 2)
    (hcoefficient : projectedTubePairCoefficientDistance T U <
      (delta : Real) / 2) :
    EssentiallyParallelAtScale T U := by
  have hD : |projectedTubeGraphD T - projectedTubeGraphD U| <
      (delta : Real) / 2 := by
    simp only [projectedTubePairCoefficientDistance, coefficientDistance,
      projectedTubePairDeltaA, projectedTubePairDeltaB,
      projectedTubePairDeltaD] at hcoefficient
    linarith [abs_nonneg (projectedTubeGraphA T - projectedTubeGraphA U),
      abs_nonneg (projectedTubeGraphB T - projectedTubeGraphB U)]
  have hdeltaNonneg : 0 ≤ (delta : Real) := by positivity
  have hCsq :
      (projectedTubeGraphC T - projectedTubeGraphC U) ^ 2 ≤
        ((delta : Real) / 2) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hC
  have hDsq :
      (projectedTubeGraphD T - projectedTubeGraphD U) ^ 2 ≤
        ((delta : Real) / 2) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (le_of_lt hD)
  have hsinSq := sin_angle_direction_sq_le_actualSlopeGapSq
    T U hverticalT hverticalU
  have hcross :
      ‖transverseVector T.axis.direction U.axis.direction‖ =
        Real.sin (InnerProductGeometry.angle
          T.axis.direction U.axis.direction) := by
    rw [norm_transverseVector, T.axis.norm_direction,
      U.axis.norm_direction]
    norm_num
  have hsin : 0 ≤ Real.sin (InnerProductGeometry.angle
      T.axis.direction U.axis.direction) := by
    rw [← hcross]
    exact norm_nonneg _
  change Real.sin (InnerProductGeometry.angle
    T.axis.direction U.axis.direction) ≤ (delta : Real)
  apply (sq_le_sq₀ hsin hdeltaNonneg).mp
  exact hsinSq.trans <| (add_le_add hCsq hDsq).trans <| by
    nlinarith [sq_nonneg ((delta : Real) / 2)]

#print axioms sin_angle_direction_sq_le_actualSlopeGapSq
#print axioms essentiallyParallelAtScale_of_halfCBucket_halfCoefficient

end

end FamilyStickyCinematicL32ActualGraphSlopeParallelV1
