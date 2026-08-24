import FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
import FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
import FamilyStickyRandomFiniteFloorParameterNetV1
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32ProjectedCoverCenterFloorGridOverlapV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyRandomFiniteFloorParameterNetV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Bounded overlap of the actual projected-coefficient maximal cover

The actual norm distance is the `l1` distance of three real coefficients.
Selected maximal-cover centres are `scale` separated.  Relative to a fixed
tube, the centres in its `3 * scale` ball therefore inject into the
width-`scale / 3` floor grid in the three-coordinate box
`[-3 * scale, 3 * scale]^3`.  This gives the dimension-only overlap bound
`19^3`, and finite double counting gives the corresponding sum bound for
all localized families.
-/

/-- The three projected coefficients, translated by a fixed anchor tube. -/
def projectedCoefficientOffsetCoordinate {delta : NNReal}
    (anchor U : Tube delta) (i : Fin 3) : Real :=
  match i.1 with
  | 0 => projectedTubeGraphA U - projectedTubeGraphA anchor
  | 1 => projectedTubeGraphB U - projectedTubeGraphB anchor
  | _ => projectedTubeGraphD U - projectedTubeGraphD anchor

/-- Each translated coordinate is bounded by the actual `l1` coefficient
distance to the anchor. -/
theorem abs_projectedCoefficientOffsetCoordinate_le_distance
    {delta : NNReal} (anchor U : Tube delta) (i : Fin 3) :
    |projectedCoefficientOffsetCoordinate anchor U i| ≤
      projectedTubePairCoefficientDistance anchor U := by
  fin_cases i <;>
    simp only [projectedCoefficientOffsetCoordinate,
      projectedTubePairCoefficientDistance, coefficientDistance,
      projectedTubePairDeltaA, projectedTubePairDeltaB,
      projectedTubePairDeltaD]
  · rw [abs_sub_comm (projectedTubeGraphA U)]
    linarith [abs_nonneg (projectedTubeGraphB anchor - projectedTubeGraphB U),
      abs_nonneg (projectedTubeGraphD anchor - projectedTubeGraphD U)]
  · rw [abs_sub_comm (projectedTubeGraphB U)]
    linarith [abs_nonneg (projectedTubeGraphA anchor - projectedTubeGraphA U),
      abs_nonneg (projectedTubeGraphD anchor - projectedTubeGraphD U)]
  · rw [abs_sub_comm (projectedTubeGraphD U)]
    linarith [abs_nonneg (projectedTubeGraphA anchor - projectedTubeGraphA U),
      abs_nonneg (projectedTubeGraphB anchor - projectedTubeGraphB U)]

/-- The selected maximal-cover centres lying in the closed triple-scale
ball about a fixed tube. -/
noncomputable def projectedCoverCentersNear {delta : NNReal}
    (family : Finset (Tube delta)) (scale : Real) (T : Tube delta) :
    Finset (Tube delta) :=
  (finiteMetricCoverCenters family projectedTubePairCoefficientDistance
    scale (fun U V => projectedTubePairCoefficientDistance_comm U V)).filter
      fun center => projectedTubePairCoefficientDistance T center ≤ 3 * scale

@[simp]
theorem mem_projectedCoverCentersNear_iff {delta : NNReal}
    {family : Finset (Tube delta)} {scale : Real} {T center : Tube delta} :
    center ∈ projectedCoverCentersNear family scale T ↔
      center ∈ finiteMetricCoverCenters family
        projectedTubePairCoefficientDistance scale
        (fun U V => projectedTubePairCoefficientDistance_comm U V) ∧
      projectedTubePairCoefficientDistance T center ≤ 3 * scale := by
  simp [projectedCoverCentersNear]

/-- A triple-scale ball meets at most `19^3` selected centres.  The constant
is independent of the tube family, radius, and scale. -/
theorem projectedCoverCentersNear_card_le_nineteen_cubed
    {delta : NNReal} (family : Finset (Tube delta))
    {scale : Real} (hscale : 0 < scale) (T : Tube delta) :
    (projectedCoverCentersNear family scale T).card ≤ 19 ^ 3 := by
  classical
  let near := projectedCoverCentersNear family scale T
  let NearCenter := {center // center ∈ near}
  let coord : NearCenter → Fin 3 → Real :=
    fun center i => projectedCoefficientOffsetCoordinate T center.1 i
  have hmesh : 0 < scale / 3 := by positivity
  have hbound : ∀ center : NearCenter, ∀ i : Fin 3,
      |coord center i| ≤ 3 * scale := by
    intro center i
    exact (abs_projectedCoefficientOffsetCoordinate_le_distance
      T center.1 i).trans
        (mem_projectedCoverCentersNear_iff.mp center.2).2
  let code : NearCenter → BoundedCode (Fin 3) (scale / 3) (3 * scale) :=
    fun center => boundedFloorCode (scale / 3) (3 * scale) hmesh
      coord hbound center
  have hcodeInjective : Function.Injective code := by
    intro center₁ center₂ hcode
    apply Subtype.ext
    by_contra hne
    have hcenter₁ := (mem_projectedCoverCentersNear_iff.mp center₁.2).1
    have hcenter₂ := (mem_projectedCoverCentersNear_iff.mp center₂.2).1
    have hseparated : scale ≤
        projectedTubePairCoefficientDistance center₁.1 center₂.1 :=
      finiteMetricCoverCenters_pairwise_separated family
        projectedTubePairCoefficientDistance scale
        (fun U V => projectedTubePairCoefficientDistance_comm U V)
        center₁.1 hcenter₁ center₂.1 hcenter₂ hne
    have hfloor : floorCode (scale / 3) coord center₁ =
        floorCode (scale / 3) coord center₂ := by
      funext i
      exact congrArg Subtype.val (congrFun hcode i)
    have hA := abs_coord_sub_lt_of_floorCode_eq hmesh coord hfloor (0 : Fin 3)
    have hB := abs_coord_sub_lt_of_floorCode_eq hmesh coord hfloor (1 : Fin 3)
    have hD := abs_coord_sub_lt_of_floorCode_eq hmesh coord hfloor (2 : Fin 3)
    have hA' :
        |projectedTubeGraphA center₁.1 - projectedTubeGraphA center₂.1| <
          scale / 3 := by
      simpa [coord, projectedCoefficientOffsetCoordinate] using hA
    have hB' :
        |projectedTubeGraphB center₁.1 - projectedTubeGraphB center₂.1| <
          scale / 3 := by
      simpa [coord, projectedCoefficientOffsetCoordinate] using hB
    have hD' :
        |projectedTubeGraphD center₁.1 - projectedTubeGraphD center₂.1| <
          scale / 3 := by
      simpa [coord, projectedCoefficientOffsetCoordinate] using hD
    have hdistanceLt :
        projectedTubePairCoefficientDistance center₁.1 center₂.1 < scale := by
      simp only [projectedTubePairCoefficientDistance, coefficientDistance,
        projectedTubePairDeltaA, projectedTubePairDeltaB,
        projectedTubePairDeltaD]
      linarith
    exact (not_lt_of_ge hseparated) hdistanceLt
  have hratio : (3 * scale) / (scale / 3) = 9 := by
    field_simp
    norm_num
  have hnegRatio : (-(3 * scale)) / (scale / 3) = -9 := by
    field_simp
    norm_num
  calc
    near.card = Fintype.card NearCenter := by simp [NearCenter]
    _ ≤ Fintype.card (BoundedCode (Fin 3) (scale / 3) (3 * scale)) :=
      Fintype.card_le_of_injective code hcodeInjective
    _ = ((Int.floor ((3 * scale) / (scale / 3)) + 1 -
          Int.floor (-(3 * scale) / (scale / 3))).toNat) ^
          Fintype.card (Fin 3) := by
      rw [Fintype.card_fun, Fintype.card_coe]
      unfold codeInterval
      rw [Int.card_Icc]
    _ = 19 ^ 3 := by
      rw [hratio, hnegRatio]
      norm_num
      decide

/-- Finite double counting: the total size of all triple-scale localized
families is at most `19^3` times the source-family cardinality. -/
theorem sum_projected_globalNormLocalizedFamily_card_le
    {delta : NNReal} (family : Finset (Tube delta))
    {scale : Real} (hscale : 0 < scale) :
    ∑ center ∈ finiteMetricCoverCenters family
        projectedTubePairCoefficientDistance scale
        (fun U V => projectedTubePairCoefficientDistance_comm U V),
      (finiteGlobalNormLocalizedFamily family
        projectedTubePairCoefficientDistance scale center).card ≤
      19 ^ 3 * family.card := by
  classical
  let centers := finiteMetricCoverCenters family
    projectedTubePairCoefficientDistance scale
    (fun U V => projectedTubePairCoefficientDistance_comm U V)
  have hdouble :
      (∑ center ∈ centers,
        (finiteGlobalNormLocalizedFamily family
          projectedTubePairCoefficientDistance scale center).card) =
      ∑ T ∈ family, (projectedCoverCentersNear family scale T).card := by
    simp only [finiteGlobalNormLocalizedFamily, finiteFamilyMetricBall,
      projectedCoverCentersNear, Finset.card_eq_sum_ones,
      Finset.sum_filter]
    rw [Finset.sum_comm]
  change (∑ center ∈ centers,
    (finiteGlobalNormLocalizedFamily family
      projectedTubePairCoefficientDistance scale center).card) ≤ _
  rw [hdouble]
  calc
    (∑ T ∈ family, (projectedCoverCentersNear family scale T).card) ≤
        ∑ _T ∈ family, 19 ^ 3 := by
      exact Finset.sum_le_sum fun T _hT =>
        projectedCoverCentersNear_card_le_nineteen_cubed family hscale T
    _ = 19 ^ 3 * family.card := by simp [Nat.mul_comm]

#print axioms abs_projectedCoefficientOffsetCoordinate_le_distance
#print axioms mem_projectedCoverCentersNear_iff
#print axioms projectedCoverCentersNear_card_le_nineteen_cubed
#print axioms sum_projected_globalNormLocalizedFamily_card_le

end

end FamilyStickyCinematicL32ProjectedCoverCenterFloorGridOverlapV1
