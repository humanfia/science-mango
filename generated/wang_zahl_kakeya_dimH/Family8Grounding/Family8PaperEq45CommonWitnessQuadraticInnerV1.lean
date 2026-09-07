import Family8Grounding.Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV13
import Family8Grounding.Family8FrostmanOneFromPointwisePackingV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8PaperEq45CommonWitnessQuadraticInnerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8FrostmanOneFromPointwisePackingV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

/-!
# A callback-free common-witness inner bound from the actual source card

The common-witness endpoint uses the isotropic dimensions `w x w x 1`, where
`w = 2 rho / (1 + 2 rho)`.  Hence `rho / w` lies between `1/2` and `1` for
`rho <= 1/2`.  A quadratic natural cap in the actual source index cardinality
then dominates the automatic pointwise-cardinality bound uniformly for
`0 <= beta <= 1`.

This is an honest, fully constructed fallback.  It does not claim the sharper
adaptive selected-parent cap from the paper.
-/

/-- The literal quadratic cap used by the common-witness fallback. -/
def commonWitnessQuadraticSourceNatCap (sourceCard : Nat) : Nat :=
  (2 * sourceCard) ^ 2

theorem maxWitnessCommonWidth_ratio_eq
    {rho : NNReal} (hrho : 0 < rho) :
    (rho : ENNReal) / (maxWitnessCommonWidth rho : ENNReal) =
      ((1 + 2 * rho : NNReal) : ENNReal) / 2 := by
  have hratio : rho / maxWitnessCommonWidth rho =
      (1 + 2 * rho) / 2 := by
    apply (div_eq_iff (maxWitnessCommonWidth_pos hrho).ne').2
    rw [maxWitnessCommonWidth, maxWitnessCommonScale]
    field_simp
  calc
    (rho : ENNReal) / (maxWitnessCommonWidth rho : ENNReal) =
        ((rho / maxWitnessCommonWidth rho : NNReal) : ENNReal) :=
      (ENNReal.coe_div (maxWitnessCommonWidth_pos hrho).ne').symm
    _ = (((1 + 2 * rho) / 2 : NNReal) : ENNReal) := by rw [hratio]
    _ = ((1 + 2 * rho : NNReal) : ENNReal) / 2 :=
      ENNReal.coe_div (by norm_num)

theorem half_le_maxWitnessCommonWidth_ratio
    {rho : NNReal} (hrho : 0 < rho) :
    (1 / 2 : ENNReal) <=
      (rho : ENNReal) / (maxWitnessCommonWidth rho : ENNReal) := by
  rw [maxWitnessCommonWidth_ratio_eq hrho]
  apply ENNReal.div_le_div_right
  norm_num

theorem maxWitnessCommonWidth_ratio_le_one
    {rho : NNReal} (hrho : 0 < rho) (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    (rho : ENNReal) / (maxWitnessCommonWidth rho : ENNReal) <= 1 := by
  rw [maxWitnessCommonWidth_ratio_eq hrho]
  have hnum : ((1 + 2 * rho : NNReal) : ENNReal) <= 2 := by
    exact_mod_cast (show 1 + 2 * rho <= (2 : NNReal) by nlinarith)
  calc
    ((1 + 2 * rho : NNReal) : ENNReal) / 2 <= 2 / 2 :=
      (ENNReal.div_le_div_right hnum) 2
    _ = 1 := ENNReal.div_self (by norm_num) (by norm_num)

/-- At the isotropic common-witness scale, the actual source cardinality is
bounded by the Proposition 6.6(A) inner scalar with the constructed quadratic
cap. -/
theorem sourceCard_le_commonWitness_innerFactor
    {rho : NNReal} (hrho : 0 < rho) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (sourceCard : Nat) {epsilon beta : Real}
    (hepsilon : 0 <= epsilon) (hbeta : 0 <= beta)
    (hbetaOne : beta <= 1) :
    (sourceCard : ENNReal) <=
      proposition66AInnerFactor rho
        (maxWitnessCommonWidth rho) (maxWitnessCommonWidth rho)
        (commonWitnessQuadraticSourceNatCap sourceCard) epsilon beta := by
  by_cases hsourceCard : sourceCard = 0
  · subst sourceCard
    norm_num
  let d : ENNReal := (rho : ENNReal)
  let w : ENNReal := (maxWitnessCommonWidth rho : ENNReal)
  let y : ENNReal := d / w
  let N : ENNReal := (sourceCard : ENNReal)
  let M : ENNReal := (commonWitnessQuadraticSourceNatCap sourceCard : ENNReal)
  let p : Real := 1 - beta / 2
  have hdPos : 0 < d := by
    dsimp only [d]
    exact ENNReal.coe_pos.mpr hrho
  have hdOne : d <= 1 := by
    dsimp only [d]
    exact_mod_cast (hrhoHalf.trans (by norm_num : (2 : NNReal)⁻¹ <= 1))
  have hw0 : w ≠ 0 := by
    dsimp only [w]
    exact ENNReal.coe_ne_zero.mpr (maxWitnessCommonWidth_pos hrho).ne'
  have hwTop : w ≠ ∞ := by
    dsimp only [w]
    exact ENNReal.coe_ne_top
  have hyHalf : (1 / 2 : ENNReal) <= y := by
    simpa only [d, w, y] using half_le_maxWitnessCommonWidth_ratio hrho
  have hyOne : y <= 1 := by
    simpa only [d, w, y] using
      maxWitnessCommonWidth_ratio_le_one hrho hrhoHalf
  have hyPos : 0 < y := (by norm_num : (0 : ENNReal) < 1 / 2).trans_le hyHalf
  have hyTop : y ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hyOne
  have hNOne : 1 <= N := by
    dsimp only [N]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hsourceCard)
  have hpHalf : (1 / 2 : Real) <= p := by
    dsimp only [p]
    linarith
  have hp : 0 <= p := (by norm_num : (0 : Real) <= 1 / 2).trans hpHalf
  have hdeltaLoss : 1 <= d ^ (-epsilon / 2) := by
    rw [<- ENNReal.rpow_zero]
    exact ENNReal.rpow_le_rpow_of_exponent_ge hdOne (by linarith)
  have haspect : (d / w) ^ (-2 * beta) >= 1 := by
    rw [show d / w = y by rfl, <- ENNReal.rpow_zero]
    exact ENNReal.rpow_le_rpow_of_exponent_ge hyOne (by linarith)
  have hbase : N ^ (2 : Nat) <= y ^ (2 : Nat) * M := by
    have hfour : (1 : ENNReal) <= y ^ (2 : Nat) * 4 := by
      calc
        (1 : ENNReal) = (1 / 2 : ENNReal) ^ (2 : Nat) * 4 := by
          have hhalfTwo : (1 / 2 : ENNReal) * 2 = 1 :=
            ENNReal.div_mul_cancel (by norm_num) (by norm_num)
          calc
            (1 : ENNReal) = 1 ^ (2 : Nat) := by simp
            _ = ((1 / 2 : ENNReal) * 2) ^ (2 : Nat) := by rw [hhalfTwo]
            _ = (1 / 2 : ENNReal) ^ (2 : Nat) * 4 := by ring
        _ <= y ^ (2 : Nat) * 4 := by gcongr
    have hM : M = 4 * N ^ (2 : Nat) := by
      dsimp only [M, N, commonWitnessQuadraticSourceNatCap]
      norm_num [Nat.cast_pow]
      ring
    rw [hM]
    calc
      N ^ (2 : Nat) = 1 * N ^ (2 : Nat) := by simp
      _ <= (y ^ (2 : Nat) * 4) * N ^ (2 : Nat) := by gcongr
      _ = y ^ (2 : Nat) * (4 * N ^ (2 : Nat)) := by ring
  have hNSq : N <= N ^ (2 : Nat) := by
    calc
      N = N * 1 := by simp
      _ <= N * N := by gcongr
      _ = N ^ (2 : Nat) := by ring
  have hbaseOne : 1 <= y ^ (2 : Nat) * M :=
    hNOne.trans (hNSq.trans hbase)
  have hpow : N <= (y ^ (2 : Nat) * M) ^ p := by
    calc
      N = (N ^ (2 : Nat)) ^ (1 / 2 : Real) := by
        rw [<- ENNReal.rpow_natCast, <- ENNReal.rpow_mul]
        norm_num
      _ <= (y ^ (2 : Nat) * M) ^ (1 / 2 : Real) := by
        exact ENNReal.rpow_le_rpow hbase (by norm_num)
      _ <= (y ^ (2 : Nat) * M) ^ p :=
        ENNReal.rpow_le_rpow_of_exponent_le hbaseOne hpHalf
  unfold proposition66AInnerFactor
  have hww : (w / w) ^ (1 - beta) = 1 := by
    rw [ENNReal.div_self hw0 hwTop, ENNReal.one_rpow]
  change N <= d ^ (-epsilon / 2) * (w / w) ^ (1 - beta) *
      y ^ (-2 * beta) * ((y ^ (2 : Nat)) * M) ^ p
  rw [hww]
  calc
    N <= (y ^ (2 : Nat) * M) ^ p := hpow
    _ = 1 * 1 * 1 * (y ^ (2 : Nat) * M) ^ p := by simp
    _ <= d ^ (-epsilon / 2) * 1 * y ^ (-2 * beta) *
        (y ^ (2 : Nat) * M) ^ p := by gcongr

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The exact `hinner` required by the SAFE V13 common-witness endpoint,
generated from the actual active-parent source cardinality. -/
theorem sourceFineLevelShading_average_le_commonWitnessQuadraticInner
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    {assemblyLoss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) assemblyLoss)
    (k : (greedyParentFactorization S P).index.coarse)
    (hrho : 0 < rho) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    {epsilon beta : Real} (hepsilon : 0 <= epsilon)
    (hbeta : 0 <= beta) (hbetaOne : beta <= 1) :
    (sourceFineLevelShading A k).averageMultiplicity <=
      proposition66AInnerFactor rho
        (maxWitnessCommonWidth rho) (maxWitnessCommonWidth rho)
        (commonWitnessQuadraticSourceNatCap
          (Fintype.card (ActiveParentIndex S))) epsilon beta := by
  exact (averageMultiplicity_le_indexCard (sourceFineLevelShading A k)).trans
    (sourceCard_le_commonWitness_innerFactor hrho hrhoHalf
      (Fintype.card (ActiveParentIndex S)) hepsilon hbeta hbetaOne)

#print axioms commonWitnessQuadraticSourceNatCap
#print axioms maxWitnessCommonWidth_ratio_eq
#print axioms half_le_maxWitnessCommonWidth_ratio
#print axioms maxWitnessCommonWidth_ratio_le_one
#print axioms sourceCard_le_commonWitness_innerFactor
#print axioms
  sourceFineLevelShading_average_le_commonWitnessQuadraticInner

end
end Family8PaperEq45CommonWitnessQuadraticInnerV1
