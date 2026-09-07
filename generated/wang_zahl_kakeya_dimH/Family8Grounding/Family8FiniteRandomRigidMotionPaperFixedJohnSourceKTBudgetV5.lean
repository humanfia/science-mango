import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossPolynomialV3
import Family8Grounding.Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperFixedJohnSourceKTBudgetV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8FiniteRandomRigidMotionPaperFixedJohnCapVsLongMeanV2
open Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWAConnectorV2
open Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossPolynomialV3

noncomputable section

/-!
# Source Katz--Tao control of the fixed-John packing concentration

The packing family is only the normalized datum reindexed by the subtype of
the full index finset.  This file records that exact reindex identity and
then transports the honest normalization estimate `C -> 128 C`.  Thus the
maximal concentration occurring in the polynomial greedy-loss bound is not
an independent premise.
-/

/-- The subtype attached to the complete finite index set is equivalent to
the original index type. -/
def fixedJohnActiveIndexEquiv
    (iota : Type) [Fintype iota] [DecidableEq iota] :
    {i // i ∈ (Finset.univ : Finset iota)} ≃ iota where
  toFun i := i.1
  invFun i := ⟨i, Finset.mem_univ i⟩
  left_inv i := by ext; rfl
  right_inv i := rfl

@[simp]
theorem fixedJohnActiveIndexEquiv_apply
    (iota : Type) [Fintype iota] [DecidableEq iota]
    (i : {i // i ∈ (Finset.univ : Finset iota)}) :
    fixedJohnActiveIndexEquiv iota i = i.1 :=
  rfl

/-- Full-subtype reindexing preserves contained mass exactly. -/
theorem containedMass_fixedJohnNormalizedActiveFamily
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (K : ConvexBody Space) :
    containedMass (fixedJohnNormalizedActiveFamily D) K =
      containedMass (eighthNormalizedDatum D).family.bodyFamily K := by
  classical
  unfold containedMass containedIndices
  simp only [Finset.sum_filter]
  have hsum := (fixedJohnActiveIndexEquiv iota).sum_comp (fun i : iota =>
    if ((eighthNormalizedDatum D).family.bodyFamily i : Set Space) ⊆
        (K : Set Space) then
      volume ((eighthNormalizedDatum D).family.bodyFamily i : Set Space)
    else 0)
  convert hsum using 1;
    simp only [fixedJohnActiveIndexEquiv_apply, fixedJohnNormalizedActiveFamily,
      eighthNormalizedDatum, eighthNormalizedTubeFamily,
      UniformTubeFamily.bodyFamily]
  apply Finset.sum_congr
  · ext i
    simp
  · intro i hi
    rfl

/-- Any normalized Katz--Tao bound controls the exact packing maximal
concentration. -/
theorem fixedJohnPackingMaximalConcentration_le_of_normalized_isKatzTao
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal}
    (hKT : IsKatzTao C (eighthNormalizedDatum D).family.bodyFamily) :
    fixedJohnPackingMaximalConcentration D hD ≤ C := by
  unfold fixedJohnPackingMaximalConcentration
  rw [maximalConcentration_le_iff_isKatzTao]
  intro K
  unfold IsKatzTaoAt
  rw [containedMass_fixedJohnNormalizedActiveFamily D K]
  exact hKT K

/-- The honest eighth-scale normalization turns a source Katz--Tao constant
`C` into the explicit fixed-John packing bound `128 C`. -/
theorem fixedJohnPackingMaximalConcentration_le_128_mul_of_source_isKatzTao
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal} (hKT : IsKatzTao C D.family.bodyFamily) :
    fixedJohnPackingMaximalConcentration D hD ≤ 128 * C :=
  fixedJohnPackingMaximalConcentration_le_of_normalized_isKatzTao D hD
    (eighthNormalizedDatum_isKatzTao D hD.delta_le_half hKT)

/-- Finite source Katz--Tao control also bounds the real concentration used
in the finite probability calculation. -/
theorem fixedJohnPackingMaximalConcentration_toReal_le_128_mul
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal} (hC : C ≠ ∞)
    (hKT : IsKatzTao C D.family.bodyFamily) :
    (fixedJohnPackingMaximalConcentration D hD).toReal ≤
      (128 * C).toReal := by
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hC)
    (fixedJohnPackingMaximalConcentration_le_128_mul_of_source_isKatzTao
      D hD hKT)

/-- Substitute source Katz--Tao control into the completely explicit
polynomial greedy-loss envelope. -/
theorem fixedJohnAutomaticGreedyLoss_cast_le_polynomial_of_source_isKatzTao
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal} (hC : C ≠ ∞)
    (hKT : IsKatzTao C D.family.bodyFamily) :
    (fixedJohnAutomaticGreedyLoss D hD : Real) ≤
      fixedJohnTailParameter D hD *
        ((46082 / (((delta / 8 : NNReal) : Real))) ^ 15 *
          ((128 * C).toReal * (2304 : Real) ^ 3 /
            ((((delta / 8 : NNReal) : Real) ^ 2) / 2))) +
        2 := by
  have hM := fixedJohnPackingMaximalConcentration_toReal_le_128_mul
    D hD hC hKT
  have htail : 0 ≤ fixedJohnTailParameter D hD :=
    zero_le_one.trans (one_le_fixedJohnTailParameter D hD)
  have hcat :
      0 ≤ (46082 / (((delta / 8 : NNReal) : Real))) ^ 15 := by positivity
  have hden : 0 < ((((delta / 8 : NNReal) : Real) ^ 2) / 2) := by
    have hrho : 0 < ((delta / 8 : NNReal) : Real) := by
      exact_mod_cast admissibleNormalizedRadiusPos hD
    positivity
  apply (fixedJohnAutomaticGreedyLoss_cast_le_polynomial D hD).trans
  gcongr

#print axioms containedMass_fixedJohnNormalizedActiveFamily
#print axioms fixedJohnPackingMaximalConcentration_le_of_normalized_isKatzTao
#print axioms fixedJohnPackingMaximalConcentration_le_128_mul_of_source_isKatzTao
#print axioms fixedJohnPackingMaximalConcentration_toReal_le_128_mul
#print axioms fixedJohnAutomaticGreedyLoss_cast_le_polynomial_of_source_isKatzTao

end
end Family8FiniteRandomRigidMotionPaperFixedJohnSourceKTBudgetV5
