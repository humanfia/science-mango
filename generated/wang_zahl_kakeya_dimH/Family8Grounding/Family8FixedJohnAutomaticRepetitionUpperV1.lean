import Family8Grounding.Family8FixedJohnSelfImprovementPropertyConnectorV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossSourceExponentV4
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FixedJohnAutomaticRepetitionUpperV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnCapVsLongMeanV2
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2

noncomputable section

/-!
# Datum-uniform upper bound for the automatic fixed-John copy count

Every member counted by `containedMass F K` is contained in `K`, hence its
volume is at most `volume K`.  Thus the maximal concentration of an arbitrary
finite convex family is at most its index cardinality.  In the automatic
density ratio this cardinality cancels the identical source-card factor in
`fixedJohnDensityUnitCost`, leaving a uniform inverse-square upper bound for
the repetition count.
-/

theorem containedMass_le_card_mul_volume
    {index : Type} [Fintype index]
    (F : ConvexFamily index) (K : ConvexBody Space) :
    containedMass F K <=
      (Fintype.card index : ENNReal) * volume (K : Set Space) := by
  classical
  unfold containedMass
  calc
    (∑ i ∈ containedIndices F K, volume (F i : Set Space)) <=
        ∑ _i ∈ containedIndices F K, volume (K : Set Space) := by
      apply Finset.sum_le_sum
      intro i hi
      exact measure_mono ((mem_containedIndices F K i).1 hi)
    _ = ((containedIndices F K).card : ENNReal) *
          volume (K : Set Space) := by simp
    _ <= (Fintype.card index : ENNReal) * volume (K : Set Space) := by
      gcongr
      exact_mod_cast Finset.card_le_univ (containedIndices F K)

theorem isKatzTao_cardinality
    {index : Type} [Fintype index]
    (F : ConvexFamily index) :
    IsKatzTao (Fintype.card index : ENNReal) F := by
  intro K
  exact containedMass_le_card_mul_volume F K

theorem maximalConcentration_le_cardinality
    {index : Type} [Fintype index]
    (F : ConvexFamily index) :
    maximalConcentration F <= (Fintype.card index : ENNReal) := by
  exact (maximalConcentration_le_iff_isKatzTao).2
    (isKatzTao_cardinality F)

theorem fixedJohnPackingMaximalConcentration_le_sourceCard
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    fixedJohnPackingMaximalConcentration D hD <=
      (Fintype.card iota : ENNReal) := by
  unfold fixedJohnPackingMaximalConcentration
  simpa only [Fintype.card_coe, Finset.card_univ] using
    (maximalConcentration_le_cardinality
      (fixedJohnNormalizedActiveFamily D))

theorem fixedJohnAutomaticDensityRepetitions_cast_le_two_mul_rho_neg_two
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    (fixedJohnAutomaticDensityRepetitions D hD : Real) <=
      2 * (((delta / 8 : NNReal) : Real) ^ (-2 : Real)) := by
  let rho : Real := ((delta / 8 : NNReal) : Real)
  let n : Real := (Fintype.card iota : Real)
  let M : Real := (fixedJohnPackingMaximalConcentration D hD).toReal
  have hrho : 0 < rho := by
    exact_mod_cast admissibleNormalizedRadiusPos hD
  have hrhoOne : rho <= 1 := by
    dsimp only [rho]
    exact_mod_cast
      ((div_le_self (show 0 <= delta from bot_le)
        (by norm_num : (1 : NNReal) <= 8)).trans
          (hD.delta_le_half.trans (by norm_num : (2 : NNReal)⁻¹ <= 1)))
  have hn : 1 <= n := by
    dsimp only [n]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hMtop : (Fintype.card iota : ENNReal) ≠ ∞ := by simp
  have hM : M <= n := by
    dsimp only [M, n]
    simpa using ENNReal.toReal_mono hMtop
      (fixedJohnPackingMaximalConcentration_le_sourceCard D hD)
  have hcost : 0 < fixedJohnDensityUnitCost delta iota :=
    fixedJohnDensityUnitCost_pos hD.delta_pos
      (Nat.ne_of_gt (Fintype.card_pos_iff.mpr inferInstance))
  have hratioNonneg : 0 <= fixedJohnDensityRatio D hD := by
    unfold fixedJohnDensityRatio
    positivity
  have hfloor :
      (Nat.floor (fixedJohnDensityRatio D hD) : Real) <=
        fixedJohnDensityRatio D hD :=
    Nat.floor_le hratioNonneg
  have hmax :
      (fixedJohnAutomaticDensityRepetitions D hD : Real) <=
        1 + fixedJohnDensityRatio D hD := by
    unfold fixedJohnAutomaticDensityRepetitions
    push_cast
    exact max_le (by linarith) (by linarith)
  have hratio : fixedJohnDensityRatio D hD <= rho ^ (-2 : Real) := by
    change M / (9504 * n * rho ^ 2) <= rho ^ (-2 : Real)
    rw [Real.rpow_neg hrho.le, Real.rpow_two]
    apply (div_le_iff₀ hcost).2
    dsimp only [fixedJohnDensityUnitCost, rho, n] at hcost
    calc
      M <= n := hM
      _ <= (rho ^ 2)⁻¹ * (9504 * n * rho ^ 2) := by
        field_simp
        nlinarith
  have hone : 1 <= rho ^ (-2 : Real) := by
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hrho hrhoOne
      (by norm_num)
  exact hmax.trans (by nlinarith [hratio, hone])

theorem fixedJohnAutomaticDensityRepetitions_le_two_mul_rho_neg_two
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    (fixedJohnAutomaticDensityRepetitions D hD : ENNReal) <=
      2 * (((delta / 8 : NNReal) : ENNReal) ^ (-2 : Real)) := by
  have hreal :=
    fixedJohnAutomaticDensityRepetitions_cast_le_two_mul_rho_neg_two D hD
  have hrho : 0 < ((delta / 8 : NNReal) : Real) := by
    exact_mod_cast admissibleNormalizedRadiusPos hD
  rw [show (((delta / 8 : NNReal) : ENNReal) ^ (-2 : Real)) =
      ENNReal.ofReal
        (((delta / 8 : NNReal) : Real) ^ (-2 : Real)) by
    simpa only [ENNReal.ofReal_coe_nnreal] using
      ENNReal.ofReal_rpow_of_pos hrho]
  rw [<- ENNReal.ofReal_ofNat, <- ENNReal.ofReal_mul (by norm_num)]
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hreal

#print axioms containedMass_le_card_mul_volume
#print axioms isKatzTao_cardinality
#print axioms maximalConcentration_le_cardinality
#print axioms fixedJohnPackingMaximalConcentration_le_sourceCard
#print axioms fixedJohnAutomaticDensityRepetitions_cast_le_two_mul_rho_neg_two
#print axioms fixedJohnAutomaticDensityRepetitions_le_two_mul_rho_neg_two

end
end Family8FixedJohnAutomaticRepetitionUpperV1
