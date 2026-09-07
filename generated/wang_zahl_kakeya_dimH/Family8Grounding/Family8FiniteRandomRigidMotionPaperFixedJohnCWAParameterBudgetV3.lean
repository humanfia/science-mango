import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnFullCatalogueCWAV3
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnDensityNondegeneracyV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperFixedJohnCWAParameterBudgetV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteRandomRigidMotionPaperFixedJohnCapVsLongMeanV2
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2
open Family8FiniteRandomRigidMotionPaperFixedJohnFullCatalogueCWAV3

noncomputable section

/-! The floor-selected repetition count cancels the maximal-concentration,
source-cardinality and normalized-radius factors in the full copied CWA
parameter.  Only the logarithmic finite-test tail remains. -/

theorem fixedJohnFullCopiedCWAParameter_toReal_le_tail
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    (fixedJohnFullCopiedCWAParameter D hD).toReal <=
      38016 * fixedJohnTailParameter D hD := by
  let rho : Real := ((delta / 8 : NNReal) : Real)
  let N : Real := Fintype.card iota
  let Jn : Nat := fixedJohnAutomaticDensityRepetitions D hD
  let J : Real := Jn
  let M : Real := (fixedJohnPackingMaximalConcentration D hD).toReal
  let tail : Real := fixedJohnTailParameter D hD
  have hrho : 0 < rho := by
    exact_mod_cast admissibleNormalizedRadiusPos hD
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast Fintype.card_pos
  have hJn : 1 <= Jn :=
    one_le_fixedJohnAutomaticDensityRepetitions D hD
  have hJ : 1 <= J := by
    dsimp only [J]
    exact_mod_cast hJn
  have hcost : 0 < 9504 * N * rho ^ 2 := by positivity
  have hratio : M / (9504 * N * rho ^ 2) - 1 < J := by
    simpa only [fixedJohnDensityRatio, fixedJohnDensityUnitCost,
      rho, N, Jn, J, M] using
        fixedJohnDensityRatio_sub_one_lt_repetitions D hD
  have hratioTwo : M / (9504 * N * rho ^ 2) < 2 * J := by
    linarith
  have hM : M <= 19008 * J * N * rho ^ 2 := by
    have hstrict : M < (2 * J) * (9504 * N * rho ^ 2) :=
      (div_lt_iff₀ hcost).mp hratioTwo
    nlinarith
  have htail : 0 <= tail := by
    dsimp only [tail]
    linarith [one_le_fixedJohnTailParameter D hD]
  have hparam :
      (fixedJohnFullCopiedCWAParameter D hD).toReal =
        tail * M / (rho ^ 2 / 2) / (J * N) := by
    unfold fixedJohnFullCopiedCWAParameter
    norm_num [ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal htail,
      Fintype.card_prod, Fintype.card_fin, rho, N, Jn, J, M, tail]
  rw [hparam]
  change tail * M / (rho ^ 2 / 2) / (J * N) <= 38016 * tail
  apply (div_le_iff₀ (mul_pos (by linarith) hN)).2
  apply (div_le_iff₀ (by positivity : 0 < rho ^ 2 / 2)).2
  calc
    tail * M <= tail * (19008 * J * N * rho ^ 2) :=
      mul_le_mul_of_nonneg_left hM htail
    _ = 38016 * tail * (J * N) * (rho ^ 2 / 2) := by ring

theorem fixedJohnFullCopiedCWAParameter_le_tail
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    fixedJohnFullCopiedCWAParameter D hD <=
      ENNReal.ofReal (38016 * fixedJohnTailParameter D hD) := by
  have htail : 0 <= 38016 * fixedJohnTailParameter D hD := by
    have := one_le_fixedJohnTailParameter D hD
    positivity
  have hMtop : fixedJohnPackingMaximalConcentration D hD ≠ ∞ := by
    unfold fixedJohnPackingMaximalConcentration
    exact
      (FamilyStickyFiniteFamilyMaximalConcentrationV1.maximalConcentration_lt_top
        (fixedJohnNormalizedActiveFamily D)).ne
  have hlower0 : (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) ≠ 0 := by
    apply (ENNReal.div_ne_zero).2
    constructor
    · exact ENNReal.pow_ne_zero
        (ENNReal.coe_ne_zero.mpr (admissibleNormalizedRadiusPos hD).ne') 2
    · norm_num
  have hcard0 :
      (Fintype.card
        (Fin (fixedJohnAutomaticDensityRepetitions D hD) × iota) : ENNReal) ≠ 0 := by
    rw [Fintype.card_prod, Fintype.card_fin]
    exact_mod_cast Nat.mul_ne_zero
      (Nat.ne_of_gt (one_le_fixedJohnAutomaticDensityRepetitions D hD))
      Fintype.card_ne_zero
  have hparamTop : fixedJohnFullCopiedCWAParameter D hD ≠ ∞ := by
    unfold fixedJohnFullCopiedCWAParameter
    apply ENNReal.div_ne_top
    · apply ENNReal.div_ne_top
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMtop
      · exact hlower0
    · exact hcard0
  apply (ENNReal.toReal_le_toReal hparamTop ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal htail] using
    fixedJohnFullCopiedCWAParameter_toReal_le_tail D hD

#print axioms fixedJohnFullCopiedCWAParameter_toReal_le_tail
#print axioms fixedJohnFullCopiedCWAParameter_le_tail

end
end Family8FiniteRandomRigidMotionPaperFixedJohnCWAParameterBudgetV3
