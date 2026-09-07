import Family8Grounding.Family8FixedJohnMaxThresholdSourcePowerV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnCWAParameterBudgetV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FixedJohnMaxThresholdRelativeLossV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteRandomRigidMotionPaperFixedJohnCapVsLongMeanV2
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2
open Family8FiniteRandomRigidMotionPaperFixedJohnTailPowerV2
open Family8FixedJohnMaxThresholdGreedyLossV1
open Family8FixedJohnMaxThresholdSourcePowerV1

noncomputable section

/-!
# Relative maximum-threshold loss

The inverse-square factor in one paper cap is exactly cancelled after the
cap is normalized by the automatic copied source cardinality.  Indeed, the
floor definition of the repetition count gives

`M <= 19008 * J * #T * rho^2`,

where `M` is normalized maximal concentration.  Consequently

`maxCap <= 38016 * 2304^3 * J * #T`.

Thus `maxGreedyLoss / (J * #T)` has only the logarithmic catalogue tail.  No
source Katz--Tao power and no inverse power of `rho` remains.  This is the
exact algebraic cancellation available to a future relative/weighted
conflict transport; the current absolute-loss Frostman connector does not
yet expose this quotient.
-/

theorem fixedJohnPackingMaximalConcentration_toReal_le_copiedCard_rhoSq
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    (fixedJohnPackingMaximalConcentration D hD).toReal <=
      19008 * (fixedJohnAutomaticDensityRepetitions D hD : Real) *
        (Fintype.card iota : Real) *
          (((delta / 8 : NNReal) : Real) ^ 2) := by
  let rho : Real := ((delta / 8 : NNReal) : Real)
  let N : Real := Fintype.card iota
  let Jn : Nat := fixedJohnAutomaticDensityRepetitions D hD
  let J : Real := Jn
  let M : Real := (fixedJohnPackingMaximalConcentration D hD).toReal
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
  have hstrict : M < (2 * J) * (9504 * N * rho ^ 2) :=
    (div_lt_iff₀ hcost).mp hratioTwo
  nlinarith

theorem fixedJohnMaxPaperCap_le_copiedCard
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    fixedJohnMaxPaperCap (fixedJohnPackingGridVector D hD) D hD <=
      (38016 * (2304 : Real) ^ 3) *
        ((fixedJohnAutomaticDensityRepetitions D hD : Real) *
          (Fintype.card iota : Real)) := by
  let rho : Real := ((delta / 8 : NNReal) : Real)
  let N : Real := Fintype.card iota
  let J : Real := fixedJohnAutomaticDensityRepetitions D hD
  let M : Real := (fixedJohnPackingMaximalConcentration D hD).toReal
  have hrho : 0 < rho := by
    exact_mod_cast admissibleNormalizedRadiusPos hD
  have hM : M <= 19008 * J * N * rho ^ 2 := by
    simpa only [M, J, N, rho] using
      fixedJohnPackingMaximalConcentration_toReal_le_copiedCard_rhoSq D hD
  calc
    fixedJohnMaxPaperCap (fixedJohnPackingGridVector D hD) D hD <=
        M * (2304 : Real) ^ 3 / (rho ^ 2 / 2) := by
      simpa only [M, rho] using fixedJohnMaxPaperCap_le_absolute D hD
    _ <= (19008 * J * N * rho ^ 2) * (2304 : Real) ^ 3 /
          (rho ^ 2 / 2) := by
      gcongr
    _ = (38016 * (2304 : Real) ^ 3) * (J * N) := by
      field_simp
      ring

theorem fixedJohnMaxAutomaticGreedyLoss_cast_le_copiedCard_mul_tail
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    (fixedJohnMaxAutomaticGreedyLoss D hD : Real) <=
      (38016 * (2304 : Real) ^ 3 * fixedJohnTailParameter D hD + 2) *
        ((fixedJohnAutomaticDensityRepetitions D hD : Real) *
          (Fintype.card iota : Real)) := by
  let J : Real := fixedJohnAutomaticDensityRepetitions D hD
  let N : Real := Fintype.card iota
  let tail : Real := fixedJohnTailParameter D hD
  let A : Real := 38016 * (2304 : Real) ^ 3
  have htail : 0 <= tail := by
    dsimp only [tail]
    linarith [one_le_fixedJohnTailParameter D hD]
  have hJN : 1 <= J * N := by
    have hJ : 1 <= J := by
      dsimp only [J]
      exact_mod_cast one_le_fixedJohnAutomaticDensityRepetitions D hD
    have hN : 1 <= N := by
      dsimp only [N]
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    nlinarith
  have hcap :
      fixedJohnMaxPaperCap (fixedJohnPackingGridVector D hD) D hD <=
        A * (J * N) := by
    simpa only [A, J, N] using fixedJohnMaxPaperCap_le_copiedCard D hD
  calc
    (fixedJohnMaxAutomaticGreedyLoss D hD : Real) <=
        tail * fixedJohnMaxPaperCap
          (fixedJohnPackingGridVector D hD) D hD + 2 := by
      simpa only [tail] using
        fixedJohnMaxAutomaticGreedyLoss_cast_le_envelope D hD
    _ <= tail * (A * (J * N)) + 2 := by gcongr
    _ <= tail * (A * (J * N)) + 2 * (J * N) := by nlinarith
    _ = (A * tail + 2) * (J * N) := by ring
    _ = (38016 * (2304 : Real) ^ 3 * fixedJohnTailParameter D hD + 2) *
          ((fixedJohnAutomaticDensityRepetitions D hD : Real) *
            (Fintype.card iota : Real)) := by
      rfl

theorem fixedJohnMaxAutomaticGreedyLoss_relative_le_tail
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    (fixedJohnMaxAutomaticGreedyLoss D hD : Real) /
        ((fixedJohnAutomaticDensityRepetitions D hD : Real) *
          (Fintype.card iota : Real)) <=
      38016 * (2304 : Real) ^ 3 * fixedJohnTailParameter D hD + 2 := by
  have hden : 0 <
      (fixedJohnAutomaticDensityRepetitions D hD : Real) *
        (Fintype.card iota : Real) := by
    have hJ : 0 < (fixedJohnAutomaticDensityRepetitions D hD : Real) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
        (one_le_fixedJohnAutomaticDensityRepetitions D hD))
    have hN : 0 < (Fintype.card iota : Real) := by
      exact_mod_cast Fintype.card_pos
    positivity
  apply (div_le_iff₀ hden).2
  simpa only [mul_assoc] using
    fixedJohnMaxAutomaticGreedyLoss_cast_le_copiedCard_mul_tail D hD

def fixedJohnMaxRelativeLossPowerConstant (tailEta : Real) : Real :=
  38016 * (2304 : Real) ^ 3 * fixedJohnTailPowerConstant tailEta + 2

theorem fixedJohnMaxRelativeLossPowerConstant_nonneg (tailEta : Real) :
    0 <= fixedJohnMaxRelativeLossPowerConstant tailEta := by
  unfold fixedJohnMaxRelativeLossPowerConstant
  have htail := fixedJohnTailPowerConstant_nonneg tailEta
  positivity

theorem fixedJohnMaxAutomaticGreedyLoss_relative_le_tailPower
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {tailEta : Real} (htailEta : 0 < tailEta) :
    (fixedJohnMaxAutomaticGreedyLoss D hD : Real) /
        ((fixedJohnAutomaticDensityRepetitions D hD : Real) *
          (Fintype.card iota : Real)) <=
      fixedJohnMaxRelativeLossPowerConstant tailEta *
        (((delta / 8 : NNReal) : Real) ^ (-tailEta)) := by
  let rho : Real := ((delta / 8 : NNReal) : Real)
  have hrho : 0 < rho := by
    exact_mod_cast admissibleNormalizedRadiusPos hD
  have hrhoOne : rho <= 1 := by
    dsimp only [rho]
    exact_mod_cast
      ((div_le_self (show 0 <= delta from bot_le)
        (by norm_num : (1 : NNReal) <= 8)).trans
          (hD.delta_le_half.trans (by norm_num : (2 : NNReal)⁻¹ <= 1)))
  have htail := fixedJohnTailParameter_le_power D hD htailEta
  have hpowerOne : 1 <= rho ^ (-tailEta) := by
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hrho hrhoOne
      (neg_nonpos.mpr htailEta.le)
  calc
    (fixedJohnMaxAutomaticGreedyLoss D hD : Real) /
          ((fixedJohnAutomaticDensityRepetitions D hD : Real) *
            (Fintype.card iota : Real)) <=
        38016 * (2304 : Real) ^ 3 * fixedJohnTailParameter D hD + 2 :=
      fixedJohnMaxAutomaticGreedyLoss_relative_le_tail D hD
    _ <= 38016 * (2304 : Real) ^ 3 *
          (fixedJohnTailPowerConstant tailEta * rho ^ (-tailEta)) + 2 := by
      gcongr
    _ <= 38016 * (2304 : Real) ^ 3 *
          (fixedJohnTailPowerConstant tailEta * rho ^ (-tailEta)) +
        2 * rho ^ (-tailEta) := by nlinarith
    _ = fixedJohnMaxRelativeLossPowerConstant tailEta *
          rho ^ (-tailEta) := by
      unfold fixedJohnMaxRelativeLossPowerConstant
      ring

#print axioms
  fixedJohnPackingMaximalConcentration_toReal_le_copiedCard_rhoSq
#print axioms fixedJohnMaxPaperCap_le_copiedCard
#print axioms fixedJohnMaxAutomaticGreedyLoss_cast_le_copiedCard_mul_tail
#print axioms fixedJohnMaxAutomaticGreedyLoss_relative_le_tail
#print axioms fixedJohnMaxAutomaticGreedyLoss_relative_le_tailPower

end
end Family8FixedJohnMaxThresholdRelativeLossV2
