import Family8Grounding.Family8KatzTaoParallelTubeGridDatumV1
import Mathlib.Tactic

open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Family8KatzTaoNegativeExponentV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8KatzTaoParallelTubeGridDatumV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-!
# Katz--Tao exponents are nonnegative

The explicit parallel grid supplies `n` disjoint full-shaded tubes at scale
`delta = 1/(100n)`.  Applying a hypothetical negative-exponent Katz--Tao
property with `epsilon = -beta/2` would give
`1 <= delta^(beta/2) n^beta = (n/100)^(beta/2) < 1` once `n > 100`.
-/

/-- At every positive terminal scale there is a grid radius below it with
more than one hundred tubes. -/
theorem exists_parallelGridDelta_le
    {delta0 : NNReal} (hdelta0 : 0 < delta0) :
    ∃ n : Nat, 100 < n ∧ parallelGridDelta n ≤ delta0 := by
  have hdelta0Real : 0 < (delta0 : Real) := by exact_mod_cast hdelta0
  obtain ⟨n, hn⟩ :=
    exists_nat_gt (max (100 : Real) (1 / (100 * (delta0 : Real))))
  have hnHundredReal : (100 : Real) < n :=
    (le_max_left _ _).trans_lt hn
  have hnHundred : 100 < n := by exact_mod_cast hnHundredReal
  have hnBound :
      1 / (100 * (delta0 : Real)) < (n : Real) :=
    (le_max_right _ _).trans_lt hn
  have hprod :
      (1 : Real) < (100 * (delta0 : Real)) * (n : Real) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (div_lt_iff₀ (by positivity : 0 < 100 * (delta0 : Real))).mp hnBound
  have hnPos : 0 < (n : Real) := by linarith
  have hreal :
      (1 / (100 * (n : Real)) : Real) ≤ (delta0 : Real) := by
    rw [div_le_iff₀ (by positivity : 0 < 100 * (n : Real))]
    nlinarith
  refine ⟨n, hnHundred, ?_⟩
  apply NNReal.coe_le_coe.mp
  have hcoe :
      (parallelGridDelta n : Real) =
        (1 / (100 * (n : Real)) : Real) := by
    unfold parallelGridDelta
    rw [NNReal.coe_inv]
    push_cast
    rw [one_div]
  rw [hcoe]
  exact hreal

/-- Exact algebra behind the negative-exponent obstruction. -/
theorem katzTaoMultiplicityRHS_parallelGrid_lt_one
    {beta : Real} (hbeta : beta < 0)
    {n : Nat} (hn : 100 < n) :
    katzTaoMultiplicityRHS (parallelGridDelta n) n (-beta / 2) beta < 1 := by
  have hnPos : 0 < n := lt_trans (by norm_num) hn
  have hn0 : (n : NNReal) ≠ 0 := by exact_mod_cast hnPos.ne'
  have hd0 : parallelGridDelta n ≠ 0 :=
    (parallelGridDelta_pos hnPos).ne'
  have hbase :
      parallelGridDelta n * ((n : NNReal) ^ (2 : Real)) =
        (n : NNReal) / 100 := by
    rw [NNReal.rpow_two]
    calc
      parallelGridDelta n * (n : NNReal) ^ 2 =
          (parallelGridDelta n * (n : NNReal)) * (n : NNReal) := by ring
      _ = (100 : NNReal)⁻¹ * (n : NNReal) := by
        rw [parallelGridDelta_mul_natCast hnPos]
      _ = (n : NNReal) / 100 := by
        rw [div_eq_mul_inv]
        ring
  have hrhsNN :
      parallelGridDelta n ^ (beta / 2) * (n : NNReal) ^ beta =
        ((n : NNReal) / 100) ^ (beta / 2) := by
    have hnPower :
        ((n : NNReal) ^ (2 : Real)) ^ (beta / 2) =
          (n : NNReal) ^ beta := by
      calc
        ((n : NNReal) ^ (2 : Real)) ^ (beta / 2) =
            (n : NNReal) ^ ((2 : Real) * (beta / 2)) :=
          (NNReal.rpow_mul (n : NNReal) 2 (beta / 2)).symm
        _ = (n : NNReal) ^ beta := by congr 1; ring
    calc
      parallelGridDelta n ^ (beta / 2) * (n : NNReal) ^ beta =
          parallelGridDelta n ^ (beta / 2) *
            ((n : NNReal) ^ (2 : Real)) ^ (beta / 2) := by rw [hnPower]
      _ = (parallelGridDelta n * ((n : NNReal) ^ (2 : Real))) ^
          (beta / 2) := NNReal.mul_rpow.symm
      _ = ((n : NNReal) / 100) ^ (beta / 2) := by rw [hbase]
  have hbaseOne : (1 : NNReal) < (n : NNReal) / 100 := by
    rw [lt_div_iff₀ (by norm_num : (0 : NNReal) < 100)]
    exact_mod_cast hn
  have hltNN :
      parallelGridDelta n ^ (beta / 2) * (n : NNReal) ^ beta < 1 := by
    rw [hrhsNN]
    exact NNReal.rpow_lt_one_of_one_lt_of_neg hbaseOne (by linarith)
  unfold katzTaoMultiplicityRHS
  rw [show -(-beta / 2) = beta / 2 by ring]
  have hcast :
      (↑(parallelGridDelta n ^ (beta / 2) *
        (n : NNReal) ^ beta) : ENNReal) < 1 := by exact_mod_cast hltNN
  simpa only [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hd0,
    ENNReal.coe_rpow_of_ne_zero hn0, ENNReal.coe_natCast] using hcast

/-- The quantified Katz--Tao property cannot hold at a negative real
exponent. -/
theorem KatzTaoProperty.nonneg
    {beta : Real} (hKT : KatzTaoProperty beta) :
    0 ≤ beta := by
  by_contra hbetaNonneg
  have hbeta : beta < 0 := lt_of_not_ge hbetaNonneg
  have hepsilon : 0 < -beta / 2 := by linarith
  obtain ⟨eta, delta0, heta, hdelta0, _hdelta0Half, hAt⟩ :=
    hKT (-beta / 2) hepsilon
  obtain ⟨n, hnHundred, hgridScale⟩ :=
    exists_parallelGridDelta_le hdelta0
  have hnPos : 0 < n := lt_trans (by norm_num) hnHundred
  have hbound :=
    hAt (parallelGridDelta n) (Fin n) (parallelGridDatum n)
      (parallelGridDatum_isAdmissible hnPos) hgridScale
      (parallelGridDatum_katzTaoHypotheses hnPos heta.le)
  rw [parallelGridDatum_averageMultiplicity_eq_one hnPos] at hbound
  have hbound' :
      (1 : ENNReal) ≤
        katzTaoMultiplicityRHS (parallelGridDelta n) n (-beta / 2) beta := by
    simpa using hbound
  exact (not_lt_of_ge hbound')
    (katzTaoMultiplicityRHS_parallelGrid_lt_one hbeta hnHundred)

#print axioms exists_parallelGridDelta_le
#print axioms katzTaoMultiplicityRHS_parallelGrid_lt_one
#print axioms KatzTaoProperty.nonneg

end
end Family8KatzTaoNegativeExponentV1
