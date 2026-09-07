import Family8Grounding.Family8ActiveCoarseFrostmanCardScaleMassLowerV3
import Family8Grounding.Family8ParameterLadderV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8ActiveCoarseFrostmanCardScaleMassLowerV3.StickyScaleCover

noncomputable section

/-!
# Automatic small-delta absorption for the coarse Frostman lower bound

The geometric theorem gives `d^e <= 8 * X`.  This file removes exactly that
factor under the sharp explicit condition `0 < d <= 8 ^ (-1 / a)`.

It also records the canonical ten-part long-interval allocation: nine parts
are requested from the active-coarse Frostman-constant producer and one part
absorbs the dimensional constant.  No Frostman certificate or power estimate
is stored as a new field.
-/

/-- The exact threshold obtained by solving `8 = d ^ (-a)`. -/
def frostmanEightSharpSmallDeltaThreshold (a : Real) : NNReal :=
  (8 : NNReal) ^ (-(1 / a))

theorem frostmanEightSharpSmallDeltaThreshold_pos (a : Real) :
    0 < frostmanEightSharpSmallDeltaThreshold a := by
  apply NNReal.rpow_pos
  norm_num

theorem frostmanEightSharpSmallDeltaThreshold_le_one
    {a : Real} (ha : 0 < a) :
    frostmanEightSharpSmallDeltaThreshold a <= 1 := by
  apply NNReal.rpow_le_one_of_one_le_of_nonpos
  · norm_num
  · have hinv : 0 < 1 / a := one_div_pos.mpr ha
    linarith

/-- At the sharp threshold the negative power is exactly eight. -/
theorem frostmanEightSharpSmallDeltaThreshold_rpow_neg
    {a : Real} (ha : 0 < a) :
    frostmanEightSharpSmallDeltaThreshold a ^ (-a) = 8 := by
  have hmul : (-(1 / a)) * (-a) = (1 : Real) := by
    field_simp [ne_of_gt ha]
  calc
    frostmanEightSharpSmallDeltaThreshold a ^ (-a) =
        ((8 : NNReal) ^ (-(1 / a))) ^ (-a) := by rfl
    _ = (8 : NNReal) ^ ((-(1 / a)) * (-a)) := by
      rw [NNReal.rpow_mul]
    _ = 8 := by rw [hmul, NNReal.rpow_one]

/-- The sharp threshold automatically produces the factor-eight negative
power premise. -/
theorem eight_le_globalDelta_rpow_neg_of_le_sharpThreshold
    {globalDelta : NNReal} {a : Real}
    (hglobal : 0 < globalDelta) (ha : 0 < a)
    (hdelta : globalDelta <= frostmanEightSharpSmallDeltaThreshold a) :
    (8 : ENNReal) <= (globalDelta : ENNReal) ^ (-a) := by
  have hnn : (8 : NNReal) <= globalDelta ^ (-a) := by
    calc
      (8 : NNReal) =
          frostmanEightSharpSmallDeltaThreshold a ^ (-a) :=
        (frostmanEightSharpSmallDeltaThreshold_rpow_neg ha).symm
      _ <= globalDelta ^ (-a) :=
        NNReal.rpow_le_rpow_of_nonpos hglobal hdelta
          (neg_nonpos.mpr ha.le)
  rw [<- ENNReal.coe_rpow_of_ne_zero hglobal.ne' (-a)]
  exact ENNReal.coe_le_coe.mpr hnn

/-- Pure scalar absorption from `d^e <= 8 X` to `d^(e+a) <= X`. -/
theorem global_rpow_add_absorb_le_of_le_eight_mul
    {globalDelta : NNReal} {X : ENNReal} {e a : Real}
    (hglobal : 0 < globalDelta) (ha : 0 < a)
    (hdelta : globalDelta <= frostmanEightSharpSmallDeltaThreshold a)
    (hrough : (globalDelta : ENNReal) ^ e <= 8 * X) :
    (globalDelta : ENNReal) ^ (e + a) <= X := by
  have hd0 : (globalDelta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hglobal.ne'
  have hdTop : (globalDelta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have h8 := eight_le_globalDelta_rpow_neg_of_le_sharpThreshold
    hglobal ha hdelta
  have hfactor : (globalDelta : ENNReal) ^ a * 8 <= 1 := by
    calc
      (globalDelta : ENNReal) ^ a * 8 <=
          (globalDelta : ENNReal) ^ a *
            (globalDelta : ENNReal) ^ (-a) :=
        mul_le_mul' le_rfl h8
      _ = 1 := by
        rw [<- ENNReal.rpow_add _ _ hd0 hdTop]
        simp
  calc
    (globalDelta : ENNReal) ^ (e + a) =
        (globalDelta : ENNReal) ^ a *
          (globalDelta : ENNReal) ^ e := by
      rw [show e + a = a + e by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]
    _ <= (globalDelta : ENNReal) ^ a * (8 * X) :=
      mul_le_mul' le_rfl hrough
    _ = ((globalDelta : ENNReal) ^ a * 8) * X := by
      ac_rfl
    _ <= 1 * X := mul_le_mul' hfactor le_rfl
    _ = X := one_mul X

/-! ## Canonical one-part allocation from the parameter ladder -/

def firstLongFrostmanAbsorbExponent
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat) : Real :=
  P.eta j / (P.epsilon * beta)

def firstLongFrostmanBaseExponent
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat) : Real :=
  9 * P.eta j / (P.epsilon * beta)

theorem firstLongFrostmanAbsorbExponent_pos
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (hbeta : 0 < beta) :
    0 < firstLongFrostmanAbsorbExponent P j := by
  exact div_pos (P.eta_pos j) (mul_pos P.epsilon_pos hbeta)

theorem firstLongFrostmanExponent_add_absorb
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat) :
    firstLongFrostmanBaseExponent P j +
        firstLongFrostmanAbsorbExponent P j =
      10 * P.eta j / (P.epsilon * beta) := by
  unfold firstLongFrostmanBaseExponent firstLongFrostmanAbsorbExponent
  ring

def firstLongFrostmanEightSmallDeltaThreshold
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat) : NNReal :=
  frostmanEightSharpSmallDeltaThreshold
    (firstLongFrostmanAbsorbExponent P j)

theorem firstLongFrostmanEightSmallDeltaThreshold_pos
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat) :
    0 < firstLongFrostmanEightSmallDeltaThreshold P j :=
  frostmanEightSharpSmallDeltaThreshold_pos _

theorem firstLongFrostmanEightSmallDeltaThreshold_le_one
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (hbeta : 0 < beta) :
    firstLongFrostmanEightSmallDeltaThreshold P j <= 1 :=
  frostmanEightSharpSmallDeltaThreshold_le_one
    (firstLongFrostmanAbsorbExponent_pos P j hbeta)

theorem parameterLadder_eight_le_globalDelta_rpow_neg
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    {globalDelta : NNReal} (hbeta : 0 < beta)
    (hglobal : 0 < globalDelta)
    (hdelta : globalDelta <=
      firstLongFrostmanEightSmallDeltaThreshold P j) :
    (8 : ENNReal) <= (globalDelta : ENNReal) ^
      (-firstLongFrostmanAbsorbExponent P j) :=
  eight_le_globalDelta_rpow_neg_of_le_sharpThreshold hglobal
    (firstLongFrostmanAbsorbExponent_pos P j hbeta) hdelta

namespace StickyScaleCover

/-- Gen's active-coarse Frostman geometry plus the automatic one-part
small-delta budget gives the exact canonical `hXLower`. -/
theorem parameterLadder_global_rpow_le_activeCoarseCardScaleMass_of_frostman
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho) (K : ConvexBody Space)
    {C : ENNReal} {globalDelta : NNReal}
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (hbeta : 0 < beta)
    (hglobal : 0 < globalDelta)
    (hrho : 0 < rho) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hcoarse : S.activeCoarse.Nonempty)
    (hKVolume : 1 <= volume (K : Set Space))
    (hF : IsFrostmanIn C S.activeCoarseFamily K)
    (hC : C <= (globalDelta : ENNReal) ^
      (-firstLongFrostmanBaseExponent P j))
    (hdelta : globalDelta <=
      firstLongFrostmanEightSmallDeltaThreshold P j) :
    globalDelta ^ (10 * P.eta j / (P.epsilon * beta)) <=
      activeCoarseCardScaleMass S := by
  have hrough : (globalDelta : ENNReal) ^
        firstLongFrostmanBaseExponent P j <=
      8 * (activeCoarseCardScaleMass S : ENNReal) :=
    global_rpow_le_eight_mul_activeCoarseCardScaleMass_of_frostman
      S K hglobal hrho hrhoHalf hcoarse hKVolume hF hC
  have hcore : (globalDelta : ENNReal) ^
        (firstLongFrostmanBaseExponent P j +
          firstLongFrostmanAbsorbExponent P j) <=
      (activeCoarseCardScaleMass S : ENNReal) :=
    global_rpow_add_absorb_le_of_le_eight_mul hglobal
      (firstLongFrostmanAbsorbExponent_pos P j hbeta) hdelta hrough
  apply ENNReal.coe_le_coe.mp
  rw [ENNReal.coe_rpow_of_ne_zero hglobal.ne',
    <- firstLongFrostmanExponent_add_absorb P j]
  exact hcore

#print axioms
  parameterLadder_global_rpow_le_activeCoarseCardScaleMass_of_frostman

end StickyScaleCover

#print axioms frostmanEightSharpSmallDeltaThreshold_pos
#print axioms frostmanEightSharpSmallDeltaThreshold_le_one
#print axioms frostmanEightSharpSmallDeltaThreshold_rpow_neg
#print axioms eight_le_globalDelta_rpow_neg_of_le_sharpThreshold
#print axioms global_rpow_add_absorb_le_of_le_eight_mul
#print axioms firstLongFrostmanAbsorbExponent_pos
#print axioms firstLongFrostmanExponent_add_absorb
#print axioms firstLongFrostmanEightSmallDeltaThreshold_pos
#print axioms firstLongFrostmanEightSmallDeltaThreshold_le_one
#print axioms parameterLadder_eight_le_globalDelta_rpow_neg

end
end Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4
