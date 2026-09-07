import Family8Grounding.Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV17
import Family8Grounding.Family8LongIntervalOrdinaryFiberCapNumericsV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open scoped ENNReal NNReal

namespace Family8LocalFiberCapRelativeSquareCancellationV1

open Family8KatzTaoSamplingMultiplicityV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV4
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV17
open Family8LongIntervalOrdinaryFiberCapNumericsV1

noncomputable section

/-!
# Exact cancellation of one local fibre cap with the relative square

The natural cap is one ceiling of
`240000 C rho^2 / (tau^2/2)`.  Since this ratio is at least one, the ceiling
costs a factor two.  Multiplication by `(tau/rho)^2` then cancels the full
scale ratio exactly, leaving only `960000 C`; in particular no artificial
`2 epsilon` power is paid.
-/

/-- The scale quotient in the incidence ratio cancels exactly against the
opposite relative square. -/
theorem incidenceScale_mul_relativeSquare_eq_two
    {tau rho : NNReal} (htau : 0 < tau) (hrho : 0 < rho) :
    ((rho : ENNReal) ^ 2 / ((tau : ENNReal) ^ 2 / 2)) *
        (((tau : ENNReal) / (rho : ENNReal)) ^ 2) = 2 := by
  have hnn :
      (rho ^ (2 : Nat) / (tau ^ (2 : Nat) / 2)) *
          (tau / rho) ^ (2 : Nat) = (2 : NNReal) := by
    rw [div_pow]
    field_simp [htau.ne', hrho.ne']
  have hden : tau ^ (2 : Nat) / 2 ≠ 0 := by positivity
  have hcast := congrArg (fun x : NNReal => (x : ENNReal)) hnn
  simpa only [ENNReal.coe_mul, ENNReal.coe_div hden,
    ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0),
    ENNReal.coe_div hrho.ne', ENNReal.coe_pow, ENNReal.coe_ofNat] using hcast

/-- Exact incidence-ratio cancellation before the natural ceiling. -/
theorem activeOwnerIncidenceRatio_mul_relativeSquare_eq
    {tau rho : NNReal} {C : ENNReal}
    (htau : 0 < tau) (hrho : 0 < rho) :
    activeOwnerKatzTaoIncidenceRatio tau rho C *
        (((tau : ENNReal) / (rho : ENNReal)) ^ 2) =
      480000 * C := by
  have hscale := incidenceScale_mul_relativeSquare_eq_two htau hrho
  unfold activeOwnerKatzTaoIncidenceRatio
  calc
    C * (240000 * (rho : ENNReal) ^ 2) /
        ((tau : ENNReal) ^ 2 / 2) *
        (((tau : ENNReal) / (rho : ENNReal)) ^ 2) =
      (C * 240000) *
        (((rho : ENNReal) ^ 2 /
          ((tau : ENNReal) ^ 2 / 2)) *
          (((tau : ENNReal) / (rho : ENNReal)) ^ 2)) := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ = (C * 240000) * 2 := by rw [hscale]
    _ = 480000 * C := by ring

/-- The sharp ceiling-inclusive local cap cancellation. -/
theorem katzTaoDoubledFiberNatCap_mul_relativeSquare_le_fixed
    {tau rho : NNReal} {C : ENNReal}
    (htau : 0 < tau) (htauRho : tau <= rho)
    (hCone : 1 <= C) (hCfinite : C ≠ ∞) :
    (katzTaoDoubledFiberNatCap tau rho C : ENNReal) *
        (((tau : ENNReal) / (rho : ENNReal)) ^ 2) <=
      ordinaryFiberNatCapFixedConstant * C := by
  have hrho : 0 < rho := htau.trans_le htauRho
  have hratioOne :
      1 <= activeOwnerKatzTaoIncidenceRatio tau rho C :=
    one_le_activeOwnerKatzTaoIncidenceRatio htau htauRho hCone
  have hratioFinite :
      activeOwnerKatzTaoIncidenceRatio tau rho C ≠ ∞ :=
    activeOwnerKatzTaoIncidenceRatio_ne_top htau hCfinite
  have hcap :
      (katzTaoDoubledFiberNatCap tau rho C : ENNReal) <=
        2 * activeOwnerKatzTaoIncidenceRatio tau rho C := by
    rw [katzTaoDoubledFiberNatCap_eq_samplingMultiplicity]
    exact katzTaoSamplingMultiplicity_coe_le_two_mul
      hratioOne hratioFinite
  calc
    (katzTaoDoubledFiberNatCap tau rho C : ENNReal) *
        (((tau : ENNReal) / (rho : ENNReal)) ^ 2) <=
      (2 * activeOwnerKatzTaoIncidenceRatio tau rho C) *
        (((tau : ENNReal) / (rho : ENNReal)) ^ 2) :=
      mul_le_mul' hcap le_rfl
    _ = 2 *
        (activeOwnerKatzTaoIncidenceRatio tau rho C *
          (((tau : ENNReal) / (rho : ENNReal)) ^ 2)) := by ac_rfl
    _ = 2 * (480000 * C) := by
      rw [activeOwnerIncidenceRatio_mul_relativeSquare_eq htau hrho]
    _ = ordinaryFiberNatCapFixedConstant * C := by
      unfold ordinaryFiberNatCapFixedConstant
      ring

#print axioms incidenceScale_mul_relativeSquare_eq_two
#print axioms activeOwnerIncidenceRatio_mul_relativeSquare_eq
#print axioms katzTaoDoubledFiberNatCap_mul_relativeSquare_le_fixed

end
end Family8LocalFiberCapRelativeSquareCancellationV1
