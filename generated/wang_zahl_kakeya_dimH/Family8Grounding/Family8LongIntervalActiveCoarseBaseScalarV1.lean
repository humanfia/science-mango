import Family8Grounding.Family8CanonicalLowerBufferedScaleV4
import Family8Grounding.Family8LongIntervalBootstrapNumericsV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8LongIntervalActiveCoarseBaseScalarV1

open Family8CanonicalLowerBufferedScaleV4

noncomputable section

/-!
# Long-interval normalized cardinality to the active-parent base scalar

If `X = N * b^2`, the long-interval lower bound on `X` and the sharp ratio
`b / tau <= d^(-epsilon)` recover a lower bound on the fine-scale scalar
`N * tau^2 / 2`.  This is exactly the scalar consumed by the weighted
selected-family base-budget bridge.
-/

/-- Pure normalized-cardinality algebra.  No cover or selection structure is
needed: those objects only have to provide the displayed identity for `X`. -/
theorem longInterval_activeCoarse_halfSq_lower
    {d tau b X : NNReal} {N : Nat} {epsilon etaPrime : Real}
    (hd : 0 < d) (htau : 0 < tau)
    (hX : X = (N : NNReal) * b ^ 2)
    (hXLower : d ^ etaPrime <= X)
    (hratio : b / tau <= d ^ (-epsilon)) :
    (d : ENNReal) ^ (etaPrime + 2 * epsilon) / 2 <=
      (N : ENNReal) * ((tau : ENNReal) ^ 2 / 2) := by
  have hb : b <= tau * d ^ (-epsilon) := by
    have h := (div_le_iff₀ htau).mp hratio
    simpa only [mul_comm] using h
  have hXUpper : X <=
      (N : NNReal) * (tau * d ^ (-epsilon)) ^ 2 := by
    rw [hX]
    gcongr
  have hchain : d ^ etaPrime <=
      (N : NNReal) * (tau * d ^ (-epsilon)) ^ 2 :=
    hXLower.trans hXUpper
  have hsquare :
      (d ^ (-epsilon)) ^ 2 = d ^ ((-epsilon) * 2) := by
    rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
    norm_num
  have hcancel :
      d ^ (2 * epsilon) * (d ^ (-epsilon)) ^ 2 = 1 := by
    rw [hsquare, ← NNReal.rpow_add hd.ne']
    convert NNReal.rpow_zero d using 1
    ring
  have hmul :
      d ^ (2 * epsilon) * d ^ etaPrime <=
        d ^ (2 * epsilon) *
          ((N : NNReal) * (tau * d ^ (-epsilon)) ^ 2) :=
    mul_le_mul' le_rfl hchain
  have hcore : d ^ (etaPrime + 2 * epsilon) <=
      (N : NNReal) * tau ^ 2 := by
    calc
      d ^ (etaPrime + 2 * epsilon) =
          d ^ (2 * epsilon) * d ^ etaPrime := by
        rw [← NNReal.rpow_add hd.ne']
        congr 1
        ring
      _ <= d ^ (2 * epsilon) *
          ((N : NNReal) * (tau * d ^ (-epsilon)) ^ 2) := hmul
      _ = ((N : NNReal) * tau ^ 2) *
          (d ^ (2 * epsilon) * (d ^ (-epsilon)) ^ 2) := by
        ring
      _ = (N : NNReal) * tau ^ 2 := by rw [hcancel, mul_one]
  have hhalf : d ^ (etaPrime + 2 * epsilon) / 2 <=
      (N : NNReal) * (tau ^ 2 / 2) := by
    calc
      d ^ (etaPrime + 2 * epsilon) / 2 <=
          ((N : NNReal) * tau ^ 2) / 2 :=
        (div_le_div_iff_of_pos_right
          (by norm_num : (0 : NNReal) < 2)).2 hcore
      _ = (N : NNReal) * (tau ^ 2 / 2) := by ring
  have hcast :
      ((d ^ (etaPrime + 2 * epsilon) / 2 : NNReal) : ENNReal) <=
        (((N : NNReal) * (tau ^ 2 / 2) : NNReal) : ENNReal) :=
    ENNReal.coe_le_coe.mpr hhalf
  simpa only [ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0),
    ENNReal.coe_rpow_of_ne_zero hd.ne', ENNReal.coe_mul,
    ENNReal.coe_pow, ENNReal.coe_natCast, ENNReal.coe_ofNat] using hcast

/-- Canonical buffered-scale instance.  The ratio premise is now supplied
by the existing sharp canonical scale theorem. -/
theorem canonicalLowerBufferedScale_activeCoarse_halfSq_lower
    {d tau theta X : NNReal} {N : Nat} {epsilon etaPrime : Real}
    (hd : 0 < d) (hdTau : d <= tau) (hthetaOne : theta <= 1)
    (hepsilon : 0 <= epsilon)
    (hX : X = (N : NNReal) *
      canonicalLowerBufferedScale tau theta epsilon ^ 2)
    (hXLower : d ^ etaPrime <= X) :
    (d : ENNReal) ^ (etaPrime + 2 * epsilon) / 2 <=
      (N : ENNReal) * ((tau : ENNReal) ^ 2 / 2) := by
  exact longInterval_activeCoarse_halfSq_lower hd
    (hd.trans_le hdTau) hX hXLower
      (canonicalLowerBufferedScale_div_tau_le_delta_rpow_neg
        hd hdTau hthetaOne hepsilon)

#print axioms longInterval_activeCoarse_halfSq_lower
#print axioms canonicalLowerBufferedScale_activeCoarse_halfSq_lower

end
end Family8LongIntervalActiveCoarseBaseScalarV1
