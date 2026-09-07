import Family6Grounding.Family6AffinePlankAnalyticHypothesesStableV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8PlankFrostmanCopyLossAlgebraV2

open Family6AffinePlankAnalyticHypothesesStableV1

/-!
# The copy-loss algebra behind the mixed plank Frostman factor

If an `M`-thick family is replaced by at most `CF / M` retained copies and
the reconstruction loses at most `M`, then the copy multiplicity and the
reconstruction loss combine to the exact mixed factor
`CF ^ (1 - beta / 2) * M ^ (beta / 2)`.

This module contains only that algebra.  It does not postulate the geometric
copy construction or any multiplicity conclusion.
-/

/-- Exact exponent identity for the intended `CF / M` copy count and `M`
reconstruction loss. -/
theorem copyLoss_rpow_eq_frostmanMix
    (CF M : ENNReal) (beta : Real)
    (hM0 : M ≠ 0) (hMtop : M ≠ ∞)
    (hbeta0 : 0 ≤ beta) (hbeta2 : beta ≤ 2) :
    M * (CF / M) ^ (1 - beta / 2) =
      CF ^ (1 - beta / 2) * M ^ (beta / 2) := by
  have hp : 0 ≤ 1 - beta / 2 := by linarith
  have hq : 0 ≤ beta / 2 := by linarith
  have hMpos : 0 < M := bot_lt_iff_ne_bot.2 hM0
  have hMp0 : M ^ (1 - beta / 2) ≠ 0 :=
    ne_of_gt (ENNReal.rpow_pos hMpos hMtop)
  have hMptop : M ^ (1 - beta / 2) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hp hMtop
  have hquot : M / M ^ (1 - beta / 2) = M ^ (beta / 2) := by
    symm
    apply (ENNReal.eq_div_iff hMp0 hMptop).2
    rw [← ENNReal.rpow_add_of_nonneg (1 - beta / 2) (beta / 2) hp hq,
      show 1 - beta / 2 + beta / 2 = 1 by ring, ENNReal.rpow_one]
  rw [ENNReal.div_rpow_of_nonneg CF M hp]
  calc
    M * (CF ^ (1 - beta / 2) / M ^ (1 - beta / 2)) =
        CF ^ (1 - beta / 2) * (M / M ^ (1 - beta / 2)) := by
      simp only [ENNReal.div_eq_inv_mul]
      ac_rfl
    _ = CF ^ (1 - beta / 2) * M ^ (beta / 2) := by
      rw [hquot]

/-- Monotone form used by a geometric producer: any loss `L ≤ M` and any
retained copy count `J ≤ CF / M` are bounded by the exact mixed factor. -/
theorem copyLoss_rpow_le_frostmanMix
    (CF M L J : ENNReal) (beta : Real)
    (hM0 : M ≠ 0) (hMtop : M ≠ ∞)
    (hbeta0 : 0 ≤ beta) (hbeta2 : beta ≤ 2)
    (hL : L ≤ M) (hJ : J ≤ CF / M) :
    L * J ^ (1 - beta / 2) ≤
      CF ^ (1 - beta / 2) * M ^ (beta / 2) := by
  have hp : 0 ≤ 1 - beta / 2 := by linarith
  calc
    L * J ^ (1 - beta / 2) ≤
        M * (CF / M) ^ (1 - beta / 2) :=
      mul_le_mul' hL (ENNReal.rpow_le_rpow hJ hp)
    _ = CF ^ (1 - beta / 2) * M ^ (beta / 2) :=
      copyLoss_rpow_eq_frostmanMix CF M beta hM0 hMtop hbeta0 hbeta2

end Family8PlankFrostmanCopyLossAlgebraV2
