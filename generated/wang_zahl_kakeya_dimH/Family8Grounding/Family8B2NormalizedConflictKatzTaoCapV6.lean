import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV5
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8B2NormalizedConflictKatzTaoCapV6

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8B2NormalizedConflictKatzTaoCapV3
open Family8B2NormalizedConflictKatzTaoCapV5

noncomputable section

/-!
# Source-Katz--Tao and loss-envelope forms of the fixed conflict cap
-/

/-- A raw source Katz--Tao constant gives the radius-free normalized conflict
cap, with the honest normalization factor `128`. -/
theorem normalizedConflictIndices_card_le_sourceFixedKatzTaoNatCap
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (a : iota) :
    (normalizedConflictIndices D a).card <=
      Nat.ceil ((480000 * (128 * C) : ENNReal).toReal) := by
  apply normalizedConflictIndices_card_le_fixedKatzTaoNatCap
    D hdeltaPos hdeltaHalf
  · exact ENNReal.mul_ne_top (by norm_num) hCfinite
  · exact eighthNormalizedDatum_isKatzTao D hdeltaHalf hKT

/-- The natural ceiling costs at most one beyond its finite ENNReal input. -/
theorem fixedKatzTaoNatCap_coe_le_add_one
    {A : ENNReal} (hAfinite : A ≠ ∞) :
    (Nat.ceil ((480000 * A : ENNReal).toReal) : ENNReal) <=
      480000 * A + 1 := by
  have hBfinite : (480000 : ENNReal) * A ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hAfinite
  have hrightTop : (480000 : ENNReal) * A + 1 ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hBfinite, by norm_num⟩
  apply (ENNReal.toReal_le_toReal ENNReal.coe_ne_top hrightTop).mp
  have hceil :=
    (Nat.ceil_lt_add_one
      (ENNReal.toReal_nonneg : 0 <= ((480000 * A : ENNReal).toReal))).le
  simpa [ENNReal.toReal_add, hBfinite] using hceil

/-- The closed-neighbourhood loss used by fresh greedy is bounded by the
same fixed Katz--Tao quantity plus two. -/
theorem fixedKatzTaoClosedLoss_coe_le_add_two
    {A : ENNReal} (hAfinite : A ≠ ∞) :
    ((Nat.ceil ((480000 * A : ENNReal).toReal) + 1 : Nat) : ENNReal) <=
      480000 * A + 2 := by
  calc
    ((Nat.ceil ((480000 * A : ENNReal).toReal) + 1 : Nat) : ENNReal) =
        (Nat.ceil ((480000 * A : ENNReal).toReal) : ENNReal) + 1 := by
      norm_num
    _ <= (480000 * A + 1) + 1 := by
      gcongr
      exact fixedKatzTaoNatCap_coe_le_add_one hAfinite
    _ = 480000 * A + 2 := by ring

#print axioms normalizedConflictIndices_card_le_sourceFixedKatzTaoNatCap
#print axioms fixedKatzTaoNatCap_coe_le_add_one
#print axioms fixedKatzTaoClosedLoss_coe_le_add_two

end
end Family8B2NormalizedConflictKatzTaoCapV6
