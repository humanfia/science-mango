import Family8Grounding.Family8SelectedParentMassPopularCordobaCoreV2
import Mathlib.Tactic

/-!
# Card-weighted Cordoba cancellation algebra

A retained source mass carrying a positive finite block weight can be fed to
the ordinary division-free Cordoba cancellation.  If the mean denominator's
count is at most twice that weight, the weight cancels and only the constant
two remains.
-/

open scoped ENNReal

namespace Family8CardWeightedCordobaCancellationAlgebraV1

open Family8SelectedParentMassPopularCordobaCoreV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-- Pure, division-free cancellation of the selected block weight against
the selected-bucket count. -/
theorem cardWeighted_massRetention_mul_cordobaQuotient_le
    {source bucket block count loss KT containerVolume : ENNReal}
    (hretained : source * block ≤ loss * bucket)
    (hbucket0 : bucket ≠ 0) (hbucketTop : bucket ≠ ∞)
    (hcount0 : count ≠ 0) (hcountTop : count ≠ ∞)
    (hblock0 : block ≠ 0) (hblockTop : block ≠ ∞)
    (hcount : count ≤ 2 * block) :
    source * (KT * (containerVolume / (bucket / count))) ≤
      loss * 2 * (KT * containerVolume) := by
  have hcore := massRetention_mul_cordobaQuotient_le hretained
    hbucket0 hbucketTop hcount0 hcountTop
    (KT := KT) (containerVolume := containerVolume)
  have hwithBlock :
      (source * (KT * (containerVolume / (bucket / count)))) * block ≤
        (loss * 2 * (KT * containerVolume)) * block := by
    calc
      (source * (KT * (containerVolume / (bucket / count)))) * block =
          (source * block) *
            (KT * (containerVolume / (bucket / count))) := by ac_rfl
      _ ≤ loss * count * (KT * containerVolume) := hcore
      _ ≤ loss * (2 * block) * (KT * containerVolume) := by
        exact mul_le_mul' (mul_le_mul' le_rfl hcount) le_rfl
      _ = (loss * 2 * (KT * containerVolume)) * block := by ac_rfl
  apply (ENNReal.mul_le_mul_iff_left hblock0 hblockTop).mp
  simpa only [mul_comm] using hwithBlock

#print axioms cardWeighted_massRetention_mul_cordobaQuotient_le

end


end Family8CardWeightedCordobaCancellationAlgebraV1
