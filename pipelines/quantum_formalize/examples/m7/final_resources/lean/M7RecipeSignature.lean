import M7ActualFactorized
import M7AffinePolynomial
import M7SignatureTau
namespace M7.RecipeSignature
noncomputable def signature {N : ℕ} (c : M7.Action.Recipe N) : M6.Cyclic.BinaryPolynomial :=
  M6.Cyclic.signature (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) (M6.Cyclic.modulus N)
def region {N : ℕ} (E : M6.Cyclic.BinaryPolynomial → Prop) (c : M7.Action.Recipe N) : Prop :=
  E (signature c)
/-- The source numerator: a unit/exchange sector indicator and separate single-block shift counts. -/
noncomputable def sourceNumerator {N : ℕ} [NeZero N] (c : M7.Action.Recipe N)
    (E : M6.Cyclic.BinaryPolynomial → Prop) (L R : Finset (ZMod N) → Prop) : ℕ :=
  M7.ActualFactorized.numerator c (fun u => E (M7.SignatureTau.sourceTau u.1 (signature c))) L R
noncomputable def sourceCount {N : ℕ} [NeZero N] (c : M7.Action.Recipe N)
    (E : M6.Cyclic.BinaryPolynomial → Prop) (L R : Finset (ZMod N) → Prop) : ℕ :=
  sourceNumerator c E L R / M7.ActualFactorized.stabilizerNumerator c
end M7.RecipeSignature
