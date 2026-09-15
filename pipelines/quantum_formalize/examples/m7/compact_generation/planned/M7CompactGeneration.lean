import M7RecipeSignatureAccepted
import M7CanonicalClassesAccepted
import M7PrefixBitsAccepted
import M7DescentTraceAccepted

/- Prepared definition, pending canonical parent compilation and exact-target acceptance. -/
namespace M7.CompactGeneration
noncomputable section
open Classical
open scoped BigOperators

noncomputable def residual {N : ℕ} [NeZero N] (w : ℕ)
    (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N))
    (p : List Bool) : ℤ :=
  M7.PrefixBits.count N w E p - ∑ c ∈ bases,
    (M7.RecipeSignature.sourceCount c (fun F => F ∈ E)
      (fun S => M7.PrefixBits.A N p ⊆ M7.ResiduePrefix.encode S ∧
        M7.ResiduePrefix.encode S ⊆ M7.PrefixBits.A N p ∪ M7.PrefixBits.WA N p)
      (fun S => M7.PrefixBits.B N p ⊆ M7.ResiduePrefix.encode S ∧
        M7.ResiduePrefix.encode S ⊆ M7.PrefixBits.B N p ∪ M7.PrefixBits.WB N p) : ℤ)

structure Emission (N : ℕ) [NeZero N] where
  path : List M7.DescentTrace.Step
  leaf : M7.Action.Recipe N
  representative : M7.Action.Recipe N
  action : M7.Action.Record N
  leafSignature : M5.BinaryPolynomial
  representativeSignature : M5.BinaryPolynomial
  stabilizer : ℕ

noncomputable def emission {N : ℕ} [NeZero N] (w : ℕ)
    (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)) : Emission N :=
  let path := M7.DescentTrace.trace (residual w E bases) [] (M7.PrefixBits.depth N)
  let p := M7.DescentTrace.endpoint [] path
  let leaf := M7.ResiduePrefix.decodePair N (M7.PrefixBits.A N p, M7.PrefixBits.B N p)
  let representative := M7.CanonicalOuter.canonical leaf
  ⟨path, leaf, representative, M7.CanonicalOuter.realizer leaf,
    M7.RecipeSignature.signature leaf, M7.RecipeSignature.signature representative,
    M7.ActualFactorized.stabilizerNumerator representative⟩

structure Output (N : ℕ) [NeZero N] where
  emitted : List (Emission N)
  finalBases : Finset (M7.Action.Recipe N)
  finalResidual : ℤ
  fuelExhausted : Bool

/-- Total finite-fuel recurrence with a cached root count. Internal correctness assumes
    the cache equals the actual residual; `generate` and every recursive call establish it.
    Downstream correctness must rule out positive exhaustion. -/
noncomputable def run {N : ℕ} [NeZero N] (w : ℕ)
    (E : Finset M5.BinaryPolynomial) : ℕ → Finset (M7.Action.Recipe N) → ℤ → Output N
  | 0, bases, root =>
    ⟨[], bases, root, decide (0 < root)⟩
  | fuel + 1, bases, root =>
    if 0 < root then
      let e := emission w E bases
      let nextBases := insert e.representative bases
      let nextRoot := residual w E nextBases []
      let tail := run w E fuel nextBases nextRoot
      { tail with emitted := e :: tail.emitted }
    else ⟨[], bases, root, false⟩

noncomputable def generate {N : ℕ} [NeZero N] (w : ℕ)
    (E : Finset M5.BinaryPolynomial) : Output N :=
  let root := residual w E (∅ : Finset (M7.Action.Recipe N)) []
  run w E root.toNat ∅ root
end
end M7.CompactGeneration
