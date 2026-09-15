import M7CompactGenerationAccepted

namespace M7.GenerationCalls
noncomputable section
open Classical

/-- The same two arithmetic child evaluations as DescentTrace.trace, with an explicit counter. -/
def traceMeasured (c : List Bool → ℤ) (p : List Bool) : ℕ → List M7.DescentTrace.Step × ℕ
  | 0 => ([], 0)
  | n + 1 =>
    let z := c (p ++ [false])
    let o := c (p ++ [true])
    let bit := M7.DescentTrace.choose z
    let tail := traceMeasured c (p ++ [bit]) n
    (⟨p,bit,z,o⟩ :: tail.1, 2 + tail.2)

noncomputable def emissionMeasured {N : ℕ} [NeZero N] (w : ℕ)
    (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)) :
    M7.CompactGeneration.Emission N × ℕ :=
  let measured := traceMeasured (M7.CompactGeneration.residual w E bases) [] (M7.PrefixBits.depth N)
  let p := M7.DescentTrace.endpoint [] measured.1
  let leaf := M7.ResiduePrefix.decodePair N (M7.PrefixBits.A N p, M7.PrefixBits.B N p)
  let representative := M7.CanonicalOuter.canonical leaf
  (⟨measured.1, leaf, representative, M7.CanonicalOuter.realizer leaf,
    M7.RecipeSignature.signature leaf, M7.RecipeSignature.signature representative,
    M7.ActualFactorized.stabilizerNumerator representative⟩, measured.2)

structure Calls where
  root : ℕ
  children : ℕ
  orbitCounts : ℕ

/-- A cached root was evaluated by the caller. Charge that evaluation exactly once at
    entry, including its actual sum over bases. Each recursive caller computes nextRoot.
    The initial caller is generateMeasured, so no initial count is duplicated. -/
noncomputable def runMeasured {N : ℕ} [NeZero N] (w : ℕ)
    (E : Finset M5.BinaryPolynomial) : ℕ → Finset (M7.Action.Recipe N) → ℤ →
    M7.CompactGeneration.Output N × Calls
  | 0, bases, root =>
    (⟨[], bases, root, decide (0 < root)⟩, ⟨1,0,bases.card⟩)
  | fuel + 1, bases, root =>
    if 0 < root then
      let measured := emissionMeasured w E bases
      let e := measured.1
      let nextBases := insert e.representative bases
      let nextRoot := M7.CompactGeneration.residual w E nextBases []
      let tail := runMeasured w E fuel nextBases nextRoot
      ({ tail.1 with emitted := e :: tail.1.emitted },
        ⟨1 + tail.2.root, measured.2 + tail.2.children,
          bases.card * (1 + measured.2) + tail.2.orbitCounts⟩)
    else (⟨[], bases, root, false⟩, ⟨1,0,bases.card⟩)

noncomputable def generateMeasured {N : ℕ} [NeZero N] (w : ℕ)
    (E : Finset M5.BinaryPolynomial) : M7.CompactGeneration.Output N × Calls :=
  let root := M7.CompactGeneration.residual w E (∅ : Finset (M7.Action.Recipe N)) []
  runMeasured w E root.toNat ∅ root
end
end M7.GenerationCalls
