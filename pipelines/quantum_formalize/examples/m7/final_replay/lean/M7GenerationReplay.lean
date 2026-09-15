import M7CompactCorrectnessAccepted
import M7RawCoverageAccepted

namespace M7.GenerationReplay
noncomputable section
open Classical

/-- Every stored field is recomputed from the actual current prefix count. -/
def stepPass {N : ℕ} [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial)
    (bases : Finset (M7.Action.Recipe N)) (e : M7.CompactGeneration.Emission N) : Bool :=
  decide (0 < M7.CompactGeneration.residual w E bases []) &&
    (M7.DescentTrace.check (M7.CompactGeneration.residual w E bases) [] e.path).1 &&
    decide (e.path.length = M7.PrefixBits.depth N ∧
      e.leaf = M7.ResiduePrefix.decodePair N
        (M7.PrefixBits.A N (M7.DescentTrace.endpoint [] e.path),
         M7.PrefixBits.B N (M7.DescentTrace.endpoint [] e.path)) ∧
      e.representative = M7.CanonicalOuter.canonical e.leaf ∧
      e.action = M7.CanonicalOuter.realizer e.leaf ∧
      e.leafSignature = M7.RecipeSignature.signature e.leaf ∧
      e.representativeSignature = M7.RecipeSignature.signature e.representative ∧
      e.stabilizer = M7.ActualFactorized.stabilizerNumerator e.representative)

/-- Success at the end requires recomputing an actual zero root residual. -/
def replay {N : ℕ} [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) :
    Finset (M7.Action.Recipe N) → List (M7.CompactGeneration.Emission N) → Option (Finset (M7.Action.Recipe N))
  | bases, [] => if M7.CompactGeneration.residual w E bases [] = 0 then some bases else none
  | bases, e :: es => if stepPass w E bases e then replay w E (insert e.representative bases) es else none

/-- The advertised final state is checked against the replay from the empty state. -/
def check {N : ℕ} [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial)
    (o : M7.CompactGeneration.Output N) : Bool :=
  match replay w E ∅ o.emitted with
  | none => false
  | some bases => decide (bases = o.finalBases ∧ o.finalResidual = 0 ∧ o.fuelExhausted = false)

/-- Semantic audit trail, not an input assumption for the checker. -/
def FreshFrom {N : ℕ} [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) :
    Finset (M7.Action.Recipe N) → List (M7.CompactGeneration.Emission N) → Prop
  | _, [] => True
  | bases, e :: es => e.representative ∉ bases ∧ M7.PrefixOrbit.ClassValid w e.representative ∧
      e.leaf ∈ M7.RecoveryPrefix.completed N w E [] ∧ FreshFrom w E (insert e.representative bases) es
end
end M7.GenerationReplay
