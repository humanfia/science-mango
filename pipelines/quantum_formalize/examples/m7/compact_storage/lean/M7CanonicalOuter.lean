import M7ActionGroup
import M7CanonicalBlockAccepted

namespace M7.CanonicalOuter
abbrev OuterIndex (N : ℕ) := Lex (Fin N × Bool)
abbrev PairKey := Lex (List ℕ × List ℕ)
abbrev ChoiceKey (N : ℕ) := Lex (PairKey × OuterIndex N)
noncomputable def indices (N : ℕ) [NeZero N] : Finset (OuterIndex N) := by
  classical
  exact Finset.univ.filter (fun i => IsUnit (((ofLex i).1.val : ℕ) : ZMod N))
noncomputable def outerUnit {N : ℕ} [NeZero N] (i : OuterIndex N) : (ZMod N)ˣ := by
  classical
  exact if h : IsUnit (((ofLex i).1.val : ℕ) : ZMod N) then h.unit else 1
noncomputable def outerRecord {N : ℕ} [NeZero N] (i : OuterIndex N) : M7.Action.Record N :=
  ⟨outerUnit i, (ofLex i).2, 0, 0⟩
noncomputable def normalizePair {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : M7.Action.Recipe N :=
  (M7.CanonicalBlock.normalize c.1, M7.CanonicalBlock.normalize c.2)
noncomputable def pairKey {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : PairKey :=
  toLex (M7.CanonicalBlock.key c.1, M7.CanonicalBlock.key c.2)
noncomputable def candidate {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (i : OuterIndex N) : M7.Action.Recipe N :=
  normalizePair (M7.Action.act (outerRecord i) c)
noncomputable def choices {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Finset (ChoiceKey N) :=
  (indices N).image (fun i => toLex (pairKey (candidate c i), i))
noncomputable def best {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : ChoiceKey N :=
  if h : (choices c).Nonempty then (choices c).min' h
  else toLex (toLex ([], []), toLex (⟨0, NeZero.pos N⟩, false))
noncomputable def chosenOuter {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : OuterIndex N :=
  (ofLex (best c)).2
noncomputable def canonical {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : M7.Action.Recipe N :=
  candidate c (chosenOuter c)
noncomputable def realizer {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : M7.Action.Record N :=
  let g := outerRecord (chosenOuter c)
  let r := M7.Action.act g c
  M7.Action.compose (M7.Action.translate (-M7.CanonicalBlock.bestAnchor r.1) (-M7.CanonicalBlock.bestAnchor r.2)) g
noncomputable def keyset {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Finset PairKey :=
  (indices N).image (fun i => pairKey (candidate c i))
end M7.CanonicalOuter
