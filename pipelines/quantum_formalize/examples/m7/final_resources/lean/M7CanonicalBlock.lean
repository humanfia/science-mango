import Mathlib

namespace M7.CanonicalBlock
abbrev Support (N : ℕ) := Finset (ZMod N)
abbrev AnchorKey := Lex (List ℕ × ℕ)
noncomputable def shift {N : ℕ} [NeZero N] (s : ZMod N) (A : Support N) : Support N :=
  A.image (fun i => i+s)
noncomputable def key {N : ℕ} [NeZero N] (A : Support N) : List ℕ :=
  (A.image ZMod.val).sort (· ≤ ·)
noncomputable def decode (N : ℕ) [NeZero N] (l : List ℕ) : Support N :=
  l.toFinset.image (fun i : ℕ => (i : ZMod N))
noncomputable def candidates {N : ℕ} [NeZero N] (A : Support N) : Finset AnchorKey :=
  A.image (fun q => toLex (key (shift (-q) A), q.val))
noncomputable def bestKey {N : ℕ} [NeZero N] (A : Support N) : AnchorKey :=
  if h : (candidates A).Nonempty then (candidates A).min' h else toLex ([],0)
noncomputable def bestAnchor {N : ℕ} [NeZero N] (A : Support N) : ZMod N :=
  (ofLex (bestKey A)).2
noncomputable def normalize {N : ℕ} [NeZero N] (A : Support N) : Support N :=
  shift (-bestAnchor A) A
end M7.CanonicalBlock
