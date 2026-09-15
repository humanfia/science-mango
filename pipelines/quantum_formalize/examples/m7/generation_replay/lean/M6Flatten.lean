import M6PhysicalAccepted
import M6Character
import M6Pinned
open scoped BigOperators
namespace M6.Flatten
noncomputable def flatten (N : ℕ) (z : M6.Physical.Word N) : M6.Pinned.Vector (2*N) := fun i =>
  if i.val < N then z.1 (i.val : ZMod N) else z.2 ((i.val-N : ℕ) : ZMod N)
noncomputable def unflatten (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2*N)) : M6.Physical.Word N :=
  (fun i => v ⟨i.val, by have hi := ZMod.val_lt i; omega⟩,
   fun i => v ⟨N+i.val, by have hi := ZMod.val_lt i; omega⟩)
noncomputable def J (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2*N)) : M6.Pinned.Vector (2*N) :=
  flatten N (M6.Physical.J N (unflatten N v))
end M6.Flatten
