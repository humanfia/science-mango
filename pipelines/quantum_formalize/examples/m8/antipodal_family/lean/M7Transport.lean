import M6FinalReady
import M7DomainAccepted
import M7Action
namespace M7.Transport
abbrev Recipe (N : ℕ) := M7.Action.Recipe N
noncomputable def BX {N : ℕ} [NeZero N] (c : Recipe N) := M6.Spaces.boundaryWords N (M7.Supports.indicator c.1) (M7.Supports.indicator c.2)
noncomputable def CX {N : ℕ} [NeZero N] (c : Recipe N) := M6.Spaces.cycleWords N (M7.Supports.indicator c.1) (M7.Supports.indicator c.2)
noncomputable def LX {N : ℕ} [NeZero N] (c : Recipe N) := CX c \ BX c
noncomputable def BZ {N : ℕ} [NeZero N] (c : Recipe N) := M6.Character.subspaceWords (M6.Spaces.D N (M7.Supports.indicator c.1) (M7.Supports.indicator c.2))
noncomputable def CZ {N : ℕ} [NeZero N] (c : Recipe N) := M6.Character.dualWords (M6.Spaces.B N (M7.Supports.indicator c.1) (M7.Supports.indicator c.2))
noncomputable def LZ {N : ℕ} [NeZero N] (c : Recipe N) := CZ c \ BZ c
noncomputable def Xmap {N : ℕ} [NeZero N] (g : M7.Action.Record N) (v : M6.Pinned.Vector (2*N)) :=
 M6.RecipeIsometries.translate N g.leftShift g.rightShift
  (M6.RecipeIsometries.multiplier N g.unit (if g.exchange then M6.RecipeIsometries.blockExchange N v else v))
noncomputable def Zmap {N : ℕ} [NeZero N] (g : M7.Action.Record N) (v : M6.Pinned.Vector (2*N)) := M6.Flatten.J N (Xmap g (M6.Flatten.J N v))
noncomputable def distance {N : ℕ} [NeZero N] (c : Recipe N) := M6.Final.quantumDistance N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2)
end M7.Transport
