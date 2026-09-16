import M7ClosedSolveAccepted
import M7RecipeSignatureAccepted
namespace M8.PhysicalBridge
abbrev Recipe (N : ℕ) := M7.Action.Recipe N
noncomputable def signature {N : ℕ} [NeZero N] (c : Recipe N) := M7.RecipeSignature.signature c
noncomputable def solve {N : ℕ} [NeZero N] (c : Recipe N) :=
  M6.ActualTransfer.solve N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2)
def Valid {N : ℕ} (w : ℕ) (c : Recipe N) : Prop :=
  c.1.card = w ∧ c.2.card = w ∧ M7.Connectivity.connected c
def Anchored {N : ℕ} (c : Recipe N) : Prop := (0 : ZMod N) ∈ c.1 ∧ (0 : ZMod N) ∈ c.2
noncomputable def undo {N : ℕ} [NeZero N] (g : M7.Action.Record N) := M7.Transport.Xmap (M7.Action.inverse g)
end M8.PhysicalBridge
