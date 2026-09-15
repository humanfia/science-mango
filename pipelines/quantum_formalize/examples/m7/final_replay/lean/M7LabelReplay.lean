import M7ClosedSolveAccepted
import M7DefaultQuery
import M7RecipeSignatureAccepted

namespace M7.LabelReplay
noncomputable def Q {N : ℕ} [NeZero N] (c : M7.Action.Recipe N)
    (P : M6.Pinned.Pins (2*N)) : Polynomial ℤ :=
  M6.ActualTransfer.Q N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) P
structure PinStep (N : ℕ) where
  index : Fin (2*N)
  before : M6.Pinned.Pins (2*N)
  zeroCoefficient : Option ℤ
  after : M6.Pinned.Pins (2*N)
  queries : ℕ
  deriving DecidableEq
noncomputable def trace {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (d : ℕ)
    (P : M6.Pinned.Pins (2*N)) : List (Fin (2*N)) → List (PinStep N)
  | [] => []
  | i :: xs =>
    let next := M6.Pinned.choose (fun P => (Q c P).coeff d) P i
    ⟨i,P,if P i = none then some ((Q c (M6.Pinned.pin P i 0)).coeff d) else none,
      next.1,next.2⟩ :: trace c d next.1 xs

def endpoint {N : ℕ} (P : M6.Pinned.Pins (2*N)) (steps : List (PinStep N)) :=
  steps.foldl (fun _ s => s.after) P
def queryCount {N : ℕ} (steps : List (PinStep N)) := (steps.map PinStep.queries).sum
noncomputable def pinData {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : List (PinStep N) :=
  match M6.Pinned.firstPositive (2*N) (Q c (M6.Pinned.free (2*N))) with
  | none => []
  | some d => trace c d (M6.Pinned.free (2*N)) (List.finRange (2*N))
structure Certificate (N : ℕ) where
  signature : M6.Cyclic.BinaryPolynomial
  coefficients : Fin (2*N+1) → ℤ
  answer : Option (ℕ × M6.Pinned.Vector (2*N) × ℕ)
  pins : List (PinStep N)
  deriving DecidableEq
noncomputable def expected {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Certificate N :=
  ⟨M7.RecipeSignature.signature c, fun i => (Q c (M6.Pinned.free (2*N))).coeff i.val,
   M6.ActualTransfer.solve N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2), pinData c⟩
/-- Finite data equality against actual recurrence and pin-recovery computations. -/
noncomputable def check {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (r : Certificate N) : Bool :=
  decide (r = expected c)
end M7.LabelReplay
