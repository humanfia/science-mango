import Mathlib

namespace M6.Transfer
abbrev Bit := ZMod 2
abbrev Memory (R : ℕ) := Fin R → Bit
abbrev Input (N : ℕ) := ZMod N → Bit

def shift {R : ℕ} (m : Memory R) (t : Bit) : Memory R :=
  fun j => if h : j.val = 0 then t else m ⟨j.val - 1, by omega⟩

def memoryAt {R N : ℕ} (h : Input N) (i : ZMod N) : Memory R :=
  fun j => h (i - (j.val + 1 : ℕ))

def Follows (R N : ℕ) (m : ZMod N → Memory R) (h : Input N) : Prop :=
  ∀ i, m (i + 1) = shift (m i) (h i)

abbrev ClosedWalk (R N : ℕ) :=
  {p : (ZMod N → Memory R) × Input N // Follows R N p.1 p.2}

noncomputable instance closedWalkFintype (R N : ℕ) [NeZero N] : Fintype (ClosedWalk R N) := by
  classical
  exact Fintype.ofFinite _

def labels {R N : ℕ} (p : ClosedWalk R N) : Input N := p.val.2

def output {R : ℕ} (c : Fin (R+1) → Bit) (m : Memory R) (t : Bit) : Bit :=
  c 0 * t + ∑ j : Fin R, c j.succ * m j

def cyclicOutput {R N : ℕ} (c : Fin (R+1) → Bit) (h : Input N) (i : ZMod N) : Bit :=
  ∑ j : Fin (R+1), c j * h (i - (j.val : ℕ))

end M6.Transfer
