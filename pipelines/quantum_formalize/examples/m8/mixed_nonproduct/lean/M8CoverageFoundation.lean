import M7ConnectivityAccepted
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

namespace M8.CoverageFoundation
noncomputable def direction {N : ℕ} (A : Finset (ZMod N)) : AddSubgroup (ZMod N) :=
  AddSubgroup.closure (M7.Connectivity.differences A)
def FullDirection {N : ℕ} (A : Finset (ZMod N)) : Prop := direction A = ⊤
def InCoset {N : ℕ} (A : Finset (ZMod N)) (H : AddSubgroup (ZMod N)) : Prop :=
  ∃ a : ZMod N, ∀ x ∈ A, x - a ∈ H
/-- Exactly the proper coprime separated directions of the revised M8 source. -/
def Separated {N : ℕ} (c : M7.Action.Recipe N) : Prop :=
  ∃ m q : ℕ, 2 ≤ m ∧ 2 ≤ q ∧ N = m*q ∧ Nat.Coprime m q ∧
    InCoset c.1 (AddSubgroup.zmultiples (q : ZMod N)) ∧
    InCoset c.2 (AddSubgroup.zmultiples (m : ZMod N))
end M8.CoverageFoundation
