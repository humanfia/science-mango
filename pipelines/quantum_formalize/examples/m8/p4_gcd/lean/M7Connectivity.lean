import Mathlib
import M7DomainAccepted
import M7Action
namespace M7.Connectivity
abbrev Recipe (N : ℕ) := M7.Action.Recipe N
def differences {N : ℕ} (A : Finset (ZMod N)) : Set (ZMod N) :=
 {x | ∃ a ∈ A, ∃ b ∈ A, x = a-b}
def connected {N : ℕ} (c : Recipe N) : Prop :=
 AddSubgroup.closure (differences c.1 ∪ differences c.2) = ⊤
noncomputable def unitEquiv {N : ℕ} (u : (ZMod N)ˣ) : ZMod N ≃+ ZMod N where
 toFun x := (u : ZMod N)*x
 invFun x := (↑(u⁻¹) : ZMod N)*x
 left_inv := by intro x; simp [← mul_assoc]
 right_inv := by intro x; simp [← mul_assoc]
 map_add' := by intro x y; exact mul_add _ _ _
end M7.Connectivity
