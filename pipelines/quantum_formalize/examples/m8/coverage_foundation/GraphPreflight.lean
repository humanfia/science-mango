import M8CoverageFoundation
def target_0 : Prop := (∀ (N : ℕ) [NeZero N], ∀ (A : Finset (ZMod N)) (H : AddSubgroup (ZMod N)), M8.CoverageFoundation.InCoset A H → M8.CoverageFoundation.direction A ≤ H)
def target_1 : Prop := (∀ (N : ℕ) [NeZero N], ∀ (A : Finset (ZMod N)) (a : ZMod N), a ∈ A → a+1 ∈ A → M8.CoverageFoundation.FullDirection A)
def target_2 : Prop := (∀ (N : ℕ) [NeZero N], ∀ (A : Finset (ZMod N)) (u : (ZMod N)ˣ) (s : ZMod N), M8.CoverageFoundation.FullDirection (A.image (M7.Action.affine u s)) ↔ M8.CoverageFoundation.FullDirection A)
def target_3 : Prop := (∀ (N : ℕ) [NeZero N], ∀ q : ℕ, 2 ≤ q → q ∣ N → AddSubgroup.zmultiples (q : ZMod N) ≠ ⊤)
def target_4 : Prop := (∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (M8.CoverageFoundation.FullDirection c.1 ∨ M8.CoverageFoundation.FullDirection c.2) → ¬ M8.CoverageFoundation.Separated c)
def target_5 : Prop := (∀ (N : ℕ) [NeZero N], ∀ (c : M7.Action.Recipe N) (g : M7.Action.Record N), (M8.CoverageFoundation.FullDirection c.1 ∨ M8.CoverageFoundation.FullDirection c.2) → ¬ M8.CoverageFoundation.Separated (M7.Action.act g c))
