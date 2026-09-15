import M6Enumerator
def check_0 : Prop := ∀ (m : ℕ) (B C : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m), B ⊆ C → M6.Pinned.enumerator (C \ B) P = M6.Pinned.enumerator C P - M6.Pinned.enumerator B P
def check_1 : Prop := ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m), (0 : M6.Pinned.Vector m) ∉ L → (M6.Pinned.enumerator L P).coeff 0 = 0
def check_2 : Prop := ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), Polynomial.eval 1 (M6.Pinned.enumerator L (M6.Pinned.free m)) = (L.card : ℤ)
