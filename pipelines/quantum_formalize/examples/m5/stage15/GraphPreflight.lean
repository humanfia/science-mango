import M5TupleCharacter
#check (∀ (D : ℕ) (lam : M5.Character.BinaryVector D), M5.Character.value lam 0 = 1)
#check (∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (t : Fin k → Fin n) (lam : M5.Character.BinaryVector D), M5.Character.value lam (M5.TupleCharacter.vectorSum f t) = ∏ i : Fin k, M5.Character.value lam (f (t i)))
#check (∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), (∑ t : Fin k → Fin n, M5.Character.value lam (M5.TupleCharacter.vectorSum f t)) = (∑ a : Fin n, M5.Character.value lam (f a)) ^ k)
#check (∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z * ∑ t : Fin k → Fin n, M5.Character.value lam (M5.TupleCharacter.vectorSum f t)) = (2 : ℤ) ^ D * (M5.TupleCharacter.count k f z : ℤ))
#check (∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z * (∑ a : Fin n, M5.Character.value lam (f a)) ^ k) = (2 : ℤ) ^ D * (M5.TupleCharacter.count k f z : ℤ))
