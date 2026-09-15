import M5Character
#check (∀ a b c : ZMod 2, M5.Character.bitSign a (b + c) = M5.Character.bitSign a b * M5.Character.bitSign a c)
#check (∀ b : ZMod 2, (∑ a : ZMod 2, M5.Character.bitSign a b) = if b = 0 then 2 else 0)
#check (∀ (D : ℕ) (lam z u : M5.Character.BinaryVector D), M5.Character.value lam (z + u) = M5.Character.value lam z * M5.Character.value lam u)
#check (∀ (D : ℕ) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z) = if z = 0 then (2 : ℤ) ^ D else 0)
#check (∀ (D n : ℕ) (f : Fin n → M5.Character.BinaryVector D) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z * ∑ u : Fin n, M5.Character.value lam (f u)) = (2 : ℤ) ^ D * ((Finset.univ.filter (fun u : Fin n => f u = z)).card : ℤ))
