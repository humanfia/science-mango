import M5TupleCharacter

theorem M5.TupleCharacter.tuple_character_count : ∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z * ∑ t : Fin k → Fin n, M5.Character.value lam (M5.TupleCharacter.vectorSum f t)) = (2 : ℤ) ^ D * (M5.TupleCharacter.count k f z : ℤ) := by
  classical
  intro D n k f z
  have hself : z + z = 0 := by
    ext i
    exact (show ∀ a : ZMod 2, a + a = 0 by decide) (z i)
  have hz : ∀ u : M5.Character.BinaryVector D, z + u = 0 ↔ u = z := by
    intro u
    constructor
    · intro h
      apply add_left_cancel (a := z)
      exact h.trans hself.symm
    · rintro rfl
      exact hself
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← M5.Character.character_add, M5.Character.character_orthogonality, hz]
  simp [← Finset.sum_filter, M5.TupleCharacter.count, mul_comm]

theorem M5.TupleCharacter.value_zero : ∀ (D : ℕ) (lam : M5.Character.BinaryVector D), M5.Character.value lam 0 = 1 := by
  change ∀ (D : ℕ) (lam : M5.Character.BinaryVector D), M5.Character.value lam 0 = 1
  intro D lam
  simp [M5.Character.value, M5.Character.bitSign]

theorem M5.TupleCharacter.character_tuple_sum : ∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (t : Fin k → Fin n) (lam : M5.Character.BinaryVector D), M5.Character.value lam (M5.TupleCharacter.vectorSum f t) = ∏ i : Fin k, M5.Character.value lam (f (t i)) := by
  change ∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (t : Fin k → Fin n) (lam : M5.Character.BinaryVector D), M5.Character.value lam (M5.TupleCharacter.vectorSum f t) = ∏ i : Fin k, M5.Character.value lam (f (t i))
  intro D n k f t lam
  classical
  have h : ∀ s : Finset (Fin k), M5.Character.value lam (∑ i ∈ s, f (t i)) = ∏ i ∈ s, M5.Character.value lam (f (t i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty, Finset.prod_empty] using M5.TupleCharacter.value_zero D lam
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha]
        first
        | rw [M5.TupleCharacter.character_add]
        | rw [M5.Character.character_add]
        rw [ih]
  simpa [M5.TupleCharacter.vectorSum, Finset.sum_apply] using h Finset.univ

theorem M5.TupleCharacter.tuple_character_power : ∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), (∑ t : Fin k → Fin n, M5.Character.value lam (M5.TupleCharacter.vectorSum f t)) = (∑ a : Fin n, M5.Character.value lam (f a)) ^ k := by
  change ∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), (∑ t : Fin k → Fin n, M5.Character.value lam (M5.TupleCharacter.vectorSum f t)) = (∑ a : Fin n, M5.Character.value lam (f a)) ^ k
  intro D n k f lam
  classical
  simp only [M5.TupleCharacter.character_tuple_sum]
  exact (Fintype.sum_pow (fun a : Fin n => M5.Character.value lam (f a)) k).symm
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z * (∑ a : Fin n, M5.Character.value lam (f a)) ^ k) = (2 : ℤ) ^ D * (M5.TupleCharacter.count k f z : ℤ)
