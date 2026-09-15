import FrozenTarget_eeebedc69f802bb1
theorem M5.ArithmeticSubset.character_sign : QuantumHarnessFrozenTarget := by
  classical
  intro P hP lam z
  have hpow {R : Type*} [CommRing R] (n : ℕ) :
      (-1 : R) ^ n = 1 ∨ (-1 : R) ^ n = -1 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rcases ih with h | h <;> simp [pow_succ, h]
  have hprod {ι R : Type*} [CommRing R] (f : ι → R) :
      ∀ s : Finset ι, (∀ i ∈ s, f i = 1 ∨ f i = -1) →
        (∏ i ∈ s, f i) = 1 ∨ (∏ i ∈ s, f i) = -1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        intro hf
        have ha' := hf a (Finset.mem_insert_self a s)
        have hs := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        rw [Finset.prod_insert ha]
        rcases ha' with ha' | ha' <;>
          rcases hs with hs | hs <;> simp [ha', hs]
  refine hprod _ _ ?_
  intro i hi
  exact hpow _
