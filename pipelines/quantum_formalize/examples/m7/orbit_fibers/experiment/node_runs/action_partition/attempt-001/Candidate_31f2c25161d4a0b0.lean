import FrozenTarget_31f2c25161d4a0b0
theorem M7.OrbitFibers.action_partition : QuantumHarnessFrozenTarget := by
  classical
  intro G _ _ X _ c P test
  have partition {α : Type} (s : Finset α) (Q : α → Prop) (b : α → Bool) :
      (s.filter Q).card =
        (s.filter (fun a => Q a ∧ b a = false)).card +
        (s.filter (fun a => Q a ∧ b a = true)).card := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      by_cases hQ : Q a <;> cases hb : b a <;>
        simp_all [Finset.filter_insert, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  simpa [M7.OrbitFibers.actionCount] using
    partition (Finset.univ : Finset G) (fun g => P (g • c)) (fun g => test (g • c))
