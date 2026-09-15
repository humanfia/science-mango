import FrozenTarget_11f1d0e1c803108c
theorem M7.OrbitFibers.action_partition : QuantumHarnessFrozenTarget := by
  classical
  intro G _ _ X _ c P test
  have partition (s : Finset G) (p : G → Prop) (b : G → Bool) :
      (s.filter p).card =
        (s.filter (fun g => p g ∧ b g = false)).card +
        (s.filter (fun g => p g ∧ b g = true)).card := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        by_cases hp : p a <;> cases hb : b a <;>
          simp_all [Finset.filter_insert, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  unfold M7.OrbitFibers.actionCount
  exact partition Finset.univ (fun g => P (g • c)) (fun g => test (g • c))
