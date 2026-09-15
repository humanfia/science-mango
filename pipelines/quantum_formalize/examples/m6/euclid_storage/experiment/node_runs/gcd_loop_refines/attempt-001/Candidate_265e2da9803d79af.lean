import FrozenTarget_265e2da9803d79af
theorem M6.EuclidStorage.gcd_loop_refines : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro fuel
  induction fuel with
  | zero =>
      intro s c e t hw
      simp [M6.EuclidStorage.gcdLoop, M6.Euclid.euclidAux,
        M6.EuclidStorage.toRun, M6.EuclidStorage.offset, hw]
  | succ fuel ih =>
      intro s c e t hw
      by_cases hq : s.q = 0
      · simp [M6.EuclidStorage.gcdLoop, M6.Euclid.euclidAux,
          M6.EuclidStorage.toRun, M6.EuclidStorage.offset, hq, hw]
      · have hr := fun (c t : ℕ) =>
          M6.EuclidStorage.rem_loop_refines (M6.Euclid.rank s.p)
            (⟨0, s.q, s.p, s.saved⟩ : M6.EuclidStorage.Slots) c t
        dsimp only at hr
        simp only [M6.EuclidStorage.gcdLoop, M6.Euclid.euclidAux,
          hq, if_false]
        simp only [M6.Euclid.remainder, hr, ih]
        simp [M6.EuclidStorage.offset, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm]
