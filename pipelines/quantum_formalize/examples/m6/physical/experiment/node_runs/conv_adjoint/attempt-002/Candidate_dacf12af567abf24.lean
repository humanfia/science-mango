import FrozenTarget_dacf12af567abf24
theorem M6.Physical.conv_adjoint : QuantumHarnessFrozenTarget := by
  intro N inst a h u
  classical
  change (∑ i : ZMod N, (∑ r : ZMod N, a r * h (-i - r)) * u i) =
    ∑ j : ZMod N, h (-j) * (∑ r : ZMod N, a r * u (j - r))
  simp only [Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ i : ZMod N, ∑ r : ZMod N, (a r * h (-i - r)) * u i) =
        ∑ r : ZMod N, ∑ i : ZMod N, (a r * h (-i - r)) * u i := Finset.sum_comm
    _ = ∑ r : ZMod N, ∑ j : ZMod N, h (-j) * (a r * u (j - r)) := by
      apply Finset.sum_congr rfl
      intro r hr
      refine Finset.sum_bij (fun i _ => i + r) ?_ ?_ ?_ ?_
      · intro i hi
        exact Finset.mem_univ _
      · intro i hi j hj hij
        exact add_right_cancel hij
      · intro j hj
        exact ⟨j - r, Finset.mem_univ _, by simp⟩
      · intro i hi
        simp [neg_add, sub_eq_add_neg, mul_assoc, mul_comm, mul_left_comm]
    _ = ∑ j : ZMod N, ∑ r : ZMod N, h (-j) * (a r * u (j - r)) := Finset.sum_comm
