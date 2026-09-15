import FrozenTarget_2ffd54f74fa72aeb
theorem M7.ActualFactorized.stabilizer_numerator : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.ActualFactorized.stabilizerNumerator c = M7.ActualOrbit.stabilizerCount c
  intro N inst c
  classical
  change M7.ActualFactorized.numerator c (fun _ => True) (fun x => x = c.1) (fun y => y = c.2) = M7.ActualOrbit.stabilizerCount c
  rw [M7.ActualFactorized.numerator_record_count N c]
  unfold M7.ActualFactorized.recordCount M7.ActualOrbit.stabilizerCount M7.ActualOrbit.fullStabilizer
  apply congrArg Finset.card
  apply Finset.ext
  intro g
  simp [Prod.ext_iff, M7.Action.act, M7.ActualFactorized.leftImage, M7.ActualFactorized.rightImage]
