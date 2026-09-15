import M7ActualFactorizedReady

theorem M7.ActualFactorized.record_coordinates : ∀ (N : ℕ) [NeZero N], Function.Bijective (@M7.ActualFactorized.toRecord N _) := by
  change ∀ (N : ℕ) [NeZero N], Function.Bijective (@M7.ActualFactorized.toRecord N _)
  intro N inst
  have hleft : Function.LeftInverse (@M7.ActualFactorized.fromRecord N _) (@M7.ActualFactorized.toRecord N _) := by
    rintro ⟨⟨u, e⟩, s, t⟩
    rfl
  have hright : Function.RightInverse (@M7.ActualFactorized.fromRecord N _) (@M7.ActualFactorized.toRecord N _) := by
    intro g
    cases g
    rfl
  exact ⟨hleft.injective, hright.surjective⟩

theorem M7.ActualFactorized.numerator_record_count : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ (sector : M7.ActualFactorized.Outer N → Prop) (L R : Finset (ZMod N) → Prop), M7.ActualFactorized.numerator c sector L R = M7.ActualFactorized.recordCount c sector L R := by
  intro N inst c sector L R
  classical
  unfold M7.ActualFactorized.numerator M7.ActualFactorized.recordCount
  rw [M7.Factorized.numerator_record_card]
  refine Finset.card_bij (fun a _ => M7.ActualFactorized.toRecord a) ?_ ?_ ?_
  · rintro ⟨⟨u, e⟩, s, t⟩ ha
    simp only [M7.Factorized.records, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha
  · intro a ha b hb hab
    exact (M7.ActualFactorized.record_coordinates N).1 hab
  · intro g hg
    refine ⟨M7.ActualFactorized.fromRecord g, ?_, ?_⟩
    · simp only [M7.Factorized.records, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      exact hg
    · cases g
      rfl

theorem M7.ActualFactorized.stabilizer_numerator : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.ActualFactorized.stabilizerNumerator c = M7.ActualOrbit.stabilizerCount c := by
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, 0 < M7.ActualFactorized.stabilizerNumerator c
