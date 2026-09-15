import M7CanonicalOuter

theorem M7.CanonicalOuter.unit_index : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (e : Bool), ∃ i ∈ M7.CanonicalOuter.indices N, M7.CanonicalOuter.outerRecord i = (⟨u,e,0,0⟩ : M7.Action.Record N) := by
   classical
   intro N inst u e
   let i : M7.CanonicalOuter.OuterIndex N :=
     toLex (⟨(u : ZMod N).val, ZMod.val_lt (u : ZMod N)⟩, e)
   have hv : (((ofLex i).1.val : ℕ) : ZMod N) = (u : ZMod N) := by
     simp [i]
   have hi : IsUnit (((ofLex i).1.val : ℕ) : ZMod N) := by
     rw [hv]
     exact u.isUnit
   refine ⟨i, ?_, ?_⟩
   · exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
   · have hu : M7.CanonicalOuter.outerUnit i = u := by
       unfold M7.CanonicalOuter.outerUnit
       rw [dif_pos hi]
       apply Units.ext
       exact hi.unit_spec.trans hv
     change (⟨M7.CanonicalOuter.outerUnit i, (ofLex i).2, 0, 0⟩ : M7.Action.Record N) = ⟨u, e, 0, 0⟩
     rw [hu]
     rfl

theorem M7.CanonicalOuter.indices_nonempty : ∀ (N : ℕ) [NeZero N], (M7.CanonicalOuter.indices N).Nonempty := by
  change ∀ (N : ℕ) [NeZero N], (M7.CanonicalOuter.indices N).Nonempty
  intro N inst
  obtain ⟨i, hi, _⟩ := M7.CanonicalOuter.unit_index N (1 : (ZMod N)ˣ) false
  exact ⟨i, hi⟩

theorem M7.CanonicalOuter.choices_nonempty : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (M7.CanonicalOuter.choices c).Nonempty := by
  classical
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (M7.CanonicalOuter.choices c).Nonempty
  intro N inst c
  obtain ⟨i, hi⟩ := M7.CanonicalOuter.indices_nonempty N
  unfold M7.CanonicalOuter.choices
  exact ⟨_, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (ofLex (M7.CanonicalOuter.best c)).1 = M7.CanonicalOuter.pairKey (M7.CanonicalOuter.canonical c)
