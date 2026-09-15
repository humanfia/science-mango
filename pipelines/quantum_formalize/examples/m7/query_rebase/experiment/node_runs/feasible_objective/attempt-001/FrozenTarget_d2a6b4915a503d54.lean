import M7ActionAccepted
import M7GlobalQueryAccepted
import M7QueryRebase

theorem M7.QueryRebase.realize_reparam : ∀ (H N : ℕ) [NeZero N] (bases : M7.GlobalQuery.Family H N) (moves : Fin H → M7.Action.Record N) (x : M7.GlobalQuery.Index H N), M7.GlobalQuery.realize (M7.QueryRebase.rebase bases moves) x = M7.GlobalQuery.realize bases (M7.QueryRebase.reparam moves x) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (H N : ℕ) [NeZero N] (bases : M7.GlobalQuery.Family H N) (moves : Fin H → M7.Action.Record N) (x : M7.GlobalQuery.Index H N), M7.GlobalQuery.realize (M7.QueryRebase.rebase bases moves) x = M7.GlobalQuery.realize bases (M7.QueryRebase.reparam moves x)
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro H N inst bases moves x
  simpa only [M7.QueryRebase.rebase, M7.QueryRebase.reparam, M7.GlobalQuery.realize] using
    (M7.Action.act_compose N x.2 (moves x.1) (bases x.1)).symm

theorem M7.QueryRebase.sector_base : ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base placed : M7.Action.Recipe N) (g : M7.Action.Record N), (M7.DefaultQuery.sectorTest q (M7.Action.act g base) placed ↔ M7.DefaultQuery.sectorTest q base placed) := by
  intro N inst q base placed g
  cases hmode : q.sectorMode <;> simp only [M7.DefaultQuery.sectorTest, hmode]
  all_goals
    first
    | exact Iff.rfl
    | constructor
      · rintro ⟨h, hh⟩
        refine ⟨M7.Action.compose h g, ?_⟩
        simpa only [M7.Action.act_compose] using hh
      · rintro ⟨h, hh⟩
        refine ⟨M7.Action.compose h (M7.Action.inverse g), ?_⟩
        simpa only [M7.Action.act_compose, M7.Action.act_inverse] using hh
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (moves : Fin H → M7.Action.Record N) (x : M7.GlobalQuery.Index H N), (M7.GlobalQuery.feasible q (M7.QueryRebase.rebase bases moves) x ↔ M7.GlobalQuery.feasible q bases (M7.QueryRebase.reparam moves x)) ∧ M7.GlobalQuery.objective q (M7.QueryRebase.rebase bases moves) x = M7.GlobalQuery.objective q bases (M7.QueryRebase.reparam moves x)
