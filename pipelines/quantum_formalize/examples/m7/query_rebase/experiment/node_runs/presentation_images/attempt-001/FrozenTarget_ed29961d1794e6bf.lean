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

theorem M7.QueryRebase.reparameterization : ∀ (H N : ℕ) [NeZero N] (moves : Fin H → M7.Action.Record N), (∀ x : M7.GlobalQuery.Index H N, M7.QueryRebase.undo moves (M7.QueryRebase.reparam moves x) = x) ∧ (∀ x : M7.GlobalQuery.Index H N, M7.QueryRebase.reparam moves (M7.QueryRebase.undo moves x) = x) ∧ Function.Bijective (M7.QueryRebase.reparam moves) := by
  intro H N inst moves
  have hundo : ∀ x : M7.GlobalQuery.Index H N,
      M7.QueryRebase.undo moves (M7.QueryRebase.reparam moves x) = x := by
    rintro ⟨i, g⟩
    simp [M7.QueryRebase.undo, M7.QueryRebase.reparam,
      M7.Action.associative, M7.Action.right_inverse,
      M7.Action.left_inverse, M7.Action.right_identity]
  have hreparam : ∀ x : M7.GlobalQuery.Index H N,
      M7.QueryRebase.reparam moves (M7.QueryRebase.undo moves x) = x := by
    rintro ⟨i, g⟩
    simp [M7.QueryRebase.undo, M7.QueryRebase.reparam,
      M7.Action.associative, M7.Action.right_inverse,
      M7.Action.left_inverse, M7.Action.right_identity]
  refine ⟨hundo, hreparam, ?_, ?_⟩
  · intro x y h
    calc
      x = M7.QueryRebase.undo moves (M7.QueryRebase.reparam moves x) := (hundo x).symm
      _ = M7.QueryRebase.undo moves (M7.QueryRebase.reparam moves y) := congrArg (M7.QueryRebase.undo moves) h
      _ = y := hundo y
  · intro y
    exact ⟨M7.QueryRebase.undo moves y, hreparam y⟩

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

theorem M7.QueryRebase.feasible_objective : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (moves : Fin H → M7.Action.Record N) (x : M7.GlobalQuery.Index H N), (M7.GlobalQuery.feasible q (M7.QueryRebase.rebase bases moves) x ↔ M7.GlobalQuery.feasible q bases (M7.QueryRebase.reparam moves x)) ∧ M7.GlobalQuery.objective q (M7.QueryRebase.rebase bases moves) x = M7.GlobalQuery.objective q bases (M7.QueryRebase.reparam moves x) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (moves : Fin H → M7.Action.Record N) (x : M7.GlobalQuery.Index H N), (M7.GlobalQuery.feasible q (M7.QueryRebase.rebase bases moves) x ↔ M7.GlobalQuery.feasible q bases (M7.QueryRebase.reparam moves x)) ∧ M7.GlobalQuery.objective q (M7.QueryRebase.rebase bases moves) x = M7.GlobalQuery.objective q bases (M7.QueryRebase.reparam moves x)
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases moves x
  constructor
  · unfold M7.GlobalQuery.feasible
    rw [M7.QueryRebase.realize_reparam]
    simp only [M7.DefaultQuery.feasible, M7.QueryRebase.rebase,
      M7.QueryRebase.reparam, M7.QueryRebase.sector_base]
  · unfold M7.GlobalQuery.objective
    rw [M7.QueryRebase.realize_reparam]

theorem M7.QueryRebase.winners_reparam : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (moves : Fin H → M7.Action.Record N) (x : M7.GlobalQuery.Index H N), x ∈ M7.GlobalQuery.winners q (M7.QueryRebase.rebase bases moves) ↔ (M7.QueryRebase.reparam moves x) ∈ M7.GlobalQuery.winners q bases := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (moves : Fin H → M7.Action.Record N) (x : M7.GlobalQuery.Index H N), x ∈ M7.GlobalQuery.winners q (M7.QueryRebase.rebase bases moves) ↔ (M7.QueryRebase.reparam moves x) ∈ M7.GlobalQuery.winners q bases
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases moves x
  rw [(M7.GlobalQuery.winners_exact H N q (M7.QueryRebase.rebase bases moves)).1 x,
    (M7.GlobalQuery.winners_exact H N q bases).1 (M7.QueryRebase.reparam moves x)]
  have hx := M7.QueryRebase.feasible_objective H N q bases moves x
  constructor
  · rintro ⟨hfx, hopt⟩
    refine ⟨hx.1.mp hfx, ?_⟩
    intro y hfy
    obtain ⟨z, rfl⟩ := (M7.QueryRebase.reparameterization H N moves).2.2.2 y
    have hz := M7.QueryRebase.feasible_objective H N q bases moves z
    have h := hopt z (hz.1.mpr hfy)
    simpa only [hz.2, hx.2] using h
  · rintro ⟨hfx, hopt⟩
    refine ⟨hx.1.mpr hfx, ?_⟩
    intro y hfy
    have hy := M7.QueryRebase.feasible_objective H N q bases moves y
    rw [hy.2, hx.2]
    exact hopt (M7.QueryRebase.reparam moves y) (hy.1.mp hfy)

theorem M7.QueryRebase.winner_images : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (moves : Fin H → M7.Action.Record N) (placed : M7.Action.Recipe N), ((∃ x ∈ M7.GlobalQuery.winners q (M7.QueryRebase.rebase bases moves), M7.GlobalQuery.realize (M7.QueryRebase.rebase bases moves) x = placed) ↔ ∃ x ∈ M7.GlobalQuery.winners q bases, M7.GlobalQuery.realize bases x = placed) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (moves : Fin H → M7.Action.Record N) (placed : M7.Action.Recipe N), ((∃ x ∈ M7.GlobalQuery.winners q (M7.QueryRebase.rebase bases moves), M7.GlobalQuery.realize (M7.QueryRebase.rebase bases moves) x = placed) ↔ ∃ x ∈ M7.GlobalQuery.winners q bases, M7.GlobalQuery.realize bases x = placed)
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases moves placed
  constructor
  · rintro ⟨x, hx, hp⟩
    refine ⟨M7.QueryRebase.reparam moves x,
      (M7.QueryRebase.winners_reparam H N q bases moves x).mp hx, ?_⟩
    exact (M7.QueryRebase.realize_reparam H N bases moves x).symm.trans hp
  · rintro ⟨x, hx, hp⟩
    have hu := (M7.QueryRebase.reparameterization H N moves).2.1 x
    refine ⟨M7.QueryRebase.undo moves x, ?_, ?_⟩
    · apply (M7.QueryRebase.winners_reparam H N q bases moves
        (M7.QueryRebase.undo moves x)).mpr
      simpa only [hu] using hx
    · rw [M7.QueryRebase.realize_reparam H N bases moves
        (M7.QueryRebase.undo moves x), hu]
      exact hp
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (moves : Fin H → M7.Action.Record N) (placed : M7.Action.Recipe N), ((∃ x : M7.GlobalQuery.Index H N, M7.GlobalQuery.present q (M7.QueryRebase.rebase bases moves) x ∧ M7.GlobalQuery.realize (M7.QueryRebase.rebase bases moves) x = placed) ↔ ∃ x : M7.GlobalQuery.Index H N, M7.GlobalQuery.present q bases x ∧ M7.GlobalQuery.realize bases x = placed)
