import M7QueryRebase
import M7ActionAccepted
import M7GlobalQueryAccepted

noncomputable def M7.QueryRebaseTarget.reparameterization : Prop :=
  ∀ (H N : ℕ) [NeZero N] (moves : Fin H → M7.Action.Record N), (∀ x : M7.GlobalQuery.Index H N, M7.QueryRebase.undo moves (M7.QueryRebase.reparam moves x) = x) ∧ (∀ x : M7.GlobalQuery.Index H N, M7.QueryRebase.reparam moves (M7.QueryRebase.undo moves x) = x) ∧ Function.Bijective (M7.QueryRebase.reparam moves)

#check M7.QueryRebaseTarget.reparameterization

noncomputable def M7.QueryRebaseTarget.realize_reparam : Prop :=
  ∀ (H N : ℕ) [NeZero N] (bases : M7.GlobalQuery.Family H N) (moves : Fin H → M7.Action.Record N) (x : M7.GlobalQuery.Index H N), M7.GlobalQuery.realize (M7.QueryRebase.rebase bases moves) x = M7.GlobalQuery.realize bases (M7.QueryRebase.reparam moves x)

#check M7.QueryRebaseTarget.realize_reparam

noncomputable def M7.QueryRebaseTarget.sector_base : Prop :=
  ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base placed : M7.Action.Recipe N) (g : M7.Action.Record N), (M7.DefaultQuery.sectorTest q (M7.Action.act g base) placed ↔ M7.DefaultQuery.sectorTest q base placed)

#check M7.QueryRebaseTarget.sector_base

noncomputable def M7.QueryRebaseTarget.feasible_objective : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (moves : Fin H → M7.Action.Record N) (x : M7.GlobalQuery.Index H N), (M7.GlobalQuery.feasible q (M7.QueryRebase.rebase bases moves) x ↔ M7.GlobalQuery.feasible q bases (M7.QueryRebase.reparam moves x)) ∧ M7.GlobalQuery.objective q (M7.QueryRebase.rebase bases moves) x = M7.GlobalQuery.objective q bases (M7.QueryRebase.reparam moves x)

#check M7.QueryRebaseTarget.feasible_objective

noncomputable def M7.QueryRebaseTarget.winners_reparam : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (moves : Fin H → M7.Action.Record N) (x : M7.GlobalQuery.Index H N), x ∈ M7.GlobalQuery.winners q (M7.QueryRebase.rebase bases moves) ↔ (M7.QueryRebase.reparam moves x) ∈ M7.GlobalQuery.winners q bases

#check M7.QueryRebaseTarget.winners_reparam

noncomputable def M7.QueryRebaseTarget.winning_classes : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (moves : Fin H → M7.Action.Record N), M7.GlobalQuery.winningClasses q (M7.QueryRebase.rebase bases moves) = M7.GlobalQuery.winningClasses q bases

#check M7.QueryRebaseTarget.winning_classes

noncomputable def M7.QueryRebaseTarget.winner_images : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (moves : Fin H → M7.Action.Record N) (placed : M7.Action.Recipe N), ((∃ x ∈ M7.GlobalQuery.winners q (M7.QueryRebase.rebase bases moves), M7.GlobalQuery.realize (M7.QueryRebase.rebase bases moves) x = placed) ↔ ∃ x ∈ M7.GlobalQuery.winners q bases, M7.GlobalQuery.realize bases x = placed)

#check M7.QueryRebaseTarget.winner_images

noncomputable def M7.QueryRebaseTarget.presentation_images : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (moves : Fin H → M7.Action.Record N) (placed : M7.Action.Recipe N), ((∃ x : M7.GlobalQuery.Index H N, M7.GlobalQuery.present q (M7.QueryRebase.rebase bases moves) x ∧ M7.GlobalQuery.realize (M7.QueryRebase.rebase bases moves) x = placed) ↔ ∃ x : M7.GlobalQuery.Index H N, M7.GlobalQuery.present q bases x ∧ M7.GlobalQuery.realize bases x = placed)

#check M7.QueryRebaseTarget.presentation_images

