import M7ActualOrbit
#check (∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), 0 < M7.ActualOrbit.stabilizerCount c)
#check (∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ y ∈ M7.ActualOrbit.orbit c, M7.ActualOrbit.fiberCount c y = M7.ActualOrbit.stabilizerCount c)
#check (∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ P : M7.Action.Recipe N → Prop, M7.ActualOrbit.actionCount c P = M7.ActualOrbit.distinctCount c P * M7.ActualOrbit.stabilizerCount c)
#check (∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ P : M7.Action.Recipe N → Prop, M7.ActualOrbit.actionCount c P / M7.ActualOrbit.stabilizerCount c = M7.ActualOrbit.distinctCount c P ∧ M7.ActualOrbit.stabilizerCount c ∣ M7.ActualOrbit.actionCount c P)
#check (∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ (P : M7.Action.Recipe N → Prop) (test : M7.Action.Recipe N → Bool), M7.ActualOrbit.distinctCount c P = M7.ActualOrbit.distinctCount c (fun y => P y ∧ test y = false) + M7.ActualOrbit.distinctCount c (fun y => P y ∧ test y = true))
#check (∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ (P : M7.Action.Recipe N → Prop) (test : M7.Action.Recipe N → Bool), M7.ActualOrbit.actionCount c P = M7.ActualOrbit.actionCount c (fun y => P y ∧ test y = false) + M7.ActualOrbit.actionCount c (fun y => P y ∧ test y = true))
