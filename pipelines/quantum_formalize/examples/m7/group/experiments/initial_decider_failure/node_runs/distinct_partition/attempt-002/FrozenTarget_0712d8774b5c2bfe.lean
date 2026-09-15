import M7ActualOrbit


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ (P : M7.Action.Recipe N → Prop) (test : M7.Action.Recipe N → Bool), M7.ActualOrbit.distinctCount c P = M7.ActualOrbit.distinctCount c (fun y => P y ∧ test y = false) + M7.ActualOrbit.distinctCount c (fun y => P y ∧ test y = true)
