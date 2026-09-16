import M8Exclusion


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (v : ℕ), 3 ≤ v → N = 2^v → ∀ g : M7.Action.Record N, M8.Cutoff.limit N < M8.Anchor.span (M7.Action.act g (M8.AntipodalFamily.recipe N))
