import M7RecoveryPrefix
import M7PrefixBitsAccepted
import M7ResiduePrefixAccepted

noncomputable def M7.RecoveryPrefixTarget.completed_partition : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (p : List Bool), p.length < M7.PrefixBits.depth N → M7.RecoveryPrefix.completed N w E p = M7.RecoveryPrefix.completed N w E (p ++ [false]) ∪ M7.RecoveryPrefix.completed N w E (p ++ [true]) ∧ Disjoint (M7.RecoveryPrefix.completed N w E (p ++ [false])) (M7.RecoveryPrefix.completed N w E (p ++ [true]))

noncomputable def M7.RecoveryPrefixTarget.completed_subroot : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (p : List Bool), M7.RecoveryPrefix.completed N w E p ⊆ M7.RecoveryPrefix.completed N w E []

noncomputable def M7.RecoveryPrefixTarget.leaf_singleton : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (p : List Bool), p.length = M7.PrefixBits.depth N → M7.RecoveryPrefix.completed N w E p ⊆ {M7.RecoveryPrefix.leaf N p}

