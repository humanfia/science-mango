import M7ActionAccepted

namespace M7.Action
instance {N : ℕ} [NeZero N] : Mul (Record N) := ⟨compose⟩
instance {N : ℕ} [NeZero N] : One (Record N) := ⟨identity N⟩
instance {N : ℕ} [NeZero N] : Inv (Record N) := ⟨inverse⟩
instance {N : ℕ} [NeZero N] : Group (Record N) :=
  Group.ofLeftAxioms (associative N) (left_identity N) (left_inverse N)
instance {N : ℕ} [NeZero N] : SMul (Record N) (Recipe N) := ⟨act⟩
instance {N : ℕ} [NeZero N] : MulAction (Record N) (Recipe N) where
  one_smul := act_identity N
  mul_smul := act_compose N
end M7.Action
