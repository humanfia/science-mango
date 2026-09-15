import M6Transfer
#check (∀ (R : ℕ) (m : M6.Transfer.Memory (R+1)) (t : M6.Transfer.Bit), M6.Transfer.shift m t 0 = t ∧ ∀ j : Fin R, M6.Transfer.shift m t j.succ = m j.castSucc)
#check (∀ (R N : ℕ) [NeZero N] (h : M6.Transfer.Input N), M6.Transfer.Follows R N (M6.Transfer.memoryAt h) h)
#check (∀ (R N : ℕ) [NeZero N] (p : M6.Transfer.ClosedWalk R N) (i : ZMod N) (j : Fin R), p.val.1 i j = M6.Transfer.labels p (i - (j.val + 1 : ℕ)))
#check (∀ (R N : ℕ) [NeZero N], Function.Bijective (M6.Transfer.labels : M6.Transfer.ClosedWalk R N → M6.Transfer.Input N))
#check (∀ (R N : ℕ) [NeZero N] (K : Type) [CommSemiring K] (W : ZMod N → M6.Transfer.Memory R → M6.Transfer.Bit → K), (∑ p : M6.Transfer.ClosedWalk R N, ∏ i : ZMod N, W i (p.val.1 i) (M6.Transfer.labels p i)) = ∑ h : M6.Transfer.Input N, ∏ i : ZMod N, W i (M6.Transfer.memoryAt h i) (h i))
#check (∀ (R N : ℕ) [NeZero N], Fintype.card (M6.Transfer.ClosedWalk R N) = 2 ^ N)
#check (∀ (R N : ℕ) (c : Fin (R+1) → M6.Transfer.Bit) (h : M6.Transfer.Input N) (i : ZMod N), M6.Transfer.output c (M6.Transfer.memoryAt h i) (h i) = M6.Transfer.cyclicOutput c h i)
