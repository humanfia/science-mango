import M7Connectivity


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : Finset (ZMod N)) (u : (ZMod N)ˣ) (s : ZMod N), M7.Connectivity.differences (A.image (M7.Action.affine u s)) = (fun x : ZMod N => (u : ZMod N)*x) '' M7.Connectivity.differences A
