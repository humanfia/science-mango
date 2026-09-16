import M8AnchorAccepted

namespace M8.ExclusionGeometry
def Antipodal {N : ℕ} (h : ℕ) (A : Finset (ZMod N)) : Prop :=
  ∃ x : ZMod N, x ∈ A ∧ x + (h : ZMod N) ∈ A
end M8.ExclusionGeometry
