import M6Transfer

namespace M6.Transfer

noncomputable def edgeMatrix {R : ℕ} {K : Type} [CommSemiring K]
    (W : Memory R → Bit → K) : Matrix (Memory R) (Memory R) K := by
  classical
  exact fun m n => ∑ t : Bit, if shift m t = n then W m t else 0

noncomputable def propagate {R : ℕ} {K : Type} [CommSemiring K]
    (W : Memory R → Bit → K) (v : Memory R → K) : Memory R → K := by
  classical
  exact fun n => ∑ m : Memory R, ∑ t : Bit,
    if shift m t = n then v m * W m t else 0

noncomputable def layers {R : ℕ} {K : Type} [CommSemiring K]
    (W : ℕ → Memory R → Bit → K) (start : Memory R) : ℕ → Memory R → K
  | 0 => fun n => if n = start then 1 else 0
  | k+1 => propagate (W k) (layers W start k)

noncomputable def matrixProduct {S K : Type} [Fintype S] [DecidableEq S] [CommSemiring K]
    (A : ℕ → Matrix S S K) : ℕ → Matrix S S K
  | 0 => 1
  | k+1 => matrixProduct A k * A k

noncomputable def arrayTrace {R : ℕ} {K : Type} [CommSemiring K]
    (W : ℕ → Memory R → Bit → K) (N : ℕ) : K :=
  ∑ start : Memory R, layers W start N start

end M6.Transfer
