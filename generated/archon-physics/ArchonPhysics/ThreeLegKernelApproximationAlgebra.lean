import ArchonPhysics.ComplexRegularizedMarkedLegBridge

/-!
# Quantitative three-leg projected-kernel approximation

This module controls three-leg contractions by entrywise replacement errors
and Frobenius norms.  An orthonormal edge-mode frame turns a uniform bound on
the effective spectral weight `lambda * weight` into an entrywise bound and
an `O(sqrt(card))` Frobenius bound, hence an `N`-uniform estimate after volume
normalization.  These are deterministic finite-dimensional statements.
-/

open scoped BigOperators

namespace ArchonPhysics.ThreeLegKernelApproximationAlgebra

open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedInteractionSpectralFactorization

noncomputable section

variable {left right : Type*} [Fintype left] [Fintype right]

def pairL1 (A B : left → right → Complex) : Real :=
  ∑ i, ∑ j, ‖A i j‖ * ‖B i j‖

def frobeniusSq (A : left → right → Complex) : Real :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

def tripleSum (A B C : left → right → Complex) : Complex :=
  ∑ i, ∑ j, A i j * B i j * C i j

theorem pairL1_le_sqrt_frobeniusSq_mul_sqrt_frobeniusSq (A B : left → right → Complex) :
    pairL1 A B ≤ Real.sqrt (frobeniusSq A) * Real.sqrt (frobeniusSq B) := by
  unfold pairL1 frobeniusSq
  calc
    (∑ i, ∑ j, ‖A i j‖ * ‖B i j‖) ≤
        ∑ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) *
          Real.sqrt (∑ j, ‖B i j‖ ^ 2) := by
      exact Finset.sum_le_sum fun i _hi ↦
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun j ↦ ‖A i j‖) (fun j ↦ ‖B i j‖)
    _ ≤ Real.sqrt (∑ i, (Real.sqrt (∑ j, ‖A i j‖ ^ 2)) ^ 2) *
          Real.sqrt (∑ i, (Real.sqrt (∑ j, ‖B i j‖ ^ 2)) ^ 2) := by
      exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ = Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) *
          Real.sqrt (∑ i, ∑ j, ‖B i j‖ ^ 2) := by
      congr 2 <;>
        apply Finset.sum_congr rfl <;>
        intro i hi <;>
        rw [Real.sq_sqrt] <;>
        exact Finset.sum_nonneg fun j hj ↦ sq_nonneg _

theorem norm_tripleSum_sub_le_pairL1
    (A B C A' B' C' : left → right → Complex)
    (epsilonA epsilonB epsilonC : Real)
    (hA : ∀ i j, ‖A i j - A' i j‖ ≤ epsilonA)
    (hB : ∀ i j, ‖B i j - B' i j‖ ≤ epsilonB)
    (hC : ∀ i j, ‖C i j - C' i j‖ ≤ epsilonC) :
    ‖tripleSum A B C - tripleSum A' B' C'‖ ≤
      epsilonA * pairL1 B C + epsilonB * pairL1 A' C +
        epsilonC * pairL1 A' B' := by
  have hpoint (i : left) (j : right) :
      ‖A i j * B i j * C i j - A' i j * B' i j * C' i j‖ ≤
        epsilonA * (‖B i j‖ * ‖C i j‖) +
          epsilonB * (‖A' i j‖ * ‖C i j‖) +
            epsilonC * (‖A' i j‖ * ‖B' i j‖) := by
    calc
      ‖A i j * B i j * C i j - A' i j * B' i j * C' i j‖ =
          ‖(A i j - A' i j) * B i j * C i j +
            A' i j * (B i j - B' i j) * C i j +
              A' i j * B' i j * (C i j - C' i j)‖ := by
        congr 1
        ring
      _ ≤ ‖(A i j - A' i j) * B i j * C i j‖ +
          ‖A' i j * (B i j - B' i j) * C i j‖ +
            ‖A' i j * B' i j * (C i j - C' i j)‖ := by
        calc
          ‖(A i j - A' i j) * B i j * C i j +
              A' i j * (B i j - B' i j) * C i j +
                A' i j * B' i j * (C i j - C' i j)‖ ≤
              ‖(A i j - A' i j) * B i j * C i j +
                A' i j * (B i j - B' i j) * C i j‖ +
                  ‖A' i j * B' i j * (C i j - C' i j)‖ :=
            norm_add_le _ _
          _ ≤ (‖(A i j - A' i j) * B i j * C i j‖ +
                ‖A' i j * (B i j - B' i j) * C i j‖) +
                  ‖A' i j * B' i j * (C i j - C' i j)‖ :=
            add_le_add (norm_add_le _ _) le_rfl
      _ ≤ epsilonA * (‖B i j‖ * ‖C i j‖) +
          epsilonB * (‖A' i j‖ * ‖C i j‖) +
            epsilonC * (‖A' i j‖ * ‖B' i j‖) := by
        simp only [norm_mul]
        apply add_le_add
        · apply add_le_add
          · calc
              ‖A i j - A' i j‖ * ‖B i j‖ * ‖C i j‖ ≤
                  epsilonA * ‖B i j‖ * ‖C i j‖ := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _))
                  (norm_nonneg _)
              _ = epsilonA * (‖B i j‖ * ‖C i j‖) := by ring
          · calc
              ‖A' i j‖ * ‖B i j - B' i j‖ * ‖C i j‖ ≤
                  ‖A' i j‖ * epsilonB * ‖C i j‖ := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (hB i j) (norm_nonneg _))
                  (norm_nonneg _)
              _ = epsilonB * (‖A' i j‖ * ‖C i j‖) := by ring
        · calc
            ‖A' i j‖ * ‖B' i j‖ * ‖C i j - C' i j‖ ≤
                ‖A' i j‖ * ‖B' i j‖ * epsilonC := by
              exact mul_le_mul_of_nonneg_left (hC i j)
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            _ = epsilonC * (‖A' i j‖ * ‖B' i j‖) := by ring
  rw [tripleSum, tripleSum, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ i, ∑ j, (A i j * B i j * C i j -
        A' i j * B' i j * C' i j)‖ ≤
        ∑ i, ∑ j, ‖A i j * B i j * C i j -
          A' i j * B' i j * C' i j‖ := by
      exact norm_sum_le _ _ |>.trans (Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j,
        (epsilonA * (‖B i j‖ * ‖C i j‖) +
          epsilonB * (‖A' i j‖ * ‖C i j‖) +
            epsilonC * (‖A' i j‖ * ‖B' i j‖)) := by
      exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hpoint i j
    _ = epsilonA * pairL1 B C + epsilonB * pairL1 A' C +
        epsilonC * pairL1 A' B' := by
      simp only [pairL1, Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]

/-- Frobenius version of the three-leg replacement estimate. -/
theorem norm_tripleSum_sub_le_frobenius
    (A B C A' B' C' : left → right → Complex)
    (epsilonA epsilonB epsilonC : Real)
    (hepsilonA : 0 ≤ epsilonA) (hepsilonB : 0 ≤ epsilonB)
    (hepsilonC : 0 ≤ epsilonC)
    (hA : ∀ i j, ‖A i j - A' i j‖ ≤ epsilonA)
    (hB : ∀ i j, ‖B i j - B' i j‖ ≤ epsilonB)
    (hC : ∀ i j, ‖C i j - C' i j‖ ≤ epsilonC) :
    ‖tripleSum A B C - tripleSum A' B' C'‖ ≤
      epsilonA *
          (Real.sqrt (frobeniusSq B) * Real.sqrt (frobeniusSq C)) +
        epsilonB *
          (Real.sqrt (frobeniusSq A') * Real.sqrt (frobeniusSq C)) +
        epsilonC *
          (Real.sqrt (frobeniusSq A') * Real.sqrt (frobeniusSq B')) := by
  refine (norm_tripleSum_sub_le_pairL1 A B C A' B' C'
    epsilonA epsilonB epsilonC hA hB hC).trans ?_
  exact add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_left
        (pairL1_le_sqrt_frobeniusSq_mul_sqrt_frobeniusSq B C) hepsilonA)
      (mul_le_mul_of_nonneg_left
        (pairL1_le_sqrt_frobeniusSq_mul_sqrt_frobeniusSq A' C) hepsilonB))
    (mul_le_mul_of_nonneg_left
      (pairL1_le_sqrt_frobeniusSq_mul_sqrt_frobeniusSq A' B') hepsilonC)

theorem norm_tripleSum_le_frobenius
    (A B C : left → right → Complex) (boundA : Real)
    (hboundA : 0 ≤ boundA) (hA : ∀ i j, ‖A i j‖ ≤ boundA) :
    ‖tripleSum A B C‖ ≤
      boundA * (Real.sqrt (frobeniusSq B) * Real.sqrt (frobeniusSq C)) := by
  calc
    ‖tripleSum A B C‖ ≤ boundA * pairL1 B C := by
      unfold tripleSum pairL1
      calc
        ‖∑ i, ∑ j, A i j * B i j * C i j‖ ≤
            ∑ i, ∑ j, ‖A i j * B i j * C i j‖ := by
          exact (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun i _hi ↦ norm_sum_le _ _)
        _ ≤ ∑ i, ∑ j, boundA * (‖B i j‖ * ‖C i j‖) := by
          apply Finset.sum_le_sum
          intro i _hi
          apply Finset.sum_le_sum
          intro j _hj
          simp only [norm_mul]
          calc
            ‖A i j‖ * ‖B i j‖ * ‖C i j‖ ≤
                boundA * ‖B i j‖ * ‖C i j‖ := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _))
                (norm_nonneg _)
            _ = boundA * (‖B i j‖ * ‖C i j‖) := by ring
        _ = boundA * (∑ i, ∑ j, ‖B i j‖ * ‖C i j‖) := by
          simp_rw [Finset.mul_sum]
    _ ≤ boundA *
        (Real.sqrt (frobeniusSq B) * Real.sqrt (frobeniusSq C)) := by
      gcongr
      exact pairL1_le_sqrt_frobeniusSq_mul_sqrt_frobeniusSq B C

theorem norm_tripleSum_div_volume_le
    (A B C : left → right → Complex)
    (volume boundA boundB boundC : Real)
    (hvolume : 0 < volume)
    (hboundA : 0 ≤ boundA) (hboundB : 0 ≤ boundB)
    (hA : ∀ i j, ‖A i j‖ ≤ boundA)
    (hB : Real.sqrt (frobeniusSq B) ≤ Real.sqrt volume * boundB)
    (hC : Real.sqrt (frobeniusSq C) ≤ Real.sqrt volume * boundC) :
    ‖tripleSum A B C / (volume : Complex)‖ ≤
      boundA * boundB * boundC := by
  have hnum : ‖tripleSum A B C‖ ≤
      volume * (boundA * boundB * boundC) := by
    calc
      ‖tripleSum A B C‖ ≤
          boundA * (Real.sqrt (frobeniusSq B) *
            Real.sqrt (frobeniusSq C)) :=
        norm_tripleSum_le_frobenius A B C boundA hboundA hA
      _ ≤ boundA * ((Real.sqrt volume * boundB) *
          (Real.sqrt volume * boundC)) := by gcongr
      _ = volume * (boundA * boundB * boundC) := by
        calc
          boundA * ((Real.sqrt volume * boundB) *
              (Real.sqrt volume * boundC)) =
              Real.sqrt volume ^ 2 * (boundA * boundB * boundC) := by ring
          _ = volume * (boundA * boundB * boundC) := by
            rw [Real.sq_sqrt hvolume.le]
  rw [norm_div]
  rw [show ‖(volume : Complex)‖ = volume by
    simpa using (abs_of_pos hvolume)]
  exact (div_le_iff₀ hvolume).2
    (by simpa [mul_comm, mul_left_comm, mul_assoc] using hnum)

theorem norm_tripleSum_sub_div_volume_le
    (A B C A' B' C' : left → right → Complex)
    (volume epsilonA epsilonB epsilonC boundA' boundB boundB' boundC : Real)
    (hvolume : 0 < volume)
    (hepsilonA : 0 ≤ epsilonA) (hepsilonB : 0 ≤ epsilonB)
    (hepsilonC : 0 ≤ epsilonC)
    (hboundA' : 0 ≤ boundA') (hboundB : 0 ≤ boundB)
    (hA : ∀ i j, ‖A i j - A' i j‖ ≤ epsilonA)
    (hB : ∀ i j, ‖B i j - B' i j‖ ≤ epsilonB)
    (hC : ∀ i j, ‖C i j - C' i j‖ ≤ epsilonC)
    (hFB : Real.sqrt (frobeniusSq B) ≤ Real.sqrt volume * boundB)
    (hFC : Real.sqrt (frobeniusSq C) ≤ Real.sqrt volume * boundC)
    (hFA' : Real.sqrt (frobeniusSq A') ≤ Real.sqrt volume * boundA')
    (hFB' : Real.sqrt (frobeniusSq B') ≤ Real.sqrt volume * boundB') :
    ‖(tripleSum A B C - tripleSum A' B' C') / (volume : Complex)‖ ≤
      epsilonA * boundB * boundC + epsilonB * boundA' * boundC +
        epsilonC * boundA' * boundB' := by
  have hsqrt_sq : Real.sqrt volume ^ 2 = volume := Real.sq_sqrt hvolume.le
  have hnum : ‖tripleSum A B C - tripleSum A' B' C'‖ ≤
      volume * (epsilonA * boundB * boundC + epsilonB * boundA' * boundC +
        epsilonC * boundA' * boundB') := by
    calc
      ‖tripleSum A B C - tripleSum A' B' C'‖ ≤
          epsilonA *
              (Real.sqrt (frobeniusSq B) * Real.sqrt (frobeniusSq C)) +
            epsilonB *
              (Real.sqrt (frobeniusSq A') * Real.sqrt (frobeniusSq C)) +
            epsilonC *
              (Real.sqrt (frobeniusSq A') * Real.sqrt (frobeniusSq B')) :=
        norm_tripleSum_sub_le_frobenius A B C A' B' C'
          epsilonA epsilonB epsilonC hepsilonA hepsilonB hepsilonC hA hB hC
      _ ≤ epsilonA * ((Real.sqrt volume * boundB) *
              (Real.sqrt volume * boundC)) +
            epsilonB * ((Real.sqrt volume * boundA') *
              (Real.sqrt volume * boundC)) +
            epsilonC * ((Real.sqrt volume * boundA') *
              (Real.sqrt volume * boundB')) := by gcongr
      _ = volume * (epsilonA * boundB * boundC +
          epsilonB * boundA' * boundC + epsilonC * boundA' * boundB') := by
        calc
          epsilonA * ((Real.sqrt volume * boundB) *
                (Real.sqrt volume * boundC)) +
              epsilonB * ((Real.sqrt volume * boundA') *
                (Real.sqrt volume * boundC)) +
              epsilonC * ((Real.sqrt volume * boundA') *
                (Real.sqrt volume * boundB')) =
              Real.sqrt volume ^ 2 *
                (epsilonA * boundB * boundC +
                  epsilonB * boundA' * boundC +
                  epsilonC * boundA' * boundB') := by ring
          _ = volume * (epsilonA * boundB * boundC +
              epsilonB * boundA' * boundC +
              epsilonC * boundA' * boundB') := by rw [hsqrt_sq]
  rw [norm_div]
  rw [show ‖(volume : Complex)‖ = volume by
    simpa using (abs_of_pos hvolume)]
  exact (div_le_iff₀ hvolume).2
    (by simpa [mul_comm, mul_left_comm, mul_assoc] using hnum)



/-! ## Orthogonal spectral-frame closure -/

variable {mode bond : Type*} [Fintype mode] [DecidableEq mode]
  [Fintype bond]

def spectralKernel (u : mode → bond → Real) (w : mode → Real) :
    bond → bond → Real :=
  fun j l ↦ ∑ k, w k * u k j * u k l

def realFrobeniusSq (K : bond → bond → Real) : Real :=
  ∑ j, ∑ l, K j l ^ 2

def rowEnergy (u : mode → bond → Real) (j : bond) : Real :=
  ∑ k, (u k j) ^ 2

theorem rowEnergy_eq_one_of_orthonormal_of_card_eq
    (u : mode → bond → Real)
    (hcard : Fintype.card mode = Fintype.card bond)
    (horth : ∀ k q, ∑ j, u k j * u q j = if k = q then 1 else 0)
    (j : bond) : rowEnergy u j = 1 := by
  classical
  let U : Matrix mode bond Real := u
  have hright : U * U.transpose = 1 := by
    ext k q
    change (∑ x, u k x * u q x) = if k = q then 1 else 0
    exact horth k q
  have hleft : U.transpose * U = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq mode bond Real hcard).mp hright
  have hj := congrArg (fun M : Matrix bond bond Real ↦ M j j) hleft
  rw [Matrix.mul_apply] at hj
  simp_rw [Matrix.transpose_apply] at hj
  have hj' : (∑ x, u x j * u x j) = 1 := by
    simpa [U] using hj
  simpa [rowEnergy, pow_two] using hj'

theorem rowEnergy_le_one_of_orthonormal_of_card_eq
    (u : mode → bond → Real)
    (hcard : Fintype.card mode = Fintype.card bond)
    (horth : ∀ k q, ∑ j, u k j * u q j = if k = q then 1 else 0)
    (j : bond) : rowEnergy u j ≤ 1 := by
  classical
  rw [rowEnergy_eq_one_of_orthonormal_of_card_eq u hcard horth j]


theorem sum_sum_eq_sum_prod {alpha beta : Type*}
    [Fintype alpha] [Fintype beta] (f : alpha → beta → Real) :
    (∑ a, ∑ b, f a b) = ∑ ab : alpha × beta, f ab.1 ab.2 := by
  simpa using
    (Finset.sum_product' (Finset.univ : Finset alpha)
      (Finset.univ : Finset beta) f).symm

theorem spectralKernel_frobeniusSq_eq
    (u : mode → bond → Real) (w : mode → Real)
    (horth : ∀ k q, ∑ j, u k j * u q j = if k = q then 1 else 0) :
    realFrobeniusSq (spectralKernel u w) = ∑ k, w k ^ 2 := by
  unfold realFrobeniusSq spectralKernel
  calc
    (∑ j, ∑ l, (∑ k, w k * u k j * u k l) ^ 2) =
        ∑ j, ∑ l, ∑ k, ∑ q,
          (w k * u k j * u k l) * (w q * u q j * u q l) := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro l _hl
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.mul_sum]
    _ = ∑ k, ∑ q, w k * w q *
          ((∑ j, u k j * u q j) * (∑ l, u k l * u q l)) := by
      calc
        (∑ j, ∑ l, ∑ k, ∑ q,
            (w k * u k j * u k l) * (w q * u q j * u q l)) =
            ∑ jl : bond × bond, ∑ kq : mode × mode,
              (w kq.1 * u kq.1 jl.1 * u kq.1 jl.2) *
                (w kq.2 * u kq.2 jl.1 * u kq.2 jl.2) := by
          rw [sum_sum_eq_sum_prod]
          apply Finset.sum_congr rfl
          intro jl _hjl
          rw [sum_sum_eq_sum_prod]
        _ = ∑ kq : mode × mode, ∑ jl : bond × bond,
              (w kq.1 * u kq.1 jl.1 * u kq.1 jl.2) *
                (w kq.2 * u kq.2 jl.1 * u kq.2 jl.2) := by
          rw [Finset.sum_comm]
        _ = ∑ k, ∑ q, w k * w q *
              ((∑ j, u k j * u q j) *
                (∑ l, u k l * u q l)) := by
          rw [← sum_sum_eq_sum_prod (fun k q ↦
            ∑ jl : bond × bond,
              (w k * u k jl.1 * u k jl.2) *
                (w q * u q jl.1 * u q jl.2))]
          apply Finset.sum_congr rfl
          intro k _hk
          apply Finset.sum_congr rfl
          intro q _hq
          rw [← sum_sum_eq_sum_prod (fun j l ↦
            (w k * u k j * u k l) * (w q * u q j * u q l))]
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _hj
          apply Finset.sum_congr rfl
          intro l _hl
          ring
    _ = ∑ k, w k ^ 2 := by
      simp_rw [horth]
      simp [pow_two]

omit [DecidableEq mode] [Fintype bond] in
theorem spectralKernel_sub_entry_abs_le
    (u : mode → bond → Real) (w w' : mode → Real)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (hrow : ∀ j, rowEnergy u j ≤ 1)
    (hweight : ∀ k, |w k - w' k| ≤ epsilon)
    (j l : bond) :
    |spectralKernel u w j l - spectralKernel u w' j l| ≤ epsilon := by
  have hrow_nonneg (a : bond) : 0 ≤ rowEnergy u a :=
    Finset.sum_nonneg fun k _hk ↦ sq_nonneg _
  calc
    |spectralKernel u w j l - spectralKernel u w' j l| =
        |∑ k, (w k - w' k) * u k j * u k l| := by
      unfold spectralKernel
      rw [← Finset.sum_sub_distrib]
      apply congrArg abs
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ ≤ ∑ k, |w k - w' k| * |u k j| * |u k l| := by
      simpa [abs_mul] using (Finset.abs_sum_le_sum_abs
        (fun k ↦ (w k - w' k) * u k j * u k l)
        (Finset.univ : Finset mode))
    _ ≤ epsilon * ∑ k, |u k j| * |u k l| := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _hk
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hweight k) (abs_nonneg (u k j)))
          (abs_nonneg (u k l)))
    _ ≤ epsilon *
        (Real.sqrt (rowEnergy u j) * Real.sqrt (rowEnergy u l)) := by
      gcongr
      simpa [rowEnergy, sq_abs] using
        (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun k ↦ |u k j|) (fun k ↦ |u k l|))
    _ ≤ epsilon * (1 * 1) := by
      gcongr
      · simpa using Real.sqrt_le_one.mpr (hrow j)
      · simpa using Real.sqrt_le_one.mpr (hrow l)
    _ = epsilon := by ring



/-! ## Effective-weight projected-kernel closure -/

theorem frobeniusSq_ofReal_eq_realFrobeniusSq
    (K : bond → bond → Real) :
    frobeniusSq (fun j l ↦ (K j l : Complex)) = realFrobeniusSq K := by
  unfold frobeniusSq realFrobeniusSq
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro l _hl
  simp [sq_abs]

theorem sqrt_realFrobeniusSq_spectralKernel_le
    (u : mode → bond → Real) (w : mode → Real)
    (horth : ∀ k q, ∑ j, u k j * u q j = if k = q then 1 else 0)
    (bound : Real) (hbound : 0 ≤ bound)
    (hweight : ∀ k, |w k| ≤ bound) :
    Real.sqrt (realFrobeniusSq (spectralKernel u w)) ≤
      Real.sqrt (Fintype.card mode : Real) * bound := by
  have hsum : (∑ k, w k ^ 2) ≤
      (Fintype.card mode : Real) * bound ^ 2 := by
    calc
      (∑ k, w k ^ 2) ≤ ∑ _k : mode, bound ^ 2 := by
        apply Finset.sum_le_sum
        intro k _hk
        have hupper : w k ≤ bound := (le_abs_self _).trans (hweight k)
        have hlower : -bound ≤ w k :=
          (neg_le_neg (hweight k)).trans (neg_abs_le (w k))
        nlinarith
      _ = (Fintype.card mode : Real) * bound ^ 2 := by simp
  rw [spectralKernel_frobeniusSq_eq u w horth]
  calc
    Real.sqrt (∑ k, w k ^ 2) ≤
        Real.sqrt ((Fintype.card mode : Real) * bound ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (Fintype.card mode : Real) * bound := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hbound]

variable {iota : Type*} [Fintype iota] [DecidableEq iota]

omit [Fintype bond] in
theorem weightedProjectedBondKernel_eq_spectralKernel_effective
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (u : Fin (Fintype.card iota) → bond → Real)
    (hfactor : ∀ k j l, projectedBondKernel B A k j l =
      orderedEigenvalue A k * u k j * u k l)
    (weight : Fin (Fintype.card iota) → Real) :
    weightedProjectedBondKernel B A weight =
      spectralKernel u (fun k ↦ orderedEigenvalue A k * weight k) := by
  ext j l
  unfold weightedProjectedBondKernel spectralKernel
  apply Finset.sum_congr rfl
  intro k _hk
  rw [hfactor]
  ring

omit [Fintype bond] in
theorem weightedProjectedBondKernel_sub_entry_norm_le_of_effectiveWeight
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (u : Fin (Fintype.card iota) → bond → Real)
    (hfactor : ∀ k j l, projectedBondKernel B A k j l =
      orderedEigenvalue A k * u k j * u k l)
    (hrow : ∀ j, rowEnergy u j ≤ 1)
    (weight weight' : Fin (Fintype.card iota) → Real)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (hweight : ∀ k,
      |orderedEigenvalue A k * weight k -
        orderedEigenvalue A k * weight' k| ≤ epsilon)
    (j l : bond) :
    ‖((weightedProjectedBondKernel B A weight j l : Real) : Complex) -
      (weightedProjectedBondKernel B A weight' j l : Real)‖ ≤ epsilon := by
  rw [weightedProjectedBondKernel_eq_spectralKernel_effective
      B A u hfactor weight,
    weightedProjectedBondKernel_eq_spectralKernel_effective
      B A u hfactor weight']
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using
    spectralKernel_sub_entry_abs_le u
    (fun k ↦ orderedEigenvalue A k * weight k)
    (fun k ↦ orderedEigenvalue A k * weight' k)
    epsilon hepsilon hrow hweight j l

omit [Fintype bond] in
theorem weightedProjectedBondKernel_entry_norm_le_of_effectiveWeight
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (u : Fin (Fintype.card iota) → bond → Real)
    (hfactor : ∀ k j l, projectedBondKernel B A k j l =
      orderedEigenvalue A k * u k j * u k l)
    (hrow : ∀ j, rowEnergy u j ≤ 1)
    (weight : Fin (Fintype.card iota) → Real)
    (bound : Real) (hbound : 0 ≤ bound)
    (hweight : ∀ k, |orderedEigenvalue A k * weight k| ≤ bound)
    (j l : bond) :
    ‖((weightedProjectedBondKernel B A weight j l : Real) : Complex)‖ ≤
      bound := by
  simpa [weightedProjectedBondKernel] using
    (weightedProjectedBondKernel_sub_entry_norm_le_of_effectiveWeight
      B A u hfactor hrow weight (fun _k ↦ 0) bound hbound
      (by simpa using hweight) j l)

theorem weightedProjectedBondKernel_sqrt_frobeniusSq_le_of_effectiveWeight
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (u : Fin (Fintype.card iota) → bond → Real)
    (hfactor : ∀ k j l, projectedBondKernel B A k j l =
      orderedEigenvalue A k * u k j * u k l)
    (horth : ∀ k q, ∑ j, u k j * u q j = if k = q then 1 else 0)
    (weight : Fin (Fintype.card iota) → Real)
    (bound : Real) (hbound : 0 ≤ bound)
    (hweight : ∀ k, |orderedEigenvalue A k * weight k| ≤ bound) :
    Real.sqrt (frobeniusSq (fun j l ↦
      ((weightedProjectedBondKernel B A weight j l : Real) : Complex))) ≤
      Real.sqrt (Fintype.card iota : Real) * bound := by
  rw [weightedProjectedBondKernel_eq_spectralKernel_effective
    B A u hfactor weight, frobeniusSq_ofReal_eq_realFrobeniusSq]
  simpa using sqrt_realFrobeniusSq_spectralKernel_le u
    (fun k ↦ orderedEigenvalue A k * weight k) horth bound hbound hweight


end
end ArchonPhysics.ThreeLegKernelApproximationAlgebra
