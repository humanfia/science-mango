import ArchonPhysics.OrderedSpectrumWeylAll

/-!
# A finite-dimensional quasimode lies near the spectrum

For a finite-dimensional real self-adjoint operator, a unit vector whose
residual at energy `lambda` has norm at most `epsilon` forces an ordered
eigenvalue within `epsilon` of `lambda`.  The proof expands the residual in
Mathlib's orthonormal eigenbasis.  It uses neither a simple-spectrum
hypothesis nor a small operator perturbation.
-/

namespace ArchonPhysics.SelfAdjointQuasimodeSpectrum

open Module

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]

/-- A unit quasimode with residual at most `epsilon` puts the target energy
within `epsilon` of the finite ordered spectrum. -/
theorem exists_eigenvalue_abs_sub_le_of_unit_quasimode
    (T : E →ₗ[Real] E) (hT : T.IsSymmetric)
    (n : Nat) (hn : Module.finrank Real E = n)
    (v : E) {lambda epsilon : Real} (hepsilon : 0 ≤ epsilon)
    (hv : ‖v‖ = 1)
    (hresidual : ‖T v - lambda • v‖ ≤ epsilon) :
    ∃ k : Fin n, |hT.eigenvalues hn k - lambda| ≤ epsilon := by
  let b := hT.eigenvectorBasis hn
  by_contra hnear
  push Not at hnear
  have hvne : v ≠ 0 := by
    intro hvzero
    simp [hvzero] at hv
  have hreprNe : b.repr v ≠ 0 := by
    intro hzero
    apply hvne
    apply b.repr.injective
    simpa using hzero
  have hcoefficient : ∃ i : Fin n, b.repr v i ≠ 0 := by
    by_contra hcoefficient
    push Not at hcoefficient
    apply hreprNe
    ext i
    exact hcoefficient i
  obtain ⟨i₀, hi₀⟩ := hcoefficient
  have hnormCoordinates :
      ∑ i : Fin n, (b.repr v i) ^ 2 = 1 := by
    calc
      ∑ i : Fin n, (b.repr v i) ^ 2 = ‖b.repr v‖ ^ 2 :=
        (EuclideanSpace.real_norm_sq_eq (b.repr v)).symm
      _ = ‖v‖ ^ 2 := by rw [LinearIsometryEquiv.norm_map]
      _ = 1 := by rw [hv]; norm_num
  have hresidualCoordinates :
      ‖T v - lambda • v‖ ^ 2 =
        ∑ i : Fin n,
          ((hT.eigenvalues hn i - lambda) * b.repr v i) ^ 2 := by
    calc
      ‖T v - lambda • v‖ ^ 2 =
          ‖b.repr (T v - lambda • v)‖ ^ 2 := by
        rw [LinearIsometryEquiv.norm_map]
      _ = ∑ i : Fin n, (b.repr (T v - lambda • v) i) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq _
      _ = ∑ i : Fin n,
          ((hT.eigenvalues hn i - lambda) * b.repr v i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [map_sub, map_smul]
        simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        rw [hT.eigenvectorBasis_apply_self_apply hn v i]
        change ((hT.eigenvalues hn i * b.repr v i -
          lambda * b.repr v i) ^ 2 =
            ((hT.eigenvalues hn i - lambda) * b.repr v i) ^ 2)
        ring
  have hgapSq (i : Fin n) :
      epsilon ^ 2 < (hT.eigenvalues hn i - lambda) ^ 2 := by
    have hgap := hnear i
    have habs := abs_nonneg (hT.eigenvalues hn i - lambda)
    rw [← sq_abs (hT.eigenvalues hn i - lambda),
      sq_lt_sq₀ hepsilon habs]
    exact hgap
  have hsumStrict :
      ∑ i : Fin n, epsilon ^ 2 * (b.repr v i) ^ 2 <
        ∑ i : Fin n,
          ((hT.eigenvalues hn i - lambda) * b.repr v i) ^ 2 := by
    apply Finset.sum_lt_sum
    · intro i _hi
      have hmul := mul_le_mul_of_nonneg_right (hgapSq i).le
        (sq_nonneg (b.repr v i))
      nlinarith
    · refine ⟨i₀, Finset.mem_univ _, ?_⟩
      have hmul := mul_lt_mul_of_pos_right (hgapSq i₀)
        (sq_pos_of_ne_zero hi₀)
      nlinarith
  have hepsilonSqLt : epsilon ^ 2 < ‖T v - lambda • v‖ ^ 2 := by
    rw [hresidualCoordinates]
    calc
      epsilon ^ 2 =
          ∑ i : Fin n, epsilon ^ 2 * (b.repr v i) ^ 2 := by
        rw [← Finset.mul_sum, hnormCoordinates, mul_one]
      _ < _ := hsumStrict
  have hresidualSqLe : ‖T v - lambda • v‖ ^ 2 ≤ epsilon ^ 2 := by
    nlinarith [norm_nonneg (T v - lambda • v)]
  linarith

end

end ArchonPhysics.SelfAdjointQuasimodeSpectrum
