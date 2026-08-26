import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Endpoint Weyl perturbation bound

This module proves, without a spectral continuity assumption, that the largest
eigenvalue of a finite-dimensional real symmetric operator is 1-Lipschitz in
the operator norm.  It is the endpoint case of Weyl's perturbation theorem and
is intended as the perturbative base for continuity of the full ordered
Hermitian spectrum.
-/

namespace ArchonPhysics.OrderedSpectrumWeyl

open Module RCLike InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
variable {T S : E →ₗ[ℝ] E}

/-- The first decreasing eigenvalue is the supremum of the Rayleigh quotient. -/
theorem largest_eigenvalue_eq_iSup_rayleigh (hT : T.IsSymmetric)
    (n : ℕ) (hn : Module.finrank ℝ E = n) (hnpos : 0 < n) :
    hT.eigenvalues hn ⟨0, hnpos⟩ =
      ⨆ x : {x : E // x ≠ 0}, inner ℝ (T x) x / ‖(x : E)‖ ^ 2 := by
  let _ : NeZero n := ⟨hnpos.ne'⟩
  let M : ℝ := ⨆ x : {x : E // x ≠ 0}, inner ℝ (T x) x / ‖(x : E)‖ ^ 2
  have hM_eigen : Module.End.HasEigenvalue T M := by
    simpa [M] using hT.hasEigenvalue_iSup_of_finiteDimensional
  obtain ⟨i, hi⟩ := hT.exists_eigenvalues_eq hn hM_eigen
  have hM_le : M ≤ hT.eigenvalues hn ⟨0, hnpos⟩ := by
    have hi' : hT.eigenvalues hn i = M := by simpa using hi
    rw [← hi']
    exact hT.eigenvalues_antitone hn (Fin.zero_le i)
  have hbdd : BddAbove (Set.range fun x : {x : E // x ≠ 0} =>
      inner ℝ (T x) x / ‖(x : E)‖ ^ 2) := by
    refine ⟨‖hT.toSelfAdjoint.val‖, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (le_abs_self _).trans (hT.toSelfAdjoint.val.rayleighQuotient_le_norm x)
  let v : E := hT.eigenvectorBasis hn ⟨0, hnpos⟩
  have hv : v ≠ 0 := hT.eigenvectorBasis hn |>.orthonormal.ne_zero ⟨0, hnpos⟩
  have hrayleigh : inner ℝ (T v) v / ‖v‖ ^ 2 = hT.eigenvalues hn ⟨0, hnpos⟩ := by
    rw [hT.apply_eigenvectorBasis hn, real_inner_smul_left]
    simp [v, inner_self_eq_norm_sq_to_K]
  change hT.eigenvalues hn ⟨0, hnpos⟩ = M
  apply le_antisymm
  · rw [← hrayleigh]
    exact le_ciSup hbdd ⟨v, hv⟩
  · exact hM_le

/-- Every Rayleigh quotient is at most the first decreasing eigenvalue. -/
theorem rayleigh_le_largest_eigenvalue (hT : T.IsSymmetric)
    (n : ℕ) (hn : Module.finrank ℝ E = n) (hnpos : 0 < n)
    (x : E) (hx : x ≠ 0) :
    inner ℝ (T x) x / ‖x‖ ^ 2 ≤ hT.eigenvalues hn ⟨0, hnpos⟩ := by
  rw [largest_eigenvalue_eq_iSup_rayleigh hT n hn hnpos]
  have hbdd : BddAbove (Set.range fun y : {y : E // y ≠ 0} =>
      inner ℝ (T y) y / ‖(y : E)‖ ^ 2) := by
    refine ⟨‖hT.toSelfAdjoint.val‖, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact (le_abs_self _).trans (hT.toSelfAdjoint.val.rayleighQuotient_le_norm y)
  convert le_ciSup hbdd (⟨x, hx⟩ : {y : E // y ≠ 0}) using 1

/-- One-sided endpoint Weyl bound. -/
theorem largest_eigenvalue_sub_le_norm (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (n : ℕ) (hn : Module.finrank ℝ E = n) (hnpos : 0 < n) :
    hT.eigenvalues hn ⟨0, hnpos⟩ - hS.eigenvalues hn ⟨0, hnpos⟩ ≤
      ‖(hT.sub hS).toSelfAdjoint.val‖ := by
  let _ : NeZero n := ⟨hnpos.ne'⟩
  let v : E := hT.eigenvectorBasis hn ⟨0, hnpos⟩
  have hv : v ≠ 0 := hT.eigenvectorBasis hn |>.orthonormal.ne_zero ⟨0, hnpos⟩
  have hTv : inner ℝ (T v) v / ‖v‖ ^ 2 = hT.eigenvalues hn ⟨0, hnpos⟩ := by
    rw [hT.apply_eigenvectorBasis hn, real_inner_smul_left]
    simp [v, inner_self_eq_norm_sq_to_K]
  have hSv : inner ℝ (S v) v / ‖v‖ ^ 2 ≤ hS.eigenvalues hn ⟨0, hnpos⟩ :=
    rayleigh_le_largest_eigenvalue hS n hn hnpos v hv
  have hdiff : inner ℝ ((T - S) v) v / ‖v‖ ^ 2 ≤ ‖(hT.sub hS).toSelfAdjoint.val‖ :=
    (le_abs_self _).trans ((hT.sub hS).toSelfAdjoint.val.rayleighQuotient_le_norm v)
  have hTS : T = S + (T - S) := by abel
  have happ : T v = S v + (T - S) v := DFunLike.congr_fun hTS v
  have hadd : inner ℝ (T v) v / ‖v‖ ^ 2 =
      inner ℝ (S v) v / ‖v‖ ^ 2 + inner ℝ ((T - S) v) v / ‖v‖ ^ 2 := by
    rw [happ, inner_add_left, add_div]
  linarith

/-- The largest eigenvalue is 1-Lipschitz in the operator norm. -/
theorem abs_largest_eigenvalue_sub_le_norm (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (n : ℕ) (hn : Module.finrank ℝ E = n) (hnpos : 0 < n) :
    |hT.eigenvalues hn ⟨0, hnpos⟩ - hS.eigenvalues hn ⟨0, hnpos⟩| ≤
      ‖(hT.sub hS).toSelfAdjoint.val‖ := by
  rw [abs_le]
  constructor
  · have h := largest_eigenvalue_sub_le_norm hS hT n hn hnpos
    have hmap : (hS.sub hT).toSelfAdjoint.val = -(hT.sub hS).toSelfAdjoint.val := by
      ext x
      rw [neg_apply]
      change ((hS.sub hT).toSelfAdjoint : E →ₗ[ℝ] E) x =
        -(((hT.sub hS).toSelfAdjoint : E →ₗ[ℝ] E) x)
      rw [(hS.sub hT).coe_toSelfAdjoint, (hT.sub hS).coe_toSelfAdjoint]
      simp
    have hnorm : ‖(hS.sub hT).toSelfAdjoint.val‖ = ‖(hT.sub hS).toSelfAdjoint.val‖ := by
      rw [hmap, norm_neg]
    rw [hnorm] at h
    linarith
  · exact largest_eigenvalue_sub_le_norm hT hS n hn hnpos

end

end ArchonPhysics.OrderedSpectrumWeyl
