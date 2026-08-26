import ArchonPhysics.OrderedSpectrumWeyl

/-!
# Minimum endpoint Weyl perturbation bound

This module complements `OrderedSpectrumWeyl` with the Rayleigh-infimum
characterization and the operator-norm perturbation bound for the last
decreasing eigenvalue.
-/

namespace ArchonPhysics.OrderedSpectrumWeyl

open Module RCLike InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
variable {T S : E →ₗ[ℝ] E}

/-- The last decreasing eigenvalue is the infimum of the Rayleigh quotient. -/
theorem smallest_eigenvalue_eq_iInf_rayleigh (hT : T.IsSymmetric)
    (n : ℕ) (hn : Module.finrank ℝ E = n) (hnpos : 0 < n) :
    hT.eigenvalues hn ⟨n - 1, by omega⟩ =
      ⨅ x : {x : E // x ≠ 0}, inner ℝ (T x) x / ‖(x : E)‖ ^ 2 := by
  let _ : NeZero n := ⟨hnpos.ne'⟩
  let k : Fin n := ⟨n - 1, by omega⟩
  let m : ℝ := ⨅ x : {x : E // x ≠ 0}, inner ℝ (T x) x / ‖(x : E)‖ ^ 2
  have hm_eigen : Module.End.HasEigenvalue T m := by
    simpa [m] using hT.hasEigenvalue_iInf_of_finiteDimensional
  obtain ⟨i, hi⟩ := hT.exists_eigenvalues_eq hn hm_eigen
  have hle_m : hT.eigenvalues hn k ≤ m := by
    have hi' : hT.eigenvalues hn i = m := by simpa using hi
    rw [← hi']
    apply hT.eigenvalues_antitone hn
    apply Fin.mk_le_mk.mpr
    omega
  have hbdd : BddBelow (Set.range fun x : {x : E // x ≠ 0} =>
      inner ℝ (T x) x / ‖(x : E)‖ ^ 2) := by
    refine ⟨-‖hT.toSelfAdjoint.val‖, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (abs_le.mp (hT.toSelfAdjoint.val.rayleighQuotient_le_norm x)).1
  let v : E := hT.eigenvectorBasis hn k
  have hv : v ≠ 0 := hT.eigenvectorBasis hn |>.orthonormal.ne_zero k
  have hrayleigh : inner ℝ (T v) v / ‖v‖ ^ 2 = hT.eigenvalues hn k := by
    rw [hT.apply_eigenvectorBasis hn, real_inner_smul_left]
    simp [v, inner_self_eq_norm_sq_to_K]
  change hT.eigenvalues hn k = m
  apply le_antisymm hle_m
  rw [← hrayleigh]
  exact ciInf_le hbdd ⟨v, hv⟩

/-- The last decreasing eigenvalue is below every Rayleigh quotient. -/
theorem smallest_eigenvalue_le_rayleigh (hT : T.IsSymmetric)
    (n : ℕ) (hn : Module.finrank ℝ E = n) (hnpos : 0 < n)
    (x : E) (hx : x ≠ 0) :
    hT.eigenvalues hn ⟨n - 1, by omega⟩ ≤ inner ℝ (T x) x / ‖x‖ ^ 2 := by
  rw [smallest_eigenvalue_eq_iInf_rayleigh hT n hn hnpos]
  have hbdd : BddBelow (Set.range fun y : {y : E // y ≠ 0} =>
      inner ℝ (T y) y / ‖(y : E)‖ ^ 2) := by
    refine ⟨-‖hT.toSelfAdjoint.val‖, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact (abs_le.mp (hT.toSelfAdjoint.val.rayleighQuotient_le_norm y)).1
  convert ciInf_le hbdd (⟨x, hx⟩ : {y : E // y ≠ 0}) using 1

/-- One-sided minimum endpoint Weyl bound. -/
theorem smallest_eigenvalue_sub_le_norm (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (n : ℕ) (hn : Module.finrank ℝ E = n) (hnpos : 0 < n) :
    hT.eigenvalues hn ⟨n - 1, by omega⟩ - hS.eigenvalues hn ⟨n - 1, by omega⟩ ≤
      ‖(hT.sub hS).toSelfAdjoint.val‖ := by
  let _ : NeZero n := ⟨hnpos.ne'⟩
  let k : Fin n := ⟨n - 1, by omega⟩
  let v : E := hS.eigenvectorBasis hn k
  have hv : v ≠ 0 := hS.eigenvectorBasis hn |>.orthonormal.ne_zero k
  have hSv : inner ℝ (S v) v / ‖v‖ ^ 2 = hS.eigenvalues hn k := by
    rw [hS.apply_eigenvectorBasis hn, real_inner_smul_left]
    simp [v, inner_self_eq_norm_sq_to_K]
  have hTv : hT.eigenvalues hn k ≤ inner ℝ (T v) v / ‖v‖ ^ 2 :=
    smallest_eigenvalue_le_rayleigh hT n hn hnpos v hv
  have hdiff : inner ℝ ((T - S) v) v / ‖v‖ ^ 2 ≤ ‖(hT.sub hS).toSelfAdjoint.val‖ :=
    (le_abs_self _).trans ((hT.sub hS).toSelfAdjoint.val.rayleighQuotient_le_norm v)
  have hTS : T = S + (T - S) := by abel
  have happ : T v = S v + (T - S) v := DFunLike.congr_fun hTS v
  have hadd : inner ℝ (T v) v / ‖v‖ ^ 2 =
      inner ℝ (S v) v / ‖v‖ ^ 2 + inner ℝ ((T - S) v) v / ‖v‖ ^ 2 := by
    rw [happ, inner_add_left, add_div]
  change hT.eigenvalues hn k - hS.eigenvalues hn k ≤ _
  linarith

/-- The smallest eigenvalue is 1-Lipschitz in the operator norm. -/
theorem abs_smallest_eigenvalue_sub_le_norm (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (n : ℕ) (hn : Module.finrank ℝ E = n) (hnpos : 0 < n) :
    |hT.eigenvalues hn ⟨n - 1, by omega⟩ - hS.eigenvalues hn ⟨n - 1, by omega⟩| ≤
      ‖(hT.sub hS).toSelfAdjoint.val‖ := by
  rw [abs_le]
  constructor
  · have h := smallest_eigenvalue_sub_le_norm hS hT n hn hnpos
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
  · exact smallest_eigenvalue_sub_le_norm hT hS n hn hnpos

end

end ArchonPhysics.OrderedSpectrumWeyl
