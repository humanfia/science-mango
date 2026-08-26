import ArchonPhysics.OrderedSpectrumWeylMinimum

/-!
# Weyl perturbation bound for every ordered eigenvalue

This module proves the finite-dimensional real self-adjoint Weyl bound

`|eigenvalues T k - eigenvalues S k| ≤ ‖T - S‖`

for every decreasing spectral coordinate.  The proof develops the needed
Courant--Fischer argument directly from Mathlib's ordered orthonormal
eigenbasis: the leading `k + 1` dimensional spectral subspace of `T` and the
trailing `n - k` dimensional spectral subspace of `S` have a nonzero
intersection, and their Rayleigh quotients bracket the two eigenvalues.
-/

namespace ArchonPhysics.OrderedSpectrumWeyl

open Module RCLike InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {T S : E →ₗ[ℝ] E}

/-- Span of the decreasing eigenvectors with indices at most `k`. -/
def leadingEigenSubspace (hT : T.IsSymmetric) (n : ℕ)
    (hn : Module.finrank ℝ E = n) (k : Fin n) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range fun i : Set.Iic k => hT.eigenvectorBasis hn i.1)

/-- Span of the decreasing eigenvectors with indices at least `k`. -/
def trailingEigenSubspace (hT : T.IsSymmetric) (n : ℕ)
    (hn : Module.finrank ℝ E = n) (k : Fin n) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range fun i : Set.Ici k => hT.eigenvectorBasis hn i.1)

private theorem range_restrict_eq_image {α β : Type*} (f : α → β) (s : Set α) :
    Set.range (fun i : s => f i.1) = f '' s := by
  ext y
  simp

/-- Diagonal expansion of a symmetric quadratic form in its ordered
orthonormal eigenbasis. -/
theorem inner_apply_eq_sum_eigenvalues_mul_sq_repr
    (hT : T.IsSymmetric) (n : ℕ) (hn : Module.finrank ℝ E = n)
    (x : E) :
    inner ℝ (T x) x = ∑ i : Fin n,
      hT.eigenvalues hn i * ((hT.eigenvectorBasis hn).repr x i) ^ 2 := by
  let b := hT.eigenvectorBasis hn
  calc
    inner ℝ (T x) x = inner ℝ (T (∑ i : Fin n, b.repr x i • b i)) x := by
      rw [b.sum_repr]
    _ = ∑ i : Fin n, hT.eigenvalues hn i * (b.repr x i) ^ 2 := by
      simp only [map_sum, map_smul, sum_inner, real_inner_smul_left,
        b.repr_apply_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [show T (b i) = hT.eigenvalues hn i • b i by
        exact hT.apply_eigenvectorBasis hn i]
      rw [real_inner_smul_left]
      ring

/-- On the leading spectral subspace, the `k`-th eigenvalue is a lower
bound for every nonzero Rayleigh quotient. -/
theorem eigenvalue_le_rayleigh_of_mem_le_span
    (hT : T.IsSymmetric) (n : ℕ) (hn : Module.finrank ℝ E = n)
    (k : Fin n) (x : E)
    (hx : x ∈ Submodule.span ℝ
      ((hT.eigenvectorBasis hn : Fin n → E) '' Set.Iic k))
    (hx0 : x ≠ 0) :
    hT.eigenvalues hn k ≤ inner ℝ (T x) x / ‖x‖ ^ 2 := by
  let b := hT.eigenvectorBasis hn
  have hsupp := b.toBasis.repr_support_subset_of_mem_span (Set.Iic k) hx
  have hzero : ∀ i : Fin n, ¬i ≤ k → b.repr x i = 0 := by
    intro i hi
    have hzero' : b.toBasis.repr x i = 0 := by
      by_contra hne
      exact hi (hsupp (Finsupp.mem_support_iff.mpr hne))
    exact hzero'
  have hnorm : ∑ i : Fin n, (b.repr x i) ^ 2 = ‖x‖ ^ 2 := by
    simpa only [b.repr_apply_apply] using b.sum_sq_inner_right x
  rw [le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx0))]
  rw [inner_apply_eq_sum_eigenvalues_mul_sq_repr hT n hn x, ← hnorm,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hik : i ≤ k
  · gcongr
    exact hT.eigenvalues_antitone hn hik
  · rw [hzero i hik]
    simp

/-- On the trailing spectral subspace, the `k`-th eigenvalue is an upper
bound for every nonzero Rayleigh quotient. -/
theorem rayleigh_le_eigenvalue_of_mem_ge_span
    (hT : T.IsSymmetric) (n : ℕ) (hn : Module.finrank ℝ E = n)
    (k : Fin n) (x : E)
    (hx : x ∈ Submodule.span ℝ
      ((hT.eigenvectorBasis hn : Fin n → E) '' Set.Ici k))
    (hx0 : x ≠ 0) :
    inner ℝ (T x) x / ‖x‖ ^ 2 ≤ hT.eigenvalues hn k := by
  let b := hT.eigenvectorBasis hn
  have hsupp := b.toBasis.repr_support_subset_of_mem_span (Set.Ici k) hx
  have hzero : ∀ i : Fin n, ¬k ≤ i → b.repr x i = 0 := by
    intro i hi
    have hzero' : b.toBasis.repr x i = 0 := by
      by_contra hne
      exact hi (hsupp (Finsupp.mem_support_iff.mpr hne))
    exact hzero'
  have hnorm : ∑ i : Fin n, (b.repr x i) ^ 2 = ‖x‖ ^ 2 := by
    simpa only [b.repr_apply_apply] using b.sum_sq_inner_right x
  rw [div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx0))]
  rw [inner_apply_eq_sum_eigenvalues_mul_sq_repr hT n hn x, ← hnorm,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hik : k ≤ i
  · gcongr
    exact hT.eigenvalues_antitone hn hik
  · rw [hzero i hik]
    simp

/-- The leading spectral subspace has dimension `k + 1`. -/
theorem finrank_leadingEigenSubspace (hT : T.IsSymmetric) (n : ℕ)
    (hn : Module.finrank ℝ E = n) (k : Fin n) :
    Module.finrank ℝ (leadingEigenSubspace hT n hn k) = k.val + 1 := by
  unfold leadingEigenSubspace
  rw [finrank_span_eq_card]
  · rw [Fintype.card_Iic, Fin.card_Iic]
  · exact (hT.eigenvectorBasis hn).toBasis.linearIndependent.comp
      (fun i : Set.Iic k => i.1) Subtype.val_injective

/-- The trailing spectral subspace has dimension `n - k`. -/
theorem finrank_trailingEigenSubspace (hT : T.IsSymmetric) (n : ℕ)
    (hn : Module.finrank ℝ E = n) (k : Fin n) :
    Module.finrank ℝ (trailingEigenSubspace hT n hn k) = n - k.val := by
  unfold trailingEigenSubspace
  rw [finrank_span_eq_card]
  · rw [Fintype.card_Ici, Fin.card_Ici]
  · exact (hT.eigenvectorBasis hn).toBasis.linearIndependent.comp
      (fun i : Set.Ici k => i.1) Subtype.val_injective

/-- A leading `T` spectral subspace and trailing `S` spectral subspace at the
same index have nonzero intersection. -/
theorem leading_inf_trailing_ne_bot (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (n : ℕ) (hn : Module.finrank ℝ E = n) (k : Fin n) :
    leadingEigenSubspace hT n hn k ⊓ trailingEigenSubspace hS n hn k ≠ ⊥ := by
  intro hbot
  have hdis : Disjoint (leadingEigenSubspace hT n hn k)
      (trailingEigenSubspace hS n hn k) := by
    rw [disjoint_iff_inf_le, hbot]
  have hdim := Submodule.finrank_add_finrank_le_of_disjoint hdis
  rw [finrank_leadingEigenSubspace, finrank_trailingEigenSubspace, hn] at hdim
  omega

/-- One-sided Weyl perturbation bound for every decreasing eigenvalue. -/
theorem ordered_eigenvalue_sub_le_norm (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (n : ℕ) (hn : Module.finrank ℝ E = n) (k : Fin n) :
    hT.eigenvalues hn k - hS.eigenvalues hn k ≤
      ‖(hT.sub hS).toSelfAdjoint.val‖ := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff
    (leadingEigenSubspace hT n hn k ⊓ trailingEigenSubspace hS n hn k)).mp
      (leading_inf_trailing_ne_bot hT hS n hn k)
  have hxT : x ∈ leadingEigenSubspace hT n hn k := hx.1
  have hxS : x ∈ trailingEigenSubspace hS n hn k := hx.2
  unfold leadingEigenSubspace at hxT
  rw [range_restrict_eq_image] at hxT
  unfold trailingEigenSubspace at hxS
  rw [range_restrict_eq_image] at hxS
  have hTx : hT.eigenvalues hn k ≤ inner ℝ (T x) x / ‖x‖ ^ 2 :=
    eigenvalue_le_rayleigh_of_mem_le_span hT n hn k x hxT hx0
  have hSx : inner ℝ (S x) x / ‖x‖ ^ 2 ≤ hS.eigenvalues hn k :=
    rayleigh_le_eigenvalue_of_mem_ge_span hS n hn k x hxS hx0
  have hdiff : inner ℝ ((T - S) x) x / ‖x‖ ^ 2 ≤
      ‖(hT.sub hS).toSelfAdjoint.val‖ :=
    (le_abs_self _).trans
      ((hT.sub hS).toSelfAdjoint.val.rayleighQuotient_le_norm x)
  have hTS : T = S + (T - S) := by abel
  have happ : T x = S x + (T - S) x := DFunLike.congr_fun hTS x
  have hadd : inner ℝ (T x) x / ‖x‖ ^ 2 =
      inner ℝ (S x) x / ‖x‖ ^ 2 + inner ℝ ((T - S) x) x / ‖x‖ ^ 2 := by
    rw [happ, inner_add_left, add_div]
  linarith

/-- Every decreasing eigenvalue is 1-Lipschitz in the self-adjoint operator
norm. -/
theorem abs_ordered_eigenvalue_sub_le_norm
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (n : ℕ) (hn : Module.finrank ℝ E = n) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤
      ‖(hT.sub hS).toSelfAdjoint.val‖ := by
  rw [abs_le]
  constructor
  · have h := ordered_eigenvalue_sub_le_norm hS hT n hn k
    have hmap : (hS.sub hT).toSelfAdjoint.val =
        -(hT.sub hS).toSelfAdjoint.val := by
      ext x
      rw [neg_apply]
      change ((hS.sub hT).toSelfAdjoint : E →ₗ[ℝ] E) x =
        -(((hT.sub hS).toSelfAdjoint : E →ₗ[ℝ] E) x)
      rw [(hS.sub hT).coe_toSelfAdjoint, (hT.sub hS).coe_toSelfAdjoint]
      simp
    have hnorm : ‖(hS.sub hT).toSelfAdjoint.val‖ =
        ‖(hT.sub hS).toSelfAdjoint.val‖ := by
      rw [hmap, norm_neg]
    rw [hnorm] at h
    linarith
  · exact ordered_eigenvalue_sub_le_norm hT hS n hn k

end

end ArchonPhysics.OrderedSpectrumWeyl
