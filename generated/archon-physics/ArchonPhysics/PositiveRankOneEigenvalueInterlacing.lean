import ArchonPhysics.SingleMassRankOnePerturbation

/-!
# Interlacing for a positive rank-one update

This module proves Cauchy interlacing for a finite-dimensional real symmetric
operator after a positive semidefinite rank-one update.  The reusable core is
slightly more general: the two quadratic forms need only agree on the kernel
of one linear functional and be ordered everywhere.

For decreasing eigenvalues and `C = A + c vvᵀ`, `c ≥ 0`, it gives

`lambda_k(A) ≤ lambda_k(C)` and `lambda_(k+1)(C) ≤ lambda_k(A)`.

The final corollaries apply this to changing one mass in the dual periodic
random-mass harmonic matrix.  No simplicity, spectral-gap, infinite-volume,
or probabilistic assertion is made.
-/

namespace ArchonPhysics.PositiveRankOneEigenvalueInterlacing

open ArchonPhysics
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSpectrumWeyl
open ArchonPhysics.SingleMassRankOnePerturbation
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison
open Module RCLike InnerProductSpace
open scoped Matrix

noncomputable section

private theorem range_restrict_eq_image {alpha beta : Type*}
    (f : alpha → beta) (s : Set alpha) :
    Set.range (fun i : s ↦ f i.1) = f '' s := by
  ext y
  simp

/-- The intersection of the leading `k + 2` dimensional spectral subspace
of one operator with the trailing `n - k` dimensional spectral subspace of
another operator has dimension at least two. -/
theorem two_le_finrank_leading_succ_inf_trailing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E]
    {A C : E →ₗ[Real] E}
    (hA : A.IsSymmetric) (hC : C.IsSymmetric)
    (n : Nat) (hn : Module.finrank Real E = n) (k : Fin n)
    (hk : k.val + 1 < n) :
    2 ≤ Module.finrank Real
      ((leadingEigenSubspace hC n hn (⟨k.val + 1, hk⟩ : Fin n) ⊓
        trailingEigenSubspace hA n hn k) : Submodule Real E) := by
  let k' : Fin n := ⟨k.val + 1, hk⟩
  let L : Submodule Real E := leadingEigenSubspace hC n hn k'
  let R : Submodule Real E := trailingEigenSubspace hA n hn k
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq L R
  have hsup : Module.finrank Real (L ⊔ R : Submodule Real E) ≤ n := by
    rw [← hn]
    exact Submodule.finrank_le _
  have hL : Module.finrank Real L = k.val + 2 := by
    simpa [L, k'] using finrank_leadingEigenSubspace hC n hn k'
  have hR : Module.finrank Real R = n - k.val := by
    simpa [R] using finrank_trailingEigenSubspace hA n hn k
  change 2 ≤ Module.finrank Real (L ⊓ R : Submodule Real E)
  rw [hL, hR] at hdim
  omega

/-- A codimension-at-most-one condition cannot remove every vector from the
two-dimensional leading/trailing spectral intersection. -/
theorem exists_ne_zero_mem_leading_succ_inf_trailing_ker
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E]
    {A C : E →ₗ[Real] E}
    (hA : A.IsSymmetric) (hC : C.IsSymmetric)
    (phi : E →ₗ[Real] Real)
    (n : Nat) (hn : Module.finrank Real E = n) (k : Fin n)
    (hk : k.val + 1 < n) :
    ∃ x : E, x ≠ 0 ∧
      x ∈ leadingEigenSubspace hC n hn (⟨k.val + 1, hk⟩ : Fin n) ∧
      x ∈ trailingEigenSubspace hA n hn k ∧ phi x = 0 := by
  let W : Submodule Real E :=
    leadingEigenSubspace hC n hn (⟨k.val + 1, hk⟩ : Fin n) ⊓
      trailingEigenSubspace hA n hn k
  let f : W →ₗ[Real] Real := phi.domRestrict W
  have hW : 1 < Module.finrank Real W :=
    lt_of_lt_of_le Nat.one_lt_two
      (two_le_finrank_leading_succ_inf_trailing hA hC n hn k hk)
  have hker : LinearMap.ker f ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hW)
  obtain ⟨y, hy, hy0⟩ :=
    (Submodule.ne_bot_iff (LinearMap.ker f)).mp hker
  refine ⟨y.1, ?_, y.2.1, y.2.2, ?_⟩
  · intro hyval
    apply hy0
    exact Subtype.ext hyval
  · simpa [f] using hy

/-- Generic decreasing-eigenvalue interlacing across an ordered quadratic
form update which vanishes on the kernel of one linear functional. -/
theorem eigenvalues_interlace_of_quadraticForm_order_and_eq_on_ker
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E]
    {A C : E →ₗ[Real] E}
    (hA : A.IsSymmetric) (hC : C.IsSymmetric)
    (horder : ∀ x, inner Real (A x) x ≤ inner Real (C x) x)
    (phi : E →ₗ[Real] Real)
    (heq : ∀ x, phi x = 0 → inner Real (C x) x = inner Real (A x) x)
    (n : Nat) (hn : Module.finrank Real E = n) (k : Fin n) :
    hA.eigenvalues hn k ≤ hC.eigenvalues hn k ∧
      ∀ hk : k.val + 1 < n,
        hC.eigenvalues hn ⟨k.val + 1, hk⟩ ≤ hA.eigenvalues hn k := by
  constructor
  · exact ordered_eigenvalue_le_of_quadraticForm_le
      hA hC horder n hn k
  · intro hk
    obtain ⟨x, hx0, hxC, hxA, hxphi⟩ :=
      exists_ne_zero_mem_leading_succ_inf_trailing_ker
        hA hC phi n hn k hk
    unfold leadingEigenSubspace at hxC
    rw [range_restrict_eq_image] at hxC
    unfold trailingEigenSubspace at hxA
    rw [range_restrict_eq_image] at hxA
    calc
      hC.eigenvalues hn ⟨k.val + 1, hk⟩ ≤
          inner Real (C x) x / ‖x‖ ^ 2 :=
        eigenvalue_le_rayleigh_of_mem_le_span
          hC n hn ⟨k.val + 1, hk⟩ x hxC hx0
      _ = inner Real (A x) x / ‖x‖ ^ 2 := by rw [heq x hxphi]
      _ ≤ hA.eigenvalues hn k :=
        rayleigh_le_eigenvalue_of_mem_ge_span hA n hn k x hxA hx0

/-- Quadratic form of a square outer-product update. -/
theorem dotProduct_mulVec_add_smul_vecMulVec
    {index : Type*} [Fintype index]
    (A : Matrix index index Real) (c : Real)
    (v x : index → Real) :
    x ⬝ᵥ ((A + c • Matrix.vecMulVec v v) *ᵥ x) =
      x ⬝ᵥ (A *ᵥ x) + c * (v ⬝ᵥ x) ^ 2 := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, op_smul_eq_mul]
  rw [dotProduct_comm x v]
  ring

/-- Matrix Cauchy interlacing for a positive outer-product update. -/
theorem orderedEigenvalues_interlace_positive_rankOne_update
    {index : Type*} [Fintype index] [DecidableEq index]
    (A C : Matrix index index Real)
    (hA : A.IsHermitian) (hC : C.IsHermitian)
    (c : Real) (hc : 0 ≤ c) (v : index → Real)
    (hupdate : C = A + c • Matrix.vecMulVec v v)
    (k : Fin (Fintype.card index)) :
    orderedEigenvalue ⟨A, hA⟩ k ≤ orderedEigenvalue ⟨C, hC⟩ k ∧
      ∀ hk : k.val + 1 < Fintype.card index,
        orderedEigenvalue ⟨C, hC⟩ ⟨k.val + 1, hk⟩ ≤
          orderedEigenvalue ⟨A, hA⟩ k := by
  let TA := Matrix.toEuclideanLin (𝕜 := Real) A
  let TC := Matrix.toEuclideanLin (𝕜 := Real) C
  let v' : EuclideanSpace Real index := WithLp.toLp 2 v
  let phi : EuclideanSpace Real index →ₗ[Real] Real :=
    (innerSL Real v').toLinearMap
  have hTA : TA.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hTC : TC.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hC
  have hquad (x : index → Real) :
      x ⬝ᵥ (C *ᵥ x) = x ⬝ᵥ (A *ᵥ x) + c * (v ⬝ᵥ x) ^ 2 := by
    rw [hupdate]
    exact dotProduct_mulVec_add_smul_vecMulVec A c v x
  have horder : ∀ x : EuclideanSpace Real index,
      inner Real (TA x) x ≤ inner Real (TC x) x := by
    intro x
    have h := hquad (WithLp.ofLp x)
    have hsquare : 0 ≤ (v ⬝ᵥ WithLp.ofLp x) ^ 2 := sq_nonneg _
    simpa [TA, TC, EuclideanSpace.inner_eq_star_dotProduct] using
      (show (WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x) ≤
          (WithLp.ofLp x) ⬝ᵥ (C *ᵥ WithLp.ofLp x) by nlinarith)
  have heq : ∀ x : EuclideanSpace Real index, phi x = 0 →
      inner Real (TC x) x = inner Real (TA x) x := by
    intro x hx
    have hx' : v ⬝ᵥ WithLp.ofLp x = 0 := by
      have hx'' : WithLp.ofLp x ⬝ᵥ v = 0 := by
        simpa [phi, v', EuclideanSpace.inner_eq_star_dotProduct] using hx
      simpa [dotProduct_comm] using hx''
    have h := hquad (WithLp.ofLp x)
    simpa [TA, TC, EuclideanSpace.inner_eq_star_dotProduct, hx'] using h
  have hinterlace :=
    eigenvalues_interlace_of_quadraticForm_order_and_eq_on_ker
      hTA hTC horder phi heq (Fintype.card index)
        finrank_euclideanSpace k
  simpa [orderedEigenvalue, Matrix.IsHermitian.eigenvalues₀, TA, TC] using
    hinterlace

/-- If one mass is increased while all other masses are fixed, the dual
harmonic matrix is a positive rank-one update in the direction from the
larger mass configuration to the smaller mass configuration. -/
theorem dualMass_orderedEigenvalues_interlace_of_single_mass_le
    {N : Nat} [NeZero N]
    (m m' : Lattice.PositiveMassConfig N) (i : Lattice.Site N)
    (hoff : ∀ j, j ≠ i → m.mass j = m'.mass j)
    (hmass : m.mass i ≤ m'.mass i)
    (k : Fin (Fintype.card (Lattice.Site N))) :
    orderedEigenvalue (dualMassWeightedHarmonicHermitian m') k ≤
        orderedEigenvalue (dualMassWeightedHarmonicHermitian m) k ∧
      ∀ hk : k.val + 1 < Fintype.card (Lattice.Site N),
        orderedEigenvalue (dualMassWeightedHarmonicHermitian m)
            ⟨k.val + 1, hk⟩ ≤
          orderedEigenvalue (dualMassWeightedHarmonicHermitian m') k := by
  let c := (m.mass i)⁻¹ - (m'.mass i)⁻¹
  have hc : 0 ≤ c := by
    exact sub_nonneg.mpr
      ((inv_le_inv₀ (m'.mass_pos i) (m.mass_pos i)).2 hmass)
  have hsub :=
    dualMassWeightedHarmonicMatrix_sub_eq_smul_rankOne_of_eq_off
      m m' i hoff
  have hupdate : dualMassWeightedHarmonicMatrix m =
      dualMassWeightedHarmonicMatrix m' +
        c • Matrix.vecMulVec (cycleMassPerturbationVector i)
          (cycleMassPerturbationVector i) := by
    calc
      dualMassWeightedHarmonicMatrix m =
          (dualMassWeightedHarmonicMatrix m -
              dualMassWeightedHarmonicMatrix m') +
            dualMassWeightedHarmonicMatrix m' := by abel
      _ = c • Matrix.vecMulVec (cycleMassPerturbationVector i)
            (cycleMassPerturbationVector i) +
          dualMassWeightedHarmonicMatrix m' := by rw [hsub]
      _ = dualMassWeightedHarmonicMatrix m' +
          c • Matrix.vecMulVec (cycleMassPerturbationVector i)
            (cycleMassPerturbationVector i) := add_comm _ _
  exact orderedEigenvalues_interlace_positive_rankOne_update
    (dualMassWeightedHarmonicMatrix m')
    (dualMassWeightedHarmonicMatrix m)
    (dualMassWeightedHarmonicHermitian m').2
    (dualMassWeightedHarmonicHermitian m).2
    c hc (cycleMassPerturbationVector i) hupdate k

/-- Site-space harmonic form of the same single-mass interlacing statement,
transported through equality of the square Gram and dual spectra. -/
theorem harmonic_orderedEigenvalues_interlace_of_single_mass_le
    {N : Nat} [NeZero N]
    (m m' : Lattice.PositiveMassConfig N) (i : Lattice.Site N)
    (hoff : ∀ j, j ≠ i → m.mass j = m'.mass j)
    (hmass : m.mass i ≤ m'.mass i)
    (k : Fin (Fintype.card (Lattice.Site N))) :
    orderedEigenvalue (harmonicHermitian m') k ≤
        orderedEigenvalue (harmonicHermitian m) k ∧
      ∀ hk : k.val + 1 < Fintype.card (Lattice.Site N),
        orderedEigenvalue (harmonicHermitian m) ⟨k.val + 1, hk⟩ ≤
          orderedEigenvalue (harmonicHermitian m') k := by
  have hinterlace :=
    dualMass_orderedEigenvalues_interlace_of_single_mass_le
      m m' i hoff hmass k
  simpa only [orderedEigenvalue_harmonic_eq_dual] using hinterlace

end

end ArchonPhysics.PositiveRankOneEigenvalueInterlacing
