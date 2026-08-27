import ArchonPhysics.MassWeightedCycleBridge
import ArchonPhysics.MeasurableOrderedModeCoupling
import ArchonPhysics.OrderedSpectrumContinuity
import ArchonPhysics.RandomEnsemble

/-!
# Uniform comparison with the clean periodic harmonic spectrum

Let `D` be the periodic forward-difference matrix and let
`D_m = D diag(m_i^(-1/2))`.  The random mass-weighted harmonic matrix is
`D_mᵀ D_m`, while its edge-space dual is `D_m D_mᵀ`.  The square-matrix
identity `charpoly (AB) = charpoly (BA)` identifies their complete decreasing
ordered spectra, including the zero mode and all multiplicities.

The dual quadratic form is

`sum_i m_i⁻¹ ((Dᵀ x)_i)²`.

Consequently coordinatewise mass bounds `mLower ≤ m_i ≤ mUpper` sandwich it
between `mUpper⁻¹` and `mLower⁻¹` times the clean dual form.  A finite
dimensional Courant--Fischer monotonicity lemma transports that pointwise
quadratic-form sandwich to every decreasing ordered eigenvalue.  For the
frozen support `[4/5, 6/5]`, the comparison factors are `5/6` and `5/4`.

No explicit sine formula, integrated density of states, localization,
probability limit, or thermalization conclusion is asserted.
-/

namespace ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison

open ArchonPhysics
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSpectrumWeyl
open Module RCLike InnerProductSpace
open scoped Matrix

noncomputable section

private theorem range_restrict_eq_image {alpha beta : Type*}
    (f : alpha → beta) (s : Set alpha) :
    Set.range (fun i : s ↦ f i.1) = f '' s := by
  ext y
  simp

/-- Quadratic-form order of real symmetric operators implies coordinatewise
order of their decreasing eigenvalue lists. -/
theorem ordered_eigenvalue_le_of_quadraticForm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E]
    {T S : E →ₗ[Real] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hquad : ∀ x, inner Real (T x) x ≤ inner Real (S x) x)
    (n : Nat) (hn : Module.finrank Real E = n) (k : Fin n) :
    hT.eigenvalues hn k ≤ hS.eigenvalues hn k := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff
    (leadingEigenSubspace hT n hn k ⊓ trailingEigenSubspace hS n hn k)).mp
      (leading_inf_trailing_ne_bot hT hS n hn k)
  have hxT : x ∈ leadingEigenSubspace hT n hn k := hx.1
  have hxS : x ∈ trailingEigenSubspace hS n hn k := hx.2
  unfold leadingEigenSubspace at hxT
  rw [range_restrict_eq_image] at hxT
  unfold trailingEigenSubspace at hxS
  rw [range_restrict_eq_image] at hxS
  have hTx :=
    eigenvalue_le_rayleigh_of_mem_le_span hT n hn k x hxT hx0
  have hSx :=
    rayleigh_le_eigenvalue_of_mem_ge_span hS n hn k x hxS hx0
  have hden : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  have hbetween : inner Real (T x) x / ‖x‖ ^ 2 ≤
      inner Real (S x) x / ‖x‖ ^ 2 :=
    (div_le_div_iff_of_pos_right hden).2 (hquad x)
  exact hTx.trans (hbetween.trans hSx)

/-- Upper comparison with a nonnegative scalar multiple of a quadratic form. -/
theorem ordered_eigenvalue_le_mul_of_quadraticForm_le_mul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E]
    {T S : E →ₗ[Real] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (c : Real) (hc : 0 ≤ c)
    (hquad : ∀ x, inner Real (T x) x ≤ c * inner Real (S x) x)
    (n : Nat) (hn : Module.finrank Real E = n) (k : Fin n) :
    hT.eigenvalues hn k ≤ c * hS.eigenvalues hn k := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff
    (leadingEigenSubspace hT n hn k ⊓ trailingEigenSubspace hS n hn k)).mp
      (leading_inf_trailing_ne_bot hT hS n hn k)
  have hxT : x ∈ leadingEigenSubspace hT n hn k := hx.1
  have hxS : x ∈ trailingEigenSubspace hS n hn k := hx.2
  unfold leadingEigenSubspace at hxT
  rw [range_restrict_eq_image] at hxT
  unfold trailingEigenSubspace at hxS
  rw [range_restrict_eq_image] at hxS
  have hTx :=
    eigenvalue_le_rayleigh_of_mem_le_span hT n hn k x hxT hx0
  have hSx :=
    rayleigh_le_eigenvalue_of_mem_ge_span hS n hn k x hxS hx0
  have hden : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  calc
    hT.eigenvalues hn k ≤ inner Real (T x) x / ‖x‖ ^ 2 := hTx
    _ ≤ (c * inner Real (S x) x) / ‖x‖ ^ 2 :=
      (div_le_div_iff_of_pos_right hden).2 (hquad x)
    _ = c * (inner Real (S x) x / ‖x‖ ^ 2) := by ring
    _ ≤ c * hS.eigenvalues hn k := mul_le_mul_of_nonneg_left hSx hc

/-- Lower comparison with a nonnegative scalar multiple of a quadratic form. -/
theorem mul_ordered_eigenvalue_le_of_mul_quadraticForm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E]
    {T S : E →ₗ[Real] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (c : Real) (hc : 0 ≤ c)
    (hquad : ∀ x, c * inner Real (S x) x ≤ inner Real (T x) x)
    (n : Nat) (hn : Module.finrank Real E = n) (k : Fin n) :
    c * hS.eigenvalues hn k ≤ hT.eigenvalues hn k := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff
    (leadingEigenSubspace hS n hn k ⊓ trailingEigenSubspace hT n hn k)).mp
      (leading_inf_trailing_ne_bot hS hT n hn k)
  have hxS : x ∈ leadingEigenSubspace hS n hn k := hx.1
  have hxT : x ∈ trailingEigenSubspace hT n hn k := hx.2
  unfold leadingEigenSubspace at hxS
  rw [range_restrict_eq_image] at hxS
  unfold trailingEigenSubspace at hxT
  rw [range_restrict_eq_image] at hxT
  have hSx :=
    eigenvalue_le_rayleigh_of_mem_le_span hS n hn k x hxS hx0
  have hTx :=
    rayleigh_le_eigenvalue_of_mem_ge_span hT n hn k x hxT hx0
  have hden : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  calc
    c * hS.eigenvalues hn k ≤
        c * (inner Real (S x) x / ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hSx hc
    _ = (c * inner Real (S x) x) / ‖x‖ ^ 2 := by ring
    _ ≤ inner Real (T x) x / ‖x‖ ^ 2 :=
      (div_le_div_iff_of_pos_right hden).2 (hquad x)
    _ ≤ hT.eigenvalues hn k := hTx

/-- Matrix form of decreasing ordered-eigenvalue monotonicity. -/
theorem orderedEigenvalue_le_of_dotProduct_mulVec_le
    {index : Type*} [Fintype index] [DecidableEq index]
    (A B : Matrix index index Real)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hquad : ∀ x : index → Real, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x))
    (k : Fin (Fintype.card index)) :
    orderedEigenvalue ⟨A, hA⟩ k ≤ orderedEigenvalue ⟨B, hB⟩ k := by
  let TA := Matrix.toEuclideanLin (𝕜 := Real) A
  let TB := Matrix.toEuclideanLin (𝕜 := Real) B
  have hTA : TA.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hTB : TB.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hquad' : ∀ x : EuclideanSpace Real index,
      inner Real (TA x) x ≤ inner Real (TB x) x := by
    intro x
    simpa [TA, TB, EuclideanSpace.inner_eq_star_dotProduct] using
      hquad (WithLp.ofLp x)
  have h := ordered_eigenvalue_le_of_quadraticForm_le hTA hTB hquad'
    (Fintype.card index) finrank_euclideanSpace k
  simpa [orderedEigenvalue, Matrix.IsHermitian.eigenvalues₀, TA, TB] using h

/-- Matrix upper comparison by a scalar multiple. -/
theorem orderedEigenvalue_le_mul_of_dotProduct_mulVec_le_mul
    {index : Type*} [Fintype index] [DecidableEq index]
    (A B : Matrix index index Real)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (c : Real) (hc : 0 ≤ c)
    (hquad : ∀ x : index → Real,
      x ⬝ᵥ (A *ᵥ x) ≤ c * (x ⬝ᵥ (B *ᵥ x)))
    (k : Fin (Fintype.card index)) :
    orderedEigenvalue ⟨A, hA⟩ k ≤ c * orderedEigenvalue ⟨B, hB⟩ k := by
  let TA := Matrix.toEuclideanLin (𝕜 := Real) A
  let TB := Matrix.toEuclideanLin (𝕜 := Real) B
  have hTA : TA.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hTB : TB.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hquad' : ∀ x : EuclideanSpace Real index,
      inner Real (TA x) x ≤ c * inner Real (TB x) x := by
    intro x
    simpa [TA, TB, EuclideanSpace.inner_eq_star_dotProduct] using
      hquad (WithLp.ofLp x)
  have h := ordered_eigenvalue_le_mul_of_quadraticForm_le_mul
    hTA hTB c hc hquad' (Fintype.card index) finrank_euclideanSpace k
  simpa [orderedEigenvalue, Matrix.IsHermitian.eigenvalues₀, TA, TB] using h

/-- Matrix lower comparison by a scalar multiple. -/
theorem mul_orderedEigenvalue_le_of_mul_dotProduct_mulVec_le
    {index : Type*} [Fintype index] [DecidableEq index]
    (A B : Matrix index index Real)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (c : Real) (hc : 0 ≤ c)
    (hquad : ∀ x : index → Real,
      c * (x ⬝ᵥ (B *ᵥ x)) ≤ x ⬝ᵥ (A *ᵥ x))
    (k : Fin (Fintype.card index)) :
    c * orderedEigenvalue ⟨B, hB⟩ k ≤ orderedEigenvalue ⟨A, hA⟩ k := by
  let TA := Matrix.toEuclideanLin (𝕜 := Real) A
  let TB := Matrix.toEuclideanLin (𝕜 := Real) B
  have hTA : TA.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hTB : TB.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hquad' : ∀ x : EuclideanSpace Real index,
      c * inner Real (TB x) x ≤ inner Real (TA x) x := by
    intro x
    simpa [TA, TB, EuclideanSpace.inner_eq_star_dotProduct] using
      hquad (WithLp.ofLp x)
  have h := mul_ordered_eigenvalue_le_of_mul_quadraticForm_le
    hTA hTB c hc hquad' (Fintype.card index) finrank_euclideanSpace k
  simpa [orderedEigenvalue, Matrix.IsHermitian.eigenvalues₀, TA, TB] using h

/-- Square Gram matrices `DᵀD` and `DDᵀ` have identical complete decreasing
ordered eigenvalue lists. -/
theorem orderedEigenvalue_transpose_mul_self_eq_mul_transpose
    {index : Type*} [Fintype index] [DecidableEq index]
    (D : Matrix index index Real) (k : Fin (Fintype.card index)) :
    orderedEigenvalue
        ⟨Matrix.transpose D * D, by
          simpa using Matrix.isHermitian_conjTranspose_mul_self D⟩ k =
      orderedEigenvalue
        ⟨D * Matrix.transpose D, by
          simpa using Matrix.isHermitian_mul_conjTranspose_self D⟩ k := by
  let hA : (Matrix.transpose D * D).IsHermitian := by
    simpa using Matrix.isHermitian_conjTranspose_mul_self D
  let hB : (D * Matrix.transpose D).IsHermitian := by
    simpa using Matrix.isHermitian_mul_conjTranspose_self D
  have heigenvalues : hA.eigenvalues = hB.eigenvalues :=
    (hA.eigenvalues_eq_eigenvalues_iff hB).2
      (Matrix.charpoly_mul_comm (Matrix.transpose D) D)
  have hcomponent := congrFun heigenvalues
    ((Fintype.equivOfCardEq (Fintype.card_fin _)) k)
  simpa [orderedEigenvalue, Matrix.IsHermitian.eigenvalues, hA, hB] using
    hcomponent

/-- Edge-space dual of the random mass-weighted harmonic matrix. -/
def dualMassWeightedHarmonicMatrix
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    Matrix (Lattice.Site N) (Lattice.Site N) Real :=
  massWeightedDifferenceMatrix m *
    Matrix.transpose (massWeightedDifferenceMatrix m)

/-- Standard clean periodic harmonic matrix `DᵀD`. -/
def cleanCycleHarmonicMatrix (N : Nat) [NeZero N] :
    Matrix (Lattice.Site N) (Lattice.Site N) Real :=
  Matrix.transpose differenceMatrix * differenceMatrix

/-- Edge-space clean dual `DDᵀ`. -/
def cleanCycleDualHarmonicMatrix (N : Nat) [NeZero N] :
    Matrix (Lattice.Site N) (Lattice.Site N) Real :=
  differenceMatrix * Matrix.transpose differenceMatrix

/-- Hermitian bundle of the random dual. -/
def dualMassWeightedHarmonicHermitian
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    HermitianMatrix (Lattice.Site N) :=
  ⟨dualMassWeightedHarmonicMatrix m, by
    simpa [dualMassWeightedHarmonicMatrix] using
      Matrix.isHermitian_mul_conjTranspose_self
        (massWeightedDifferenceMatrix m)⟩

/-- Hermitian bundle of the standard clean cycle. -/
def cleanCycleHarmonicHermitian (N : Nat) [NeZero N] :
    HermitianMatrix (Lattice.Site N) :=
  ⟨cleanCycleHarmonicMatrix N, by
    simpa [cleanCycleHarmonicMatrix] using
      Matrix.isHermitian_conjTranspose_mul_self
        (differenceMatrix : Matrix (Lattice.Site N) (Lattice.Site N) Real)⟩

/-- Hermitian bundle of the clean edge-space dual. -/
def cleanCycleDualHarmonicHermitian (N : Nat) [NeZero N] :
    HermitianMatrix (Lattice.Site N) :=
  ⟨cleanCycleDualHarmonicMatrix N, by
    simpa [cleanCycleDualHarmonicMatrix] using
      Matrix.isHermitian_mul_conjTranspose_self
        (differenceMatrix : Matrix (Lattice.Site N) (Lattice.Site N) Real)⟩

/-- Random site-space and edge-space Gram matrices have the same complete
ordered spectrum. -/
theorem orderedEigenvalue_harmonic_eq_dual
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k : Fin (Fintype.card (Lattice.Site N))) :
    orderedEigenvalue (harmonicHermitian m) k =
      orderedEigenvalue (dualMassWeightedHarmonicHermitian m) k := by
  simpa [harmonicHermitian, massWeightedHarmonicMatrix,
    dualMassWeightedHarmonicHermitian, dualMassWeightedHarmonicMatrix] using
    orderedEigenvalue_transpose_mul_self_eq_mul_transpose
      (massWeightedDifferenceMatrix m) k

/-- The two clean Gram presentations have the same complete ordered
spectrum. -/
theorem orderedEigenvalue_clean_eq_cleanDual
    (N : Nat) [NeZero N] (k : Fin (Fintype.card (Lattice.Site N))) :
    orderedEigenvalue (cleanCycleHarmonicHermitian N) k =
      orderedEigenvalue (cleanCycleDualHarmonicHermitian N) k := by
  simpa [cleanCycleHarmonicHermitian, cleanCycleHarmonicMatrix,
    cleanCycleDualHarmonicHermitian, cleanCycleDualHarmonicMatrix] using
    orderedEigenvalue_transpose_mul_self_eq_mul_transpose
      (differenceMatrix : Matrix (Lattice.Site N) (Lattice.Site N) Real) k

/-- Exact weighted-cycle quadratic-form formula. -/
theorem weightedCycleLaplacian_quadraticForm
    {N : Nat} [NeZero N] (w : Lattice.Site N → Real)
    (x : Lattice.Configuration N) :
    x ⬝ᵥ (weightedCycleLaplacian w *ᵥ x) =
      ∑ i : Lattice.Site N,
        w i * (Matrix.mulVec (Matrix.transpose differenceMatrix) x i) ^ 2 := by
  let y : Lattice.Configuration N :=
    Matrix.mulVec (Matrix.transpose differenceMatrix) x
  let W : Matrix (Lattice.Site N) (Lattice.Site N) Real :=
    Matrix.diagonal w
  calc
    x ⬝ᵥ (weightedCycleLaplacian w *ᵥ x) =
        x ⬝ᵥ (differenceMatrix *ᵥ (W *ᵥ y)) := by
      simp only [weightedCycleLaplacian, y, W, ← Matrix.mulVec_mulVec,
        Matrix.mul_assoc]
    _ = (W *ᵥ y) ⬝ᵥ y := by
      simpa [y] using
        (Matrix.dotProduct_transpose_mulVec
          (Matrix.transpose differenceMatrix) x (W *ᵥ y))
    _ = ∑ i : Lattice.Site N, w i * y i ^ 2 := by
      simp only [W, Matrix.mulVec_diagonal, dotProduct, pow_two]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = ∑ i : Lattice.Site N,
        w i * (Matrix.mulVec (Matrix.transpose differenceMatrix) x i) ^ 2 := rfl

/-- Coordinatewise mass bounds give the exact dual quadratic-form sandwich. -/
theorem weightedCycleLaplacian_quadratic_sandwich
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (mLower mUpper : Real) (hmLower : 0 < mLower)
    (hmUpper : 0 < mUpper)
    (hmassLower : ∀ i, mLower ≤ m.mass i)
    (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (x : Lattice.Configuration N) :
    mUpper⁻¹ *
        (x ⬝ᵥ (weightedCycleLaplacian (fun _ ↦ 1) *ᵥ x)) ≤
      x ⬝ᵥ (weightedCycleLaplacian (fun i ↦ (m.mass i)⁻¹) *ᵥ x) ∧
    x ⬝ᵥ (weightedCycleLaplacian (fun i ↦ (m.mass i)⁻¹) *ᵥ x) ≤
      mLower⁻¹ *
        (x ⬝ᵥ (weightedCycleLaplacian (fun _ ↦ 1) *ᵥ x)) := by
  let y : Lattice.Configuration N :=
    Matrix.mulVec (Matrix.transpose differenceMatrix) x
  rw [weightedCycleLaplacian_quadraticForm,
    weightedCycleLaplacian_quadraticForm]
  simp only [one_mul]
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    exact mul_le_mul_of_nonneg_right
      ((inv_le_inv₀ hmUpper (m.mass_pos i)).2 (hmassUpper i))
      (sq_nonneg (y i))
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    exact mul_le_mul_of_nonneg_right
      ((inv_le_inv₀ (m.mass_pos i) hmLower).2 (hmassLower i))
      (sq_nonneg (y i))

/-- The random dual quadratic form is sandwiched by scalar multiples of the
clean dual quadratic form. -/
theorem dualMassWeightedHarmonic_quadratic_sandwich
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (mLower mUpper : Real) (hmLower : 0 < mLower)
    (hmUpper : 0 < mUpper)
    (hmassLower : ∀ i, mLower ≤ m.mass i)
    (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (x : Lattice.Configuration N) :
    mUpper⁻¹ * (x ⬝ᵥ (cleanCycleDualHarmonicMatrix N *ᵥ x)) ≤
      x ⬝ᵥ (dualMassWeightedHarmonicMatrix m *ᵥ x) ∧
    x ⬝ᵥ (dualMassWeightedHarmonicMatrix m *ᵥ x) ≤
      mLower⁻¹ * (x ⬝ᵥ (cleanCycleDualHarmonicMatrix N *ᵥ x)) := by
  rw [dualMassWeightedHarmonicMatrix,
    massWeighted_selfTranspose_eq_weightedCycleLaplacian]
  simpa [cleanCycleDualHarmonicMatrix, weightedCycleLaplacian] using
    weightedCycleLaplacian_quadratic_sandwich
      m mLower mUpper hmLower hmUpper hmassLower hmassUpper x

/-- Every decreasing random harmonic eigenvalue is trapped between the same
clean-cycle eigenvalue times the two inverse mass bounds. -/
theorem orderedEigenvalue_harmonic_compare_clean
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (mLower mUpper : Real) (hmLower : 0 < mLower)
    (hmUpper : 0 < mUpper)
    (hmassLower : ∀ i, mLower ≤ m.mass i)
    (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (k : Fin (Fintype.card (Lattice.Site N))) :
    mUpper⁻¹ * orderedEigenvalue (cleanCycleHarmonicHermitian N) k ≤
      orderedEigenvalue (harmonicHermitian m) k ∧
    orderedEigenvalue (harmonicHermitian m) k ≤
      mLower⁻¹ * orderedEigenvalue (cleanCycleHarmonicHermitian N) k := by
  have hsandwich := dualMassWeightedHarmonic_quadratic_sandwich
    m mLower mUpper hmLower hmUpper hmassLower hmassUpper
  have hLowerNonneg : 0 ≤ mLower⁻¹ := inv_nonneg.mpr hmLower.le
  have hUpperNonneg : 0 ≤ mUpper⁻¹ := inv_nonneg.mpr hmUpper.le
  have hlower : mUpper⁻¹ *
      orderedEigenvalue (cleanCycleDualHarmonicHermitian N) k ≤
      orderedEigenvalue (dualMassWeightedHarmonicHermitian m) k :=
    mul_orderedEigenvalue_le_of_mul_dotProduct_mulVec_le
      (dualMassWeightedHarmonicMatrix m) (cleanCycleDualHarmonicMatrix N)
      (dualMassWeightedHarmonicHermitian m).property
      (cleanCycleDualHarmonicHermitian N).property
      mUpper⁻¹ hUpperNonneg (fun x ↦ (hsandwich x).1) k
  have hupper :
      orderedEigenvalue (dualMassWeightedHarmonicHermitian m) k ≤
      mLower⁻¹ * orderedEigenvalue (cleanCycleDualHarmonicHermitian N) k :=
    orderedEigenvalue_le_mul_of_dotProduct_mulVec_le_mul
      (dualMassWeightedHarmonicMatrix m) (cleanCycleDualHarmonicMatrix N)
      (dualMassWeightedHarmonicHermitian m).property
      (cleanCycleDualHarmonicHermitian N).property
      mLower⁻¹ hLowerNonneg (fun x ↦ (hsandwich x).2) k
  rw [← orderedEigenvalue_harmonic_eq_dual m k,
    ← orderedEigenvalue_clean_eq_cleanDual N k] at hlower hupper
  exact ⟨hlower, hupper⟩

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Frozen-support specialization: every iid realization is squeezed between
`5/6` and `5/4` times the corresponding clean ordered eigenvalue. -/
theorem iid_orderedEigenvalue_harmonic_compare_clean
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (k : Fin (Fintype.card (Lattice.Site N))) :
    (5 / 6 : Real) * orderedEigenvalue (cleanCycleHarmonicHermitian N) k ≤
      orderedEigenvalue
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := N) omega)) k ∧
    orderedEigenvalue
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := N) omega)) k ≤
      (5 / 4 : Real) * orderedEigenvalue
        (cleanCycleHarmonicHermitian N) k := by
  simpa [RandomEnsemble.massLower, RandomEnsemble.massUpper] using
    orderedEigenvalue_harmonic_compare_clean
      (ensemble.restrictPositiveMass (N := N) omega)
      RandomEnsemble.massLower RandomEnsemble.massUpper
      RandomEnsemble.massLower_pos
      (RandomEnsemble.massLower_pos.trans_le
        RandomEnsemble.massLower_le_massUpper)
      (fun i ↦ by simpa using (ensemble.mass_mem_support i.val omega).1)
      (fun i ↦ by simpa using (ensemble.mass_mem_support i.val omega).2) k

end

end ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison
