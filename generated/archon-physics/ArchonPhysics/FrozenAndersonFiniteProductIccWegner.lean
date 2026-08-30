import ArchonPhysics.FrozenAndersonFiniteProductSmoothedTraceWegner
import ArchonPhysics.OrderedSpectrumContinuity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Closed-interval finite-volume Wegner estimate for frozen iid Anderson masses

This module removes the eta smoothing from the finite-product trace estimate.
It diagonalizes the real Hermitian Anderson Hamiltonian after embedding its
orthogonal eigenbasis into the complex field, identifies the imaginary
resolvent trace with a finite sum of Poisson kernels, and integrates over a
slightly enlarged energy interval.

For an eigenvalue in the closed interval `[a,b]`, that energy integral is at
least `2 * arctan (delta / eta)`. Explicit mass-energy Fubini then applies
the already proved iid `Uniform[4/5,6/5]` smoothed trace estimate. The scalar
limits `eta -> 0` and `delta -> 0` give the sharp closed-endpoint bound

`E rank(1_[a,b](H)) <= (n+1) * (5 / (2 * |lambda|)) * (b-a)`.

The spectral projector constructed below is Hermitian and idempotent; its
trace is the real eigenvalue count and its matrix rank is the corresponding
natural-number count. No Stone formula, Markov inequality, localization
estimate, custom axiom, or endpoint atom assumption is used.
-/

namespace ArchonPhysics.FrozenAndersonFiniteProductIccWegner

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.FrozenAndersonOneSitePoissonAveraging
open ArchonPhysics.FrozenAndersonFiniteProductSmoothedTraceWegner
open Matrix MeasureTheory Set Filter
open scoped BigOperators ENNReal Matrix Interval Topology

noncomputable section



variable {index : Type*} [Fintype index] [DecidableEq index]

def mappedEigenvectorUnitary
    (H : Matrix index index Real) (hH : H.IsHermitian) : Matrix index index Complex :=
  (hH.eigenvectorUnitary : Matrix index index Real).map Complex.ofRealHom

theorem mappedEigenvectorUnitary_mul_star
    (H : Matrix index index Real) (hH : H.IsHermitian) :
    mappedEigenvectorUnitary H hH * star (mappedEigenvectorUnitary H hH) = 1 := by
  let U : Matrix index index Real := hH.eigenvectorUnitary
  have hstar : star (U.map Complex.ofRealHom) = (star U).map Complex.ofRealHom := by
    ext i j
    simp [star_apply]
  have hreal : U * star U = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hmapped := congrArg
    (fun A : Matrix index index Real => A.map Complex.ofRealHom) hreal
  rw [Matrix.map_mul] at hmapped
  unfold mappedEigenvectorUnitary
  change U.map Complex.ofRealHom * star (U.map Complex.ofRealHom) = 1
  rw [hstar]
  simpa using hmapped

theorem mappedEigenvectorUnitary_star_mul
    (H : Matrix index index Real) (hH : H.IsHermitian) :
    star (mappedEigenvectorUnitary H hH) * mappedEigenvectorUnitary H hH = 1 := by
  let U : Matrix index index Real := hH.eigenvectorUnitary
  have hstar : star (U.map Complex.ofRealHom) = (star U).map Complex.ofRealHom := by
    ext i j
    simp [star_apply]
  have hreal : star U * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hmapped := congrArg
    (fun A : Matrix index index Real => A.map Complex.ofRealHom) hreal
  rw [Matrix.map_mul] at hmapped
  unfold mappedEigenvectorUnitary
  change star (U.map Complex.ofRealHom) * U.map Complex.ofRealHom = 1
  rw [hstar]
  simpa using hmapped

theorem map_spectral_theorem
    (H : Matrix index index Real) (hH : H.IsHermitian) :
    H.map Complex.ofRealHom =
      mappedEigenvectorUnitary H hH *
        Matrix.diagonal (fun i => (hH.eigenvalues i : Complex)) *
          star (mappedEigenvectorUnitary H hH) := by
  let U : Matrix index index Real := hH.eigenvectorUnitary
  have hstar : star (U.map Complex.ofRealHom) = (star U).map Complex.ofRealHom := by
    ext i j
    simp [star_apply]
  have hs := congrArg
    (fun A : Matrix index index Real => A.map Complex.ofRealHom)
    hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  change H.map Complex.ofRealHom =
    (U * Matrix.diagonal hH.eigenvalues * star U).map Complex.ofRealHom at hs
  calc
    H.map Complex.ofRealHom =
        (U * Matrix.diagonal hH.eigenvalues * star U).map Complex.ofRealHom := hs
    _ = U.map Complex.ofRealHom *
        Matrix.diagonal (fun i => (hH.eigenvalues i : Complex)) *
          (star U).map Complex.ofRealHom := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (by simp)]
      rfl
    _ = mappedEigenvectorUnitary H hH *
        Matrix.diagonal (fun i => (hH.eigenvalues i : Complex)) *
          star (mappedEigenvectorUnitary H hH) := by
      unfold mappedEigenvectorUnitary
      rw [hstar]

theorem complexHermitianResolventMatrix_eq_conjugate_diagonal
    (H : Matrix index index Real) (hH : H.IsHermitian)
    (z : Complex) :
    complexHermitianResolventMatrix (H.map Complex.ofRealHom) z =
      mappedEigenvectorUnitary H hH *
        Matrix.diagonal (fun i => z - (hH.eigenvalues i : Complex)) *
          star (mappedEigenvectorUnitary H hH) := by
  let U := mappedEigenvectorUnitary H hH
  have hU : U * star U = 1 := mappedEigenvectorUnitary_mul_star H hH
  have hzU : U * (z • (1 : Matrix index index Complex)) * star U = z • 1 := by
    calc
      U * (z • (1 : Matrix index index Complex)) * star U =
          (z • U) * star U := by rw [Matrix.mul_smul]; simp
      _ = z • (U * star U) := by rw [Matrix.smul_mul]
      _ = z • 1 := by rw [hU]
  have hdiag : z • (1 : Matrix index index Complex) -
      Matrix.diagonal (fun i => (hH.eigenvalues i : Complex)) =
      Matrix.diagonal (fun i => z - (hH.eigenvalues i : Complex)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  unfold complexHermitianResolventMatrix
  rw [map_spectral_theorem H hH]
  change z • 1 - U * Matrix.diagonal (fun i => (hH.eigenvalues i : Complex)) * star U = _
  rw [← hzU]
  calc
    U * (z • (1 : Matrix index index Complex)) * star U -
        U * Matrix.diagonal (fun i => (hH.eigenvalues i : Complex)) * star U =
      U * (z • (1 : Matrix index index Complex) -
        Matrix.diagonal (fun i => (hH.eigenvalues i : Complex))) * star U := by
          noncomm_ring
    _ = U * Matrix.diagonal (fun i => z - (hH.eigenvalues i : Complex)) * star U := by
      rw [hdiag]

theorem complexHermitianResolventMatrix_inv_eq_conjugate_diagonal
    (H : Matrix index index Real) (hH : H.IsHermitian)
    (z : Complex) (hz : z.im ≠ 0) :
    (complexHermitianResolventMatrix (H.map Complex.ofRealHom) z)⁻¹ =
      mappedEigenvectorUnitary H hH *
        Matrix.diagonal (fun i => (z - (hH.eigenvalues i : Complex))⁻¹) *
          star (mappedEigenvectorUnitary H hH) := by
  let U := mappedEigenvectorUnitary H hH
  let D := Matrix.diagonal (fun i => z - (hH.eigenvalues i : Complex))
  let Dinv := Matrix.diagonal (fun i => (z - (hH.eigenvalues i : Complex))⁻¹)
  have hU : U * star U = 1 := mappedEigenvectorUnitary_mul_star H hH
  have hstarU : star U * U = 1 := mappedEigenvectorUnitary_star_mul H hH
  have hne : forall i, z - (hH.eigenvalues i : Complex) ≠ 0 := by
    intro i hi
    apply hz
    calc
      z.im = (z - (hH.eigenvalues i : Complex)).im := by simp
      _ = 0 := by rw [hi]; simp
  have hDDinv : D * Dinv = 1 := by
    unfold D Dinv
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hne]
    · simp [hij]
  have hright :
      complexHermitianResolventMatrix (H.map Complex.ofRealHom) z *
          (U * Dinv * star U) = 1 := by
    rw [complexHermitianResolventMatrix_eq_conjugate_diagonal H hH z]
    change (U * D * star U) * (U * Dinv * star U) = 1
    calc
      (U * D * star U) * (U * Dinv * star U) =
          U * D * (star U * U) * Dinv * star U := by noncomm_ring
      _ = U * D * Dinv * star U := by rw [hstarU]; simp
      _ = U * (D * Dinv) * star U := by noncomm_ring
      _ = 1 := by rw [hDDinv]; simpa using hU
  exact Matrix.inv_eq_right_inv hright

theorem trace_complexHermitianResolventMatrix_inv_eq_sum
    (H : Matrix index index Real) (hH : H.IsHermitian)
    (z : Complex) (hz : z.im ≠ 0) :
    Matrix.trace (complexHermitianResolventMatrix (H.map Complex.ofRealHom) z)⁻¹ =
      ∑ i : index, (z - (hH.eigenvalues i : Complex))⁻¹ := by
  rw [complexHermitianResolventMatrix_inv_eq_conjugate_diagonal H hH z hz]
  rw [Matrix.trace_mul_cycle]
  rw [mappedEigenvectorUnitary_star_mul H hH]
  simp

theorem finiteAndersonEtaSmoothedTrace_eq_sum_poisson
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda energy eta : Real) (mass : index -> Real) (heta : 0 < eta) :
    finiteAndersonEtaSmoothedTrace background lambda energy eta mass =
      ∑ i : index, realLinePoissonKernel energy eta
        ((finiteAndersonHamiltonian_isHermitian
          background hbackground lambda mass).eigenvalues i) := by
  let H := finiteAndersonHamiltonian background lambda mass
  have hH : H.IsHermitian :=
    finiteAndersonHamiltonian_isHermitian background hbackground lambda mass
  unfold finiteAndersonEtaSmoothedTrace finiteAndersonSmoothedTrace finiteAndersonShiftedMatrix
  change -(Matrix.trace (complexHermitianResolventMatrix
    (H.map Complex.ofRealHom)
    ((energy : Complex) + (eta : Complex) * Complex.I))⁻¹).im = _
  rw [trace_complexHermitianResolventMatrix_inv_eq_sum H hH
    ((energy : Complex) + (eta : Complex) * Complex.I) (by simpa using heta.ne')]
  rw [Complex.im_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hzre : ((energy : Complex) + (eta : Complex) * Complex.I).re = energy := by simp
  have hzim : ((energy : Complex) + (eta : Complex) * Complex.I).im = eta := by simp
  simpa only [hzre, hzim] using
    neg_im_inv_sub_real_eq_realLinePoissonKernel
      ((energy : Complex) + (eta : Complex) * Complex.I)
      (hH.eigenvalues i)

theorem realLinePoissonKernel_symmetric (center eta x : Real) :
    realLinePoissonKernel center eta x = realLinePoissonKernel x eta center := by
  unfold realLinePoissonKernel
  congr 1
  ring

theorem intervalIntegral_realLinePoissonKernel_symmetric
    (center eta delta : Real) :
    (∫ energy in center - delta..center + delta,
      realLinePoissonKernel energy eta center) =
      2 * Real.arctan (delta / eta) := by
  have htranslate := intervalIntegral.integral_comp_add_right
    (fun energy : Real => realLinePoissonKernel energy eta center) center
    (a := -delta) (b := delta)
  have hshift :
      (∫ energy in center - delta..center + delta,
        realLinePoissonKernel energy eta center) =
      ∫ x in -delta..delta,
        realLinePoissonKernel (x + center) eta center := by
    symm
    convert htranslate using 1; ring_nf
  rw [hshift]
  have hbasic := integral_div_sq_add_sq
    (a := -delta) (b := delta) (c := eta)
  calc
    (∫ x in -delta..delta,
        realLinePoissonKernel (x + center) eta center) =
        ∫ x in -delta..delta, eta / (eta ^ 2 + x ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x _
      unfold realLinePoissonKernel
      ring
    _ = Real.arctan (delta / eta) - Real.arctan (-delta / eta) := hbasic
    _ = 2 * Real.arctan (delta / eta) := by
      rw [show -delta / eta = -(delta / eta) by ring]
      rw [Real.arctan_neg]
      ring

theorem two_mul_arctan_le_intervalIntegral_realLinePoissonKernel
    {a b center eta delta : Real}
    (_hab : a <= b) (hcenter : center ∈ Set.Icc a b)
    (heta : 0 < eta) (hdelta : 0 <= delta) :
    2 * Real.arctan (delta / eta) <=
      ∫ energy in a - delta..b + delta,
        realLinePoissonKernel energy eta center := by
  rw [← intervalIntegral_realLinePoissonKernel_symmetric center eta delta]
  apply intervalIntegral.integral_mono_interval (μ := volume)
  · linarith [hcenter.1]
  · linarith
  · linarith [hcenter.2]
  · filter_upwards [] with energy
    exact realLinePoissonKernel_nonneg energy center heta.le
  · rw [show (fun energy => realLinePoissonKernel energy eta center) =
        realLinePoissonKernel center eta by
      funext energy
      exact realLinePoissonKernel_symmetric energy eta center]
    exact (continuous_realLinePoissonKernel center eta heta.ne').intervalIntegrable
      (μ := volume) (a - delta) (b + delta)

variable {index : Type*} [Fintype index] [DecidableEq index]

def finiteAndersonHermitianSample
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda : Real) (mass : index -> Real) : HermitianMatrix index :=
  ⟨finiteAndersonHamiltonian background lambda mass,
    finiteAndersonHamiltonian_isHermitian background hbackground lambda mass⟩

theorem continuous_finiteAndersonHermitianSample
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda : Real) :
    Continuous (finiteAndersonHermitianSample background hbackground lambda) := by
  apply Continuous.subtype_mk
  exact continuous_finiteAndersonHamiltonian background lambda

theorem continuous_finiteAndersonEigenvalue
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda : Real) (i : index) :
    Continuous fun mass : index -> Real =>
      (finiteAndersonHamiltonian_isHermitian
        background hbackground lambda mass).eigenvalues i := by
  let k : Fin (Fintype.card index) :=
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i
  have hcont := (continuous_orderedEigenvalue k).comp
    (continuous_finiteAndersonHermitianSample background hbackground lambda)
  change Continuous (fun mass => orderedEigenvalue
    (finiteAndersonHermitianSample background hbackground lambda mass) k) at hcont
  exact hcont

def finiteAndersonIccEigenvalueCount
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda a b : Real) (mass : index -> Real) : Real :=
  ∑ i : index, if
      (finiteAndersonHamiltonian_isHermitian
        background hbackground lambda mass).eigenvalues i ∈ Set.Icc a b
    then 1 else 0

theorem measurable_finiteAndersonIccEigenvalueCount
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda a b : Real) :
    Measurable (finiteAndersonIccEigenvalueCount
      background hbackground lambda a b) := by
  unfold finiteAndersonIccEigenvalueCount
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite
    (measurableSet_Icc.preimage
      (continuous_finiteAndersonEigenvalue
        background hbackground lambda i).measurable)
    measurable_const measurable_const

theorem finiteAndersonIccEigenvalueCount_nonneg
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda a b : Real) (mass : index -> Real) :
    0 <= finiteAndersonIccEigenvalueCount
      background hbackground lambda a b mass := by
  unfold finiteAndersonIccEigenvalueCount
  positivity

theorem finiteAndersonIccEigenvalueCount_le_card
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda a b : Real) (mass : index -> Real) :
    finiteAndersonIccEigenvalueCount background hbackground lambda a b mass <=
      Fintype.card index := by
  unfold finiteAndersonIccEigenvalueCount
  calc
    (∑ i : index, if
        (finiteAndersonHamiltonian_isHermitian
          background hbackground lambda mass).eigenvalues i ∈ Set.Icc a b
      then (1 : Real) else 0) <= ∑ _i : index, (1 : Real) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs <;> norm_num
    _ = Fintype.card index := by simp

theorem integrable_finiteAndersonIccEigenvalueCount
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda a b : Real) (mu : Measure (index -> Real)) [IsFiniteMeasure mu] :
    Integrable (finiteAndersonIccEigenvalueCount
      background hbackground lambda a b) mu := by
  apply Integrable.of_mem_Icc 0 (Fintype.card index)
    (measurable_finiteAndersonIccEigenvalueCount
      background hbackground lambda a b).aemeasurable
  exact Filter.Eventually.of_forall fun mass =>
    ⟨finiteAndersonIccEigenvalueCount_nonneg
      background hbackground lambda a b mass,
     finiteAndersonIccEigenvalueCount_le_card
      background hbackground lambda a b mass⟩

theorem continuous_finiteAndersonSpectralPoissonSum
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda eta : Real) (heta : 0 < eta) :
    Continuous fun state : (index -> Real) × Real =>
      ∑ i : index, realLinePoissonKernel state.2 eta
        ((finiteAndersonHamiltonian_isHermitian
          background hbackground lambda state.1).eigenvalues i) := by
  apply continuous_finsetSum
  intro i _
  unfold realLinePoissonKernel
  apply Continuous.div continuous_const
  · have heig : Continuous
        (fun state : (index -> Real) × Real =>
          (finiteAndersonHamiltonian_isHermitian
            background hbackground lambda state.1).eigenvalues i) :=
      (continuous_finiteAndersonEigenvalue
        background hbackground lambda i).comp continuous_fst
    exact ((heig.sub continuous_snd).pow 2).add continuous_const
  · intro state
    have hpos : 0 <
        ((finiteAndersonHamiltonian_isHermitian
          background hbackground lambda state.1).eigenvalues i - state.2) ^ 2 + eta ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos heta)
    exact hpos.ne'

theorem finiteAndersonSpectralPoissonSum_nonneg
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda eta : Real) (heta : 0 < eta)
    (state : (index -> Real) × Real) :
    0 <= ∑ i : index, realLinePoissonKernel state.2 eta
      ((finiteAndersonHamiltonian_isHermitian
        background hbackground lambda state.1).eigenvalues i) := by
  apply Finset.sum_nonneg
  intro i _
  exact realLinePoissonKernel_nonneg _ _ heta.le

theorem realLinePoissonKernel_le_eta_div_sq
    (center x eta : Real) (heta : 0 < eta) :
    realLinePoissonKernel center eta x <= eta / eta ^ 2 := by
  unfold realLinePoissonKernel
  apply div_le_div_of_nonneg_left heta.le (sq_pos_of_pos heta)
  nlinarith [sq_nonneg (x - center)]

theorem finiteAndersonSpectralPoissonSum_le
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda eta : Real) (heta : 0 < eta)
    (state : (index -> Real) × Real) :
    (∑ i : index, realLinePoissonKernel state.2 eta
      ((finiteAndersonHamiltonian_isHermitian
        background hbackground lambda state.1).eigenvalues i)) <=
      (Fintype.card index : Real) * (eta / eta ^ 2) := by
  calc
    _ <= ∑ _i : index, eta / eta ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact realLinePoissonKernel_le_eta_div_sq _ _ eta heta
    _ = _ := by simp

variable {index : Type*} [Fintype index] [DecidableEq index]

theorem two_mul_arctan_mul_finiteAndersonIccEigenvalueCount_le
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda a b eta delta : Real) (mass : index -> Real)
    (hab : a <= b) (heta : 0 < eta) (hdelta : 0 <= delta) :
    2 * Real.arctan (delta / eta) *
        finiteAndersonIccEigenvalueCount
          background hbackground lambda a b mass <=
      ∫ energy in a - delta..b + delta,
        finiteAndersonEtaSmoothedTrace
          background lambda energy eta mass := by
  let hH := finiteAndersonHamiltonian_isHermitian
    background hbackground lambda mass
  unfold finiteAndersonIccEigenvalueCount
  calc
    2 * Real.arctan (delta / eta) *
        (∑ i : index, if hH.eigenvalues i ∈ Set.Icc a b
          then (1 : Real) else 0) =
      ∑ i : index, 2 * Real.arctan (delta / eta) *
        (if hH.eigenvalues i ∈ Set.Icc a b then (1 : Real) else 0) := by
      rw [Finset.mul_sum]
    _ <= ∑ i : index, ∫ energy in a - delta..b + delta,
        realLinePoissonKernel energy eta (hH.eigenvalues i) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : hH.eigenvalues i ∈ Set.Icc a b
      · simp only [hi, ↓reduceIte, mul_one]
        exact two_mul_arctan_le_intervalIntegral_realLinePoissonKernel
          hab hi heta hdelta
      · simp only [hi, ↓reduceIte, mul_zero]
        apply intervalIntegral.integral_nonneg_of_forall
        · linarith
        · intro energy
          exact realLinePoissonKernel_nonneg energy (hH.eigenvalues i) heta.le
    _ = ∫ energy in a - delta..b + delta,
        ∑ i : index, realLinePoissonKernel energy eta (hH.eigenvalues i) := by
      symm
      apply intervalIntegral.integral_finsetSum
      intro i _
      rw [show (fun energy => realLinePoissonKernel energy eta (hH.eigenvalues i)) =
          realLinePoissonKernel (hH.eigenvalues i) eta by
        funext energy
        exact realLinePoissonKernel_symmetric energy eta (hH.eigenvalues i)]
      exact (continuous_realLinePoissonKernel (hH.eigenvalues i) eta heta.ne').intervalIntegrable
        (μ := volume) (a - delta) (b + delta)
    _ = ∫ energy in a - delta..b + delta,
        finiteAndersonEtaSmoothedTrace background lambda energy eta mass := by
      apply intervalIntegral.integral_congr
      intro energy _
      exact (finiteAndersonEtaSmoothedTrace_eq_sum_poisson
        background hbackground lambda energy eta mass heta).symm

theorem integrable_finiteAndersonSpectralPoissonSum_prod_restrict_Icc
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hbackground : background.IsHermitian)
    (lambda eta left right : Real) (heta : 0 < eta) :
    Integrable
      (fun state : (Fin (n + 1) -> Real) × Real =>
        ∑ i : Fin (n + 1), realLinePoissonKernel state.2 eta
          ((finiteAndersonHamiltonian_isHermitian
            background hbackground lambda state.1).eigenvalues i))
      ((canonicalFiniteIIDMassLaw (n + 1)).prod
        (volume.restrict (Set.Icc left right))) := by
  let _ : IsProbabilityMeasure (canonicalFiniteIIDMassLaw (n + 1)) := by
    unfold canonicalFiniteIIDMassLaw
    infer_instance
  let _ : IsFiniteMeasure (volume.restrict (Set.Icc left right)) := by
    infer_instance
  let _ : IsFiniteMeasure ((canonicalFiniteIIDMassLaw (n + 1)).prod
      (volume.restrict (Set.Icc left right))) := by
    infer_instance
  let F := fun state : (Fin (n + 1) -> Real) × Real =>
    ∑ i : Fin (n + 1), realLinePoissonKernel state.2 eta
      ((finiteAndersonHamiltonian_isHermitian
        background hbackground lambda state.1).eigenvalues i)
  apply Integrable.of_bound
    (continuous_finiteAndersonSpectralPoissonSum
      background hbackground lambda eta heta).aestronglyMeasurable
    ((n + 1 : Real) * (eta / eta ^ 2))
  exact Filter.Eventually.of_forall fun state => by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
        finiteAndersonSpectralPoissonSum_le
          background hbackground lambda eta heta state
    · exact finiteAndersonSpectralPoissonSum_nonneg
        background hbackground lambda eta heta state

theorem integral_energy_finiteAndersonEtaSmoothedTrace_canonicalFiniteIIDMassLaw_le
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hbackground : background.IsHermitian)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (left right eta : Real) (hle : left <= right) (heta : 0 < eta) :
    integral (canonicalFiniteIIDMassLaw (n + 1))
        (fun mass => ∫ energy in left..right,
          finiteAndersonEtaSmoothedTrace background lambda energy eta mass) <=
      (right - left) *
        ((n + 1 : Real) * ((5 / 2 : Real) * |lambda|⁻¹ * Real.pi)) := by
  let mu := canonicalFiniteIIDMassLaw (n + 1)
  let energyMeasure : Measure Real := volume.restrict (Set.Icc left right)
  let _ : IsProbabilityMeasure mu := by
    dsimp [mu, canonicalFiniteIIDMassLaw]
    infer_instance
  let _ : IsFiniteMeasure energyMeasure := by
    dsimp [energyMeasure]
    infer_instance
  let _ : IsFiniteMeasure (mu.prod energyMeasure) := by
    infer_instance
  let F := fun state : (Fin (n + 1) -> Real) × Real =>
    ∑ i : Fin (n + 1), realLinePoissonKernel state.2 eta
      ((finiteAndersonHamiltonian_isHermitian
        background hbackground lambda state.1).eigenvalues i)
  have hF_integrable : Integrable F (mu.prod energyMeasure) := by
    exact integrable_finiteAndersonSpectralPoissonSum_prod_restrict_Icc
      background hbackground lambda eta left right heta
  have hmass_inner : Integrable
      (fun mass => integral energyMeasure fun energy => F (mass, energy)) mu :=
    hF_integrable.integral_prod_left
  have henergy_inner : Integrable
      (fun energy => integral mu fun mass => F (mass, energy)) energyMeasure :=
    hF_integrable.integral_prod_right
  have hsection_le : forall energy : Real,
      integral mu (fun mass => F (mass, energy)) <=
        (n + 1 : Real) * ((5 / 2 : Real) * |lambda|⁻¹ * Real.pi) := by
    intro energy
    calc
      integral mu (fun mass => F (mass, energy)) =
          integral mu (finiteAndersonEtaSmoothedTrace
            background lambda energy eta) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun mass =>
          (finiteAndersonEtaSmoothedTrace_eq_sum_poisson
            background hbackground lambda energy eta mass heta).symm
      _ <= _ :=
        integral_finiteAndersonEtaSmoothedTrace_canonicalFiniteIIDMassLaw_le
          background hbackground lambda hlambda energy eta heta
  calc
    integral (canonicalFiniteIIDMassLaw (n + 1))
        (fun mass => ∫ energy in left..right,
          finiteAndersonEtaSmoothedTrace background lambda energy eta mass) =
      integral mu (fun mass => integral energyMeasure fun energy => F (mass, energy)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun mass => by
          dsimp [energyMeasure]
          rw [intervalIntegral.integral_of_le hle,
            ← integral_Icc_eq_integral_Ioc]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun energy =>
            finiteAndersonEtaSmoothedTrace_eq_sum_poisson
              background hbackground lambda energy eta mass heta
    _ = integral (mu.prod energyMeasure) F :=
      (integral_prod F hF_integrable).symm
    _ = integral energyMeasure
        (fun energy => integral mu fun mass => F (mass, energy)) :=
      integral_prod_symm F hF_integrable
    _ <= integral energyMeasure (fun _ =>
        (n + 1 : Real) * ((5 / 2 : Real) * |lambda|⁻¹ * Real.pi)) := by
      exact integral_mono henergy_inner (integrable_const _) hsection_le
    _ = (right - left) *
        ((n + 1 : Real) * ((5 / 2 : Real) * |lambda|⁻¹ * Real.pi)) := by
      dsimp [energyMeasure]
      rw [integral_const]
      simp
      ring_nf
      exact Or.inl hle

theorem two_mul_arctan_mul_integral_finiteAndersonIccEigenvalueCount_le
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hbackground : background.IsHermitian)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (a b eta delta : Real) (hab : a <= b)
    (heta : 0 < eta) (hdelta : 0 <= delta) :
    2 * Real.arctan (delta / eta) *
        integral (canonicalFiniteIIDMassLaw (n + 1))
          (finiteAndersonIccEigenvalueCount
            background hbackground lambda a b) <=
      (b - a + 2 * delta) *
        ((n + 1 : Real) * ((5 / 2 : Real) * |lambda|⁻¹ * Real.pi)) := by
  let mu := canonicalFiniteIIDMassLaw (n + 1)
  let left := a - delta
  let right := b + delta
  let energyMeasure : Measure Real := volume.restrict (Set.Icc left right)
  let _ : IsProbabilityMeasure mu := by
    dsimp [mu, canonicalFiniteIIDMassLaw]
    infer_instance
  let _ : IsFiniteMeasure energyMeasure := by
    dsimp [energyMeasure]
    infer_instance
  let _ : IsFiniteMeasure (mu.prod energyMeasure) := by
    infer_instance
  let F := fun state : (Fin (n + 1) -> Real) × Real =>
    ∑ i : Fin (n + 1), realLinePoissonKernel state.2 eta
      ((finiteAndersonHamiltonian_isHermitian
        background hbackground lambda state.1).eigenvalues i)
  have hle_lr : left <= right := by dsimp [left, right]; linarith
  have hF_integrable : Integrable F (mu.prod energyMeasure) := by
    exact integrable_finiteAndersonSpectralPoissonSum_prod_restrict_Icc
      background hbackground lambda eta left right heta
  have henergy_integrable : Integrable
      (fun mass => ∫ energy in left..right,
        finiteAndersonEtaSmoothedTrace background lambda energy eta mass) mu := by
    have hinner := hF_integrable.integral_prod_left
    apply hinner.congr
    exact Filter.Eventually.of_forall fun mass => by
      dsimp [energyMeasure]
      rw [intervalIntegral.integral_of_le hle_lr,
        ← integral_Icc_eq_integral_Ioc]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun energy =>
        (finiteAndersonEtaSmoothedTrace_eq_sum_poisson
          background hbackground lambda energy eta mass heta).symm
  have hcount_integrable := integrable_finiteAndersonIccEigenvalueCount
    background hbackground lambda a b mu
  have hmono :
      integral mu (fun mass =>
        2 * Real.arctan (delta / eta) *
          finiteAndersonIccEigenvalueCount
            background hbackground lambda a b mass) <=
      integral mu (fun mass => ∫ energy in left..right,
        finiteAndersonEtaSmoothedTrace background lambda energy eta mass) := by
    apply integral_mono
    · exact hcount_integrable.const_mul _
    · exact henergy_integrable
    · intro mass
      exact two_mul_arctan_mul_finiteAndersonIccEigenvalueCount_le
        background hbackground lambda a b eta delta mass hab heta hdelta
  calc
    2 * Real.arctan (delta / eta) *
        integral (canonicalFiniteIIDMassLaw (n + 1))
          (finiteAndersonIccEigenvalueCount
            background hbackground lambda a b) =
      integral mu (fun mass =>
        2 * Real.arctan (delta / eta) *
          finiteAndersonIccEigenvalueCount
            background hbackground lambda a b mass) := by
      rw [integral_const_mul]
    _ <= integral mu (fun mass => ∫ energy in left..right,
        finiteAndersonEtaSmoothedTrace background lambda energy eta mass) := hmono
    _ <= (right - left) *
        ((n + 1 : Real) * ((5 / 2 : Real) * |lambda|⁻¹ * Real.pi)) :=
      integral_energy_finiteAndersonEtaSmoothedTrace_canonicalFiniteIIDMassLaw_le
        background hbackground lambda hlambda left right eta hle_lr heta
    _ = (b - a + 2 * delta) *
        ((n + 1 : Real) * ((5 / 2 : Real) * |lambda|⁻¹ * Real.pi)) := by
      dsimp [left, right]
      ring

theorem integral_finiteAndersonIccEigenvalueCount_le_expanded
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hbackground : background.IsHermitian)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (a b delta : Real) (hab : a <= b) (hdelta : 0 < delta) :
    integral (canonicalFiniteIIDMassLaw (n + 1))
        (finiteAndersonIccEigenvalueCount
          background hbackground lambda a b) <=
      (b - a + 2 * delta) *
        ((n + 1 : Real) * ((5 / 2 : Real) * |lambda|⁻¹)) := by
  let X := integral (canonicalFiniteIIDMassLaw (n + 1))
    (finiteAndersonIccEigenvalueCount background hbackground lambda a b)
  let C := (n + 1 : Real) * ((5 / 2 : Real) * |lambda|⁻¹)
  have harctan : Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop
  have hcoeffRaw : Tendsto (fun x : Real => 2 * Real.arctan x)
      atTop (𝓝 (2 * (Real.pi / 2))) := tendsto_const_nhds.mul harctan
  have hcoeff : Tendsto (fun x : Real => 2 * Real.arctan x) atTop (𝓝 Real.pi) := by
    convert hcoeffRaw using 1
    ring_nf
  have hprod : Tendsto (fun x : Real => (2 * Real.arctan x) * X)
      atTop (𝓝 (Real.pi * X)) := hcoeff.mul tendsto_const_nhds
  have hevent : ∀ᶠ x : Real in atTop,
      (2 * Real.arctan x) * X <=
        (b - a + 2 * delta) * (C * Real.pi) := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    have hraw :=
      two_mul_arctan_mul_integral_finiteAndersonIccEigenvalueCount_le
        background hbackground lambda hlambda a b (delta / x) delta
        hab (div_pos hdelta hx) hdelta.le
    have hratio : delta / (delta / x) = x := by
      field_simp [hdelta.ne', hx.ne']
    simpa only [hratio, X, C, mul_assoc] using hraw
  have hlimit : Real.pi * X <=
      (b - a + 2 * delta) * (C * Real.pi) :=
    le_of_tendsto hprod hevent
  apply le_of_mul_le_mul_left _ Real.pi_pos
  calc
    Real.pi * X <= (b - a + 2 * delta) * (C * Real.pi) := hlimit
    _ = Real.pi * ((b - a + 2 * delta) * C) := by ring

theorem integral_finiteAndersonIccEigenvalueCount_le
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hbackground : background.IsHermitian)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (a b : Real) (hab : a <= b) :
    integral (canonicalFiniteIIDMassLaw (n + 1))
        (finiteAndersonIccEigenvalueCount
          background hbackground lambda a b) <=
      (b - a) * ((n + 1 : Real) * ((5 / 2 : Real) * |lambda|⁻¹)) := by
  let X := integral (canonicalFiniteIIDMassLaw (n + 1))
    (finiteAndersonIccEigenvalueCount background hbackground lambda a b)
  let C := (n + 1 : Real) * ((5 / 2 : Real) * |lambda|⁻¹)
  have htwo : Tendsto (fun x : Real => (2 : Real) * x⁻¹)
      atTop (𝓝 ((2 : Real) * 0)) :=
    tendsto_const_nhds.mul tendsto_inv_atTop_zero
  have hadd : Tendsto (fun x : Real => (b - a) + 2 * x⁻¹)
      atTop (𝓝 ((b - a) + 2 * 0)) := tendsto_const_nhds.add htwo
  have hmul : Tendsto (fun x : Real => ((b - a) + 2 * x⁻¹) * C)
      atTop (𝓝 (((b - a) + 2 * 0) * C)) := hadd.mul tendsto_const_nhds
  have hlim : Tendsto (fun x : Real => (b - a + 2 * x⁻¹) * C)
      atTop (𝓝 ((b - a) * C)) := by simpa using hmul
  have hevent : ∀ᶠ x : Real in atTop,
      X <= (b - a + 2 * x⁻¹) * C := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    have hraw := integral_finiteAndersonIccEigenvalueCount_le_expanded
      background hbackground lambda hlambda a b x⁻¹ hab (inv_pos.mpr hx)
    simpa only [X, C] using hraw
  exact ge_of_tendsto hlim hevent

variable {index : Type*} [Fintype index] [DecidableEq index]

def finiteAndersonIccEigenvalueNatCount
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda a b : Real) (mass : index -> Real) : Nat :=
  (Finset.univ.filter fun i =>
    (finiteAndersonHamiltonian_isHermitian
      background hbackground lambda mass).eigenvalues i ∈ Set.Icc a b).card

theorem finiteAndersonIccEigenvalueCount_eq_natCast
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda a b : Real) (mass : index -> Real) :
    finiteAndersonIccEigenvalueCount background hbackground lambda a b mass =
      finiteAndersonIccEigenvalueNatCount
        background hbackground lambda a b mass := by
  unfold finiteAndersonIccEigenvalueCount finiteAndersonIccEigenvalueNatCount
  rw [← Finset.sum_filter]
  simp

def finiteAndersonIccSpectralProjector
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda a b : Real) (mass : index -> Real) : Matrix index index Complex :=
  let H := finiteAndersonHamiltonian background lambda mass
  let hH := finiteAndersonHamiltonian_isHermitian
    background hbackground lambda mass
  mappedEigenvectorUnitary H hH *
    Matrix.diagonal (fun i => if hH.eigenvalues i ∈ Set.Icc a b
      then (1 : Complex) else 0) *
    star (mappedEigenvectorUnitary H hH)

theorem finiteAndersonIccSpectralProjector_trace
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda a b : Real) (mass : index -> Real) :
    Matrix.trace (finiteAndersonIccSpectralProjector
      background hbackground lambda a b mass) =
      (finiteAndersonIccEigenvalueCount
        background hbackground lambda a b mass : Complex) := by
  let H := finiteAndersonHamiltonian background lambda mass
  let hH := finiteAndersonHamiltonian_isHermitian
    background hbackground lambda mass
  unfold finiteAndersonIccSpectralProjector
  rw [Matrix.trace_mul_cycle]
  rw [mappedEigenvectorUnitary_star_mul H hH]
  simp [finiteAndersonIccEigenvalueCount]

theorem finiteAndersonIccSpectralProjector_idempotent
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda a b : Real) (mass : index -> Real) :
    finiteAndersonIccSpectralProjector background hbackground lambda a b mass *
      finiteAndersonIccSpectralProjector background hbackground lambda a b mass =
    finiteAndersonIccSpectralProjector background hbackground lambda a b mass := by
  let H := finiteAndersonHamiltonian background lambda mass
  let hH := finiteAndersonHamiltonian_isHermitian
    background hbackground lambda mass
  let U := mappedEigenvectorUnitary H hH
  let D := Matrix.diagonal (fun i => if hH.eigenvalues i ∈ Set.Icc a b
    then (1 : Complex) else 0)
  have hstarU : star U * U = 1 := mappedEigenvectorUnitary_star_mul H hH
  have hD : D * D = D := by
    unfold D
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  unfold finiteAndersonIccSpectralProjector
  change (U * D * star U) * (U * D * star U) = U * D * star U
  calc
    (U * D * star U) * (U * D * star U) =
        U * D * (star U * U) * D * star U := by noncomm_ring
    _ = U * (D * D) * star U := by rw [hstarU]; noncomm_ring
    _ = U * D * star U := by rw [hD]

theorem finiteAndersonIccSpectralProjector_isHermitian
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda a b : Real) (mass : index -> Real) :
    (finiteAndersonIccSpectralProjector
      background hbackground lambda a b mass).IsHermitian := by
  let H := finiteAndersonHamiltonian background lambda mass
  let hH := finiteAndersonHamiltonian_isHermitian
    background hbackground lambda mass
  let U := mappedEigenvectorUnitary H hH
  let D := Matrix.diagonal (fun i => if hH.eigenvalues i ∈ Set.Icc a b
    then (1 : Complex) else 0)
  have hD : star D = D := by
    unfold D
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij, Ne.symm hij]
  unfold finiteAndersonIccSpectralProjector Matrix.IsHermitian
  change star (U * D * star U) = U * D * star U
  simp [hD, Matrix.mul_assoc]

theorem finiteAndersonIccSpectralProjector_rank
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda a b : Real) (mass : index -> Real) :
    (finiteAndersonIccSpectralProjector
      background hbackground lambda a b mass).rank =
      finiteAndersonIccEigenvalueNatCount
        background hbackground lambda a b mass := by
  let H := finiteAndersonHamiltonian background lambda mass
  let hH := finiteAndersonHamiltonian_isHermitian
    background hbackground lambda mass
  let U := mappedEigenvectorUnitary H hH
  let D := Matrix.diagonal (fun i => if hH.eigenvalues i ∈ Set.Icc a b
    then (1 : Complex) else 0)
  have hU : U * star U = 1 := mappedEigenvectorUnitary_mul_star H hH
  have hstarU : star U * U = 1 := mappedEigenvectorUnitary_star_mul H hH
  have hUdet : IsUnit U.det := Matrix.isUnit_det_of_left_inverse hstarU
  have hstarUdet : IsUnit (star U).det := Matrix.isUnit_det_of_left_inverse hU
  unfold finiteAndersonIccSpectralProjector
  change (U * D * star U).rank = _
  calc
    (U * D * star U).rank = (D * star U).rank := by
      rw [Matrix.mul_assoc]
      exact Matrix.rank_mul_eq_right_of_isUnit_det U (D * star U) hUdet
    _ = D.rank := by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det (star U) D hstarUdet]
    _ = finiteAndersonIccEigenvalueNatCount
        background hbackground lambda a b mass := by
      unfold D finiteAndersonIccEigenvalueNatCount
      rw [Matrix.rank_diagonal]
      simp [Fintype.card_subtype]

theorem integral_finiteAndersonIccSpectralProjector_rank_le
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hbackground : background.IsHermitian)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (a b : Real) (hab : a <= b) :
    integral (canonicalFiniteIIDMassLaw (n + 1))
        (fun mass => ((finiteAndersonIccSpectralProjector
          background hbackground lambda a b mass).rank : Real)) <=
      (n + 1 : Real) * ((5 / (2 * |lambda|)) * (b - a)) := by
  calc
    integral (canonicalFiniteIIDMassLaw (n + 1))
        (fun mass => ((finiteAndersonIccSpectralProjector
          background hbackground lambda a b mass).rank : Real)) =
      integral (canonicalFiniteIIDMassLaw (n + 1))
        (finiteAndersonIccEigenvalueCount
          background hbackground lambda a b) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun mass => by
        change ((finiteAndersonIccSpectralProjector
          background hbackground lambda a b mass).rank : Real) = _
        rw [finiteAndersonIccSpectralProjector_rank]
        exact (finiteAndersonIccEigenvalueCount_eq_natCast
          background hbackground lambda a b mass).symm
    _ <= (b - a) *
        ((n + 1 : Real) * ((5 / 2 : Real) * |lambda|⁻¹)) :=
      integral_finiteAndersonIccEigenvalueCount_le
        background hbackground lambda hlambda a b hab
    _ = (n + 1 : Real) * ((5 / (2 * |lambda|)) * (b - a)) := by
      field_simp

end

end ArchonPhysics.FrozenAndersonFiniteProductIccWegner
