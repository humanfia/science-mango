import Mathlib
import ArchonPhysics.Lattice
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic

/-!
# Harmonic normal modes for a finite disordered chain

This module records the mass-weighted harmonic operator and its modal data for
the finite periodic chain of Wang--Fu--Zhang--Zhao, arXiv:1903.09502v2, p. 2,
eqs. (2)--(3).  The normal-mode construction uses the finite-dimensional real
spectral theorem for positive semidefinite matrices.  The oscillator adapter
uses Physlib's `HarmonicOscillator`; see the campaign roadmap, Section 3.
-/

namespace ArchonPhysics.HarmonicModes

noncomputable section

/-- The matrix of the periodic forward nearest-neighbour difference. -/
def differenceMatrix {N : Nat} : Matrix (Lattice.Site N) (Lattice.Site N) Real :=
  fun i j => (if j = i + 1 then 1 else 0) - (if j = i then 1 else 0)

/-- The matrix realization of the periodic forward difference. -/
theorem differenceMatrix_mulVec {N : Nat} [NeZero N] (q : Lattice.Configuration N) :
    Matrix.mulVec differenceMatrix q = Lattice.forwardDifference q := by
  ext i
  simp only [Matrix.mulVec, differenceMatrix, dotProduct, Lattice.forwardDifference]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp

/-- The difference matrix after inverse-square-root mass weighting. -/
def massWeightedDifferenceMatrix {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    Matrix (Lattice.Site N) (Lattice.Site N) Real :=
  differenceMatrix * Matrix.diagonal (fun i => (Real.sqrt (m.mass i))⁻¹)

/-- The symmetric positive-semidefinite mass-weighted harmonic matrix. -/
def massWeightedHarmonicMatrix {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    Matrix (Lattice.Site N) (Lattice.Site N) Real :=
  Matrix.transpose (massWeightedDifferenceMatrix m) * massWeightedDifferenceMatrix m

/-- The mass-weighted harmonic matrix is the Gram matrix of the weighted difference. -/
theorem massWeightedHarmonicMatrix_eq_transpose_mul_self {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :
    massWeightedHarmonicMatrix m =
      Matrix.transpose (massWeightedDifferenceMatrix m) * massWeightedDifferenceMatrix m := by
  rfl

/-- The Gram form makes the mass-weighted harmonic matrix positive semidefinite. -/
theorem massWeightedHarmonicMatrix_posSemidef {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :
    Matrix.PosSemidef (massWeightedHarmonicMatrix m) := by
  constructor
  · unfold massWeightedHarmonicMatrix Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul]
    simp
  · intro x
    classical
    simp only [Finsupp.sum]
    simp only [star_trivial]
    calc
      0 ≤ ∑ j, (∑ i ∈ x.support, massWeightedDifferenceMatrix m j i * x i) ^ 2 := by
        positivity
      _ = ∑ j, ∑ i ∈ x.support, ∑ k ∈ x.support,
          (massWeightedDifferenceMatrix m j i * x i) *
            (massWeightedDifferenceMatrix m j k * x k) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [pow_two, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
      _ = ∑ i ∈ x.support, ∑ k ∈ x.support, ∑ j,
          (massWeightedDifferenceMatrix m j i * x i) *
            (massWeightedDifferenceMatrix m j k * x k) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ i ∈ x.support, ∑ k ∈ x.support,
          (x i * ∑ j, massWeightedDifferenceMatrix m j i *
            massWeightedDifferenceMatrix m j k) * x k := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- Energy of a real harmonic mode with squared frequency `omegaSq`. -/
def modalEnergy : Real → Real → Real → Real :=
  fun omegaSq a v => (v ^ 2 + omegaSq * a ^ 2) / 2

/-- A differentiable real harmonic mode conserves its modal energy. -/
theorem modalEnergy_conserved (omegaSq : Real) (a v : Real → Real)
    (ha : ∀ t, HasDerivAt a (v t) t)
    (hv : ∀ t, HasDerivAt v (-omegaSq * a t) t) :
    ∀ t, modalEnergy omegaSq (a t) (v t) = modalEnergy omegaSq (a 0) (v 0) := by
  let e : ℝ → ℝ := fun t => modalEnergy omegaSq (a t) (v t)
  have he : ∀ t, HasDerivAt e 0 t := by
    intro t
    have hconst : HasDerivAt (fun _ : ℝ => omegaSq) 0 t :=
      hasDerivAt_const t omegaSq
    have hderiv : HasDerivAt (v ^ 2 + (fun _ : ℝ => omegaSq) * a ^ 2)
        (2 * v t * (-omegaSq * a t) + omegaSq * (2 * a t * v t)) t := by
      simpa only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Nat.reduceSub,
        Nat.cast_ofNat, zero_mul, zero_add, pow_one] using
        ((hv t).pow 2).add (hconst.mul ((ha t).pow 2))
    have hzero : 2 * v t * (-omegaSq * a t) + omegaSq * (2 * a t * v t) = 0 := by
      ring
    change HasDerivAt (fun x => (v x ^ 2 + omegaSq * a x ^ 2) / 2) 0 t
    simpa only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, hzero, zero_div] using
      hderiv.div_const 2
  intro t
  change e t = e 0
  exact is_const_of_deriv_eq_zero (fun x => (he x).differentiableAt)
    (fun x => (he x).deriv) t 0

/-- Nonnegative squared frequency gives nonnegative modal energy. -/
theorem modalEnergy_nonneg (omegaSq a v : Real) (homegaSq : 0 ≤ omegaSq) :
    0 ≤ modalEnergy omegaSq a v := by
  unfold modalEnergy
  positivity

/-- The spectral squared frequency of the selected normal mode. -/
def modeFrequencySq {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k : Lattice.Site N) : Real :=
  let h : (massWeightedHarmonicMatrix m).IsHermitian := by
    unfold massWeightedHarmonicMatrix
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul]
    simp
  h.eigenvalues k

/-- Spectral squared frequencies of a positive-semidefinite harmonic matrix are nonnegative. -/
theorem modeFrequencySq_nonneg {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k : Lattice.Site N) : 0 ≤ modeFrequencySq m k := by
  let h : (massWeightedHarmonicMatrix m).IsHermitian := by
    unfold massWeightedHarmonicMatrix Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul]
    simp
  change 0 ≤ h.eigenvalues k
  exact (h.posSemidef_iff_eigenvalues_nonneg.mp
    (massWeightedHarmonicMatrix_posSemidef m)) k

/-- An orthonormal eigenbasis of the mass-weighted harmonic matrix. -/
def normalModeBasis {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    OrthonormalBasis (Lattice.Site N) Real (EuclideanSpace Real (Lattice.Site N)) :=
  let h : (massWeightedHarmonicMatrix m).IsHermitian := by
    unfold massWeightedHarmonicMatrix
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul]
    simp
  h.eigenvectorBasis

/-- Each vector in the selected normal-mode basis is an eigenvector. -/
theorem normalMode_eigenvector {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k : Lattice.Site N) :
    Matrix.mulVec (massWeightedHarmonicMatrix m) ⇑(normalModeBasis m k) =
      modeFrequencySq m k • ⇑(normalModeBasis m k) := by
  let h : (massWeightedHarmonicMatrix m).IsHermitian := by
    unfold massWeightedHarmonicMatrix Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul]
    simp
  exact h.mulVec_eigenvectorBasis k

/-- The unit-mass Physlib oscillator associated with a positive mode frequency. -/
def positiveModeOscillator (omega : Real) (homega : 0 < omega) :
    ClassicalMechanics.HarmonicOscillator :=
  ⟨1, omega ^ 2, by norm_num, sq_pos_of_pos homega⟩

/-- The oscillator adapter has unit mass and spring constant `omega²`. -/
theorem positiveModeOscillator_spec (omega : Real) (homega : 0 < omega) :
    (positiveModeOscillator omega homega).m = 1 ∧
      (positiveModeOscillator omega homega).k = omega ^ 2 := by
  exact ⟨rfl, rfl⟩

/-- A positive normal-mode oscillator conserves Physlib's energy along its equation of motion. -/
theorem positiveMode_energy_conserved (omega : Real) (homega : 0 < omega)
    (x : Time → EuclideanSpace Real (Fin 1)) (hx : ContDiff Real (↑⊤) x)
    (heom : (positiveModeOscillator omega homega).EquationOfMotion x) (t : Time) :
    (positiveModeOscillator omega homega).energy x t =
      (positiveModeOscillator omega homega).energy x 0 := by
  apply ClassicalMechanics.HarmonicOscillator.energy_conservation_of_equationOfMotion'
    (positiveModeOscillator omega homega) x (hx.of_le (by simp)) heom t

/-- The mass-square-root translation vector, the zero-frequency mode. -/
def translationMode {N : Nat} (m : Lattice.PositiveMassConfig N) :
    Lattice.Configuration N :=
  fun i => Real.sqrt (m.mass i)

/-- Formula-level specification of the mass-weighted operator and one mode. -/
theorem harmonicData_spec {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (omegaSq a v : Real) :
    massWeightedDifferenceMatrix m =
        differenceMatrix * Matrix.diagonal (fun i => (Real.sqrt (m.mass i))⁻¹) ∧
      (∀ i, translationMode m i = Real.sqrt (m.mass i)) ∧
      modalEnergy omegaSq a v = (v ^ 2 + omegaSq * a ^ 2) / 2 := by
  exact ⟨rfl, fun _ => rfl, rfl⟩

/-- The translation vector lies in the kernel of the harmonic matrix. -/
theorem translationMode_is_zero {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    Matrix.mulVec (massWeightedHarmonicMatrix m) (translationMode m) = 0 := by
  have hdiagonal :
      Matrix.mulVec (Matrix.diagonal (fun i => (Real.sqrt (m.mass i))⁻¹))
        (translationMode m) = 1 := by
    ext i
    rw [Matrix.mulVec_diagonal]
    simp only [translationMode]
    exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (m.mass_pos i))
  have hweighted : Matrix.mulVec (massWeightedDifferenceMatrix m) (translationMode m) = 0 := by
    unfold massWeightedDifferenceMatrix
    rw [← Matrix.mulVec_mulVec]
    rw [hdiagonal]
    rw [differenceMatrix_mulVec]
    ext i
    simp [Lattice.forwardDifference]
  unfold massWeightedHarmonicMatrix
  rw [← Matrix.mulVec_mulVec]
  rw [hweighted]
  exact Matrix.mulVec_zero _

/-- Positive masses make the translation vector nonzero. -/
theorem translationMode_ne_zero {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    translationMode m ≠ 0 := by
  intro hzero
  have hcomponent : translationMode m 0 = 0 := by
    simpa using congrFun hzero 0
  have hpositive : 0 < Real.sqrt (m.mass 0) :=
    Real.sqrt_pos.2 (m.mass_pos 0)
  exact (ne_of_gt hpositive) (by simpa [translationMode] using hcomponent)

end

end ArchonPhysics.HarmonicModes
