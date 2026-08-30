import ArchonPhysics.SelfAdjointQuasimodeSpectrum

/-!
# Spectral-window mass of a finite-dimensional quasimode

A small residual for a unit vector controls not only the distance to the
spectrum.  In a self-adjoint eigenbasis, the squared coefficient mass outside
a radius-`delta` window is at most `epsilon ^ 2 / delta ^ 2`.  Consequently
the mass inside the window is at least its complementary lower bound.

The result is deterministic and finite-dimensional.  It assumes no spectral
simplicity and no small operator-norm perturbation.
-/

namespace ArchonPhysics.SelfAdjointQuasimodeSpectralWindow

open Module

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]

/-- Parseval's identity for the real self-adjoint eigenbasis. -/
theorem sum_sq_eigenbasis_repr_eq_norm_sq
    (T : E →ₗ[Real] E) (hT : T.IsSymmetric)
    (n : Nat) (hn : Module.finrank Real E = n) (v : E) :
    ∑ i : Fin n, ((hT.eigenvectorBasis hn).repr v i) ^ 2 = ‖v‖ ^ 2 := by
  let b := hT.eigenvectorBasis hn
  calc
    ∑ i : Fin n, (b.repr v i) ^ 2 = ‖b.repr v‖ ^ 2 :=
      (EuclideanSpace.real_norm_sq_eq (b.repr v)).symm
    _ = ‖v‖ ^ 2 := by rw [LinearIsometryEquiv.norm_map]

/-- Exact squared-residual expansion in the self-adjoint eigenbasis. -/
theorem residual_norm_sq_eq_sum_eigenbasis
    (T : E →ₗ[Real] E) (hT : T.IsSymmetric)
    (n : Nat) (hn : Module.finrank Real E = n)
    (v : E) (lambda : Real) :
    ‖T v - lambda • v‖ ^ 2 =
      ∑ i : Fin n,
        ((hT.eigenvalues hn i - lambda) *
          (hT.eigenvectorBasis hn).repr v i) ^ 2 := by
  let b := hT.eigenvectorBasis hn
  calc
    ‖T v - lambda • v‖ ^ 2 = ‖b.repr (T v - lambda • v)‖ ^ 2 := by
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

/-- A quasimode has at most `epsilon² / delta²` eigenbasis mass at spectral
distance at least `delta` from its target energy. -/
theorem outside_window_eigenbasis_mass_le
    (T : E →ₗ[Real] E) (hT : T.IsSymmetric)
    (n : Nat) (hn : Module.finrank Real E = n)
    (v : E) {lambda epsilon delta : Real}
    (hdelta : 0 < delta)
    (hresidual : ‖T v - lambda • v‖ ≤ epsilon) :
    ∑ i ∈ Finset.univ.filter
        (fun i : Fin n => delta ≤ |hT.eigenvalues hn i - lambda|),
        ((hT.eigenvectorBasis hn).repr v i) ^ 2 ≤
      epsilon ^ 2 / delta ^ 2 := by
  let b := hT.eigenvectorBasis hn
  let outside : Finset (Fin n) := Finset.univ.filter
    (fun i : Fin n => delta ≤ |hT.eigenvalues hn i - lambda|)
  have hepsilon : 0 ≤ epsilon :=
    (norm_nonneg (T v - lambda • v)).trans hresidual
  have hresidualSq : ‖T v - lambda • v‖ ^ 2 ≤ epsilon ^ 2 := by
    nlinarith [norm_nonneg (T v - lambda • v)]
  have hterm (i : Fin n) (hi : i ∈ outside) :
      delta ^ 2 * (b.repr v i) ^ 2 ≤
        ((hT.eigenvalues hn i - lambda) * b.repr v i) ^ 2 := by
    have hgap : delta ≤ |hT.eigenvalues hn i - lambda| := by
      simpa [outside] using hi
    have hgapSq : delta ^ 2 ≤ (hT.eigenvalues hn i - lambda) ^ 2 := by
      rw [← sq_abs (hT.eigenvalues hn i - lambda)]
      nlinarith [abs_nonneg (hT.eigenvalues hn i - lambda)]
    have hmul := mul_le_mul_of_nonneg_right hgapSq (sq_nonneg (b.repr v i))
    nlinarith
  have houtsideResidual :
      delta ^ 2 * ∑ i ∈ outside, (b.repr v i) ^ 2 ≤
        ∑ i : Fin n,
          ((hT.eigenvalues hn i - lambda) * b.repr v i) ^ 2 := by
    calc
      delta ^ 2 * ∑ i ∈ outside, (b.repr v i) ^ 2 =
          ∑ i ∈ outside, delta ^ 2 * (b.repr v i) ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ outside,
          ((hT.eigenvalues hn i - lambda) * b.repr v i) ^ 2 :=
        Finset.sum_le_sum fun i hi => hterm i hi
      _ ≤ ∑ i : Fin n,
          ((hT.eigenvalues hn i - lambda) * b.repr v i) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _hi _hinot
        exact sq_nonneg _
  have houtsideSq :
      delta ^ 2 * ∑ i ∈ outside, (b.repr v i) ^ 2 ≤ epsilon ^ 2 := by
    calc
      _ ≤ ∑ i : Fin n,
          ((hT.eigenvalues hn i - lambda) * b.repr v i) ^ 2 :=
        houtsideResidual
      _ = ‖T v - lambda • v‖ ^ 2 :=
        (residual_norm_sq_eq_sum_eigenbasis T hT n hn v lambda).symm
      _ ≤ epsilon ^ 2 := hresidualSq
  apply (le_div_iff₀ (sq_pos_of_pos hdelta)).2
  simpa [outside, b, mul_comm] using houtsideSq

/-- A unit quasimode has at least the complementary coefficient mass in the
open spectral window of radius `delta`. -/
theorem inside_window_eigenbasis_mass_ge
    (T : E →ₗ[Real] E) (hT : T.IsSymmetric)
    (n : Nat) (hn : Module.finrank Real E = n)
    (v : E) {lambda epsilon delta : Real}
    (hdelta : 0 < delta) (hv : ‖v‖ = 1)
    (hresidual : ‖T v - lambda • v‖ ≤ epsilon) :
    1 - epsilon ^ 2 / delta ^ 2 ≤
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin n => |hT.eigenvalues hn i - lambda| < delta),
        ((hT.eigenvectorBasis hn).repr v i) ^ 2 := by
  let b := hT.eigenvectorBasis hn
  let inside : Finset (Fin n) := Finset.univ.filter
    (fun i : Fin n => |hT.eigenvalues hn i - lambda| < delta)
  let outside : Finset (Fin n) := Finset.univ.filter
    (fun i : Fin n => delta ≤ |hT.eigenvalues hn i - lambda|)
  have houtside :
      ∑ i ∈ outside, (b.repr v i) ^ 2 ≤ epsilon ^ 2 / delta ^ 2 := by
    simpa [outside, b] using
      outside_window_eigenbasis_mass_le T hT n hn v hdelta hresidual
  have htotal : ∑ i : Fin n, (b.repr v i) ^ 2 = 1 := by
    rw [sum_sq_eigenbasis_repr_eq_norm_sq T hT n hn v, hv]
    norm_num
  have hsplit :
      (∑ i ∈ inside, (b.repr v i) ^ 2) +
          ∑ i ∈ outside, (b.repr v i) ^ 2 = 1 := by
    rw [← htotal]
    simpa only [inside, outside, not_lt] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin n => |hT.eigenvalues hn i - lambda| < delta)
        (fun i : Fin n => (b.repr v i) ^ 2))
  calc
    1 - epsilon ^ 2 / delta ^ 2 ≤
        1 - ∑ i ∈ outside, (b.repr v i) ^ 2 :=
      sub_le_sub_left houtside 1
    _ = ∑ i ∈ inside, (b.repr v i) ^ 2 := by linarith

end

end ArchonPhysics.SelfAdjointQuasimodeSpectralWindow
