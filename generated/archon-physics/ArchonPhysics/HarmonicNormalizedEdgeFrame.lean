import ArchonPhysics.ThreeLegKernelApproximationAlgebra
import ArchonPhysics.OrderedTranslationLastMode

/-!
# A complete normalized harmonic edge frame

For every simple positive-mass harmonic cycle, the positive ordered modes are
normalized incidence images `B v_k / sqrt(lambda_k)`.  The unique ordered
translation mode is completed by the normalized constant edge vector.  The
result is an explicit orthonormal basis of edge space, and every projected
bond kernel factors as `lambda_k u_k u_k`.  Thus downstream Frobenius and
entrywise bounds require no abstract factorization or frame assumptions.
-/

open scoped BigOperators Matrix

namespace ArchonPhysics.HarmonicNormalizedEdgeFrame

open ArchonPhysics
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.ComplexRegularizedMarkedLegBridge

noncomputable section

abbrev HarmonicOrderedModeIndex (N : Nat) [NeZero N] :=
  Fin (Fintype.card (Lattice.Site N))

def orderedSiteMode {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : HarmonicOrderedModeIndex N) :
    Lattice.Configuration N :=
  ⇑((harmonicHermitian m).2.eigenvectorBasis (orderedIndexEquiv k))

def orderedRawEdgeMode {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : HarmonicOrderedModeIndex N) :
    Lattice.Configuration N :=
  Matrix.mulVec (massWeightedDifferenceMatrix m) (orderedSiteMode m k)

def constantEdgeMode {N : Nat} [NeZero N] : Lattice.Configuration N :=
  fun _j ↦ (Real.sqrt (N : Real))⁻¹

def harmonicNormalizedEdgeFrame {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :
    HarmonicOrderedModeIndex N → Lattice.Site N → Real :=
  fun k j ↦ if k = lastOrderedIndex (ι := Lattice.Site N) then
    constantEdgeMode j
  else
    orderedRawEdgeMode m k j /
      orderedModeFrequency (harmonicHermitian m) k

theorem sum_orderedRawEdgeMode_eq_zero {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : HarmonicOrderedModeIndex N) :
    ∑ j, orderedRawEdgeMode m k j = 0 := by
  let q : Lattice.Configuration N :=
    Matrix.mulVec (Matrix.diagonal (fun i ↦ (Real.sqrt (m.mass i))⁻¹))
      (orderedSiteMode m k)
  have hraw : orderedRawEdgeMode m k = Lattice.forwardDifference q := by
    rw [← differenceMatrix_mulVec]
    simp only [orderedRawEdgeMode, massWeightedDifferenceMatrix, q]
    rw [Matrix.mulVec_mulVec]
  rw [hraw]
  exact Lattice.sum_forwardDifference q

theorem orderedRawEdgeMode_inner {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k q : HarmonicOrderedModeIndex N) :
    (∑ j, orderedRawEdgeMode m k j * orderedRawEdgeMode m q j) =
      if k = q then orderedEigenvalue (harmonicHermitian m) k else 0 := by
  let B := massWeightedDifferenceMatrix m
  let vk : Lattice.Configuration N := orderedSiteMode m k
  let vq : Lattice.Configuration N := orderedSiteMode m q
  have heigen : Matrix.mulVec (massWeightedHarmonicMatrix m) vq =
      orderedEigenvalue (harmonicHermitian m) q • vq := by
    change Matrix.mulVec (matrixVal (harmonicHermitian m)) vq =
      orderedEigenvalue (harmonicHermitian m) q • vq
    simpa [vq, orderedSiteMode] using
      (matrixVal_mulVec_eigenvectorBasis (harmonicHermitian m) q)
  have hinner : (∑ i, vk i * vq i) = if k = q then 1 else 0 := by
    have h := (harmonicHermitian m).2.eigenvectorBasis.inner_eq_ite
      (orderedIndexEquiv q) (orderedIndexEquiv k)
    simpa [vk, vq, orderedSiteMode, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, eq_comm] using h
  calc
    (∑ j, orderedRawEdgeMode m k j * orderedRawEdgeMode m q j) =
        (Matrix.mulVec B vk) ⬝ᵥ (Matrix.mulVec B vq) := by
      simp [orderedRawEdgeMode, B, vk, vq, orderedSiteMode, dotProduct]
    _ = vk ⬝ᵥ Matrix.mulVec (Matrix.transpose B) (Matrix.mulVec B vq) := by
      rw [dotProduct_comm]
      exact (Matrix.dotProduct_transpose_mulVec B vk (Matrix.mulVec B vq)).symm
    _ = vk ⬝ᵥ Matrix.mulVec (massWeightedHarmonicMatrix m) vq := by
      rw [Matrix.mulVec_mulVec]
      rfl
    _ = vk ⬝ᵥ (orderedEigenvalue (harmonicHermitian m) q • vq) := by
      rw [heigen]
    _ = orderedEigenvalue (harmonicHermitian m) q * (∑ i, vk i * vq i) := by
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = if k = q then orderedEigenvalue (harmonicHermitian m) k else 0 := by
      rw [hinner]
      split_ifs with hkq
      · subst q
        ring
      · ring


theorem orderedRawEdgeMode_last_eq_zero {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :
    orderedRawEdgeMode m (lastOrderedIndex (ι := Lattice.Site N)) = 0 := by
  let z : HarmonicOrderedModeIndex N := lastOrderedIndex (ι := Lattice.Site N)
  have hsum : ∑ j, (orderedRawEdgeMode m z j) ^ 2 = 0 := by
    have h := orderedRawEdgeMode_inner m z z
    simpa [z, pow_two, harmonic_lastOrderedEigenvalue_eq_zero] using h
  funext j
  have hzfun : (fun i ↦ (orderedRawEdgeMode m z i) ^ 2) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg fun i ↦ sq_nonneg
      (orderedRawEdgeMode m z i)).mp hsum
  exact sq_eq_zero_iff.mp (congrFun hzfun j)

theorem constantEdgeMode_inner {N : Nat} [NeZero N] :
    (∑ j : Lattice.Site N, constantEdgeMode j * constantEdgeMode j) = 1 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hsqrt : Real.sqrt (N : Real) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hN)
  simp only [constantEdgeMode, Finset.sum_const, Finset.card_univ,
    ZMod.card]
  rw [nsmul_eq_mul]
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt hN.le]

theorem constantEdgeMode_orderedRawEdgeMode_inner {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : HarmonicOrderedModeIndex N) :
    (∑ j, constantEdgeMode j * orderedRawEdgeMode m k j) = 0 := by
  simp only [constantEdgeMode]
  rw [← Finset.mul_sum]
  rw [sum_orderedRawEdgeMode_eq_zero]
  ring


theorem orderedModeFrequency_sq_eq_orderedEigenvalue {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : HarmonicOrderedModeIndex N) :
    orderedModeFrequency (harmonicHermitian m) k ^ 2 =
      orderedEigenvalue (harmonicHermitian m) k := by
  exact Real.sq_sqrt
    (harmonicHermitian_orderedEigenvalue_nonneg m k)

theorem normalizedOrderedRawEdgeMode_inner {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k q : HarmonicOrderedModeIndex N)
    (hk : k ≠ lastOrderedIndex (ι := Lattice.Site N))
    (hq : q ≠ lastOrderedIndex (ι := Lattice.Site N)) :
    (∑ j,
      (orderedRawEdgeMode m k j /
        orderedModeFrequency (harmonicHermitian m) k) *
      (orderedRawEdgeMode m q j /
        orderedModeFrequency (harmonicHermitian m) q)) =
      if k = q then 1 else 0 := by
  by_cases hkq : k = q
  · subst q
    have hfrequency : 0 < orderedModeFrequency (harmonicHermitian m) k :=
      (orderedModeFrequency_pos_iff_ne_last m hsimple k).2 hk
    calc
      (∑ j,
          (orderedRawEdgeMode m k j /
            orderedModeFrequency (harmonicHermitian m) k) *
          (orderedRawEdgeMode m k j /
            orderedModeFrequency (harmonicHermitian m) k)) =
          (∑ j, orderedRawEdgeMode m k j * orderedRawEdgeMode m k j) /
            (orderedModeFrequency (harmonicHermitian m) k ^ 2) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _hj
        field_simp
      _ = orderedEigenvalue (harmonicHermitian m) k /
          (orderedModeFrequency (harmonicHermitian m) k ^ 2) := by
        rw [orderedRawEdgeMode_inner]
        simp
      _ = 1 := by
        have hlambda : 0 < orderedEigenvalue (harmonicHermitian m) k := by
          rw [← orderedModeFrequency_sq_eq_orderedEigenvalue]
          positivity
        rw [orderedModeFrequency_sq_eq_orderedEigenvalue]
        exact div_self (ne_of_gt hlambda)
      _ = if k = k then 1 else 0 := by simp
  · calc
      (∑ j,
          (orderedRawEdgeMode m k j /
            orderedModeFrequency (harmonicHermitian m) k) *
          (orderedRawEdgeMode m q j /
            orderedModeFrequency (harmonicHermitian m) q)) =
          (∑ j, orderedRawEdgeMode m k j * orderedRawEdgeMode m q j) /
            (orderedModeFrequency (harmonicHermitian m) k *
              orderedModeFrequency (harmonicHermitian m) q) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _hj
        field_simp
      _ = 0 := by rw [orderedRawEdgeMode_inner, if_neg hkq, zero_div]
      _ = if k = q then 1 else 0 := by simp [hkq]


theorem constantEdgeMode_normalizedRawEdgeMode_inner
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : HarmonicOrderedModeIndex N) :
    (∑ j, constantEdgeMode j *
      (orderedRawEdgeMode m k j /
        orderedModeFrequency (harmonicHermitian m) k)) = 0 := by
  calc
    (∑ j, constantEdgeMode j *
        (orderedRawEdgeMode m k j /
          orderedModeFrequency (harmonicHermitian m) k)) =
        (∑ j, constantEdgeMode j * orderedRawEdgeMode m k j) /
          orderedModeFrequency (harmonicHermitian m) k := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = 0 := by rw [constantEdgeMode_orderedRawEdgeMode_inner, zero_div]

theorem harmonicNormalizedEdgeFrame_orthonormal
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k q : HarmonicOrderedModeIndex N) :
    (∑ j, harmonicNormalizedEdgeFrame m k j *
      harmonicNormalizedEdgeFrame m q j) =
      if k = q then 1 else 0 := by
  let z : HarmonicOrderedModeIndex N := lastOrderedIndex (ι := Lattice.Site N)
  by_cases hk : k = z
  · subst k
    by_cases hq : q = z
    · subst q
      simpa [harmonicNormalizedEdgeFrame, z] using
        (constantEdgeMode_inner (N := N))
    · have hq' : q ≠ lastOrderedIndex (ι := Lattice.Site N) := by
        simpa [z] using hq
      have hzq : z ≠ q := Ne.symm hq
      simpa [harmonicNormalizedEdgeFrame, z, hq', hzq] using
        (constantEdgeMode_normalizedRawEdgeMode_inner m q)
  · by_cases hq : q = z
    · subst q
      have hk' : k ≠ lastOrderedIndex (ι := Lattice.Site N) := by
        simpa [z] using hk
      have hkz : k ≠ z := hk
      calc
        (∑ j, harmonicNormalizedEdgeFrame m k j *
            harmonicNormalizedEdgeFrame m z j) =
            ∑ j, constantEdgeMode j *
              (orderedRawEdgeMode m k j /
                orderedModeFrequency (harmonicHermitian m) k) := by
          apply Finset.sum_congr rfl
          intro j _hj
          simp only [harmonicNormalizedEdgeFrame, z, if_neg hk', if_pos]
          ring
        _ = 0 := constantEdgeMode_normalizedRawEdgeMode_inner m k
        _ = if k = z then 1 else 0 := by simp [hkz]
    · have hk' : k ≠ lastOrderedIndex (ι := Lattice.Site N) := by
        simpa [z] using hk
      have hq' : q ≠ lastOrderedIndex (ι := Lattice.Site N) := by
        simpa [z] using hq
      simpa [harmonicNormalizedEdgeFrame, hk', hq'] using
        (normalizedOrderedRawEdgeMode_inner m hsimple k q hk' hq')


theorem projectedBondKernel_eq_harmonicNormalizedEdgeFrame
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : HarmonicOrderedModeIndex N) (j l : Lattice.Site N) :
    projectedBondKernel (massWeightedDifferenceMatrix m)
        (harmonicHermitian m) k j l =
      orderedEigenvalue (harmonicHermitian m) k *
        harmonicNormalizedEdgeFrame m k j *
          harmonicNormalizedEdgeFrame m k l := by
  rw [projectedBondKernel_apply_eq_mul
    (massWeightedDifferenceMatrix m) (harmonicHermitian m) hsimple]
  change orderedRawEdgeMode m k j * orderedRawEdgeMode m k l = _
  by_cases hk : k = lastOrderedIndex (ι := Lattice.Site N)
  · subst k
    have hzero := orderedRawEdgeMode_last_eq_zero m
    have hzj : orderedRawEdgeMode m
        (lastOrderedIndex (ι := Lattice.Site N)) j = 0 := by
      exact congrFun hzero j
    have hzl : orderedRawEdgeMode m
        (lastOrderedIndex (ι := Lattice.Site N)) l = 0 := by
      exact congrFun hzero l
    rw [hzj, hzl, zero_mul,
      harmonic_lastOrderedEigenvalue_eq_zero, zero_mul]
    ring
  · have hfrequency : 0 < orderedModeFrequency (harmonicHermitian m) k :=
      (orderedModeFrequency_pos_iff_ne_last m hsimple k).2 hk
    simp only [harmonicNormalizedEdgeFrame, if_neg hk]
    rw [← orderedModeFrequency_sq_eq_orderedEigenvalue]
    field_simp [ne_of_gt hfrequency]

end
end ArchonPhysics.HarmonicNormalizedEdgeFrame
