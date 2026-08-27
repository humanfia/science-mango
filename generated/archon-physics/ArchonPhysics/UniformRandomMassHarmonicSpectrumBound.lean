import ArchonPhysics.AcousticVertexScaling
import ArchonPhysics.MeasurableOrderedModeCoupling
import ArchonPhysics.RandomEnsemble

/-!
# Uniform upper band edge for the random-mass harmonic spectrum

For a periodic nearest-neighbour chain whose masses satisfy
`mLower <= m_i`, every squared harmonic frequency is at most
`4 / mLower`.  The proof is deterministic: the periodic forward difference
has squared norm at most four times the squared coordinate norm, while
inverse-square-root mass weighting contributes at most `mLower⁻¹`.

The result is then transported to the decreasing ordered Hermitian spectrum.
For every realization of any `IIDMassPhaseEnsemble`, the frozen support
`[4/5, 6/5]` therefore gives the pointwise band bounds

* `orderedEigenvalue <= 5`, and
* `orderedModeFrequency <= sqrt 5`.

No simple-spectrum, localization, kinetic-limit, or thermalization hypothesis
is used.
-/

namespace ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

open ArchonPhysics
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open scoped BigOperators

noncomputable section

/-- The squared periodic forward difference is bounded by four times the
squared coordinate norm. -/
theorem sum_sq_forwardDifference_le_four_mul_sum_sq
    {N : Nat} [NeZero N] (q : Lattice.Configuration N) :
    (∑ i, Lattice.forwardDifference q i ^ 2) ≤
      4 * ∑ i, q i ^ 2 := by
  have hpoint : ∀ i : Lattice.Site N,
      Lattice.forwardDifference q i ^ 2 ≤
        2 * q (i + 1) ^ 2 + 2 * q i ^ 2 := by
    intro i
    rw [Lattice.forwardDifference_apply]
    nlinarith [sq_nonneg (q (i + 1) + q i)]
  have hshift : (∑ i : Lattice.Site N, q (i + 1) ^ 2) =
      ∑ i : Lattice.Site N, q i ^ 2 := by
    exact Fintype.sum_equiv (Equiv.addRight 1)
      (fun i => q (i + 1) ^ 2) (fun i => q i ^ 2) (fun _ => rfl)
  calc
    (∑ i, Lattice.forwardDifference q i ^ 2) ≤
        ∑ i, (2 * q (i + 1) ^ 2 + 2 * q i ^ 2) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = 2 * (∑ i, q (i + 1) ^ 2) + 2 * (∑ i, q i ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = 4 * ∑ i, q i ^ 2 := by rw [hshift]; ring

/-- A positive coordinatewise mass lower bound controls the norm of the
inverse-square-root mass action. -/
theorem sum_sq_inverseSqrtMassAction_le_inv_mul_sum_sq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (mLower : Real) (hmLower : 0 < mLower)
    (hm : ∀ i, mLower ≤ m.mass i) (x : Lattice.Configuration N) :
    (∑ i, Lattice.inverseSqrtMassAction m x i ^ 2) ≤
      mLower⁻¹ * ∑ i, x i ^ 2 := by
  calc
    (∑ i, Lattice.inverseSqrtMassAction m x i ^ 2) ≤
        ∑ i, mLower⁻¹ * x i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [Lattice.inverseSqrtMassAction, mul_pow, inv_pow,
        Real.sq_sqrt (m.mass_pos i).le]
      exact mul_le_mul_of_nonneg_right
        ((inv_le_inv₀ (m.mass_pos i) hmLower).2 (hm i)) (sq_nonneg (x i))
    _ = mLower⁻¹ * ∑ i, x i ^ 2 := by rw [Finset.mul_sum]

/-- Every eigenbasis-indexed squared harmonic frequency lies below the common
band edge `4 / mLower`. -/
theorem modeFrequencySq_le_four_div_massLower
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (mLower : Real) (hmLower : 0 < mLower)
    (hm : ∀ i, mLower ≤ m.mass i) (k : Lattice.Site N) :
    modeFrequencySq m k ≤ 4 / mLower := by
  let e : Lattice.Configuration N :=
    ⇑(normalModeBasis m k)
  let q : Lattice.Configuration N := Lattice.inverseSqrtMassAction m e
  have hnorm : ∑ i, e i ^ 2 = 1 := by
    calc
      ∑ i, e i ^ 2 = ‖normalModeBasis m k‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
      _ = 1 := by simp
  calc
    modeFrequencySq m k =
        ∑ i, (ModeCoupling.bondModeCoefficient m i k) ^ 2 :=
      (AcousticVertexScaling.sum_sq_bondModeCoefficient m k).symm
    _ = ∑ i, Lattice.forwardDifference q i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [ModeCoupling.bondModeCoefficient_eq_forwardDifference]
    _ ≤ 4 * ∑ i, q i ^ 2 :=
      sum_sq_forwardDifference_le_four_mul_sum_sq q
    _ ≤ 4 * (mLower⁻¹ * ∑ i, e i ^ 2) := by
      gcongr
      exact sum_sq_inverseSqrtMassAction_le_inv_mul_sum_sq
        m mLower hmLower hm e
    _ = 4 / mLower := by rw [hnorm, mul_one, div_eq_mul_inv]

/-- The same deterministic band edge for the decreasing ordered Hermitian
spectrum. -/
theorem orderedEigenvalue_harmonic_le_four_div_massLower
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (mLower : Real) (hmLower : 0 < mLower)
    (hm : ∀ i, mLower ≤ m.mass i)
    (k : Fin (Fintype.card (Lattice.Site N))) :
    orderedEigenvalue (harmonicHermitian m) k ≤ 4 / mLower := by
  rw [← orderedEigenvalue_equiv]
  exact modeFrequencySq_le_four_div_massLower m mLower hmLower hm _

/-- Square-root form of the common ordered harmonic band edge. -/
theorem orderedModeFrequency_harmonic_le_sqrt_four_div_massLower
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (mLower : Real) (hmLower : 0 < mLower)
    (hm : ∀ i, mLower ≤ m.mass i)
    (k : Fin (Fintype.card (Lattice.Site N))) :
    orderedModeFrequency (harmonicHermitian m) k ≤
      Real.sqrt (4 / mLower) := by
  exact Real.sqrt_le_sqrt
    (orderedEigenvalue_harmonic_le_four_div_massLower
      m mLower hmLower hm k)

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Every realization of every frozen iid ensemble has squared harmonic
frequencies at most five. -/
theorem iid_modeFrequencySq_le_five
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) (k : Lattice.Site N) :
    modeFrequencySq (ensemble.restrictPositiveMass (N := N) omega) k ≤ 5 := by
  simpa [RandomEnsemble.massLower] using
    modeFrequencySq_le_four_div_massLower
      (ensemble.restrictPositiveMass (N := N) omega)
      RandomEnsemble.massLower RandomEnsemble.massLower_pos
      (fun i => by
        simpa using (ensemble.mass_mem_support i.val omega).1) k

/-- Pointwise frozen-support bound for every decreasingly ordered squared
frequency. -/
theorem iid_orderedEigenvalue_harmonic_le_five
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (k : Fin (Fintype.card (Lattice.Site N))) :
    orderedEigenvalue
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := N) omega)) k ≤ 5 := by
  simpa [RandomEnsemble.massLower] using
    orderedEigenvalue_harmonic_le_four_div_massLower
      (ensemble.restrictPositiveMass (N := N) omega)
      RandomEnsemble.massLower RandomEnsemble.massLower_pos
      (fun i => by
        simpa using (ensemble.mass_mem_support i.val omega).1) k

/-- Pointwise frozen-support bound for every ordered physical frequency. -/
theorem iid_orderedModeFrequency_harmonic_le_sqrt_five
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (k : Fin (Fintype.card (Lattice.Site N))) :
    orderedModeFrequency
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := N) omega)) k ≤
      Real.sqrt 5 := by
  exact Real.sqrt_le_sqrt
    (iid_orderedEigenvalue_harmonic_le_five ensemble omega k)

end

end ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
