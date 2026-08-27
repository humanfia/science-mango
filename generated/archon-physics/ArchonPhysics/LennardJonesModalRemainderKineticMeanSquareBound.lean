import ArchonPhysics.LennardJonesModalRemainderMeanSquareBound

/-!
# Kinetic-window integral of the all-mode LJ remainder mean square

The volume-uniform instantaneous estimate is integrated on the explicit
physical window `[0, L / g^2]`.  A pointwise `O(g^6)` mean square therefore
has integral `O(L * g^4)`, and, when `L > 0`, time average `O(g^6)`.

These bounds use only a uniform-in-time strain tube and amplitude bound.
They do not use or prove oscillatory time cancellation, random-phase
propagation, tube persistence, or a microscopic-to-kinetic limit.
-/

namespace ArchonPhysics.LennardJonesModalRemainderKineticMeanSquareBound

open Set
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.LennardJonesKineticTimeForceRemainder
open ArchonPhysics.LennardJonesModalRemainderMeanSquareBound

noncomputable section

/-- The modal higher-residual mean square is nonnegative at every finite
volume. -/
theorem modalHigherResidualMeanSquare_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ g : Real)
    (q : HilbertConfiguration N) :
    0 ≤ modalHigherResidualMeanSquare m depth r₀ g q := by
  unfold modalHigherResidualMeanSquare
  exact div_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)
    (Nat.cast_nonneg N)

/-- Integral of the all-mode mean square over the physical kinetic window.
The norm is used so the statement does not depend on a separate positivity
lemma for interval integrals. -/
theorem intervalIntegrable_and_norm_integral_modalHigherResidualMeanSquare_le_kinetic
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mLower : Real) (hmLower : 0 < mLower)
    (hmass : ∀ i, mLower ≤ m.mass i)
    {depth r₀ g rho L amplitudeBound : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hL : 0 ≤ L) (hAmplitude : 0 ≤ amplitudeBound)
    (q : Real → HilbertConfiguration N)
    (hIntegrable : IntervalIntegrable
      (fun t => modalHigherResidualMeanSquare m depth r₀ g (q t))
      MeasureTheory.volume 0 (kineticWindowTime g L))
    (htube : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      ∀ i : Lattice.Site N,
        |g * Lattice.forwardDifference (asConfiguration (q t)) i| ≤ rho * r₀)
    (hamplitude : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      ∀ i : Lattice.Site N,
        |Lattice.forwardDifference (asConfiguration (q t)) i| ≤ amplitudeBound) :
    IntervalIntegrable
        (fun t => modalHigherResidualMeanSquare m depth r₀ g (q t))
        MeasureTheory.volume 0 (kineticWindowTime g L) ∧
      ‖∫ t in 0..kineticWindowTime g L,
          modalHigherResidualMeanSquare m depth r₀ g (q t)‖ ≤
        4 * mLower⁻¹ *
          kineticForceRemainderCoefficient r₀ rho amplitudeBound ^ 2 *
            L * g ^ 4 := by
  refine ⟨hIntegrable, ?_⟩
  have htime : 0 ≤ kineticWindowTime g L := by
    unfold kineticWindowTime
    exact div_nonneg hL (sq_nonneg g)
  calc
    ‖∫ t in 0..kineticWindowTime g L,
        modalHigherResidualMeanSquare m depth r₀ g (q t)‖ ≤
      (4 * mLower⁻¹ *
          kineticForceRemainderCoefficient r₀ rho amplitudeBound ^ 2 * g ^ 6) *
        |kineticWindowTime g L - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      have htIcc : t ∈ Icc 0 (kineticWindowTime g L) := by
        simpa only [uIcc_of_le htime] using Set.uIoc_subset_uIcc ht
      have hpoint := modalHigherResidualMeanSquare_le_g_six
        m mLower hmLower hmass hdepth hr₀ hg hrho0 hrho1 hAmplitude
          (q t) (htube t htIcc) (hamplitude t htIcc)
      rw [Real.norm_eq_abs, abs_of_nonneg
        (modalHigherResidualMeanSquare_nonneg m depth r₀ g (q t))]
      exact hpoint
    _ = 4 * mLower⁻¹ *
          kineticForceRemainderCoefficient r₀ rho amplitudeBound ^ 2 *
            L * g ^ 4 := by
      rw [sub_zero, abs_of_nonneg htime]
      unfold kineticWindowTime
      field_simp [ne_of_gt hg]

/-- Time average of the all-mode higher-residual mean square on the kinetic
window. -/
def kineticWindowModalHigherResidualMeanSquareAverage
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ g L : Real)
    (q : Real → HilbertConfiguration N) : Real :=
  (∫ t in 0..kineticWindowTime g L,
      modalHigherResidualMeanSquare m depth r₀ g (q t)) /
    kineticWindowTime g L

/-- Dividing the `O(L * g^4)` integral by the positive window length
`L / g^2` recovers a volume-independent `O(g^6)` time average. -/
theorem abs_kineticWindowModalHigherResidualMeanSquareAverage_le_g_six
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mLower : Real) (hmLower : 0 < mLower)
    (hmass : ∀ i, mLower ≤ m.mass i)
    {depth r₀ g rho L amplitudeBound : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hL : 0 < L) (hAmplitude : 0 ≤ amplitudeBound)
    (q : Real → HilbertConfiguration N)
    (hIntegrable : IntervalIntegrable
      (fun t => modalHigherResidualMeanSquare m depth r₀ g (q t))
      MeasureTheory.volume 0 (kineticWindowTime g L))
    (htube : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      ∀ i : Lattice.Site N,
        |g * Lattice.forwardDifference (asConfiguration (q t)) i| ≤ rho * r₀)
    (hamplitude : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      ∀ i : Lattice.Site N,
        |Lattice.forwardDifference (asConfiguration (q t)) i| ≤ amplitudeBound) :
    |kineticWindowModalHigherResidualMeanSquareAverage
        m depth r₀ g L q| ≤
      4 * mLower⁻¹ *
        kineticForceRemainderCoefficient r₀ rho amplitudeBound ^ 2 * g ^ 6 := by
  have hintegral :=
    (intervalIntegrable_and_norm_integral_modalHigherResidualMeanSquare_le_kinetic
      m mLower hmLower hmass hdepth hr₀ hg hrho0 hrho1 hL.le hAmplitude
        q hIntegrable htube hamplitude).2
  have htime : 0 < kineticWindowTime g L := by
    unfold kineticWindowTime
    exact div_pos hL (sq_pos_of_pos hg)
  unfold kineticWindowModalHigherResidualMeanSquareAverage
  rw [abs_div, abs_of_pos htime]
  calc
    |∫ t in 0..kineticWindowTime g L,
        modalHigherResidualMeanSquare m depth r₀ g (q t)| /
          kineticWindowTime g L ≤
      (4 * mLower⁻¹ *
          kineticForceRemainderCoefficient r₀ rho amplitudeBound ^ 2 *
            L * g ^ 4) /
          kineticWindowTime g L := by
      exact (div_le_div_iff_of_pos_right htime).2 (by
        simpa [Real.norm_eq_abs] using hintegral)
    _ = 4 * mLower⁻¹ *
        kineticForceRemainderCoefficient r₀ rho amplitudeBound ^ 2 * g ^ 6 := by
      unfold kineticWindowTime
      field_simp [ne_of_gt hg, ne_of_gt hL]

end

end ArchonPhysics.LennardJonesModalRemainderKineticMeanSquareBound
