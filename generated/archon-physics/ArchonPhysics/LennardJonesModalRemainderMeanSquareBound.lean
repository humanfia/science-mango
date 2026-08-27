import ArchonPhysics.LennardJonesModalRemainderKineticBound
import ArchonPhysics.RandomMassHarmonicTransferMatrix
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Volume-uniform mean-square bound for the LJ modal remainder

The one-mode `l1` estimate loses a factor `sqrt(N)`.  For the collection of
all modes this loss is avoidable: the normal-mode transform is an isometry,
and the physical higher force is the transpose periodic difference of the
bond-remainder vector.  The elementary `l2` operator bound

`sum |D^T r|^2 <= 4 * sum |r|^2`

therefore gives an `O(N * g^6)` bound for the total modal square and an
`O(g^6)` bound for its per-mode mean.  The latter is uniform in the volume,
provided the masses have a common positive lower bound.

This is a deterministic instantaneous estimate under the explicit strain
tube and amplitude hypotheses.  It does not prove persistence of that tube,
time cancellation, random-phase propagation, or a microscopic-to-kinetic
limit.
-/

namespace ArchonPhysics.LennardJonesModalRemainderMeanSquareBound

open ArchonPhysics
open ArchonPhysics.BondPotentialHamiltonianPhyslib
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.HarmonicModes
open ArchonPhysics.LennardJonesForceTaylorTube
open ArchonPhysics.LennardJonesKineticTimeForceRemainder
open ArchonPhysics.LennardJonesModalRemainderKineticBound
open ArchonPhysics.LennardJonesNormalizedForceScaling
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.RandomMassHarmonicTransferMatrix
open ArchonPhysics.ReducedModeTransform
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

noncomputable section

/-- The bond-indexed normalized force remainder. -/
def normalizedHigherResidualBondVector {N : Nat} [NeZero N]
    (depth r₀ g : Real) (q : HilbertConfiguration N) :
    Lattice.Configuration N :=
  fun i => normalizedForceRemainder depth r₀ g
    (Lattice.forwardDifference (asConfiguration q) i)

/-- The periodic transpose difference has `l2` operator norm at most two. -/
theorem sum_sq_transposeDifferenceMatrix_mulVec_le_four_mul_sum_sq
    {N : Nat} [NeZero N] (x : Lattice.Configuration N) :
    (∑ i, Matrix.mulVec (Matrix.transpose differenceMatrix) x i ^ 2) ≤
      4 * ∑ i, x i ^ 2 := by
  rw [transposeDifferenceMatrix_mulVec]
  have hpoint : ∀ i : Lattice.Site N,
      (x (i - 1) - x i) ^ 2 ≤ 2 * x (i - 1) ^ 2 + 2 * x i ^ 2 := by
    intro i
    nlinarith [sq_nonneg (x (i - 1) + x i)]
  have hshift : (∑ i : Lattice.Site N, x (i - 1) ^ 2) =
      ∑ i : Lattice.Site N, x i ^ 2 := by
    simpa [sub_eq_add_neg] using
      (Fintype.sum_equiv (Equiv.addRight (-1))
        (fun i : Lattice.Site N => x (i + (-1)) ^ 2)
        (fun i : Lattice.Site N => x i ^ 2) (fun _ => rfl))
  calc
    (∑ i : Lattice.Site N, (x (i - 1) - x i) ^ 2) ≤
        ∑ i : Lattice.Site N, (2 * x (i - 1) ^ 2 + 2 * x i ^ 2) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = 2 * (∑ i : Lattice.Site N, x (i - 1) ^ 2) +
        2 * (∑ i : Lattice.Site N, x i ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = 4 * ∑ i : Lattice.Site N, x i ^ 2 := by rw [hshift]; ring

/-- The normalized higher residual gradient is exactly `D^T` applied to its
bond-remainder vector. -/
theorem normalizedHigherResidualGradient_eq_transposeDifferenceMatrix
    {N : Nat} [NeZero N] (depth r₀ g : Real)
    (q : HilbertConfiguration N) :
    normalizedHigherResidualGradient depth r₀ g q =
      WithLp.toLp 2 (Matrix.mulVec (Matrix.transpose differenceMatrix)
        (normalizedHigherResidualBondVector depth r₀ g q)) := by
  ext j
  unfold normalizedHigherResidualGradient
    normalizedHigherResidualBondVector potentialGradient
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [MassWeightedHamiltonianDynamics.bondDirection_apply_eq_differenceMatrix]
  ring

/-- The physical normalized higher gradient has square norm at most four
times the square norm of the bond-remainder vector. -/
theorem sum_sq_normalizedHigherResidualGradient_le_four_mul_bond_sum_sq
    {N : Nat} [NeZero N] (depth r₀ g : Real)
    (q : HilbertConfiguration N) :
    (∑ j, normalizedHigherResidualGradient depth r₀ g q j ^ 2) ≤
      4 * ∑ i, (normalizedHigherResidualBondVector depth r₀ g q i) ^ 2 := by
  rw [normalizedHigherResidualGradient_eq_transposeDifferenceMatrix]
  exact sum_sq_transposeDifferenceMatrix_mulVec_le_four_mul_sum_sq
    (normalizedHigherResidualBondVector depth r₀ g q)

/-- Parseval plus the mass lower bound controls the complete modal square by
the bond-remainder square, without applying a separate `l1` estimate to each
mode. -/
theorem sum_sq_normalizedHigherResidualModalForce_le_bond_sum_sq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mLower : Real) (hmLower : 0 < mLower)
    (hmass : ∀ i, mLower ≤ m.mass i)
    (depth r₀ g : Real) (q : HilbertConfiguration N) :
    (∑ k, normalizedHigherResidualModalForce m depth r₀ g q k ^ 2) ≤
      4 * mLower⁻¹ *
        ∑ i, (normalizedHigherResidualBondVector depth r₀ g q i) ^ 2 := by
  let gradient := normalizedHigherResidualGradient depth r₀ g q
  have hgradient :
      (∑ j, gradient j ^ 2) ≤
        4 * ∑ i, (normalizedHigherResidualBondVector depth r₀ g q i) ^ 2 := by
    exact sum_sq_normalizedHigherResidualGradient_le_four_mul_bond_sum_sq
      depth r₀ g q
  calc
    (∑ k, normalizedHigherResidualModalForce m depth r₀ g q k ^ 2) =
        ∑ k, (modalCoordinates m
          (transformedNormalizedHigherResidualForce m depth r₀ g q) k) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [modalCoordinates_transformedNormalizedHigherResidualForce]
    _ = ‖transformedNormalizedHigherResidualForce m depth r₀ g q‖ ^ 2 :=
      sum_sq_modalCoordinates m _
    _ = ∑ j, (Lattice.inverseSqrtMassAction m
          (asConfiguration gradient) j) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_congr rfl
      intro j _hj
      simp [transformedNormalizedHigherResidualForce,
        inverseSqrtMassTransform_apply, Lattice.inverseSqrtMassAction,
        asConfiguration, gradient]
    _ ≤ mLower⁻¹ * ∑ j, gradient j ^ 2 :=
      sum_sq_inverseSqrtMassAction_le_inv_mul_sum_sq
        m mLower hmLower hmass (asConfiguration gradient)
    _ ≤ mLower⁻¹ *
        (4 * ∑ i, (normalizedHigherResidualBondVector depth r₀ g q i) ^ 2) :=
      mul_le_mul_of_nonneg_left hgradient (inv_nonneg.mpr hmLower.le)
    _ = 4 * mLower⁻¹ *
        ∑ i, (normalizedHigherResidualBondVector depth r₀ g q i) ^ 2 := by
      ring

/-- Mean square of the normalized higher LJ force over all normal modes. -/
def modalHigherResidualMeanSquare {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ g : Real)
    (q : HilbertConfiguration N) : Real :=
  (∑ k, normalizedHigherResidualModalForce m depth r₀ g q k ^ 2) /
    (N : Real)

/-- On the strain tube, the complete modal mean square is `O(g^6)` with a
constant independent of `N`.  The only volume-uniform mass input is the
explicit coordinatewise lower bound `mLower <= m_i`. -/
theorem modalHigherResidualMeanSquare_le_g_six
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mLower : Real) (hmLower : 0 < mLower)
    (hmass : ∀ i, mLower ≤ m.mass i)
    {depth r₀ g rho amplitudeBound : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (_hAmplitude : 0 ≤ amplitudeBound)
    (q : HilbertConfiguration N)
    (htube : ∀ i : Lattice.Site N,
      |g * Lattice.forwardDifference (asConfiguration q) i| ≤ rho * r₀)
    (hamplitude : ∀ i : Lattice.Site N,
      |Lattice.forwardDifference (asConfiguration q) i| ≤ amplitudeBound) :
    modalHigherResidualMeanSquare m depth r₀ g q ≤
      4 * mLower⁻¹ *
        kineticForceRemainderCoefficient r₀ rho amplitudeBound ^ 2 * g ^ 6 := by
  let coefficient := kineticForceRemainderCoefficient r₀ rho amplitudeBound
  have hcoefficient : 0 ≤ coefficient := by
    unfold coefficient kineticForceRemainderCoefficient
    have hfour : 0 ≤ (amplitudeBound / r₀) ^ 4 := by positivity
    exact mul_nonneg
      (mul_nonneg (div_nonneg hr₀.le (by norm_num))
        (forceRemainderTubeConstant_pos hrho0 hrho1).le) hfour
  have hbound : 0 ≤ coefficient * g ^ 3 :=
    mul_nonneg hcoefficient (pow_nonneg hg.le 3)
  have hpoint : ∀ i : Lattice.Site N,
      (normalizedHigherResidualBondVector depth r₀ g q i) ^ 2 ≤
        (coefficient * g ^ 3) ^ 2 := by
    intro i
    have hres := abs_normalizedForceRemainder_le_g_cubed
      hdepth hr₀ (ne_of_gt hg) hrho0 hrho1 (htube i)
    have hratio :
        |Lattice.forwardDifference (asConfiguration q) i| / r₀ ≤
          amplitudeBound / r₀ :=
      (div_le_div_iff_of_pos_right hr₀).2 (hamplitude i)
    have hpow :
        (|Lattice.forwardDifference (asConfiguration q) i| / r₀) ^ 4 ≤
          (amplitudeBound / r₀) ^ 4 :=
      pow_le_pow_left₀
        (div_nonneg (abs_nonneg _) hr₀.le) hratio 4
    have hprefactor :
        0 ≤ r₀ / 72 * forceRemainderTubeConstant rho * |g| ^ 3 := by
      exact mul_nonneg
        (mul_nonneg (div_nonneg hr₀.le (by norm_num))
          (forceRemainderTubeConstant_pos hrho0 hrho1).le)
        (pow_nonneg (abs_nonneg g) 3)
    have habs :
        |normalizedHigherResidualBondVector depth r₀ g q i| ≤
          coefficient * g ^ 3 := by
      unfold normalizedHigherResidualBondVector
      have h := hres.trans (mul_le_mul_of_nonneg_left hpow hprefactor)
      simpa [coefficient, kineticForceRemainderCoefficient, abs_of_pos hg,
        mul_comm, mul_left_comm, mul_assoc] using h
    have hsquare := (sq_le_sq₀ (abs_nonneg _) hbound).2 habs
    simpa [sq_abs] using hsquare
  have hN : 0 < (N : Real) := by
    exact_mod_cast NeZero.pos N
  have hbondSum :
      (∑ i, (normalizedHigherResidualBondVector depth r₀ g q i) ^ 2) ≤
        (N : Real) * (coefficient * g ^ 3) ^ 2 := by
    calc
      (∑ i, (normalizedHigherResidualBondVector depth r₀ g q i) ^ 2) ≤
          ∑ _i : Lattice.Site N, (coefficient * g ^ 3) ^ 2 :=
        Finset.sum_le_sum fun i _ => hpoint i
      _ = (N : Real) * (coefficient * g ^ 3) ^ 2 := by
        simp [Lattice.Site, ZMod.card]
  have hmodal := sum_sq_normalizedHigherResidualModalForce_le_bond_sum_sq
    m mLower hmLower hmass depth r₀ g q
  unfold modalHigherResidualMeanSquare
  calc
    (∑ k, normalizedHigherResidualModalForce m depth r₀ g q k ^ 2) /
          (N : Real) ≤
        (4 * mLower⁻¹ *
          ∑ i, (normalizedHigherResidualBondVector depth r₀ g q i) ^ 2) /
          (N : Real) :=
      (div_le_div_iff_of_pos_right hN).2 hmodal
    _ ≤ (4 * mLower⁻¹ *
          ((N : Real) * (coefficient * g ^ 3) ^ 2)) /
          (N : Real) := by
      exact (div_le_div_iff_of_pos_right hN).2
        (mul_le_mul_of_nonneg_left hbondSum
          (mul_nonneg (by norm_num) (inv_nonneg.mpr hmLower.le)))
    _ = 4 * mLower⁻¹ * coefficient ^ 2 * g ^ 6 := by
      field_simp [ne_of_gt hN]
    _ = 4 * mLower⁻¹ *
        kineticForceRemainderCoefficient r₀ rho amplitudeBound ^ 2 * g ^ 6 := rfl

end

end ArchonPhysics.LennardJonesModalRemainderMeanSquareBound
