import ArchonPhysics.ActualThreeMassProjectorWeightJacobian
import ArchonPhysics.RandomMassHarmonicTrace
import ArchonPhysics.RandomMassThreeWaveCollisionNetwork

/-!
# Summability of actual three-mass projector minors

For a simple finite-volume spectrum, the quadratic weight of any direction
in one ordered spectral projector is nonnegative, and the weights sum over
all modes to the squared norm of that direction.  Combining this completeness
identity with the six-term expansion of a `3 x 3` determinant gives an
`N`-independent bound on the sum of all absolute projector-weight minors.

For the three genuine periodic-cycle mass directions, every squared norm is
exactly two.  Consequently the full ordered-mode-triple sum is at most
`3! * 2^3 = 48`.  This is an actual spectral sum rule; it does not bound the
reciprocal Jacobian on a coarea fiber.
-/

open scoped Matrix BigOperators

namespace ArchonPhysics.ActualThreeMassProjectorMinorSummability

open ArchonPhysics
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassHarmonicTrace
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.SingleMassRankOnePerturbation
open ArchonPhysics.ThreeParameterProjectorWeightJacobian
open ArchonPhysics.ThreeParameterSpectralAveragingDensity

noncomputable section

variable {iota : Type*} [Fintype iota] [DecidableEq iota]

/-- A simple ordered spectral projector has nonnegative quadratic weight. -/
theorem orderedModeProjector_quadraticWeight_nonneg
    (A : HermitianMatrix iota) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card iota)) (v : iota -> Real) :
    0 <= v ⬝ᵥ (orderedModeProjector A k *ᵥ v) := by
  rw [orderedModeProjector_eq_vecMulVec A hsimple k,
    Matrix.vecMulVec_mulVec]
  simp only [dotProduct_smul, op_smul_eq_smul, smul_eq_mul]
  rw [dotProduct_comm
    ((A.2.eigenvectorBasis (orderedIndexEquiv k)) : iota -> Real) v]
  simpa [pow_two] using
    (sq_nonneg
      (v ⬝ᵥ
        ((A.2.eigenvectorBasis (orderedIndexEquiv k)) : iota -> Real)))

/-- Totalized ordered projectors remain positive semidefinite even at a
spectral collision: a colliding Lagrange projector is zero, while an isolated
one is the canonical rank-one eigenprojector. -/
theorem orderedModeProjector_quadraticWeight_nonneg_global
    (A : HermitianMatrix iota)
    (k : Fin (Fintype.card iota)) (v : iota -> Real) :
    0 <= v ⬝ᵥ (orderedModeProjector A k *ᵥ v) := by
  rcases orderedModeProjector_eq_zero_or_vecMulVec A k with hzero | houter
  · simp [hzero]
  · rw [houter, Matrix.vecMulVec_mulVec]
    simp only [dotProduct_smul, op_smul_eq_smul, smul_eq_mul]
    rw [dotProduct_comm
      ((A.2.eigenvectorBasis (orderedIndexEquiv k)) : iota -> Real) v]
    simpa [pow_two] using
      (sq_nonneg
        (v ⬝ᵥ
          ((A.2.eigenvectorBasis (orderedIndexEquiv k)) : iota -> Real)))

private theorem orderedModeProjector_quadraticWeight_le_eigenWeight
    (A : HermitianMatrix iota)
    (k : Fin (Fintype.card iota)) (v : iota -> Real) :
    v ⬝ᵥ (orderedModeProjector A k *ᵥ v) <=
      (v ⬝ᵥ
        ((A.2.eigenvectorBasis (orderedIndexEquiv k)) : iota -> Real)) ^ 2 := by
  rcases orderedModeProjector_eq_zero_or_vecMulVec A k with hzero | houter
  · simp [hzero, sq_nonneg]
  · rw [houter, Matrix.vecMulVec_mulVec]
    simp only [dotProduct_smul, op_smul_eq_smul, smul_eq_mul]
    rw [dotProduct_comm
      ((A.2.eigenvectorBasis (orderedIndexEquiv k)) : iota -> Real) v]
    rw [pow_two]

private theorem sum_orderedEigenvector_dot_sq
    (A : HermitianMatrix iota) (v : iota -> Real) :
    (∑ k : Fin (Fintype.card iota),
      (v ⬝ᵥ
        ((A.2.eigenvectorBasis (orderedIndexEquiv k)) : iota -> Real)) ^ 2) =
      v ⬝ᵥ v := by
  have hsumOuter :
      (∑ k : Fin (Fintype.card iota),
        Matrix.vecMulVec
          ((A.2.eigenvectorBasis (orderedIndexEquiv k)) : iota -> Real)
          ((A.2.eigenvectorBasis (orderedIndexEquiv k)) : iota -> Real)) =
        (1 : Matrix iota iota Real) := by
    apply matrix_eq_of_mulVec_eigenvectorBasis_eq A
    intro r
    rw [Matrix.sum_mulVec, Matrix.one_mulVec]
    simp_rw [Matrix.vecMulVec_mulVec]
    have hdot (k : Fin (Fintype.card iota)) :
        ((A.2.eigenvectorBasis (orderedIndexEquiv k)) : iota -> Real) ⬝ᵥ
            ((A.2.eigenvectorBasis (orderedIndexEquiv r)) : iota -> Real) =
          if r = k then 1 else 0 := by
      have hinner := A.2.eigenvectorBasis.inner_eq_ite
        (orderedIndexEquiv r) (orderedIndexEquiv k)
      simpa [EuclideanSpace.inner_eq_star_dotProduct, eq_comm] using hinner
    simp_rw [hdot]
    simp
  calc
    _ = ∑ k : Fin (Fintype.card iota),
        v ⬝ᵥ (Matrix.vecMulVec
          ((A.2.eigenvectorBasis (orderedIndexEquiv k)) : iota -> Real)
          ((A.2.eigenvectorBasis (orderedIndexEquiv k)) : iota -> Real) *ᵥ v) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Matrix.vecMulVec_mulVec]
      simp only [dotProduct_smul, op_smul_eq_smul, smul_eq_mul]
      rw [dotProduct_comm
        ((A.2.eigenvectorBasis (orderedIndexEquiv k)) : iota -> Real) v]
      ring
    _ = v ⬝ᵥ ((∑ k : Fin (Fintype.card iota),
        Matrix.vecMulVec
          ((A.2.eigenvectorBasis (orderedIndexEquiv k)) : iota -> Real)
          ((A.2.eigenvectorBasis (orderedIndexEquiv k)) : iota -> Real)) *ᵥ v) := by
      rw [Matrix.sum_mulVec, dotProduct_sum]
    _ = v ⬝ᵥ v := by rw [hsumOuter, Matrix.one_mulVec]

/-- At collisions, the surviving isolated ordered projectors form an
incomplete orthogonal resolution, so their quadratic weights sum to at most
the squared norm of the direction. -/
theorem sum_orderedModeProjector_quadraticWeight_le
    (A : HermitianMatrix iota) (v : iota -> Real) :
    (∑ k : Fin (Fintype.card iota),
      v ⬝ᵥ (orderedModeProjector A k *ᵥ v)) <= v ⬝ᵥ v := by
  calc
    _ <= ∑ k : Fin (Fintype.card iota),
        (v ⬝ᵥ
          ((A.2.eigenvectorBasis (orderedIndexEquiv k)) : iota -> Real)) ^ 2 :=
      Finset.sum_le_sum fun k _hk =>
        orderedModeProjector_quadraticWeight_le_eigenWeight A k v
    _ = _ := sum_orderedEigenvector_dot_sq A v
/-- Projector completeness recovers the squared norm of the direction. -/
theorem sum_orderedModeProjector_quadraticWeight
    (A : HermitianMatrix iota) (hsimple : SimpleOrderedSpectrum A)
    (v : iota -> Real) :
    (∑ k : Fin (Fintype.card iota),
      v ⬝ᵥ (orderedModeProjector A k *ᵥ v)) = v ⬝ᵥ v := by
  rw [← dotProduct_sum]
  rw [← Matrix.sum_mulVec]
  rw [orderedModeProjector_sum_eq_one A hsimple]
  simp

/-- A genuine periodic-cycle mass direction has squared norm two. -/
theorem cycleMassPerturbationVector_dot_self
    {N : Nat} [NeZero N] (hN : 2 <= N) (i : Lattice.Site N) :
    cycleMassPerturbationVector i ⬝ᵥ cycleMassPerturbationVector i = 2 := by
  simpa [dotProduct, cycleMassPerturbationVector, pow_two] using
    differenceMatrix_column_sq_sum hN i

private def finThreeFunctionEquivTriple (alpha : Type*) :
    (Fin 3 -> alpha) ≃ alpha × (alpha × alpha) where
  toFun f := (f 0, (f 1, f 2))
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv f := by
    funext r
    fin_cases r <;> simp
  right_inv p := by
    rcases p with ⟨a, b, c⟩
    simp

private def rowWeightMatrix {kappa : Type*}
    (q : kappa -> Fin 3 -> Real) (modes : Fin 3 -> kappa) :
    Matrix (Fin 3) (Fin 3) Real :=
  fun r s => q (modes r) s

private theorem sum_abs_det_rowWeightMatrix_le_48
    {kappa : Type*} [Fintype kappa]
    (q : kappa -> Fin 3 -> Real)
    (hq : forall k s, 0 <= q k s)
    (hsum : forall s, (∑ k : kappa, q k s) <= 2) :
    (∑ modes : Fin 3 -> kappa, |(rowWeightMatrix q modes).det|) <= 48 := by
  classical
  have hpoint (a b c : kappa) :
      |(rowWeightMatrix q ![a, b, c]).det| <=
        q a 0 * q b 1 * q c 2 +
        q a 0 * q b 2 * q c 1 +
        q a 1 * q b 0 * q c 2 +
        q a 1 * q b 2 * q c 0 +
        q a 2 * q b 0 * q c 1 +
        q a 2 * q b 1 * q c 0 := by
    have h1 : 0 <= q a 0 * q b 1 * q c 2 :=
      mul_nonneg (mul_nonneg (hq a 0) (hq b 1)) (hq c 2)
    have h2 : 0 <= q a 0 * q b 2 * q c 1 :=
      mul_nonneg (mul_nonneg (hq a 0) (hq b 2)) (hq c 1)
    have h3 : 0 <= q a 1 * q b 0 * q c 2 :=
      mul_nonneg (mul_nonneg (hq a 1) (hq b 0)) (hq c 2)
    have h4 : 0 <= q a 1 * q b 2 * q c 0 :=
      mul_nonneg (mul_nonneg (hq a 1) (hq b 2)) (hq c 0)
    have h5 : 0 <= q a 2 * q b 0 * q c 1 :=
      mul_nonneg (mul_nonneg (hq a 2) (hq b 0)) (hq c 1)
    have h6 : 0 <= q a 2 * q b 1 * q c 0 :=
      mul_nonneg (mul_nonneg (hq a 2) (hq b 1)) (hq c 0)
    simp only [rowWeightMatrix, Matrix.det_fin_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [abs_le]
    constructor <;> nlinarith
  have hterm (s0 s1 s2 : Fin 3) :
      (∑ a : kappa, ∑ b : kappa, ∑ c : kappa,
        q a s0 * q b s1 * q c s2) <= 8 := by
    calc
      (∑ a : kappa, ∑ b : kappa, ∑ c : kappa,
          q a s0 * q b s1 * q c s2) =
          ∑ a : kappa, ∑ b : kappa,
            (q a s0 * q b s1) * (∑ c : kappa, q c s2) := by
              apply Finset.sum_congr rfl
              intro a _ha
              apply Finset.sum_congr rfl
              intro b _hb
              rw [Finset.mul_sum]
      _ <= ∑ a : kappa, ∑ b : kappa,
          (q a s0 * q b s1) * 2 := by
            apply Finset.sum_le_sum
            intro a _ha
            apply Finset.sum_le_sum
            intro b _hb
            exact mul_le_mul_of_nonneg_left (hsum s2)
              (mul_nonneg (hq a s0) (hq b s1))
      _ = ∑ a : kappa,
          q a s0 * (∑ b : kappa, q b s1) * 2 := by
            apply Finset.sum_congr rfl
            intro a _ha
            rw [Finset.mul_sum, Finset.sum_mul]
      _ <= ∑ a : kappa, q a s0 * 2 * 2 := by
            apply Finset.sum_le_sum
            intro a _ha
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hsum s1) (hq a s0))
              (by norm_num)
      _ = (∑ a : kappa, q a s0) * 2 * 2 := by
            rw [Finset.sum_mul, Finset.sum_mul]
      _ <= 2 * 2 * 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hsum s0) (by norm_num))
              (by norm_num)
      _ = 8 := by norm_num
  calc
    (∑ modes : Fin 3 -> kappa, |(rowWeightMatrix q modes).det|) =
        ∑ p : kappa × (kappa × kappa),
          |(rowWeightMatrix q ((finThreeFunctionEquivTriple kappa).symm p)).det| :=
      (Equiv.sum_comp (finThreeFunctionEquivTriple kappa).symm
        (fun modes : Fin 3 -> kappa =>
          |(rowWeightMatrix q modes).det|)).symm
    _ = ∑ a : kappa, ∑ b : kappa, ∑ c : kappa,
        |(rowWeightMatrix q ![a, b, c]).det| := by
      simp only [Fintype.sum_prod_type]
      rfl
    _ <= ∑ a : kappa, ∑ b : kappa, ∑ c : kappa,
        (q a 0 * q b 1 * q c 2 +
        q a 0 * q b 2 * q c 1 +
        q a 1 * q b 0 * q c 2 +
        q a 1 * q b 2 * q c 0 +
        q a 2 * q b 0 * q c 1 +
        q a 2 * q b 1 * q c 0) := by
      apply Finset.sum_le_sum
      intro a _ha
      apply Finset.sum_le_sum
      intro b _hb
      apply Finset.sum_le_sum
      intro c _hc
      exact hpoint a b c
    _ <= 48 := by
      simp_rw [Finset.sum_add_distrib]
      linarith [hterm 0 1 2, hterm 0 2 1, hterm 1 0 2,
        hterm 1 2 0, hterm 2 0 1, hterm 2 1 0]

/-- If three directions all have squared norm two, the sum of the absolute
values of their ordered projector-weight minors is at most `48`, independently
of the dimension of the Hermitian matrix. -/
theorem orderedProjectorWeightMatrix_sum_abs_det_le_48
    (A : HermitianMatrix iota) (hsimple : SimpleOrderedSpectrum A)
    (directions : Fin 3 -> iota -> Real)
    (hdirections : forall s, directions s ⬝ᵥ directions s = 2) :
    (∑ modes : Fin 3 -> Fin (Fintype.card iota),
      |(orderedProjectorWeightMatrix A modes directions).det|) <= 48 := by
  let q : Fin (Fintype.card iota) -> Fin 3 -> Real :=
    fun k s => directions s ⬝ᵥ
      (orderedModeProjector A k *ᵥ directions s)
  have hq : forall k s, 0 <= q k s := by
    intro k s
    exact orderedModeProjector_quadraticWeight_nonneg
      A hsimple k (directions s)
  have hsum : forall s, (∑ k, q k s) <= 2 := by
    intro s
    exact (sum_orderedModeProjector_quadraticWeight
      A hsimple (directions s)).le.trans_eq (hdirections s)
  change (∑ modes : Fin 3 -> Fin (Fintype.card iota),
    |(rowWeightMatrix q modes).det|) <= 48
  exact sum_abs_det_rowWeightMatrix_le_48 q hq hsum


/-- The same `48` determinant sum rule holds without spectral simplicity.
At a collision the totalized projectors of repeated modes vanish, so only an
incomplete orthogonal family remains and the determinant budget can only
decrease. -/
theorem orderedProjectorWeightMatrix_sum_abs_det_le_48_global
    (A : HermitianMatrix iota)
    (directions : Fin 3 -> iota -> Real)
    (hdirections : forall s, directions s ⬝ᵥ directions s = 2) :
    (∑ modes : Fin 3 -> Fin (Fintype.card iota),
      |(orderedProjectorWeightMatrix A modes directions).det|) <= 48 := by
  let q : Fin (Fintype.card iota) -> Fin 3 -> Real :=
    fun k s => directions s ⬝ᵥ
      (orderedModeProjector A k *ᵥ directions s)
  have hq : forall k s, 0 <= q k s := by
    intro k s
    exact orderedModeProjector_quadraticWeight_nonneg_global
      A k (directions s)
  have hsum : forall s, (∑ k, q k s) <= 2 := by
    intro s
    exact (sum_orderedModeProjector_quadraticWeight_le
      A (directions s)).trans_eq (hdirections s)
  change (∑ modes : Fin 3 -> Fin (Fintype.card iota),
    |(rowWeightMatrix q modes).det|) <= 48
  exact sum_abs_det_rowWeightMatrix_le_48 q hq hsum
/-- Actual periodic random-mass specialization: at every simple dual spectrum,
the complete mode-triple sum of genuine three-site projector minors is bounded
by `48`, uniformly in the finite volume and in the chosen sites and masses. -/
theorem actualThreeMassProjectorWeightMatrix_sum_abs_det_le_48
    {N : Nat} [NeZero N] (hN : 2 <= N)
    (fixed : Lattice.PositiveMassConfig N)
    (site0 site1 site2 : Lattice.Site N)
    (triple : MassTriple)
    (hsimple : SimpleOrderedSpectrum
      (actualThreeMassDualHermitian fixed site0 site1 site2 triple)) :
    (∑ modes : Fin 3 -> Fin (Fintype.card (Lattice.Site N)),
      |(actualThreeMassProjectorWeightMatrix
        fixed site0 site1 site2 modes triple).det|) <= 48 := by
  unfold actualThreeMassProjectorWeightMatrix
  apply orderedProjectorWeightMatrix_sum_abs_det_le_48 _ hsimple
  intro s
  unfold actualThreeMassCycleDirection
  exact cycleMassPerturbationVector_dot_self hN
    (actualThreeMassSelectedSite site0 site1 site2 s)


/-- Actual periodic random-mass specialization of the global sum rule.  It is
uniform in volume, sites, and masses, and has no simple-spectrum or
projector-minor nonvanishing hypothesis. -/
theorem actualThreeMassProjectorWeightMatrix_sum_abs_det_le_48_global
    {N : Nat} [NeZero N] (hN : 2 <= N)
    (fixed : Lattice.PositiveMassConfig N)
    (site0 site1 site2 : Lattice.Site N)
    (triple : MassTriple) :
    (∑ modes : Fin 3 -> Fin (Fintype.card (Lattice.Site N)),
      |(actualThreeMassProjectorWeightMatrix
        fixed site0 site1 site2 modes triple).det|) <= 48 := by
  unfold actualThreeMassProjectorWeightMatrix
  apply orderedProjectorWeightMatrix_sum_abs_det_le_48_global
  intro s
  unfold actualThreeMassCycleDirection
  exact cycleMassPerturbationVector_dot_self hN
    (actualThreeMassSelectedSite site0 site1 site2 s)
end

end ArchonPhysics.ActualThreeMassProjectorMinorSummability
