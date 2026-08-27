import ArchonPhysics.ActualThreeMassLiftedJacobianFactorization
import ArchonPhysics.SingleMassRankOnePerturbation
import ArchonPhysics.ThreeParameterProjectorWeightJacobian

/-!
# Actual random-mass three-parameter projector Jacobian

For any periodic volume and any three selected mass sites, this module defines
the genuine dual-cycle mode-by-site projector matrix
`v_s dot P_{k_r} v_s`.  Raw physical mass differentiation contributes the
column scale `-m_s⁻²`, while passing from energy to positive frequency
contributes the row scale `(2 omega_r)⁻¹`.

The determinant is factored exactly.  Thus, at an interior simple-positive
configuration, all elementary scales are nonzero and actual Jacobian
nondegeneracy reduces to the single explicit projector-weight minor.
No finite-volume witness is used in this reduction.
-/

open scoped Matrix

namespace ArchonPhysics.ActualThreeMassProjectorWeightJacobian

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.SingleMassRankOnePerturbation
open ArchonPhysics.ThreeParameterProjectorWeightJacobian
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison
open Set

noncomputable section

/-- The three physical sites, in the same order as the nested `MassTriple`
coordinates. -/
def actualThreeMassSelectedSite {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N) : Fin 3 → Lattice.Site N :=
  ![site₀, site₁, site₂]

/-- The three unclipped raw mass coordinates. -/
def actualThreeMassRawCoordinate (triple : MassTriple) : Fin 3 → Real :=
  ![triple.1.1, triple.1.2, triple.2]

/-- The true edge-space dual Hermitian matrix of the three-mass family. -/
def actualThreeMassDualHermitian {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) (triple : MassTriple) :
    HermitianMatrix (Lattice.Site N) :=
  dualMassWeightedHarmonicHermitian
    (threeMassSiteConfig fixed site₀ site₁ site₂ triple)

/-- Rank-one edge directions associated to the selected physical mass
coordinates. -/
def actualThreeMassCycleDirection {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N) :
    Fin 3 → Lattice.Configuration N :=
  fun s => cycleMassPerturbationVector
    (actualThreeMassSelectedSite site₀ site₁ site₂ s)

/-- Positive-energy-to-frequency row scales. -/
def actualThreeMassFrequencyRowScale {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple) : Fin 3 → Real :=
  fun r => (2 * orderedModeFrequency
    (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
      (modes r))⁻¹

/-- Raw-mass-to-inverse-mass column scales. -/
def actualThreeMassRawMassColumnScale
    (triple : MassTriple) : Fin 3 → Real :=
  fun s => -((actualThreeMassRawCoordinate triple s) ^ 2)⁻¹

/-- The unscaled genuine dual-cycle mode-by-site projector matrix. -/
def actualThreeMassProjectorWeightMatrix {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple) : Matrix (Fin 3) (Fin 3) Real :=
  orderedProjectorWeightMatrix
    (actualThreeMassDualHermitian fixed site₀ site₁ site₂ triple) modes
    (actualThreeMassCycleDirection site₀ site₁ site₂)

/-- The predicted raw-mass derivative matrix of the three positive ordered
frequencies.  Its derivative interpretation is supplied by
Hellmann--Feynman; this definition records the exact actual-model entries. -/
def actualThreeMassFrequencyProjectorJacobianMatrix
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple) : Matrix (Fin 3) (Fin 3) Real :=
  scaledOrderedProjectorWeightMatrix
    (actualThreeMassDualHermitian fixed site₀ site₁ site₂ triple) modes
    (actualThreeMassCycleDirection site₀ site₁ site₂)
    (actualThreeMassFrequencyRowScale
      fixed site₀ site₁ site₂ modes triple)
    (actualThreeMassRawMassColumnScale triple)

/-- Exact actual-model determinant factorization. -/
theorem actualThreeMassFrequencyProjectorJacobianMatrix_det
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple) :
    (actualThreeMassFrequencyProjectorJacobianMatrix
      fixed site₀ site₁ site₂ modes triple).det =
      (∏ r, actualThreeMassFrequencyRowScale
        fixed site₀ site₁ site₂ modes triple r) *
        (actualThreeMassProjectorWeightMatrix
          fixed site₀ site₁ site₂ modes triple).det *
          (∏ s, actualThreeMassRawMassColumnScale triple s) := by
  exact det_scaledOrderedProjectorWeightMatrix _ _ _ _ _

theorem actualThreeMassRawCoordinate_ne_zero
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport) :
    ∀ s, actualThreeMassRawCoordinate triple s ≠ 0 := by
  have hs := interior_subset htriple
  intro s
  fin_cases s
  · exact ne_of_gt
      (RandomEnsemble.massLower_pos.trans_le hs.1.1.1)
  · exact ne_of_gt
      (RandomEnsemble.massLower_pos.trans_le hs.1.2.1)
  · exact ne_of_gt
      (RandomEnsemble.massLower_pos.trans_le hs.2.1)

/-- At an interior positive-energy configuration, every row and column scale
is nonzero.  Hence the actual frequency matrix is nondegenerate exactly when
the true dual-cycle projector-weight minor is nonzero. -/
theorem actualThreeMassFrequencyProjectorJacobianMatrix_det_ne_zero_iff
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport)
    (hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
        (modes r)) :
    (actualThreeMassFrequencyProjectorJacobianMatrix
      fixed site₀ site₁ site₂ modes triple).det ≠ 0 ↔
      (actualThreeMassProjectorWeightMatrix
        fixed site₀ site₁ site₂ modes triple).det ≠ 0 := by
  apply det_scaledOrderedProjectorWeightMatrix_ne_zero_iff
  · intro r
    unfold actualThreeMassFrequencyRowScale orderedModeFrequency
    exact inv_ne_zero (mul_ne_zero (by norm_num)
      (Real.sqrt_ne_zero'.2 (hpositive r)))
  · intro s
    unfold actualThreeMassRawMassColumnScale
    exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2
      (actualThreeMassRawCoordinate_ne_zero htriple s)))

end

end ArchonPhysics.ActualThreeMassProjectorWeightJacobian
