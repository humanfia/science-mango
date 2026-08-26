import ArchonPhysics.ModeCoupling
import ArchonPhysics.NormalizedModeCoupling
import ArchonPhysics.OrderedSingleModeProjector

/-!
# Basis-free measurable squared mode couplings

The sign of a real eigenvector is not canonically measurable, while the
squared interaction coefficient entering a second-order collision kernel is
sign-invariant.  This module writes that square directly in terms of the
ordered rank-one spectral projectors.

For a bond matrix `B` and a simple Hermitian matrix `A`, the projected bond
kernel is `B P_k(A) Bᵀ`.  Its `(j,l)` entry is the product of the `j` and
`l` bond coefficients of the corresponding normalized eigenvector.  A double
bond sum therefore recovers the square of every finite interaction tensor.
The projector formula is total and measurable even at degeneracies; equality
with an individual-mode tensor is asserted only under simple spectrum.
-/

open scoped Matrix

namespace ArchonPhysics.MeasurableOrderedModeCoupling

open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector

noncomputable section

variable {iota bond : Type*}
variable [Fintype iota] [DecidableEq iota]

/-- The bond covariance carried by one ordered spectral projector. -/
def projectedBondKernel (B : Matrix bond iota Real)
    (A : HermitianMatrix iota) (k : Fin (Fintype.card iota)) :
    Matrix bond bond Real :=
  B * orderedModeProjector A k * B.transpose

/-- A basis-free double-bond formula for a squared order-`n` interaction
coefficient. -/
def orderedInteractionWeightSq [Fintype bond] {n : Nat} (B : Matrix bond iota Real)
    (A : HermitianMatrix iota)
    (modes : Fin n → Fin (Fintype.card iota)) : Real :=
  ∑ j, ∑ l, ∏ r, projectedBondKernel B A (modes r) j l

/-- On simple spectrum, the Lagrange projector is the outer product of the
corresponding normalized eigenvector with itself. -/
theorem orderedModeProjector_eq_vecMulVec
    (A : HermitianMatrix iota) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card iota)) :
    orderedModeProjector A k =
      Matrix.vecMulVec
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k))
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k)) := by
  apply matrix_eq_of_mulVec_eigenvectorBasis_eq A
  intro r
  rw [orderedModeProjector_mulVec_eigenvectorBasis A hsimple]
  rw [Matrix.vecMulVec_mulVec]
  have hdot :
      ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k)) ⬝ᵥ
          ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
        if r = k then 1 else 0 := by
    have hinner := A.2.eigenvectorBasis.inner_eq_ite
      (orderedIndexEquiv r) (orderedIndexEquiv k)
    simpa [EuclideanSpace.inner_eq_star_dotProduct, eq_comm] using hinner
  rw [hdot]
  by_cases hr : r = k
  · subst r
    simp
  · simp [hr]

/-- On simple spectrum the projected bond kernel is the outer product of the
corresponding bond-coordinate vector. -/
theorem projectedBondKernel_apply_eq_mul
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card iota)) (j l : bond) :
    projectedBondKernel B A k j l =
      (B *ᵥ ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k))) j *
        (B *ᵥ ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k))) l := by
  unfold projectedBondKernel
  rw [orderedModeProjector_eq_vecMulVec A hsimple k,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  rfl

/-- The basis-free double-bond expression is exactly the square of the usual
eigenvector interaction coefficient on simple spectrum. -/
theorem orderedInteractionWeightSq_eq_sq [Fintype bond]
    {n : Nat} (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (hsimple : SimpleOrderedSpectrum A)
    (modes : Fin n → Fin (Fintype.card iota)) :
    orderedInteractionWeightSq B A modes =
      (∑ j, ∏ r,
        (B *ᵥ ⇑(A.2.eigenvectorBasis (orderedIndexEquiv (modes r)))) j) ^ 2 := by
  unfold orderedInteractionWeightSq
  simp_rw [projectedBondKernel_apply_eq_mul B A hsimple]
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _hl
  rw [← Finset.prod_mul_distrib]

/-- Every entry of the projected bond kernel is measurable when both the
Hermitian sample and the bond-matrix entries are measurable. -/
theorem measurable_projectedBondKernel_apply
    {Omega : Type*} [MeasurableSpace Omega]
    (B : Omega → Matrix bond iota Real)
    (hB : ∀ j u, Measurable fun omega ↦ B omega j u)
    (A : Omega → HermitianMatrix iota) (hA : Measurable A)
    (k : Fin (Fintype.card iota)) (j l : bond) :
    Measurable fun omega ↦ projectedBondKernel (B omega) (A omega) k j l := by
  unfold projectedBondKernel
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.measurable_sum
  intro u _hu
  apply Measurable.mul
  · apply Finset.measurable_sum
    intro v _hv
    exact (hB j v).mul
      ((measurable_orderedModeProjector_apply k v u).comp hA)
  · simpa using hB l u

/-- The basis-free squared interaction weight is measurable without choosing
a measurable eigenvector. -/
theorem measurable_orderedInteractionWeightSq [Fintype bond]
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (B : Omega → Matrix bond iota Real)
    (hB : ∀ j u, Measurable fun omega ↦ B omega j u)
    (A : Omega → HermitianMatrix iota) (hA : Measurable A)
    (modes : Fin n → Fin (Fintype.card iota)) :
    Measurable fun omega ↦ orderedInteractionWeightSq (B omega) (A omega) modes := by
  unfold orderedInteractionWeightSq
  apply Finset.measurable_sum
  intro j _hj
  apply Finset.measurable_sum
  intro l _hl
  apply Finset.measurable_prod
  intro r _hr
  exact measurable_projectedBondKernel_apply B hB A hA (modes r) j l

namespace Harmonic

open ArchonPhysics
open ArchonPhysics.HarmonicModes
open ArchonPhysics.ModeCoupling
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.MeasurableHarmonicData
open ArchonPhysics.OrderedSpectrumContinuity

/-- The mass-weighted harmonic matrix bundled as a real Hermitian matrix. -/
def harmonicHermitian {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :
    HermitianMatrix (Lattice.Site N) :=
  ⟨massWeightedHarmonicMatrix m,
    (massWeightedHarmonicMatrix_posSemidef m).isHermitian⟩

/-- Basis-free squared ordered interaction tensor for one positive-mass realization. -/
def harmonicOrderedInteractionWeightSq {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (modes : Fin n → Fin (Fintype.card (Lattice.Site N))) : Real :=
  orderedInteractionWeightSq (massWeightedDifferenceMatrix m)
    (harmonicHermitian m) modes

/-- The basis-free expression recovers the square of the existing tensor. -/
theorem harmonicOrderedInteractionWeightSq_eq
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (modes : Fin n → Fin (Fintype.card (Lattice.Site N))) :
    harmonicOrderedInteractionWeightSq m modes =
      (interactionTensor m n (fun r ↦ orderedIndexEquiv (modes r))) ^ 2 := by
  rw [harmonicOrderedInteractionWeightSq,
    orderedInteractionWeightSq_eq_sq _ _ hsimple]
  congr 1

/-- The ordered basis-free tensor square is measurable for every measurable mass sample. -/
theorem measurable_harmonicOrderedInteractionWeightSq
    {Omega : Type*} [MeasurableSpace Omega]
    {N n : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ i, Measurable fun omega ↦ (massSample omega).mass i)
    (modes : Fin n → Fin (Fintype.card (Lattice.Site N))) :
    Measurable fun omega ↦
      harmonicOrderedInteractionWeightSq (massSample omega) modes := by
  apply measurable_orderedInteractionWeightSq
    (B := fun omega ↦ massWeightedDifferenceMatrix (massSample omega))
    (A := fun omega ↦ harmonicHermitian (massSample omega))
  · intro j u
    exact (measurable_massWeightedDifferenceMatrix_of_coordinate
      massSample hmass).eval.eval
  · apply Measurable.subtype_mk
    exact measurable_massWeightedHarmonicMatrix_of_coordinate massSample hmass

/-- Ordered positive-frequency normalization of the basis-free tensor square. -/
def harmonicOrderedNormalizedInteractionWeight
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (modes : Fin n → Fin (Fintype.card (Lattice.Site N))) : Real :=
  harmonicOrderedInteractionWeightSq m modes *
    ∏ r, (2 * orderedModeFrequency (harmonicHermitian m) (modes r))⁻¹

/-- Ordered harmonic frequencies agree with the existing eigenbasis indexing. -/
theorem orderedModeFrequency_harmonicHermitian_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k : Fin (Fintype.card (Lattice.Site N))) :
    orderedModeFrequency (harmonicHermitian m) k =
      modeFrequency m (orderedIndexEquiv k) := by
  unfold orderedModeFrequency modeFrequency
  congr 1
  rw [← orderedEigenvalue_equiv (harmonicHermitian m) k]
  unfold harmonicHermitian modeFrequencySq
  rfl

/-- On simple spectrum the measurable basis-free normalized weight is exactly
the physical squared vertex previously defined from the normal-mode basis. -/
theorem harmonicOrderedNormalizedInteractionWeight_eq
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (modes : Fin n → Fin (Fintype.card (Lattice.Site N))) :
    harmonicOrderedNormalizedInteractionWeight m modes =
      ArchonPhysics.NormalizedModeCoupling.normalizedInteractionWeight m
        (fun r ↦ orderedIndexEquiv (modes r)) := by
  unfold harmonicOrderedNormalizedInteractionWeight
    ArchonPhysics.NormalizedModeCoupling.normalizedInteractionWeight
  rw [harmonicOrderedInteractionWeightSq_eq m hsimple]
  congr 1
  apply Finset.prod_congr rfl
  intro r _hr
  rw [orderedModeFrequency_harmonicHermitian_eq]

/-- The physical squared ordered vertex is measurable without an eigenbasis selection. -/
theorem measurable_harmonicOrderedNormalizedInteractionWeight
    {Omega : Type*} [MeasurableSpace Omega]
    {N n : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ i, Measurable fun omega ↦ (massSample omega).mass i)
    (modes : Fin n → Fin (Fintype.card (Lattice.Site N))) :
    Measurable fun omega ↦
      harmonicOrderedNormalizedInteractionWeight (massSample omega) modes := by
  apply (measurable_harmonicOrderedInteractionWeightSq
    massSample hmass modes).mul
  apply Finset.measurable_prod
  intro r _hr
  have hA : Measurable (fun omega ↦ harmonicHermitian (massSample omega)) := by
    apply Measurable.subtype_mk
    exact measurable_massWeightedHarmonicMatrix_of_coordinate massSample hmass
  have hfrequency : Measurable fun omega ↦
      orderedModeFrequency (harmonicHermitian (massSample omega)) (modes r) :=
    (measurable_orderedModeFrequencies_unconditional
      (fun omega ↦ harmonicHermitian (massSample omega)) hA).eval
  exact (measurable_const.mul hfrequency).inv

end Harmonic

end

end ArchonPhysics.MeasurableOrderedModeCoupling
