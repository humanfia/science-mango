import ArchonPhysics.CoerciveHamiltonianContinuation
import ArchonPhysics.MassWeightedHamiltonianDynamics
import ArchonPhysics.MeasurableOrderedHarmonicEnergy
import ArchonPhysics.MeasurableOrderedModeCoupling
import ArchonPhysics.RandomMassOrderedProjectorBridge

/-!
# Vanishing physical energy of the translation zero mode

For canonical momentum in the translation-reduced sector, the mass-weighted
momentum `Y = M^(-1/2) p` is orthogonal to the mass-square-root translation
vector.  On a simple harmonic spectrum the unique ordered zero projector is
the rank-one projector onto that translation line, hence it annihilates `Y`.
The zero ordered mode consequently carries exactly zero physical harmonic
energy, and summing over the strictly positive ordered modes gives both the
complete ordered sum and the mass-weighted harmonic energy.

No measurable eigenbasis is selected.  Mathlib's noncomputable Hermitian
eigenbasis occurs only inside deterministic proofs of projector identities.
-/

open scoped Matrix

namespace ArchonPhysics.TranslationZeroModeEnergy

open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedHarmonicEnergy
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.ReducedHarmonicSpectrum
open ArchonPhysics.SpectralBandEnergyObservable

noncomputable section

/-- The basis-free mass-weighted harmonic energy on the reduced physical
phase space. -/
def reducedMassWeightedHarmonicEnergy
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (q : ReducedPositionSpace m) (p : ReducedMomentumSpace N) : Real :=
  let X := sqrtMassTransform m (q : HilbertConfiguration N)
  let Y := inverseSqrtMassTransform m (p : HilbertConfiguration N)
  (coordinateEnergy Y +
      (X : Lattice.Configuration N) ⬝ᵥ
        (massWeightedHarmonicMatrix m *ᵥ
          (X : Lattice.Configuration N))) / 2

/-- Zero total canonical momentum is exactly orthogonality, after the
inverse-square-root mass transform, to the translation vector. -/
theorem inverseSqrtMassTransform_dot_translationMode_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (p : ReducedMomentumSpace N) :
    (inverseSqrtMassTransform m (p : HilbertConfiguration N) :
        Lattice.Configuration N) ⬝ᵥ translationMode m = 0 := by
  rw [dotProduct_comm]
  calc
    translationMode m ⬝ᵥ
          (inverseSqrtMassTransform m (p : HilbertConfiguration N) :
            Lattice.Configuration N) =
        ∑ i : Lattice.Site N, (p : HilbertConfiguration N) i := by
          unfold dotProduct
          apply Finset.sum_congr rfl
          intro i _hi
          rw [inverseSqrtMassTransform_apply]
          change Real.sqrt (m.mass i) *
              ((Real.sqrt (m.mass i))⁻¹ * (p : HilbertConfiguration N) i) = _
          rw [← mul_assoc,
            mul_inv_cancel₀ (Real.sqrt_ne_zero'.2 (m.mass_pos i)), one_mul]
    _ = 0 := (mem_reducedMomentumSpace_iff _).1 p.property

/-- The ordered zero eigenspace is the translation line, so its rank-one
projector kills every mass-weighted reduced momentum. -/
theorem orderedZeroModeProjector_mul_massWeightedMomentum_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (z : Fin (Fintype.card (Lattice.Site N)))
    (hz : orderedEigenvalue (harmonicHermitian m) z = 0)
    (p : ReducedMomentumSpace N) :
    orderedModeProjector (harmonicHermitian m) z *ᵥ
        (inverseSqrtMassTransform m (p : HilbertConfiguration N) :
          Lattice.Configuration N) = 0 := by
  let A := harmonicHermitian m
  let v : Lattice.Configuration N :=
    ⇑(A.2.eigenvectorBasis (orderedIndexEquiv z))
  have hvker : v ∈ LinearMap.ker (harmonicLinearMap m) := by
    rw [LinearMap.mem_ker]
    change massWeightedHarmonicMatrix m *ᵥ v = 0
    have heigen := matrixVal_mulVec_eigenvectorBasis A z
    have hmatrix : matrixVal A = massWeightedHarmonicMatrix m := by
      rfl
    rw [hmatrix] at heigen
    have heigen' : massWeightedHarmonicMatrix m *ᵥ v =
        orderedEigenvalue A z • v := by
      simpa [v] using heigen
    rw [heigen', show orderedEigenvalue A z = 0 by simpa [A] using hz, zero_smul]
  have hvspan : v ∈ Real ∙ translationMode m := by
    rw [← harmonicLinearMap_ker_eq_span]
    exact hvker
  rw [Submodule.mem_span_singleton] at hvspan
  obtain ⟨c, hc⟩ := hvspan
  have htranslationOrthogonal : translationMode m ⬝ᵥ
      (inverseSqrtMassTransform m (p : HilbertConfiguration N) :
        Lattice.Configuration N) = 0 := by
    rw [dotProduct_comm]
    exact inverseSqrtMassTransform_dot_translationMode_eq_zero m p
  have hvorth : v ⬝ᵥ
      (inverseSqrtMassTransform m (p : HilbertConfiguration N) :
        Lattice.Configuration N) = 0 := by
    rw [← hc, smul_dotProduct, htranslationOrthogonal, smul_zero]
  rw [orderedModeProjector_eq_vecMulVec (harmonicHermitian m) hsimple z,
    Matrix.vecMulVec_mulVec]
  simp [A, v, hvorth]

/-- The unique ordered translation mode has exactly zero physical harmonic
energy for every reduced physical state. -/
theorem orderedZeroMode_physicalHarmonicEnergy_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (z : Fin (Fintype.card (Lattice.Site N)))
    (hz : orderedEigenvalue (harmonicHermitian m) z = 0)
    (q : ReducedPositionSpace m) (p : ReducedMomentumSpace N) :
    orderedHarmonicModeEnergy (harmonicHermitian m) z
        (sqrtMassTransform m (q : HilbertConfiguration N))
        (inverseSqrtMassTransform m (p : HilbertConfiguration N)) = 0 := by
  have hprojected :=
    orderedZeroModeProjector_mul_massWeightedMomentum_eq_zero
      m hsimple z hz p
  unfold orderedHarmonicModeEnergy orderedModeEnergy
    orderedModeProjectedState coordinateEnergy
  rw [hprojected, hz]
  simp

/-- Under simple spectrum, the strictly positive ordered indices are the
complete ordered index set with its unique zero index erased. -/
theorem positiveModeIndices_eq_univ_erase_zeroMode
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (z : Fin (Fintype.card (Lattice.Site N)))
    (hz : orderedEigenvalue (harmonicHermitian m) z = 0) :
    positiveModeIndices (harmonicHermitian m) = Finset.univ.erase z := by
  ext k
  rw [mem_positiveModeIndices_iff]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  rw [orderedModeFrequency]
  constructor
  · intro hk hEq
    subst k
    simp [hz] at hk
  · intro hk
    have hnonneg : 0 ≤ orderedEigenvalue (harmonicHermitian m) k := by
      have h := (massWeightedHarmonicMatrix_posSemidef m).eigenvalues_nonneg
        (orderedIndexEquiv k)
      rw [← orderedEigenvalue_equiv (harmonicHermitian m) k]
      simpa [harmonicHermitian] using h
    have hne : orderedEigenvalue (harmonicHermitian m) k ≠ 0 := by
      intro hkzero
      exact hk (hsimple (hkzero.trans hz.symm))
    exact Real.sqrt_pos.2 (lt_of_le_of_ne hnonneg (Ne.symm hne))

/-- Removing the zero-energy translation index does not change the complete
ordered physical harmonic-energy sum. -/
theorem sum_positive_physicalHarmonicModeEnergy_eq_sum_all
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (z : Fin (Fintype.card (Lattice.Site N)))
    (hz : orderedEigenvalue (harmonicHermitian m) z = 0)
    (q : ReducedPositionSpace m) (p : ReducedMomentumSpace N) :
    (∑ k ∈ positiveModeIndices (harmonicHermitian m),
        orderedHarmonicModeEnergy (harmonicHermitian m) k
          (sqrtMassTransform m (q : HilbertConfiguration N))
          (inverseSqrtMassTransform m (p : HilbertConfiguration N))) =
      ∑ k : Fin (Fintype.card (Lattice.Site N)),
        orderedHarmonicModeEnergy (harmonicHermitian m) k
          (sqrtMassTransform m (q : HilbertConfiguration N))
          (inverseSqrtMassTransform m (p : HilbertConfiguration N)) := by
  rw [positiveModeIndices_eq_univ_erase_zeroMode m hsimple z hz]
  have hzero := orderedZeroMode_physicalHarmonicEnergy_eq_zero
    m hsimple z hz q p
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ z), hzero, add_zero]

/-- The positive ordered modes carry exactly the full reduced mass-weighted
harmonic energy; the translation mode contributes no hidden kinetic term. -/
theorem sum_positive_physicalHarmonicModeEnergy_eq_reducedEnergy
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (z : Fin (Fintype.card (Lattice.Site N)))
    (hz : orderedEigenvalue (harmonicHermitian m) z = 0)
    (q : ReducedPositionSpace m) (p : ReducedMomentumSpace N) :
    (∑ k ∈ positiveModeIndices (harmonicHermitian m),
        orderedHarmonicModeEnergy (harmonicHermitian m) k
          (sqrtMassTransform m (q : HilbertConfiguration N))
          (inverseSqrtMassTransform m (p : HilbertConfiguration N))) =
      reducedMassWeightedHarmonicEnergy m q p := by
  rw [sum_positive_physicalHarmonicModeEnergy_eq_sum_all
    m hsimple z hz q p]
  rw [sum_orderedHarmonicModeEnergy (harmonicHermitian m) hsimple]
  rfl

end

end ArchonPhysics.TranslationZeroModeEnergy
