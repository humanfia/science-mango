import ArchonPhysics.OrderedSingleModeProjector
import ArchonPhysics.RandomMassSimpleSpectrum

/-!
# Almost-sure ordered single-mode resolution for iid random masses

The positive spectrum is almost surely simple by the nonzero resultant
certificate.  The deterministic harmonic kernel has dimension exactly one,
so this upgrades to simplicity of the full ordered spectrum: a second zero
eigenvalue would produce two independent vectors in that kernel.

All deterministic ordered-projector identities can therefore be applied
almost surely.  The Lagrange projector formula remains globally defined and
measurable, including on the null exceptional set.
-/

open scoped Matrix

namespace ArchonPhysics.RandomMassOrderedProjectorBridge

open ArchonPhysics.HarmonicModes
open ArchonPhysics.HermitianEigenvalueMultiplicity
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassSimpleSpectrum
open ArchonPhysics.ReducedHarmonicSpectrum
open MeasureTheory

noncomputable section

/-- Positive ordered simplicity plus the deterministic one-dimensional
translation kernel imply simplicity of the complete harmonic spectrum. -/
theorem simpleOrderedSpectrum_of_not_orderedPositiveDuplicate
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hpositive : ¬ HasOrderedPositiveDuplicate m) :
    SimpleOrderedSpectrum
      ⟨massWeightedHarmonicMatrix m,
        (massWeightedHarmonicMatrix_posSemidef m).isHermitian⟩ := by
  let A : HermitianMatrix (Lattice.Site N) :=
    ⟨massWeightedHarmonicMatrix m,
      (massWeightedHarmonicMatrix_posSemidef m).isHermitian⟩
  intro i j hij
  by_contra hne
  have hi_nonneg : 0 ≤ orderedEigenvalue A i := by
    have hi := (massWeightedHarmonicMatrix_posSemidef m).eigenvalues_nonneg
      (orderedIndexEquiv i)
    rw [← orderedEigenvalue_equiv A i]
    simpa [A] using hi
  by_cases hi_pos : 0 < orderedEigenvalue A i
  · exact hpositive ⟨i, j, hne, hi_pos, hij⟩
  · have hi_zero : orderedEigenvalue A i = 0 :=
      le_antisymm (not_lt.mp hi_pos) hi_nonneg
    obtain ⟨v, hv, heigen⟩ :=
      exists_linearIndependent_eigenvectors_of_eigenvalues₀_eq A.2
        (by simpa [orderedEigenvalue, A] using hij) hne
    let u : Fin 2 → LinearMap.ker (harmonicLinearMap m) := fun k ↦
      ⟨v k, by
        rw [LinearMap.mem_ker]
        change Matrix.mulVec (massWeightedHarmonicMatrix m) (v k) = 0
        have hk := heigen k
        rw [show A.2.eigenvalues₀ i = 0 by
          simpa [orderedEigenvalue, A] using hi_zero] at hk
        simpa [A] using hk⟩
    have hu : LinearIndependent Real u := by
      apply LinearIndependent.of_comp
        (LinearMap.ker (harmonicLinearMap m)).subtype
      simpa [u, Function.comp_def] using hv
    have htwo : 2 ≤
        Module.finrank Real (LinearMap.ker (harmonicLinearMap m)) := by
      simpa using hu.fintype_card_le_finrank
    rw [harmonicKernel_finrank] at htwo
    omega

/-- Every positive-mass realization has exactly one ordered zero eigenvalue.
No convention about which concrete ordered index is the last index is needed. -/
theorem existsUnique_orderedEigenvalue_eq_zero_of_simple
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum
      ⟨massWeightedHarmonicMatrix m,
        (massWeightedHarmonicMatrix_posSemidef m).isHermitian⟩) :
    ∃! k : Fin (Fintype.card (Lattice.Site N)),
      orderedEigenvalue
        ⟨massWeightedHarmonicMatrix m,
          (massWeightedHarmonicMatrix_posSemidef m).isHermitian⟩ k = 0 := by
  let sample : Unit → Lattice.PositiveMassConfig N := fun _ ↦ m
  obtain ⟨k, hk⟩ :=
    exists_harmonicOrderedEigenvalue_eq_zero sample ()
  refine ⟨k, ?_, ?_⟩
  · simpa [harmonicOrderedEigenvalue, harmonicHermitianSample, sample] using hk
  · intro y hy
    apply hsimple
    calc
      orderedEigenvalue
          ⟨massWeightedHarmonicMatrix m,
            (massWeightedHarmonicMatrix_posSemidef m).isHermitian⟩ y = 0 := hy
      _ = orderedEigenvalue
          ⟨massWeightedHarmonicMatrix m,
            (massWeightedHarmonicMatrix_posSemidef m).isHermitian⟩ k := by
        symm
        simpa [harmonicOrderedEigenvalue, harmonicHermitianSample, sample] using hk

/-- The unique zero index exactly complements the positive ordered sector. -/
theorem exists_orderedZeroMode_and_positive_iff_ne_of_simple
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum
      ⟨massWeightedHarmonicMatrix m,
        (massWeightedHarmonicMatrix_posSemidef m).isHermitian⟩) :
    ∃ z : Fin (Fintype.card (Lattice.Site N)),
      orderedEigenvalue
          ⟨massWeightedHarmonicMatrix m,
            (massWeightedHarmonicMatrix_posSemidef m).isHermitian⟩ z = 0 ∧
      ∀ k, 0 < orderedEigenvalue
          ⟨massWeightedHarmonicMatrix m,
            (massWeightedHarmonicMatrix_posSemidef m).isHermitian⟩ k ↔ k ≠ z := by
  obtain ⟨z, hz, hunique⟩ :=
    existsUnique_orderedEigenvalue_eq_zero_of_simple m hsimple
  refine ⟨z, hz, fun k ↦ ?_⟩
  constructor
  · intro hk hEq
    subst k
    linarith
  · intro hk
    have hnonneg : 0 ≤ orderedEigenvalue
        ⟨massWeightedHarmonicMatrix m,
          (massWeightedHarmonicMatrix_posSemidef m).isHermitian⟩ k := by
      let A : HermitianMatrix (Lattice.Site N) :=
        ⟨massWeightedHarmonicMatrix m,
          (massWeightedHarmonicMatrix_posSemidef m).isHermitian⟩
      have h := (massWeightedHarmonicMatrix_posSemidef m).eigenvalues_nonneg
        (orderedIndexEquiv k)
      rw [← orderedEigenvalue_equiv A k]
      simpa [A] using h
    exact lt_of_le_of_ne hnonneg (Ne.symm fun hzero ↦ hk (hunique k hzero))

/-- Package of all exact ordered single-mode resolution identities requested
downstream.  Hermitian plus idempotent means each `P_k` is an orthogonal
projector; pairwise products and projected-state dot products vanish. -/
def OrderedModeResolutionIdentities
    {N : Nat} [NeZero N]
    (A : HermitianMatrix (Lattice.Site N))
    (state : Lattice.Configuration N) : Prop :=
  (∀ k, (orderedModeProjector A k).IsHermitian) ∧
  (∀ k, IsIdempotentElem (orderedModeProjector A k)) ∧
  (∀ k l, k ≠ l →
    orderedModeProjector A k * orderedModeProjector A l = 0) ∧
  (∀ k l, k ≠ l →
    orderedModeProjectedState A k state ⬝ᵥ
      orderedModeProjectedState A l state = 0) ∧
  (∑ k, orderedModeProjector A k) = 1 ∧
  (∀ k, matrixVal A * orderedModeProjector A k =
    orderedEigenvalue A k • orderedModeProjector A k) ∧
  (∑ k, orderedModeEnergy A k state) =
    SpectralBandEnergyObservable.coordinateEnergy state

theorem orderedModeResolutionIdentities_of_simple
    {N : Nat} [NeZero N]
    (A : HermitianMatrix (Lattice.Site N))
    (state : Lattice.Configuration N)
    (hsimple : SimpleOrderedSpectrum A) :
    OrderedModeResolutionIdentities A state := by
  refine ⟨orderedModeProjector_isHermitian A,
    orderedModeProjector_isIdempotentElem A hsimple,
    ?_, ?_, orderedModeProjector_sum_eq_one A hsimple,
    matrixVal_mul_orderedModeProjector A hsimple,
    orderedModeEnergy_sum_eq_coordinateEnergy A hsimple state⟩
  · intro k l hkl
    exact orderedModeProjector_mul_eq_zero A hsimple hkl
  · intro k l hkl
    exact orderedModeProjectedState_orthogonal A hsimple hkl state

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Coordinate measurability of the finite positive-mass sample supplied by
any verified iid ensemble. -/
theorem measurable_restrictPositiveMass_coordinate
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (i : Lattice.Site N) :
    Measurable fun omega ↦
      (ensemble.restrictPositiveMass (N := N) omega).mass i := by
  simpa using ensemble.mass_measurable i.val

/-- Full ordered harmonic spectrum simplicity holds almost surely for every
verified iid ensemble. -/
theorem simpleOrderedSpectrum_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    ∀ᵐ omega ∂ensemble.probability,
      SimpleOrderedSpectrum
        (harmonicHermitianSample
          (ensemble.restrictPositiveMass (N := N)) omega) := by
  have hnot : ∀ᵐ omega ∂ensemble.probability,
      ¬ HasOrderedPositiveDuplicate
        (ensemble.restrictPositiveMass (N := N) omega) :=
    measure_eq_zero_iff_ae_notMem.mp
      (probability_orderedPositiveDuplicate_eq_zero ensemble hN)
  filter_upwards [hnot] with omega homega
  exact simpleOrderedSpectrum_of_not_orderedPositiveDuplicate _ homega

/-- The unique translation zero mode is the sole ordered zero eigenvalue,
almost surely (in fact deterministically once simplicity holds). -/
theorem existsUnique_orderedZeroMode_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    ∀ᵐ omega ∂ensemble.probability,
      ∃! k : Fin (Fintype.card (Lattice.Site N)),
        harmonicOrderedEigenvalue
          (ensemble.restrictPositiveMass (N := N)) omega k = 0 := by
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN] with omega hsimple
  simpa [harmonicOrderedEigenvalue, harmonicHermitianSample] using
    existsUnique_orderedEigenvalue_eq_zero_of_simple
      (ensemble.restrictPositiveMass (N := N) omega) hsimple
/-- Almost surely, one random ordered index is the translation zero mode and
all other ordered indices are exactly the positive sector. -/
theorem orderedPositive_iff_ne_zeroMode_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    ∀ᵐ omega ∂ensemble.probability,
      ∃ z : Fin (Fintype.card (Lattice.Site N)),
        harmonicOrderedEigenvalue
            (ensemble.restrictPositiveMass (N := N)) omega z = 0 ∧
        ∀ k, 0 < harmonicOrderedEigenvalue
            (ensemble.restrictPositiveMass (N := N)) omega k ↔ k ≠ z := by
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN] with omega hsimple
  simpa [harmonicOrderedEigenvalue, harmonicHermitianSample] using
    exists_orderedZeroMode_and_positive_iff_ne_of_simple
      (ensemble.restrictPositiveMass (N := N) omega) hsimple


/-- Every exact ordered projector identity and the per-mode energy sum hold
almost surely for an arbitrary realization-dependent state. -/
theorem orderedModeResolutionIdentities_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (state : Omega → Lattice.Configuration N) :
    ∀ᵐ omega ∂ensemble.probability,
      OrderedModeResolutionIdentities
        (harmonicHermitianSample
          (ensemble.restrictPositiveMass (N := N)) omega)
        (state omega) := by
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN] with omega hsimple
  exact orderedModeResolutionIdentities_of_simple _ _ hsimple

/-- Projector entries remain measurable globally, without restricting the
sample space to the almost-sure simplicity event. -/
theorem measurable_orderedModeProjector_apply
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (k : Fin (Fintype.card (Lattice.Site N)))
    (u v : Lattice.Site N) :
    Measurable fun omega ↦
      OrderedSingleModeProjector.orderedModeProjector
        (harmonicHermitianSample
          (ensemble.restrictPositiveMass (N := N)) omega) k u v := by
  exact (OrderedSingleModeProjector.measurable_orderedModeProjector_apply
      k u v).comp
    (measurable_harmonicHermitianSample _
      (measurable_restrictPositiveMass_coordinate ensemble))

/-- For a measurable random state, every fixed ordered-mode energy is
measurable globally. -/
theorem measurable_orderedModeEnergy
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (state : Omega → Lattice.Configuration N) (hstate : Measurable state)
    (k : Fin (Fintype.card (Lattice.Site N))) :
    Measurable fun omega ↦
      OrderedSingleModeProjector.orderedModeEnergy
        (harmonicHermitianSample
          (ensemble.restrictPositiveMass (N := N)) omega) k
        (state omega) := by
  exact OrderedSingleModeProjector.measurable_orderedModeEnergy
    _ (measurable_harmonicHermitianSample _
      (measurable_restrictPositiveMass_coordinate ensemble))
    state hstate k

/-- Canonical `[4/5,6/5]` iid masses have a complete measurable ordered
single-mode resolution almost surely. -/
theorem canonical_orderedModeResolutionIdentities_ae
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (state : RandomEnsemble.SampleSpace → Lattice.Configuration N) :
    ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
      OrderedModeResolutionIdentities
        (harmonicHermitianSample
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N)) omega)
        (state omega) :=
  orderedModeResolutionIdentities_ae
    canonicalIIDMassPhaseEnsemble hN state

end

end ArchonPhysics.RandomMassOrderedProjectorBridge
