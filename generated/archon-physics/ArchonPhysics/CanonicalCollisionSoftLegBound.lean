import ArchonPhysics.FrozenCollisionPerSiteNormalization
import ArchonPhysics.HarmonicNormalizedEdgeFrame
import ArchonPhysics.RandomMassThreeWaveCollisionNetwork
import ArchonPhysics.NormalizedPhaseEffectiveWeightBound
import ArchonPhysics.ReducedHarmonicSpectrum
import ArchonPhysics.ThreeLegKernelApproximationAlgebra
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Infrared mass bound for the canonical cubic collision measure

This module proves a deterministic, finite-volume estimate for the part of
the physical positive-mode cubic collision measure in which at least one
frequency is at most `delta`.  The proof uses the complete normalized bond
edge frame and finite-dimensional Parseval/Bessel identities.  It does not
use an integrated density of states or a scalar eigenvalue counting bound.

The canonical ordered Lagrange projector is totalized to zero at a repeated
eigenvalue.  We retain that exact convention below: isolated modes factor
through the normalized edge frame, while repeated modes have zero active
coefficient.  Consequently no simple-spectrum assumption is needed.
-/

open scoped BigOperators Matrix ENNReal

namespace ArchonPhysics.CanonicalCollisionSoftLegBound

open ArchonPhysics
open ArchonPhysics.CollisionFourierWeakLimitBridge
open ArchonPhysics.ComplexRegularizedMarkedLegBridge
open ArchonPhysics.FrozenCollisionPerSiteNormalization
open ArchonPhysics.FrozenUniformCollisionFiniteMeasureBound
open ArchonPhysics.HarmonicModes
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedInteractionSpectralFactorization
open ArchonPhysics.OrderedInteractionSpectralFactorization.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.NormalizedPhaseEffectiveWeightBound
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open ArchonPhysics.ReducedHarmonicSpectrum
open ArchonPhysics.ThreeLegKernelApproximationAlgebra
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open MeasureTheory

noncomputable section

/-! ## The unique translation zero mode, without positive-mode simplicity -/

/-- The fixed last ordered index is the only zero-frequency harmonic mode.
Positive eigenvalues may still be repeated. -/
theorem orderedModeFrequency_pos_iff_ne_last_unconditional
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k : HarmonicOrderedModeIndex N) :
    0 < orderedModeFrequency (harmonicHermitian m) k ↔
      k ≠ lastOrderedIndex (ι := Lattice.Site N) := by
  classical
  let A := harmonicHermitian m
  let z : HarmonicOrderedModeIndex N :=
    lastOrderedIndex (ι := Lattice.Site N)
  constructor
  · intro hk hkz
    subst k
    simp [orderedModeFrequency, harmonic_lastOrderedEigenvalue_eq_zero]
      at hk
  · intro hk
    have hlambda : 0 ≤ orderedEigenvalue A k := by
      simpa [A] using harmonicHermitian_orderedEigenvalue_nonneg m k
    rw [orderedModeFrequency]
    exact Real.sqrt_pos.2 (lt_of_le_of_ne hlambda (Ne.symm fun hzero => by
      have hz : orderedEigenvalue A z = 0 := by
        simpa [A, z] using harmonic_lastOrderedEigenvalue_eq_zero m
      let f : Fin 2 → Lattice.Site N :=
        ![orderedIndexEquiv k, orderedIndexEquiv z]
      have hkz' : k ≠ z := by simpa [z] using hk
      have hf : Function.Injective f := by
        intro a b
        fin_cases a <;> fin_cases b <;>
          simp [f, hkz', Ne.symm hkz']
      let rawv : Fin 2 → Lattice.Configuration N :=
        fun r => ⇑(A.2.eigenvectorBasis (f r))
      have hrawv : LinearIndependent Real rawv := by
        have hb := A.2.eigenvectorBasis.toBasis.linearIndependent.comp f hf
        rw [Fintype.linearIndependent_iff] at hb ⊢
        intro g hg
        apply hb g
        ext x
        have hx := congrFun hg x
        simpa [rawv] using hx
      let v : Fin 2 → LinearMap.ker (harmonicLinearMap m) := fun r =>
        ⟨rawv r, by
          rw [LinearMap.mem_ker]
          change Matrix.mulVec (matrixVal A) (rawv r) = 0
          fin_cases r
          · have heigen := matrixVal_mulVec_eigenvectorBasis A k
            simpa [A, f, rawv, hzero] using heigen
          · have heigen := matrixVal_mulVec_eigenvectorBasis A z
            simpa [A, f, rawv, hz] using heigen⟩
      have hv : LinearIndependent Real v := by
        rw [Fintype.linearIndependent_iff]
        intro g hg
        have hcoe := congrArg
          (fun x : LinearMap.ker (harmonicLinearMap m) =>
            (x : Lattice.Configuration N)) hg
        simp only [Submodule.coe_sum, Submodule.coe_smul,
          Submodule.coe_zero] at hcoe
        have hrawv' := hrawv
        rw [Fintype.linearIndependent_iff] at hrawv'
        exact hrawv' g (by simpa [v] using hcoe)
      have htwo : 2 ≤ Module.finrank Real
          (LinearMap.ker (harmonicLinearMap m)) := by
        simpa using hv.fintype_card_le_finrank
      rw [harmonicKernel_finrank m] at htwo
      omega))

/-! ## An unconditional complete normalized edge frame -/

/-- Positive raw edge modes remain orthonormal after division by frequency;
only uniqueness of the translation zero mode is needed. -/
theorem normalizedOrderedRawEdgeMode_inner_unconditional
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
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
      (orderedModeFrequency_pos_iff_ne_last_unconditional m k).2 hk
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

/-- The harmonic normalized edge frame is an orthonormal basis for every
positive mass configuration, even when positive eigenvalues are repeated. -/
theorem harmonicNormalizedEdgeFrame_orthonormal_unconditional
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
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
        (normalizedOrderedRawEdgeMode_inner_unconditional m k q hk' hq')


/-! ## Exact factorization of the totalized canonical projector -/

/-- The eigenvalue coefficient that survives Mathlib's totalized ordered
Lagrange projector: repeated ordered eigenvalues have coefficient zero. -/
def activeOrderedEigenvalue {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : OrderedModeIndex N) : Real := by
  classical
  exact if IsolatedOrderedMode (harmonicHermitian m) k then
    orderedEigenvalue (harmonicHermitian m) k
  else 0

/-- Every canonical projected bond kernel factors through the complete edge
frame with the active (isolated-mode) eigenvalue coefficient.  This matches
exactly the repository's totalized projector at spectral degeneracies. -/
theorem projectedBondKernel_eq_activeOrderedEigenvalue_mul_edgeFrame
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (k : OrderedModeIndex N) (j l : Lattice.Site N) :
    projectedBondKernel (massWeightedDifferenceMatrix m)
        (harmonicHermitian m) k j l =
      activeOrderedEigenvalue m k *
        harmonicNormalizedEdgeFrame m k j *
          harmonicNormalizedEdgeFrame m k l := by
  classical
  by_cases hisolated : IsolatedOrderedMode (harmonicHermitian m) k
  · have hprojector := orderedModeProjector_eq_vecMulVec_of_isolated
      (harmonicHermitian m) hisolated
    unfold projectedBondKernel
    rw [hprojector, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMul_transpose]
    change orderedRawEdgeMode m k j * orderedRawEdgeMode m k l = _
    simp only [activeOrderedEigenvalue, if_pos hisolated]
    by_cases hk : k = lastOrderedIndex (ι := Lattice.Site N)
    · subst k
      have hzero := orderedRawEdgeMode_last_eq_zero m
      have hzj : orderedRawEdgeMode m
          (lastOrderedIndex (ι := Lattice.Site N)) j = 0 := congrFun hzero j
      have hzl : orderedRawEdgeMode m
          (lastOrderedIndex (ι := Lattice.Site N)) l = 0 := congrFun hzero l
      rw [hzj, hzl, zero_mul, harmonic_lastOrderedEigenvalue_eq_zero m,
        zero_mul]
      ring
    · have hfrequency : 0 < orderedModeFrequency (harmonicHermitian m) k :=
        (orderedModeFrequency_pos_iff_ne_last_unconditional m k).2 hk
      simp only [harmonicNormalizedEdgeFrame, if_neg hk]
      rw [← orderedModeFrequency_sq_eq_orderedEigenvalue]
      field_simp [ne_of_gt hfrequency]
  · have hrepeat : ∃ q, ∃ _ : q ≠ k,
        orderedEigenvalue (harmonicHermitian m) q =
          orderedEigenvalue (harmonicHermitian m) k := by
      simpa only [IsolatedOrderedMode, not_forall, Classical.not_imp,
        not_ne_iff] using hisolated
    obtain ⟨q, hqk, heq⟩ := hrepeat
    have hprojector : orderedModeProjector (harmonicHermitian m) k = 0 :=
      orderedModeProjector_eq_zero_of_repeated
        (harmonicHermitian m) hqk heq
    simp [projectedBondKernel, hprojector, activeOrderedEigenvalue, hisolated]

/-! ## Pure orthonormal-frame cubic tensor bound -/

/-- A finite-dimensional Parseval/Bessel bound for a cubic contraction of
three spectral kernels.  One kernel is controlled entrywise and the other two
by their exact Frobenius (Parseval) norms, so division by the common frame
cardinality removes the volume factor. -/
theorem abs_cubicSpectralKernel_div_card_le
    {mode bond : Type*} [Fintype mode] [DecidableEq mode] [Nonempty mode]
    [Fintype bond]
    (u : mode → bond → Real)
    (hcard : Fintype.card mode = Fintype.card bond)
    (horth : ∀ k q, ∑ j, u k j * u q j = if k = q then 1 else 0)
    (weight : Fin 3 → mode → Real) (bound : Fin 3 → Real)
    (hbound : ∀ r, 0 ≤ bound r)
    (hweight : ∀ r k, |weight r k| ≤ bound r) :
    |(∑ j, ∑ l, ∏ r : Fin 3,
        spectralKernel u (weight r) j l) /
        (Fintype.card mode : Real)| ≤
      bound 0 * bound 1 * bound 2 := by
  classical
  let K : Fin 3 → bond → bond → Complex := fun r j l =>
    (spectralKernel u (weight r) j l : Complex)
  have hrow : ∀ j, rowEnergy u j ≤ 1 :=
    rowEnergy_le_one_of_orthonormal_of_card_eq u hcard horth
  have hentry : ∀ j l, ‖K 0 j l‖ ≤ bound 0 := by
    intro j l
    dsimp [K]
    rw [Complex.norm_real, Real.norm_eq_abs]
    simpa [spectralKernel] using spectralKernel_sub_entry_abs_le u (weight 0)
      (fun _ => 0) (bound 0) (hbound 0) hrow
      (fun k => by simpa using hweight 0 k) j l
  have hfrob (r : Fin 3) :
      Real.sqrt (frobeniusSq (K r)) ≤
        Real.sqrt (Fintype.card mode : Real) * bound r := by
    change Real.sqrt (frobeniusSq (fun j l =>
      ((spectralKernel u (weight r) j l : Real) : Complex))) ≤ _
    rw [frobeniusSq_ofReal_eq_realFrobeniusSq]
    exact sqrt_realFrobeniusSq_spectralKernel_le u (weight r) horth
      (bound r) (hbound r) (hweight r)
  have hmain := norm_tripleSum_div_volume_le
    (K 0) (K 1) (K 2) (Fintype.card mode : Real)
    (bound 0) (bound 1) (bound 2)
    (by exact_mod_cast Fintype.card_pos)
    (hbound 0) (hbound 1) hentry (hfrob 1) (hfrob 2)
  have hcardpos : 0 < (Fintype.card mode : Real) := by
    exact_mod_cast Fintype.card_pos
  rw [abs_div, abs_of_pos hcardpos]
  simpa [K, tripleSum, Fin.prod_univ_three, ← Complex.ofReal_sum,
    ← Complex.ofReal_mul, Real.norm_eq_abs] using hmain

/-! ## Exact normalized effective-leg weights -/

/-- Multiplying the physical inverse-frequency normalization by one harmonic
eigenvalue gives exactly half the frequency, including at zero. -/
theorem abs_orderedEigenvalue_mul_inv_two_frequency
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k : OrderedModeIndex N) :
    |orderedEigenvalue (harmonicHermitian m) k *
        (2 * orderedModeFrequency (harmonicHermitian m) k)⁻¹| =
      orderedModeFrequency (harmonicHermitian m) k / 2 := by
  have h := norm_eigenvalue_mul_orderedNormalizedPhaseLeg
    m (fun _ => InteractionSign.plus) 0 0 k
  simpa [orderedNormalizedPhaseLeg, orderedPhaseLeg, orderedModeFrequency] using h

/-- Totalized repeated-mode projectors can only decrease the normalized
one-leg effective weight. -/
theorem abs_activeOrderedEigenvalue_mul_inv_two_frequency_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k : OrderedModeIndex N) :
    |activeOrderedEigenvalue m k *
        (2 * orderedModeFrequency (harmonicHermitian m) k)⁻¹| ≤
      orderedModeFrequency (harmonicHermitian m) k / 2 := by
  classical
  by_cases hisolated : IsolatedOrderedMode (harmonicHermitian m) k
  · simp only [activeOrderedEigenvalue, if_pos hisolated]
    exact le_of_eq (abs_orderedEigenvalue_mul_inv_two_frequency m k)
  · rw [activeOrderedEigenvalue, if_neg hisolated, zero_mul, abs_zero]
    exact div_nonneg (Real.sqrt_nonneg _) (by norm_num)

/-! ## Positive and soft physical leg filters -/

/-- Numeric indicator of the strictly positive ordered harmonic sector. -/
def orderedPositiveFrequencyIndicator {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : OrderedModeIndex N) : Real :=
  if 0 < orderedModeFrequency (harmonicHermitian m) k then 1 else 0

/-- Numeric indicator of a strictly positive ordered frequency at most
`delta`. -/
def orderedSoftPositiveFrequencyIndicator {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (delta : Real)
    (k : OrderedModeIndex N) : Real :=
  if 0 < orderedModeFrequency (harmonicHermitian m) k ∧
      orderedModeFrequency (harmonicHermitian m) k ≤ delta then 1 else 0

/-- For one selected leg `r`, use the soft-positive indicator there and the
strictly-positive indicator on the other two legs. -/
def orderedSingleSoftLegIndicator {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (delta : Real) (r : Fin 3)
    (s : Fin 3) (k : OrderedModeIndex N) : Real :=
  if s = r then orderedSoftPositiveFrequencyIndicator m delta k
  else orderedPositiveFrequencyIndicator m k

/-- Numeric indicator of the selected positive-and-soft triple event. -/
def orderedSingleSoftTripleIndicator {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (delta : Real) (r : Fin 3)
    (modes : OrderedModeTriple N) : Real := by
  classical
  exact if IsPositiveOrderedTriple m modes ∧
      orderedModeFrequency (harmonicHermitian m) (modes r) ≤ delta then 1 else 0

/-- The product of the three numeric leg indicators is exactly the canonical
positive-triple filter together with softness of the selected leg. -/
theorem prod_orderedSingleSoftLegIndicator
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) (r : Fin 3) (modes : OrderedModeTriple N) :
    (∏ s, orderedSingleSoftLegIndicator m delta r s (modes s)) =
      orderedSingleSoftTripleIndicator m delta r modes := by
  classical
  unfold orderedSingleSoftTripleIndicator
  by_cases htarget : IsPositiveOrderedTriple m modes ∧
      orderedModeFrequency (harmonicHermitian m) (modes r) ≤ delta
  · rw [if_pos htarget]
    apply Finset.prod_eq_one
    intro s _hs
    have hspos : 0 < orderedModeFrequency
        (harmonicHermitian m) (modes s) :=
      (mem_orderedPositiveModeIndices_iff m (modes s)).1 (htarget.1 s)
    by_cases hsr : s = r
    · subst s
      simp [orderedSingleSoftLegIndicator,
        orderedSoftPositiveFrequencyIndicator, hspos, htarget.2]
    · simp [orderedSingleSoftLegIndicator, orderedPositiveFrequencyIndicator,
        hsr, hspos]
  · rw [if_neg htarget]
    by_cases hpositive : IsPositiveOrderedTriple m modes
    · have hrpos : 0 < orderedModeFrequency
          (harmonicHermitian m) (modes r) :=
        (mem_orderedPositiveModeIndices_iff m (modes r)).1 (hpositive r)
      have hrnot : ¬ orderedModeFrequency
          (harmonicHermitian m) (modes r) ≤ delta :=
        fun hr => htarget ⟨hpositive, hr⟩
      apply Finset.prod_eq_zero (Finset.mem_univ r)
      simp [orderedSingleSoftLegIndicator,
        orderedSoftPositiveFrequencyIndicator, hrpos, hrnot]
    · simp only [IsPositiveOrderedTriple, not_forall] at hpositive
      obtain ⟨s, hs⟩ := hpositive
      have hsnot : ¬ 0 < orderedModeFrequency
          (harmonicHermitian m) (modes s) := by
        intro hspos
        exact hs ((mem_orderedPositiveModeIndices_iff m (modes s)).2 hspos)
      apply Finset.prod_eq_zero (Finset.mem_univ s)
      by_cases hsr : s = r
      · subst s
        simp [orderedSingleSoftLegIndicator,
          orderedSoftPositiveFrequencyIndicator, hsnot]
      · simp [orderedSingleSoftLegIndicator, orderedPositiveFrequencyIndicator,
          hsr, hsnot]

/-- Total physical normalized collision weight for positive triples whose
selected leg has frequency at most `delta`. -/
def positiveOrderedSingleSoftLegInteractionWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) (r : Fin 3) : Real := by
  classical
  exact ∑ modes : OrderedModeTriple N,
    if IsPositiveOrderedTriple m modes ∧
        orderedModeFrequency (harmonicHermitian m) (modes r) ≤ delta then
      harmonicOrderedNormalizedInteractionWeight m modes
    else 0

/-- Total physical normalized collision weight for positive triples with at
least one frequency at most `delta`. -/
def positiveOrderedSoftLegInteractionWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) : Real := by
  classical
  exact ∑ modes : OrderedModeTriple N,
    if IsPositiveOrderedTriple m modes ∧ ∃ r,
        orderedModeFrequency (harmonicHermitian m) (modes r) ≤ delta then
      harmonicOrderedNormalizedInteractionWeight m modes
    else 0

/-- Every single-leg soft collision weight is nonnegative. -/
theorem positiveOrderedSingleSoftLegInteractionWeight_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) (r : Fin 3) :
    0 ≤ positiveOrderedSingleSoftLegInteractionWeight m delta r := by
  classical
  unfold positiveOrderedSingleSoftLegInteractionWeight
  apply Finset.sum_nonneg
  intro modes _hmodes
  split_ifs
  · exact harmonicOrderedNormalizedInteractionWeight_nonneg m modes
  · exact le_rfl

/-- The any-leg soft collision weight is nonnegative. -/
theorem positiveOrderedSoftLegInteractionWeight_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) :
    0 ≤ positiveOrderedSoftLegInteractionWeight m delta := by
  classical
  unfold positiveOrderedSoftLegInteractionWeight
  apply Finset.sum_nonneg
  intro modes _hmodes
  split_ifs
  · exact harmonicOrderedNormalizedInteractionWeight_nonneg m modes
  · exact le_rfl

/-! ## Exact factorization of one-soft-leg collision mass -/

/-- Effective edge-frame coefficient of one additional real leg indicator
after the exact physical inverse-frequency normalization. -/
def activeNormalizedIndicatorEffectiveWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (indicator : OrderedModeIndex N → Real) (k : OrderedModeIndex N) : Real :=
  activeOrderedEigenvalue m k * indicator k *
    (2 * orderedModeFrequency (harmonicHermitian m) k)⁻¹

/-- A physically normalized, indicator-weighted projected bond kernel is
exactly the spectral kernel of the active effective weights. -/
theorem weightedProjectedBondKernel_harmonicNormalizedLegWeight_eq_spectralKernel
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (weight : Fin 3 → OrderedModeIndex N → Real) (r : Fin 3) :
    weightedProjectedBondKernel (massWeightedDifferenceMatrix m)
        (harmonicHermitian m) (harmonicNormalizedLegWeight m weight r) =
      spectralKernel (harmonicNormalizedEdgeFrame m)
        (activeNormalizedIndicatorEffectiveWeight m (weight r)) := by
  classical
  ext j l
  unfold weightedProjectedBondKernel spectralKernel
    harmonicNormalizedLegWeight activeNormalizedIndicatorEffectiveWeight
  apply Finset.sum_congr rfl
  intro k _hk
  rw [projectedBondKernel_eq_activeOrderedEigenvalue_mul_edgeFrame]
  ring

/-- The selected-soft-leg physical collision weight is the exact cubic
contraction of three active spectral kernels. -/
theorem positiveOrderedSingleSoftLegInteractionWeight_eq_spectralKernel
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) (r : Fin 3) :
    positiveOrderedSingleSoftLegInteractionWeight m delta r =
      ∑ j, ∑ l, ∏ s : Fin 3,
        spectralKernel (harmonicNormalizedEdgeFrame m)
          (activeNormalizedIndicatorEffectiveWeight m
            (orderedSingleSoftLegIndicator m delta r s)) j l := by
  classical
  let weight : Fin 3 → OrderedModeIndex N → Real :=
    orderedSingleSoftLegIndicator m delta r
  calc
    positiveOrderedSingleSoftLegInteractionWeight m delta r =
        ∑ modes : OrderedModeTriple N,
          harmonicOrderedNormalizedInteractionWeight m modes *
            ∏ s, weight s (modes s) := by
      unfold positiveOrderedSingleSoftLegInteractionWeight
      apply Finset.sum_congr rfl
      intro modes _hmodes
      rw [prod_orderedSingleSoftLegIndicator]
      unfold orderedSingleSoftTripleIndicator
      by_cases hsoft : IsPositiveOrderedTriple m modes ∧
          orderedModeFrequency (harmonicHermitian m) (modes r) ≤ delta
      · simp [hsoft]
      · simp [hsoft]
    _ = ∑ j, ∑ l, ∏ s,
        weightedProjectedBondKernel (massWeightedDifferenceMatrix m)
          (harmonicHermitian m) (harmonicNormalizedLegWeight m weight s) j l :=
      harmonicWeightedNormalizedInteractionMoment_factorization m weight
    _ = ∑ j, ∑ l, ∏ s : Fin 3,
        spectralKernel (harmonicNormalizedEdgeFrame m)
          (activeNormalizedIndicatorEffectiveWeight m (weight s)) j l := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro l _hl
      apply Finset.prod_congr rfl
      intro s _hs
      rw [weightedProjectedBondKernel_harmonicNormalizedLegWeight_eq_spectralKernel]
    _ = ∑ j, ∑ l, ∏ s : Fin 3,
        spectralKernel (harmonicNormalizedEdgeFrame m)
          (activeNormalizedIndicatorEffectiveWeight m
            (orderedSingleSoftLegIndicator m delta r s)) j l := by
      rfl

/-! ## Per-site bound for one selected soft leg -/

/-- A positive-sector normalized leg is bounded by half any supplied uniform
frequency ceiling. -/
theorem abs_activeNormalized_positiveIndicator_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (ceiling : Real) (hceiling : 0 ≤ ceiling)
    (hfrequency : ∀ k, orderedModeFrequency (harmonicHermitian m) k ≤ ceiling)
    (k : OrderedModeIndex N) :
    |activeNormalizedIndicatorEffectiveWeight m
        (orderedPositiveFrequencyIndicator m) k| ≤ ceiling / 2 := by
  classical
  by_cases hpositive : 0 < orderedModeFrequency (harmonicHermitian m) k
  · have hmain := abs_activeOrderedEigenvalue_mul_inv_two_frequency_le m k
    have hupper := hmain.trans
      (div_le_div_of_nonneg_right (hfrequency k) (by norm_num))
    simpa [activeNormalizedIndicatorEffectiveWeight,
      orderedPositiveFrequencyIndicator, hpositive] using hupper
  · rw [activeNormalizedIndicatorEffectiveWeight,
      orderedPositiveFrequencyIndicator, if_neg hpositive, mul_zero,
      zero_mul, abs_zero]
    exact div_nonneg hceiling (by norm_num)

/-- A soft-positive normalized leg has effective weight at most `delta / 2`,
with no input on the number of soft modes. -/
theorem abs_activeNormalized_softPositiveIndicator_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) (hdelta : 0 ≤ delta) (k : OrderedModeIndex N) :
    |activeNormalizedIndicatorEffectiveWeight m
        (orderedSoftPositiveFrequencyIndicator m delta) k| ≤ delta / 2 := by
  classical
  by_cases hsoft : 0 < orderedModeFrequency (harmonicHermitian m) k ∧
      orderedModeFrequency (harmonicHermitian m) k ≤ delta
  · have hmain := abs_activeOrderedEigenvalue_mul_inv_two_frequency_le m k
    have hupper := hmain.trans
      (div_le_div_of_nonneg_right hsoft.2 (by norm_num))
    simpa [activeNormalizedIndicatorEffectiveWeight,
      orderedSoftPositiveFrequencyIndicator, hsoft] using hupper
  · rw [activeNormalizedIndicatorEffectiveWeight,
      orderedSoftPositiveFrequencyIndicator, if_neg hsoft, mul_zero,
      zero_mul, abs_zero]
    exact div_nonneg hdelta (by norm_num)

/-- Per-site `O(delta)` bound for collision mass with one prescribed soft leg.
The constant depends only on a uniform harmonic frequency ceiling. -/
theorem positiveOrderedSingleSoftLegInteractionWeight_div_volume_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta ceiling : Real) (hdelta : 0 ≤ delta) (hceiling : 0 ≤ ceiling)
    (hfrequency : ∀ k,
      orderedModeFrequency (harmonicHermitian m) k ≤ ceiling)
    (r : Fin 3) :
    positiveOrderedSingleSoftLegInteractionWeight m delta r /
        (N : Real) ≤
      (delta / 2) * (ceiling / 2) * (ceiling / 2) := by
  classical
  let indicator : Fin 3 → OrderedModeIndex N → Real :=
    orderedSingleSoftLegIndicator m delta r
  let effectiveWeight : Fin 3 → OrderedModeIndex N → Real := fun s =>
    activeNormalizedIndicatorEffectiveWeight m (indicator s)
  let bound : Fin 3 → Real := fun s =>
    if s = r then delta / 2 else ceiling / 2
  have hbound : ∀ s, 0 ≤ bound s := by
    intro s
    dsimp [bound]
    split_ifs
    · exact div_nonneg hdelta (by norm_num)
    · exact div_nonneg hceiling (by norm_num)
  have heffective : ∀ s k, |effectiveWeight s k| ≤ bound s := by
    intro s k
    dsimp [effectiveWeight, indicator, bound]
    by_cases hsr : s = r
    · subst s
      rw [if_pos rfl]
      have hindicator : orderedSingleSoftLegIndicator m delta r r =
          orderedSoftPositiveFrequencyIndicator m delta := by
        funext q
        simp [orderedSingleSoftLegIndicator]
      rw [hindicator]
      exact abs_activeNormalized_softPositiveIndicator_le m delta hdelta k
    · rw [if_neg hsr]
      have hindicator : orderedSingleSoftLegIndicator m delta r s =
          orderedPositiveFrequencyIndicator m := by
        funext q
        simp [orderedSingleSoftLegIndicator, hsr]
      rw [hindicator]
      exact abs_activeNormalized_positiveIndicator_le
        m ceiling hceiling hfrequency k
  have hparseval := abs_cubicSpectralKernel_div_card_le
    (u := harmonicNormalizedEdgeFrame m)
    (by simp [Lattice.Site])
    (harmonicNormalizedEdgeFrame_orthonormal_unconditional m)
    effectiveWeight bound hbound heffective
  rw [← positiveOrderedSingleSoftLegInteractionWeight_eq_spectralKernel]
    at hparseval
  have hparsevalN :
      |positiveOrderedSingleSoftLegInteractionWeight m delta r / (N : Real)| ≤
        bound 0 * bound 1 * bound 2 := by
    simpa [Lattice.Site] using hparseval
  have hNpos : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hquotient : 0 ≤
      positiveOrderedSingleSoftLegInteractionWeight m delta r / (N : Real) :=
    div_nonneg (positiveOrderedSingleSoftLegInteractionWeight_nonneg m delta r)
      hNpos.le
  rw [abs_of_nonneg hquotient] at hparsevalN
  calc
    positiveOrderedSingleSoftLegInteractionWeight m delta r / (N : Real) ≤
        bound 0 * bound 1 * bound 2 := hparsevalN
    _ = (delta / 2) * (ceiling / 2) * (ceiling / 2) := by
      fin_cases r <;> dsimp [bound]
      all_goals ring

/-! ## At least one soft leg -/

/-- A union bound over the three labeled legs.  It loses only the explicit
factor three and uses nonnegativity of the exact canonical collision weight. -/
theorem positiveOrderedSoftLegInteractionWeight_le_sum_single
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) :
    positiveOrderedSoftLegInteractionWeight m delta ≤
      ∑ r : Fin 3, positiveOrderedSingleSoftLegInteractionWeight m delta r := by
  classical
  unfold positiveOrderedSoftLegInteractionWeight
    positiveOrderedSingleSoftLegInteractionWeight
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro modes _hmodes
  by_cases hany : IsPositiveOrderedTriple m modes ∧ ∃ r,
      orderedModeFrequency (harmonicHermitian m) (modes r) ≤ delta
  · rw [if_pos hany]
    obtain ⟨hpositive, r, hrsoft⟩ := hany
    let term : Fin 3 → Real := fun s =>
      if IsPositiveOrderedTriple m modes ∧
          orderedModeFrequency (harmonicHermitian m) (modes s) ≤ delta then
        harmonicOrderedNormalizedInteractionWeight m modes
      else 0
    have hterm_nonneg : ∀ s ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ term s := by
      intro s _hs
      dsimp [term]
      split_ifs
      · exact harmonicOrderedNormalizedInteractionWeight_nonneg m modes
      · exact le_rfl
    calc
      harmonicOrderedNormalizedInteractionWeight m modes = term r := by
        simp [term, hpositive, hrsoft]
      _ ≤ ∑ s, term s :=
        Finset.single_le_sum hterm_nonneg (Finset.mem_univ r)
      _ = ∑ s : Fin 3,
          if IsPositiveOrderedTriple m modes ∧
              orderedModeFrequency (harmonicHermitian m) (modes s) ≤ delta then
            harmonicOrderedNormalizedInteractionWeight m modes
          else 0 := by rfl
  · rw [if_neg hany]
    apply Finset.sum_nonneg
    intro s _hs
    split_ifs
    · exact harmonicOrderedNormalizedInteractionWeight_nonneg m modes
    · exact le_rfl

/-- Volume-uniform `O(delta)` estimate for the total mass with at least one
soft leg, at any deterministic frequency ceiling. -/
theorem positiveOrderedSoftLegInteractionWeight_div_volume_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta ceiling : Real) (hdelta : 0 ≤ delta) (hceiling : 0 ≤ ceiling)
    (hfrequency : ∀ k,
      orderedModeFrequency (harmonicHermitian m) k ≤ ceiling) :
    positiveOrderedSoftLegInteractionWeight m delta / (N : Real) ≤
      3 * ((delta / 2) * (ceiling / 2) * (ceiling / 2)) := by
  have hNpos : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  calc
    positiveOrderedSoftLegInteractionWeight m delta / (N : Real) ≤
        (∑ r : Fin 3,
          positiveOrderedSingleSoftLegInteractionWeight m delta r) /
            (N : Real) :=
      div_le_div_of_nonneg_right
        (positiveOrderedSoftLegInteractionWeight_le_sum_single m delta)
        hNpos.le
    _ = ∑ r : Fin 3,
        positiveOrderedSingleSoftLegInteractionWeight m delta r / (N : Real) := by
      rw [Finset.sum_div]
    _ ≤ ∑ _r : Fin 3,
        ((delta / 2) * (ceiling / 2) * (ceiling / 2)) := by
      apply Finset.sum_le_sum
      intro r _hr
      exact positiveOrderedSingleSoftLegInteractionWeight_div_volume_le
        m delta ceiling hdelta hceiling hfrequency r
    _ = 3 * ((delta / 2) * (ceiling / 2) * (ceiling / 2)) := by
      norm_num

variable {Omega : Type*} [MeasurableSpace Omega]

/-- For every frozen iid mass realization in `[4/5,6/5]`, the exact
positive-mode collision mass with at least one frequency at most `delta` is
at most `(15/8) delta` per site.  No simple-spectrum or IDS hypothesis is
used. -/
theorem iid_positiveOrderedSoftLegInteractionWeight_div_volume_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (delta : Real) (hdelta : 0 ≤ delta) :
    positiveOrderedSoftLegInteractionWeight
        (ensemble.restrictPositiveMass (N := N) omega) delta / (N : Real) ≤
      (15 / 8 : Real) * delta := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  have hfrequency : ∀ k,
      orderedModeFrequency (harmonicHermitian m) k ≤ Real.sqrt 5 := by
    intro k
    exact iid_orderedModeFrequency_harmonic_le_sqrt_five ensemble omega k
  have hmain := positiveOrderedSoftLegInteractionWeight_div_volume_le
    m delta (Real.sqrt 5) hdelta (Real.sqrt_nonneg _) hfrequency
  calc
    positiveOrderedSoftLegInteractionWeight m delta / (N : Real) ≤
        3 * ((delta / 2) * (Real.sqrt 5 / 2) *
          (Real.sqrt 5 / 2)) := hmain
    _ = (15 / 8 : Real) * delta := by
      nlinarith [Real.sq_sqrt (show (0 : Real) ≤ 5 by norm_num)]

/-! ## Genuine soft-filtered mismatch finite measure -/

/-- The physical positive-mode weighted mismatch measure, filtered at tuple
level to triples with at least one frequency at most `delta`. -/
def positiveSoftLegWeightedMismatchMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (delta : Real) : Measure Real := by
  classical
  exact ∑ modes : OrderedModeTriple N,
    if IsPositiveOrderedTriple m modes ∧ ∃ r,
        orderedModeFrequency (harmonicHermitian m) (modes r) ≤ delta then
      ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight m modes) •
        Measure.dirac (orderedThreeWaveMismatch m sign modes)
    else 0

/-- The tuple-filtered soft mismatch measure is finite at every finite
volume. -/
theorem positiveSoftLegWeightedMismatchMeasure_isFinite
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (delta : Real) :
    IsFiniteMeasure (positiveSoftLegWeightedMismatchMeasure m sign delta) := by
  constructor
  unfold positiveSoftLegWeightedMismatchMeasure
  classical
  simp only [Measure.coe_finsetSum, Finset.sum_apply, ENNReal.sum_lt_top,
    Finset.mem_univ, forall_const]
  intro modes
  by_cases hsoft : IsPositiveOrderedTriple m modes ∧ ∃ r,
      orderedModeFrequency (harmonicHermitian m) (modes r) ≤ delta
  · simp [hsoft]
  · simp [hsoft]

/-- The genuine soft-filtered mismatch measure bundled as a finite measure. -/
def positiveSoftLegWeightedMismatchFiniteMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (delta : Real) : FiniteMeasure Real :=
  ⟨positiveSoftLegWeightedMismatchMeasure m sign delta,
    positiveSoftLegWeightedMismatchMeasure_isFinite m sign delta⟩

/-- Its mass is exactly the nonnegative-real lift of the tuple-level physical
soft collision weight. -/
theorem positiveSoftLegWeightedMismatchFiniteMeasure_mass_eq_toNNReal
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (delta : Real) :
    (positiveSoftLegWeightedMismatchFiniteMeasure m sign delta).mass =
      Real.toNNReal (positiveOrderedSoftLegInteractionWeight m delta) := by
  classical
  apply NNReal.eq
  rw [Real.coe_toNNReal _
    (positiveOrderedSoftLegInteractionWeight_nonneg m delta)]
  change (positiveSoftLegWeightedMismatchMeasure m sign delta Set.univ).toReal = _
  unfold positiveSoftLegWeightedMismatchMeasure
    positiveOrderedSoftLegInteractionWeight
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  have hfinite : ∀ modes ∈ (Finset.univ : Finset (OrderedModeTriple N)),
      (((if IsPositiveOrderedTriple m modes ∧ ∃ r,
          orderedModeFrequency (harmonicHermitian m) (modes r) ≤ delta then
          ENNReal.ofReal
              (harmonicOrderedNormalizedInteractionWeight m modes) •
            Measure.dirac (orderedThreeWaveMismatch m sign modes)
        else 0) : Measure Real) Set.univ) ≠ (⊤ : ENNReal) := by
    intro modes _hmodes
    by_cases hsoft : IsPositiveOrderedTriple m modes ∧ ∃ r,
        orderedModeFrequency (harmonicHermitian m) (modes r) ≤ delta
    · simp [hsoft]
    · simp [hsoft]
  rw [ENNReal.toReal_sum hfinite]
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hsoft : IsPositiveOrderedTriple m modes ∧ ∃ r,
      orderedModeFrequency (harmonicHermitian m) (modes r) ≤ delta
  · simp [hsoft, ENNReal.toReal_ofReal,
      harmonicOrderedNormalizedInteractionWeight_nonneg m modes]
  · simp [hsoft]

/-- Exact normalization by the physical number of sites, not by the number of
mode triples. -/
def perSitePositiveSoftLegWeightedMismatchFiniteMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (delta : Real) : FiniteMeasure Real :=
  ((N : NNReal)⁻¹) •
    positiveSoftLegWeightedMismatchFiniteMeasure m sign delta

/-- The real mass of the per-site soft collision measure is exactly the soft
tuple weight divided by `N`. -/
theorem perSitePositiveSoftLegWeightedMismatchFiniteMeasure_mass_real
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (delta : Real) :
    ((perSitePositiveSoftLegWeightedMismatchFiniteMeasure
        m sign delta).mass : Real) =
      (N : Real)⁻¹ * positiveOrderedSoftLegInteractionWeight m delta := by
  unfold perSitePositiveSoftLegWeightedMismatchFiniteMeasure
  have hsmul :
      ((((N : NNReal)⁻¹) •
        positiveSoftLegWeightedMismatchFiniteMeasure m sign delta).mass) =
        (N : NNReal)⁻¹ *
          (positiveSoftLegWeightedMismatchFiniteMeasure m sign delta).mass := by
    unfold FiniteMeasure.mass
    rw [FiniteMeasure.smul_apply]
    rfl
  rw [hsmul,
    positiveSoftLegWeightedMismatchFiniteMeasure_mass_eq_toNNReal]
  simp only [NNReal.coe_mul, NNReal.coe_inv]
  rw [Real.coe_toNNReal _
    (positiveOrderedSoftLegInteractionWeight_nonneg m delta)]
  norm_cast

/-- Uniform `O(delta)` mass bound for the genuine `/N`-normalized frozen
soft collision measure. -/
theorem iid_perSitePositiveSoftLegWeightedMismatchFiniteMeasure_mass_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (sign : Fin 3 → InteractionSign) (delta : Real) (hdelta : 0 ≤ delta) :
    ((perSitePositiveSoftLegWeightedMismatchFiniteMeasure
        (ensemble.restrictPositiveMass (N := N) omega)
        sign delta).mass : Real) ≤
      (15 / 8 : Real) * delta := by
  rw [perSitePositiveSoftLegWeightedMismatchFiniteMeasure_mass_real]
  simpa [div_eq_inv_mul] using
    iid_positiveOrderedSoftLegInteractionWeight_div_volume_le
      ensemble omega delta hdelta

/-- The soft tuple filter is formally a submeasure of the repository's
existing positive weighted mismatch measure. -/
theorem positiveSoftLegWeightedMismatchMeasure_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (delta : Real) :
    positiveSoftLegWeightedMismatchMeasure m sign delta ≤
      positiveWeightedMismatchMeasure m sign := by
  classical
  unfold positiveSoftLegWeightedMismatchMeasure
    positiveWeightedMismatchMeasure
  apply Finset.sum_le_sum
  intro modes _hmodes
  by_cases hsoft : IsPositiveOrderedTriple m modes ∧ ∃ r,
      orderedModeFrequency (harmonicHermitian m) (modes r) ≤ delta
  · rw [if_pos hsoft, if_pos hsoft.1]
  · rw [if_neg hsoft]
    exact bot_le
end

end ArchonPhysics.CanonicalCollisionSoftLegBound
