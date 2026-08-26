import ArchonPhysics.ReducedHarmonicSpectrum

/-!
# Translation-reduced coercivity for the periodic difference

The periodic forward difference has the constant configurations as its kernel.
This module fixes the translation gauge by restricting to configurations with
zero coordinate sum.  On that finite-dimensional subspace the forward
difference is injective, and Mathlib's
`LinearMap.injective_iff_antilipschitz` supplies a positive Poincare constant.

The constant is existential and depends only on the finite chain size and the
ambient sup norm.  No spectral-gap value, eigenbasis choice, probability law,
or external analytic hypothesis is introduced.
-/

namespace ArchonPhysics.TranslationReducedCoercivity

open ReducedHarmonicSpectrum

noncomputable section

/-- Sum of all coordinates of a finite periodic configuration. -/
def configurationSumLinearMap (N : Nat) [NeZero N] :
    Lattice.Configuration N →ₗ[Real] Real where
  toFun q := ∑ i, q i
  map_add' q r := by
    simp [Finset.sum_add_distrib]
  map_smul' c q := by
    simp [Finset.mul_sum]

@[simp] theorem configurationSumLinearMap_apply {N : Nat} [NeZero N]
    (q : Lattice.Configuration N) :
    configurationSumLinearMap N q = ∑ i, q i := by
  rfl

/-- Concrete translation gauge: configurations whose coordinate sum is zero. -/
def zeroMeanSubspace (N : Nat) [NeZero N] :
    Submodule Real (Lattice.Configuration N) :=
  LinearMap.ker (configurationSumLinearMap N)

theorem mem_zeroMeanSubspace_iff {N : Nat} [NeZero N]
    (q : Lattice.Configuration N) :
    q ∈ zeroMeanSubspace N ↔ ∑ i, q i = 0 := by
  simp [zeroMeanSubspace]

/-- The periodic forward difference as a linear map. -/
def forwardDifferenceLinearMap (N : Nat) [NeZero N] :
    Lattice.Configuration N →ₗ[Real] Lattice.Configuration N :=
  HarmonicModes.differenceMatrix.mulVecLin

@[simp] theorem forwardDifferenceLinearMap_apply {N : Nat} [NeZero N]
    (q : Lattice.Configuration N) :
    forwardDifferenceLinearMap N q = Lattice.forwardDifference q := by
  exact HarmonicModes.differenceMatrix_mulVec q

/-- Forward difference restricted to the zero-mean translation gauge. -/
def translationReducedDifferenceLinearMap (N : Nat) [NeZero N] :
    zeroMeanSubspace N →ₗ[Real] Lattice.Configuration N :=
  (forwardDifferenceLinearMap N).comp (zeroMeanSubspace N).subtype

@[simp] theorem translationReducedDifferenceLinearMap_apply {N : Nat} [NeZero N]
    (q : zeroMeanSubspace N) :
    translationReducedDifferenceLinearMap N q =
      Lattice.forwardDifference (q : Lattice.Configuration N) := by
  simp [translationReducedDifferenceLinearMap]

/-- A zero-mean configuration with zero forward difference is zero. -/
theorem eq_zero_of_mem_zeroMean_of_forwardDifference_eq_zero
    {N : Nat} [NeZero N] (q : Lattice.Configuration N)
    (hmean : q ∈ zeroMeanSubspace N)
    (hdifference : Lattice.forwardDifference q = 0) : q = 0 := by
  obtain ⟨c, hq⟩ :=
    (forwardDifference_eq_zero_iff_constant q).mp hdifference
  have hsum : ∑ i : Lattice.Site N, q i = 0 :=
    (mem_zeroMeanSubspace_iff q).mp hmean
  have hcProduct : (N : Real) * c = 0 := by
    rw [hq] at hsum
    simpa [ZMod.card, nsmul_eq_mul] using hsum
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  have hc : c = 0 := (mul_eq_zero.mp hcProduct).resolve_left hN
  ext i
  simp [hq, hc]

/-- The translation-reduced forward difference has trivial kernel. -/
theorem translationReducedDifferenceLinearMap_ker_eq_bot
    {N : Nat} [NeZero N] :
    LinearMap.ker (translationReducedDifferenceLinearMap N) = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro q hq
  rw [LinearMap.mem_ker] at hq
  apply Subtype.ext
  exact eq_zero_of_mem_zeroMean_of_forwardDifference_eq_zero
    q q.property (by simpa using hq)

/-- Equivalently, the translation-reduced forward difference is injective. -/
theorem translationReducedDifferenceLinearMap_injective
    {N : Nat} [NeZero N] :
    Function.Injective (translationReducedDifferenceLinearMap N) := by
  exact LinearMap.ker_eq_bot.mp translationReducedDifferenceLinearMap_ker_eq_bot

/-- Finite-dimensional Poincare inequality on the concrete zero-mean gauge. -/
theorem exists_translationReduced_poincareConstant
    {N : Nat} [NeZero N] :
    ∃ C : Real, 0 < C ∧ ∀ q : zeroMeanSubspace N,
      ‖q‖ ≤ C * ‖Lattice.forwardDifference (q : Lattice.Configuration N)‖ := by
  obtain ⟨K, hK, hAnti⟩ :=
    (LinearMap.injective_iff_antilipschitz
      (translationReducedDifferenceLinearMap N)).mp
      translationReducedDifferenceLinearMap_injective
  refine ⟨K, by exact_mod_cast hK, fun q ↦ ?_⟩
  have hbound := ZeroHomClass.bound_of_antilipschitz
    (translationReducedDifferenceLinearMap N) hAnti q
  simpa using hbound

/-- Raw-configuration form of the zero-mean Poincare inequality. -/
theorem exists_zeroMean_poincareConstant {N : Nat} [NeZero N] :
    ∃ C : Real, 0 < C ∧ ∀ q : Lattice.Configuration N,
      q ∈ zeroMeanSubspace N →
        ‖q‖ ≤ C * ‖Lattice.forwardDifference q‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_translationReduced_poincareConstant (N := N)
  refine ⟨C, hC, fun q hq ↦ ?_⟩
  simpa using hbound ⟨q, hq⟩

end

end ArchonPhysics.TranslationReducedCoercivity
