import Mathlib.Topology.Order.Compact
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Uniform separation of Jacobian degeneracy from resonance

For the lifted spectral coarea argument, ordinary small measure of a bad
Jacobian set is not enough: the normalized sinc-square kernel has height of
order `T` near zero mismatch.  What is sufficient is algebraic exclusion of a
simultaneous Jacobian zero and resonance zero on the compact mass support.

Continuity and compactness then upgrade this pointwise exclusion to two
strictly positive uniform thresholds: whenever the Jacobian is smaller than
the first threshold, the mismatch is bounded below by the second one.
-/

namespace ArchonPhysics.CompactResonanceJacobianSeparation

open Set

noncomputable section

/-- On a compact set, two continuous real observables with no common zero are
uniformly separated: sufficiently small values of the first force a positive
lower bound for the absolute value of the second. -/
theorem exists_positive_jacobianThreshold_resonanceGap
    {Alpha : Type*} [TopologicalSpace Alpha]
    (compactSet : Set Alpha) (hcompact : IsCompact compactSet)
    (jacobian mismatch : Alpha -> Real)
    (hjacobian : ContinuousOn jacobian compactSet)
    (hmismatch : ContinuousOn mismatch compactSet)
    (hnoCommonZero : ∀ point ∈ compactSet,
      jacobian point ≠ 0 ∨ mismatch point ≠ 0) :
    ∃ jacobianThreshold resonanceGap : Real,
      0 < jacobianThreshold ∧
      0 < resonanceGap ∧
      ∀ point ∈ compactSet,
        |jacobian point| < jacobianThreshold ->
          resonanceGap <= |mismatch point| := by
  let jointSize : Alpha -> Real :=
    fun point => |jacobian point| + |mismatch point|
  have hjointContinuous : ContinuousOn jointSize compactSet := by
    exact hjacobian.abs.add hmismatch.abs
  have hjointPositive : ∀ point ∈ compactSet, 0 < jointSize point := by
    intro point hpoint
    rcases hnoCommonZero point hpoint with hjacobianNonzero | hmismatchNonzero
    · exact add_pos_of_pos_of_nonneg (abs_pos.mpr hjacobianNonzero)
        (abs_nonneg _)
    · exact add_pos_of_nonneg_of_pos (abs_nonneg _)
        (abs_pos.mpr hmismatchNonzero)
  obtain ⟨jointLower, hjointLowerPositive, hjointLower⟩ :=
    hcompact.exists_forall_le' hjointContinuous hjointPositive
  refine ⟨jointLower / 2, jointLower / 2,
    half_pos hjointLowerPositive, half_pos hjointLowerPositive, ?_⟩
  intro point hpoint hjacobianSmall
  have htotal := hjointLower point hpoint
  dsimp [jointSize] at htotal
  linarith

end

end ArchonPhysics.CompactResonanceJacobianSeparation
