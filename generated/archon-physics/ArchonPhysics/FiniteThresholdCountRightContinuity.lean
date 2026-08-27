import ArchonPhysics.FiniteThresholdCountLocalConstancy

/-!
# Right continuity of finite spectral threshold counts

Because the convention is `lambda <= E`, every finite Hermitian spectral
count is locally constant when the threshold approaches `E` from within
`[E, infinity)`, even when `E` itself is an eigenvalue.  This supplies the
zero-energy endpoint needed by the finite-block IDS continuity argument.
-/

namespace ArchonPhysics.FiniteThresholdCountRightContinuity

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomMassAcousticCountingComparison
open Filter Set Topology

noncomputable section

theorem eventually_orderedEigenvalueThresholdCount_eq_within_Ici
    {index : Type*} [Fintype index] [DecidableEq index]
    (A : HermitianMatrix index) (E : Real) :
    ∀ᶠ x in 𝓝[Ici E] E,
      orderedEigenvalueThresholdCount A x =
        orderedEigenvalueThresholdCount A E := by
  have hleg (k : Fin (Fintype.card index)) :
      ∀ᶠ x in 𝓝[Ici E] E,
        (orderedEigenvalue A k ≤ x ↔
          orderedEigenvalue A k ≤ E) := by
    by_cases hle : orderedEigenvalue A k ≤ E
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact ⟨fun _ => hle, fun _ => hle.trans hx⟩
    · have hgt : E < orderedEigenvalue A k := lt_of_not_ge hle
      have hnear : ∀ᶠ x in 𝓝[Ici E] E,
          x < orderedEigenvalue A k :=
        (show ∀ᶠ x in 𝓝 E, x < orderedEigenvalue A k from
          Iio_mem_nhds hgt).filter_mono inf_le_left
      filter_upwards [hnear] with x hx
      constructor <;> intro h
      · exact (not_le_of_gt hx h).elim
      · exact (hle h).elim
  have hall : ∀ᶠ x in 𝓝[Ici E] E, ∀ k : Fin (Fintype.card index),
      (orderedEigenvalue A k ≤ x ↔ orderedEigenvalue A k ≤ E) :=
    Filter.eventually_all.2 hleg
  filter_upwards [hall] with x hx
  unfold orderedEigenvalueThresholdCount orderedEigenvalueThresholdIndices
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hx k

/-- Real-valued finite threshold counts are continuous from the right at
every threshold, including spectral thresholds. -/
theorem continuousWithinAt_orderedEigenvalueThresholdCount_Ici
    {index : Type*} [Fintype index] [DecidableEq index]
    (A : HermitianMatrix index) (E : Real) :
    ContinuousWithinAt
      (fun x : Real => (orderedEigenvalueThresholdCount A x : Real))
      (Ici E) E := by
  have hlocal :=
    eventually_orderedEigenvalueThresholdCount_eq_within_Ici A E
  apply (continuousWithinAt_const :
    ContinuousWithinAt (fun _ : Real =>
      (orderedEigenvalueThresholdCount A E : Real)) (Ici E) E).congr_of_eventuallyEq
  · filter_upwards [hlocal] with x hx
    exact_mod_cast hx
  · rfl

end

end ArchonPhysics.FiniteThresholdCountRightContinuity
