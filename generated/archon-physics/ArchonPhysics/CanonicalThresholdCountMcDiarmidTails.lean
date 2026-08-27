import ArchonPhysics.CanonicalThresholdCountMcDiarmid

/-!
# Lower and two-sided canonical McDiarmid tails

This module derives the lower and two-sided fixed-volume bounds from the
sharp sub-Gaussian certificate in `CanonicalThresholdCountMcDiarmid`.
-/

namespace ArchonPhysics.CanonicalThresholdCountMcDiarmidTails

open ArchonPhysics
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open ArchonPhysics.CanonicalThresholdCountMcDiarmid
open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- Sharp lower-tail form, written as a positive deviation of the negated
centered count. -/
theorem canonicalNormalizedHarmonicThresholdCount_mcDiarmid_lowerTail
    (N : Nat) [NeZero N] (E : Real) {epsilon : Real}
    (hepsilon : 0 <= epsilon) :
    RandomEnsemble.canonicalLaw.real
        {omega | epsilon <=
          -(canonicalNormalizedHarmonicThresholdCount N E omega -
            (∫ eta, canonicalNormalizedHarmonicThresholdCount N E eta
              ∂(RandomEnsemble.canonicalLaw)))} <=
      Real.exp (-2 * (N : Real) * epsilon ^ 2) := by
  have htail :=
    (canonicalNormalizedHarmonicThresholdCount_hasMcDiarmidMGF N E).neg.measure_ge_le
      hepsilon
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  convert htail using 1
  · rfl
  · congr 1
    simp only [canonicalMcDiarmidParameter, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast]
    field_simp
    ring_nf

/-- Two-sided McDiarmid concentration, obtained from the two one-sided
bounds and the real-valued measure union inequality. -/
theorem canonicalNormalizedHarmonicThresholdCount_mcDiarmid_twoSided
    (N : Nat) [NeZero N] (E : Real) {epsilon : Real}
    (hepsilon : 0 <= epsilon) :
    RandomEnsemble.canonicalLaw.real
        {omega | epsilon <=
          |canonicalNormalizedHarmonicThresholdCount N E omega -
            (∫ eta, canonicalNormalizedHarmonicThresholdCount N E eta
              ∂(RandomEnsemble.canonicalLaw))|} <=
      2 * Real.exp (-2 * (N : Real) * epsilon ^ 2) := by
  let X : RandomEnsemble.SampleSpace -> Real := fun omega =>
    canonicalNormalizedHarmonicThresholdCount N E omega -
      (∫ eta, canonicalNormalizedHarmonicThresholdCount N E eta
        ∂(RandomEnsemble.canonicalLaw))
  have hset : {omega | epsilon <= |X omega|} =
      {omega | epsilon <= X omega} ∪ {omega | epsilon <= -X omega} := by
    ext omega
    change epsilon <= |X omega| ↔ epsilon <= X omega ∨ epsilon <= -X omega
    exact le_abs
  rw [show {omega | epsilon <=
        |canonicalNormalizedHarmonicThresholdCount N E omega -
          (∫ eta, canonicalNormalizedHarmonicThresholdCount N E eta
            ∂(RandomEnsemble.canonicalLaw))|} =
      {omega | epsilon <= |X omega|} by rfl, hset]
  calc
    RandomEnsemble.canonicalLaw.real
        ({omega | epsilon <= X omega} ∪ {omega | epsilon <= -X omega}) <=
      RandomEnsemble.canonicalLaw.real {omega | epsilon <= X omega} +
        RandomEnsemble.canonicalLaw.real {omega | epsilon <= -X omega} :=
      measureReal_union_le _ _
    _ <= Real.exp (-2 * (N : Real) * epsilon ^ 2) +
        Real.exp (-2 * (N : Real) * epsilon ^ 2) := by
      apply add_le_add
      · simpa [X] using
          canonicalNormalizedHarmonicThresholdCount_mcDiarmid_upperTail
            N E hepsilon
      · simpa [X] using
          canonicalNormalizedHarmonicThresholdCount_mcDiarmid_lowerTail
            N E hepsilon
    _ = 2 * Real.exp (-2 * (N : Real) * epsilon ^ 2) := by ring

end

end ArchonPhysics.CanonicalThresholdCountMcDiarmidTails
