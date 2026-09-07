import Family6Grounding.Family6Lemma69UnionOfOverlapBudgetV1
import Submission.Kakeya.ConvexFactoring.DyadicOverlapSummation

/-!
# Lemma 6.9: overlap-budget producer

This file supplies the first division-free producer for the overlap budget
consumed by `lemma69_union_of_overlapBudget`.  The geometric input remains at
the honest pairwise/Katz--Tao seam: a dyadic pair majorant, containment in its
row container, nonconcentration, and the scale comparison for that container.

In particular, this file does not identify a `delta x b x c` plank with the
existing normalized slab certificate.  Such an affine-normalization bridge
belongs upstream of `hpairwise` and `hscale`.
-/

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

set_option autoImplicit false

/-- An overlap-sum factor and the scalar absorption inequality give exactly
the cross-multiplied budget required by Lemma 6.9.  No cancellation or
nonvanishing assumption is needed. -/
theorem lemma69_overlapBudget_of_overlapSum_le
    {ι : Type*} [Fintype ι] {F : ConvexFamily ι} (Y : Shading F)
    {L Q : ENNReal}
    (hoverlap :
      (∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
        Q * Y.shadingMass)
    (habsorb : L * Q ≤ Y.shadingMass) :
    L * (∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
      Y.shadingMass ^ 2 := by
  calc
    L * (∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
        L * (Q * Y.shadingMass) := by gcongr
    _ = (L * Q) * Y.shadingMass := by ac_rfl
    _ ≤ Y.shadingMass * Y.shadingMass := by gcongr
    _ = Y.shadingMass ^ 2 := by rw [pow_two]

/-- Explicit pairwise majorants plus a uniform row bound produce the Lemma
6.9 overlap budget.  This is the smallest reusable interface before choosing
a particular geometric dyadic decomposition. -/
theorem lemma69_overlapBudget_of_pairwiseMajorant_row_le
    {ι : Type*} [Fintype ι] {F : ConvexFamily ι} (Y : Shading F)
    (B : PairwiseOverlapBound Y) {L Q : ENNReal}
    (hrow : ∀ i,
      (∑ j, B.majorant i j) ≤ Q * volume (Y.carrier i))
    (habsorb : L * Q ≤ Y.shadingMass) :
    L * (∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
      Y.shadingMass ^ 2 := by
  apply lemma69_overlapBudget_of_overlapSum_le Y
  · exact B.overlapSum_le_factor_mul_shadingMass_of_row_le Q hrow
  · exact habsorb

/-- The existing dyadic pair-overlap and Katz--Tao/Frostman summation layer
feeds directly into the exact `hBudget` consumed by Lemma 6.9.  Thus the only
remaining scalar input is absorption of the explicit dyadic row factor by
the shading mass. -/
theorem lemma69_overlapBudget_of_dyadicPairwiseFrostman
    {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    {F : ConvexFamily ι} (Y : Shading F)
    (levels : Finset κ)
    (level : ι → ι → κ)
    (container : ι → κ → ConvexBody Space)
    (q : ι → κ → ENNReal)
    (C A L : ENNReal)
    (hlevel : ∀ i j, level i j ∈ levels)
    (hpairwise : ∀ i j,
      volume (Y.carrier i ∩ Y.carrier j) ≤
        q i (level i j) * volume (F j : Set Space))
    (hcontained : ∀ i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao C F)
    (hscale : ∀ i k, k ∈ levels →
      q i k * volume (container i k : Set Space) ≤
        A * volume (Y.carrier i))
    (habsorb :
      L * (((levels.card : ENNReal) * C * A)) ≤ Y.shadingMass) :
    L * (∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
      Y.shadingMass ^ 2 := by
  let B : PairwiseOverlapBound Y :=
    dyadicPairwiseOverlapBound level q hpairwise
  apply lemma69_overlapBudget_of_pairwiseMajorant_row_le
    Y B (Q := ((levels.card : ENNReal) * C * A))
  · intro i
    exact dyadicOverlapMajorant_row_le levels level container q C A
      hlevel hcontained hKT hscale i
  · exact habsorb

#print axioms lemma69_overlapBudget_of_overlapSum_le
#print axioms lemma69_overlapBudget_of_pairwiseMajorant_row_le
#print axioms lemma69_overlapBudget_of_dyadicPairwiseFrostman

end

end Submission.Kakeya.ConvexFactoring
