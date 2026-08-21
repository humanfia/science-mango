import Submission.Kakeya.ConvexFactoring.NonConcentration

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family6CanonicalFrostmanConstantCoreV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring

noncomputable section

universe u

/-- The exact ratio that normalizes global maximal concentration by the mass
captured in the ambient convex body.  This is the pure generic core of the
canonical Frostman selector. -/
def canonicalFrostmanConstant
    {index : Type u} [Fintype index]
    (F : ConvexFamily index) (K : ConvexBody Space) : ENNReal :=
  maximalConcentration F * volume (K : Set Space) / containedMass F K

/-- If every indexed body lies in `K`, its contained mass is the full indexed
family volume. -/
theorem containedMass_eq_familyVolume_of_contained
    {index : Type u} [Fintype index]
    (F : ConvexFamily index) (K : ConvexBody Space)
    (hcontained : ∀ i, (F i : Set Space) ⊆ (K : Set Space)) :
    containedMass F K = familyVolume F := by
  classical
  unfold containedMass familyVolume containedIndices
  simp [hcontained]

#print axioms canonicalFrostmanConstant
#print axioms containedMass_eq_familyVolume_of_contained

end
end Family6CanonicalFrostmanConstantCoreV1
