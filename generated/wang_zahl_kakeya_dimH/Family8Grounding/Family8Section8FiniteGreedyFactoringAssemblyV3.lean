import Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
import Submission.Kakeya.ConvexFactoring.RefinementMultiplicity

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Family8Section8FiniteGreedyFactoringAssemblyV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# A callback-free finite greedy factoring/assembly connector

This theorem combines two existing actual constructions: the full finite
closed-convex-hull maximal-density partition and the exact two-stage
multiplicity-level assembly on its occurrence-indexed factorization.  Thus no
factorization object, selected level, retention statement, or multiplicity
bound is supplied by the caller.

This is deliberately not advertised as paper Lemma 5.11.  Its explicit loss
is a coarse finite-cardinality loss, and the product on the right is the
product of selected natural multiplicity levels.  In particular it does not
assert the mass-comparable coarse density or the product of the two actual
average multiplicities required by the paper-strength factorization lemma.
-/

/-- Every finite shaded convex family has an actual globally maximal greedy
partition and an actual exact two-level multiplicity refinement.  The source
average multiplicity transports to the refinement with the explicit finite
loss, while the refinement is bounded pointwise and on average by the product
of its automatically selected levels. -/
theorem exists_fullConvexGreedyExactMultiplicityAssembly
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (Y : Shading F) :
    ∃ G : GreedyDensityPartition F
        (hullCandidates (Finset.univ : Finset ι)) (hullContainer F)
        Finset.univ,
      G.coveredIndices = Finset.univ ∧
      G.length ≤ Fintype.card ι ∧
      AllWinnerGlobalCross F Finset.univ G ∧
      ∃ A : ExactAssembly (convexFactorization F G) Y
          (((Fintype.card ι + 1) * (Fintype.card ι + 1)) *
            (Fintype.card (Option (Fin (blocks F G).length)) + 1)),
        A.fineLevel ≤ Fintype.card ι ∧
        A.outerLevel ≤
          Fintype.card (Option (Fin (blocks F G).length)) ∧
        Y.averageMultiplicity ≤
          (((Fintype.card ι + 1) * (Fintype.card ι + 1)) *
              (Fintype.card (Option (Fin (blocks F G).length)) + 1)) •
            A.refinement.shading.averageMultiplicity ∧
        (∀ x,
          A.refinement.shading.pointMultiplicity x ≤
            A.outerLevel * A.fineLevel) ∧
        A.refinement.shading.averageMultiplicity ≤
          (A.outerLevel * A.fineLevel : ℕ) := by
  classical
  obtain ⟨G, hcovered, hlength, hcross⟩ :=
    exists_fullConvexGreedyDensityPartition F Finset.univ
  obtain ⟨A, hfine, houter⟩ := exists_greedyExactAssembly G Y
  have hrestrict :
      (IndexedShadingRefinement.restrictTo Y Finset.univ).shading.shadingMass =
        Y.shadingMass := by
    rw [shadingMass_restrictTo_eq_sum, Shading.shadingMass]
  have hretained : WithinFactor
      (((Fintype.card ι + 1) * (Fintype.card ι + 1)) *
        (Fintype.card (Option (Fin (blocks F G).length)) + 1))
      Y.shadingMass A.refinement.shading.shadingMass := by
    have h := A.retained
    change WithinFactor _
      (IndexedShadingRefinement.restrictTo Y Finset.univ).shading.shadingMass
      A.refinement.shading.shadingMass at h
    simpa only [hrestrict] using h
  exact ⟨G, hcovered, hlength, hcross, A, hfine, houter,
    IndexedShadingRefinement.averageMultiplicity_le A.refinement _ hretained,
    A.pointMultiplicity_le_product,
    A.averageMultiplicity_le_product⟩

#print axioms exists_fullConvexGreedyExactMultiplicityAssembly

end

end Family8Section8FiniteGreedyFactoringAssemblyV3
