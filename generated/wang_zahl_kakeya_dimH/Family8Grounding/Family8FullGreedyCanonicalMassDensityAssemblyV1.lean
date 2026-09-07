import Family8Grounding.Family8CanonicalExactAssemblyMassDensityRetentionV1
import Mathlib.Tactic

/-!
# Full-greedy canonical assembly with actual mass and density retention

For the full convex greedy partition the active fine set is literally
`Finset.univ`.  Therefore the source active-fine subtype density in the generic
mass/density bridge is exactly the original shading density.  This file
specializes the canonical saturated assembly to that actual partition and
removes the last source-active bookkeeping seam without any supplied
factorization, refinement, level, or density comparison.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullGreedyCanonicalMassDensityAssemblyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Family8ExactAssemblySameDataFiberBridgeV1.ExactAssembly
open Family8CanonicalExactAssemblyMassDensityRetentionV1
open Family8CanonicalExactAssemblyMassDensityRetentionV1.ExactAssembly

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota}

/-- In the full greedy factorization, restricting the source shading to the
active fine set changes no mass. -/
theorem fullGreedy_sourceActive_mass_eq
    (G : GreedyDensityPartition F
      (hullCandidates (Finset.univ : Finset iota)) (hullContainer F)
      Finset.univ)
    (Y : Shading F) :
    (IndexedShadingRefinement.restrictTo Y
      (convexFactorization F G).index.fine).shading.shadingMass =
        Y.shadingMass := by
  change (IndexedShadingRefinement.restrictTo Y
    (Finset.univ : Finset iota)).shading.shadingMass = Y.shadingMass
  rw [shadingMass_restrictTo_eq_sum, Shading.shadingMass]

/-- The literal active-fine subtype family of the full greedy factorization
has exactly the source family volume. -/
theorem fullGreedy_sourceActive_familyVolume_eq
    (G : GreedyDensityPartition F
      (hullCandidates (Finset.univ : Finset iota)) (hullContainer F)
      Finset.univ) :
    familyVolume
        (sourceActiveFineFamily (convexFactorization F G)) =
      familyVolume F := by
  unfold sourceActiveFineFamily
  change familyVolume
    (selectedCoarseFamily F (Finset.univ : Finset iota)) = familyVolume F
  rw [selectedCoarseFamily_volume]
  unfold familyVolume
  simp

/-- Hence the source active-fine subtype density is exactly the original
shading density, including the zero-family-volume case. -/
theorem fullGreedy_sourceActive_shadingDensity_eq
    (G : GreedyDensityPartition F
      (hullCandidates (Finset.univ : Finset iota)) (hullContainer F)
      Finset.univ)
    (Y : Shading F) :
    (sourceActiveFineShading
      (convexFactorization F G) Y).shadingDensity =
        Y.shadingDensity := by
  unfold Shading.shadingDensity
  rw [sourceActiveFineShading_shadingMass,
    fullGreedy_sourceActive_mass_eq,
    fullGreedy_sourceActive_familyVolume_eq]

/-- A fully constructed full greedy partition and canonical exact assembly retain
actual source mass and density on the literal final subtype, and realize the
two multiplicity levels as actual averages on the same final data.

The loss remains the explicit finite pigeonhole loss; replacing it by a
small power of scale is the remaining quantitative Lemma 5.11 input. -/
theorem exists_fullGreedyCanonicalActualAverageMassDensityAssembly
    (F : ConvexFamily iota) (Y : Shading F)
    (hY : Y.shadingMass ≠ 0) :
    ∃ G : GreedyDensityPartition F
        (hullCandidates (Finset.univ : Finset iota)) (hullContainer F)
        Finset.univ,
      G.coveredIndices = Finset.univ ∧
      G.length ≤ Fintype.card iota ∧
      AllWinnerGlobalCross F Finset.univ G ∧
      ∃ A : FactoringMultiplicityAssembly.ExactAssembly
          (convexFactorization F G) Y
          (((Fintype.card iota + 1) * (Fintype.card iota + 1)) *
            (Fintype.card (Option (Fin (blocks F G).length)) + 1)),
        A.fineLevel ≤ Fintype.card iota ∧
        A.outerLevel ≤
          Fintype.card (Option (Fin (blocks F G).length)) ∧
        Y.shadingMass ≤
          (((((Fintype.card iota + 1) * (Fintype.card iota + 1)) *
            (Fintype.card (Option (Fin (blocks F G).length)) + 1) : Nat) :
              ENNReal) *
            (actualRefinementShading A).shadingMass) ∧
        Y.shadingDensity /
            ((((Fintype.card iota + 1) * (Fintype.card iota + 1)) *
              (Fintype.card (Option (Fin (blocks F G).length)) + 1) : Nat) :
                ENNReal) ≤
          (actualRefinementShading A).shadingDensity ∧
        (∀ i : {i // i ∈ A.refinement.indices},
          actualRefinementFamily A i = F i.1) ∧
        ∃ k ∈ (convexFactorization F G).index.coarse,
          0 < volume (finalFiberShading A k).shadedUnion ∧
          (finalFiberShading A k).averageMultiplicity =
            (A.fineLevel : ENNReal) ∧
          ((convexFactorization F G).inducedShading
            A.refinement.shading).averageMultiplicity =
              (A.outerLevel : ENNReal) ∧
          (actualRefinementShading A).averageMultiplicity ≤
            ((convexFactorization F G).inducedShading
              A.refinement.shading).averageMultiplicity *
                (finalFiberShading A k).averageMultiplicity := by
  obtain ⟨G, hcovered, hlength, hcross⟩ :=
    exists_fullConvexGreedyDensityPartition F Finset.univ
  let P := convexFactorization F G
  have hM : ∀ k ∈ P.index.coarse,
      (P.index.fiber k).card ≤ Fintype.card iota := by
    intro k _hk
    exact Finset.card_le_card (Finset.subset_univ _)
  have hsource :
      (IndexedShadingRefinement.restrictTo Y
        P.index.fine).shading.shadingMass ≠ 0 := by
    simpa only [P, fullGreedy_sourceActive_mass_eq G Y] using hY
  obtain ⟨A, hfine, houter, hdensity, k, hk, hvolume,
      hfineAverage, houterAverage, hproduct⟩ :=
    exists_exactAssembly_with_actualAverages_mass_density_of_fiber_card_le
      P Y (Fintype.card iota) hM hsource
  have hmass : Y.shadingMass ≤
      (((((Fintype.card iota + 1) * (Fintype.card iota + 1)) *
        (Fintype.card (Option (Fin (blocks F G).length)) + 1) : Nat) :
          ENNReal) * (actualRefinementShading A).shadingMass) := by
    have hretained :=
      sourceActiveFineShading_mass_le_loss_mul_actualRefinementShading A
    rw [sourceActiveFineShading_shadingMass,
      fullGreedy_sourceActive_mass_eq G Y] at hretained
    exact hretained
  have hdensity' : Y.shadingDensity /
      ((((Fintype.card iota + 1) * (Fintype.card iota + 1)) *
        (Fintype.card (Option (Fin (blocks F G).length)) + 1) : Nat) :
          ENNReal) ≤ (actualRefinementShading A).shadingDensity := by
    rw [← fullGreedy_sourceActive_shadingDensity_eq G Y]
    exact hdensity
  refine ⟨G, hcovered, hlength, hcross, A, hfine, houter,
    hmass, hdensity', ?_, k, ?_, hvolume, hfineAverage, ?_, ?_⟩
  · intro i
    exact actualRefinementFamily_apply A i
  · simpa only [P] using hk
  · simpa only [P] using houterAverage
  · simpa only [P] using hproduct

#print axioms fullGreedy_sourceActive_mass_eq
#print axioms fullGreedy_sourceActive_familyVolume_eq
#print axioms fullGreedy_sourceActive_shadingDensity_eq
#print axioms exists_fullGreedyCanonicalActualAverageMassDensityAssembly

end


end Family8FullGreedyCanonicalMassDensityAssemblyV1
