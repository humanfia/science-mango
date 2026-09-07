import Family8Grounding.Family8EighthNormalizedWZL3SourceV3
import Family8Grounding.Family8Family7FirstCrossingGraphAverageIdentityV4
import Family8Grounding.Family8FiniteRandomRigidMotionB2NormalizationCoreV1
import Family8Grounding.Family8FullCoefficientActualMassProxyAverageV10
import Family8Grounding.Family8StickyGraphContractedJohnProxyDatumV2

/-!
# Exact active average after eighth normalization

Restricting an eighth-normalized shading to a literal active subtype and to
the whole spatial window has the same mass and shaded union as the eighth
normalization of the source active subtype.  The proof compares those two
quantities directly, avoiding a proof-dependent equality between their
ambient convex families.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullCoefficientEighthNormalizedActiveAverageV10

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8EighthNormalizedWZL3SourceV3
open Family8Family7FirstCrossingGraphAverageIdentityV4
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FullCoefficientActualMassProxyAverageV10
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8StickyGraphContractedJohnProxyDatumV2
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

/-- Passing from an indexed active restriction to its literal subtype does
not change average multiplicity. -/
theorem stickyGraphSourceDatum_averageMultiplicity_eq_restrictTo
    {radius : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {F : UniformTubeFamily radius iota}
    (Y : Shading F.bodyFamily) (active : Finset iota) :
    (stickyGraphSourceDatum Y active).shading.averageMultiplicity =
      (IndexedShadingRefinement.restrictTo
        Y active).shading.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [stickyGraphSourceDatum_shadingMass_eq_restrictTo,
    stickyGraphSourceDatum_shadedUnion_eq_restrictTo]

/-- The exact average identity consumed when the full-metric route uses
`f = 0` and the whole projected plane as its measurable window. -/
theorem eighthNormalized_activeRestricted_univ_averageMultiplicity
    {radius : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily) (active : Finset iota) :
    (activeRestrictedShading
      (eighthNormalizedWZL3Source S)
      (eighthNormalizedShading S.family Y) active Set.univ
      MeasurableSet.univ).averageMultiplicity =
    (IndexedShadingRefinement.restrictTo
      Y active).shading.averageMultiplicity := by
  let D := stickyGraphSourceDatum Y active
  let lhs := activeRestrictedShading
    (eighthNormalizedWZL3Source S)
    (eighthNormalizedShading S.family Y) active Set.univ
    MeasurableSet.univ
  let rhs := (eighthNormalizedDatum D).shading
  have hcarrier : ∀ i, lhs.carrier i = rhs.carrier i := by
    intro i
    change
      (eighthDilationPoint '' Y.carrier i.1) ∩ Set.univ =
        eighthDilationPoint '' Y.carrier i.1
    exact Set.inter_univ _
  have hmass : lhs.shadingMass = rhs.shadingMass := by
    unfold Shading.shadingMass
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hcarrier i]
  have hunion : lhs.shadedUnion = rhs.shadedUnion := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i, by simpa only [hcarrier i] using hxi⟩
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i, by simpa only [hcarrier i] using hxi⟩
  have haverage : lhs.averageMultiplicity = rhs.averageMultiplicity := by
    unfold Shading.averageMultiplicity
    rw [hmass, hunion]
  rw [show
      (activeRestrictedShading
        (eighthNormalizedWZL3Source S)
        (eighthNormalizedShading S.family Y) active Set.univ
        MeasurableSet.univ).averageMultiplicity =
          (eighthNormalizedDatum D).shading.averageMultiplicity by
        simpa only [lhs, rhs] using haverage]
  rw [eighthNormalizedDatum_averageMultiplicity]
  exact stickyGraphSourceDatum_averageMultiplicity_eq_restrictTo Y active

#print axioms stickyGraphSourceDatum_averageMultiplicity_eq_restrictTo
#print axioms
  eighthNormalized_activeRestricted_univ_averageMultiplicity

end
end Family8FullCoefficientEighthNormalizedActiveAverageV10
