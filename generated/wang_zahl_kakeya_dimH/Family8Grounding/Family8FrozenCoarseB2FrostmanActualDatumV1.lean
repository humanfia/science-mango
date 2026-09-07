import Family8Grounding.Family8FiniteRandomRigidMotionB2FrostmanScaleSupportV2
import Family8Grounding.Family8CoarseTubePartitionFrozenComparableAdapterV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FrozenCoarseB2FrostmanActualDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionB2AutomaticConflictCapV1
open Family8FiniteRandomRigidMotionB2FrostmanScaleSupportV2

noncomputable section

/-!
# The frozen coarse shading as an actual B2 Frostman datum

A frozen comparable assembly carries a literal shading on the actual coarse
uniform tube family of its `CoarseTubePartition`.  This file packages that
same shading as an `ActualTubeDatum` and applies the scale-support-only fresh
B2 Frostman connector.  Hence the outer average in the same-data product is
the source average bounded here, definitionally and without a renamed
`houter` premise.

The remaining displayed Katz--Tao, density, and base budgets are the genuine
analytic inputs.  Pairwise essential distinctness of the raw coarse parents
is not an input; the normalized greedy selection manufactures it.
-/

variable {delta rho : NNReal} {iota kappa : Type}
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}

/-- The literal frozen outer shading, on its actual coarse tube family. -/
def frozenCoarseActualDatum
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y r) :
    ActualTubeDatum rho kappa where
  family := coarse
  shading := A.frozenCoarse

@[simp] theorem frozenCoarseActualDatum_family
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y r) :
    (frozenCoarseActualDatum P Y A).family = coarse :=
  rfl

@[simp] theorem frozenCoarseActualDatum_shading
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y r) :
    (frozenCoarseActualDatum P Y A).shading = A.frozenCoarse :=
  rfl

theorem frozenCoarseActualDatum_averageMultiplicity
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y r) :
    (frozenCoarseActualDatum P Y A).shading.averageMultiplicity =
      A.frozenCoarse.averageMultiplicity :=
  rfl

theorem frozenCoarseActualDatum_actualFamilyVolume
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y r) :
    (frozenCoarseActualDatum P Y A).actualFamilyVolume =
      familyVolume coarse.bodyFamily :=
  rfl

/-- The same frozen outer average is controlled by an honest selected
Frostman datum after normalization.  Every object in the conclusion is
constructed from `A`; no desired outer estimate is a premise. -/
theorem exists_normalized_frozenCoarse_averageMultiplicity_le_frostmanRHS
    {beta epsilon eta : Real} {delta0 : NNReal}
    [Nonempty kappa]
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y r)
    (hrhoPos : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hB2 : forall k,
      (coarse.tubes k).carrier ⊆ Metric.closedBall (0 : Space) 2)
    {conflictThreshold : Nat}
    (hconflict : forall k,
      (normalizedConflictIndices (frozenCoarseActualDatum P Y A) k).card <=
        conflictThreshold)
    {C : ENNReal}
    (hKT : IsKatzTao C coarse.bodyFamily)
    (hdelta0 : rho / 8 <= delta0)
    (hdensityBudget :
      ((rho / 8 : NNReal) : ENNReal) ^ eta <=
        (eighthNormalizedDatum
          (frozenCoarseActualDatum P Y A)).shading.shadingDensity /
            (conflictThreshold + 1 : Nat))
    (hbaseBudget :
      (conflictThreshold + 1 : Nat) *
          ((128 * C) * volume (unitBallBody : Set Space)) <=
        ((rho / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card kappa : ENNReal) *
            (((rho / 8 : NNReal) : ENNReal) ^ 2 / 2))) :
    exists selected : Finset kappa,
      selected.Nonempty ∧
      A.frozenCoarse.averageMultiplicity <=
        (conflictThreshold + 1 : Nat) *
          frostmanMultiplicityRHS (rho / 8)
            (restrictActualTubeDatum
              (eighthNormalizedDatum (frozenCoarseActualDatum P Y A))
              selected).actualFamilyVolume epsilon beta := by
  simpa only [frozenCoarseActualDatum_averageMultiplicity] using
    (exists_normalized_source_averageMultiplicity_le_frostmanRHS_of_scale_support
      hF (frozenCoarseActualDatum P Y A) hrhoPos hrhoHalf hB2
        hconflict hKT hdelta0 hdensityBudget hbaseBudget)

/-- Cardinality-conflict fallback for the same literal frozen outer datum. -/
theorem exists_automatic_normalized_frozenCoarse_averageMultiplicity_le_frostmanRHS
    {beta epsilon eta : Real} {delta0 : NNReal}
    [Nonempty kappa]
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y r)
    (hrhoPos : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hB2 : forall k,
      (coarse.tubes k).carrier ⊆ Metric.closedBall (0 : Space) 2)
    {C : ENNReal}
    (hKT : IsKatzTao C coarse.bodyFamily)
    (hdelta0 : rho / 8 <= delta0)
    (hdensityBudget :
      ((rho / 8 : NNReal) : ENNReal) ^ eta <=
        (eighthNormalizedDatum
          (frozenCoarseActualDatum P Y A)).shading.shadingDensity /
            (Fintype.card kappa + 1 : Nat))
    (hbaseBudget :
      (Fintype.card kappa + 1 : Nat) *
          ((128 * C) * volume (unitBallBody : Set Space)) <=
        ((rho / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card kappa : ENNReal) *
            (((rho / 8 : NNReal) : ENNReal) ^ 2 / 2))) :
    exists selected : Finset kappa,
      selected.Nonempty ∧
      A.frozenCoarse.averageMultiplicity <=
        (Fintype.card kappa + 1 : Nat) *
          frostmanMultiplicityRHS (rho / 8)
            (restrictActualTubeDatum
              (eighthNormalizedDatum (frozenCoarseActualDatum P Y A))
              selected).actualFamilyVolume epsilon beta := by
  simpa only [frozenCoarseActualDatum_averageMultiplicity] using
    (exists_automatic_normalized_source_averageMultiplicity_le_frostmanRHS_of_scale_support
      hF (frozenCoarseActualDatum P Y A) hrhoPos hrhoHalf hB2
        hKT hdelta0 hdensityBudget hbaseBudget)

#print axioms frozenCoarseActualDatum
#print axioms frozenCoarseActualDatum_averageMultiplicity
#print axioms
  exists_normalized_frozenCoarse_averageMultiplicity_le_frostmanRHS
#print axioms
  exists_automatic_normalized_frozenCoarse_averageMultiplicity_le_frostmanRHS

end
end Family8FrozenCoarseB2FrostmanActualDatumV1
