import Family8Grounding.Family8StickyActiveRestrictedCoarseB2SupportV1
import Family8Grounding.Family8StickyActiveRestrictedCoarseKatzTaoV1
import Submission.Kakeya.ConvexFactoring.CoarseTubePartition

/-!
# Actual datum for a recomputed coarse neighborhood, V2

V1 is a frozen universe draft.  This clean successor keeps the literal
coarse family and recomputed neighborhood shading in the universe required
by `ActualTubeDatum`, with all coarse-index binders explicit.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8RecomputedNeighborhoodActualTubeDatumV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyActiveRestrictedCoarseB2SupportV1
open Family8StickyActiveRestrictedCoarseKatzTaoV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {iota kappa : Type}
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}

/-- The coarse actual datum whose shading is recomputed from the same fine
shading by the partition's literal `rho`-neighborhood operation. -/
def recomputedNeighborhoodActualTubeDatum
    (P : CoarseTubePartition fine coarse)
    (Z : Shading fine.bodyFamily) : ActualTubeDatum rho kappa where
  family := coarse
  shading := P.asConvexFactorization.neighborhoodInducedShading
    Z (rho : Real)

@[simp] theorem recomputedNeighborhoodActualTubeDatum_family
    (P : CoarseTubePartition fine coarse)
    (Z : Shading fine.bodyFamily) :
    (recomputedNeighborhoodActualTubeDatum P Z).family = coarse :=
  rfl

@[simp] theorem recomputedNeighborhoodActualTubeDatum_family_tubes
    (P : CoarseTubePartition fine coarse)
    (Z : Shading fine.bodyFamily) (k : kappa) :
    (recomputedNeighborhoodActualTubeDatum P Z).family.tubes k =
      coarse.tubes k :=
  rfl

@[simp] theorem recomputedNeighborhoodActualTubeDatum_shading
    (P : CoarseTubePartition fine coarse)
    (Z : Shading fine.bodyFamily) :
    (recomputedNeighborhoodActualTubeDatum P Z).shading =
      P.asConvexFactorization.neighborhoodInducedShading
        Z (rho : Real) :=
  rfl

@[simp] theorem recomputedNeighborhoodActualTubeDatum_shading_carrier
    (P : CoarseTubePartition fine coarse)
    (Z : Shading fine.bodyFamily) (k : kappa) :
    (recomputedNeighborhoodActualTubeDatum P Z).shading.carrier k =
      (P.asConvexFactorization.neighborhoodInducedShading
        Z (rho : Real)).carrier k :=
  rfl

@[simp] theorem recomputedNeighborhoodActualTubeDatum_averageMultiplicity
    (P : CoarseTubePartition fine coarse)
    (Z : Shading fine.bodyFamily) :
    (recomputedNeighborhoodActualTubeDatum P Z).shading.averageMultiplicity =
      (P.asConvexFactorization.neighborhoodInducedShading
        Z (rho : Real)).averageMultiplicity :=
  rfl

@[simp] theorem recomputedNeighborhoodActualTubeDatum_shadingDensity
    (P : CoarseTubePartition fine coarse)
    (Z : Shading fine.bodyFamily) :
    (recomputedNeighborhoodActualTubeDatum P Z).shading.shadingDensity =
      (P.asConvexFactorization.neighborhoodInducedShading
        Z (rho : Real)).shadingDensity :=
  rfl

/-- A lower density bound proved by the relative-square normalization can be
passed to the datum without any change of object or constant. -/
theorem recomputedNeighborhoodActualTubeDatum_density_lower
    (P : CoarseTubePartition fine coarse)
    (Z : Shading fine.bodyFamily) {q : ENNReal}
    (h : q <= (P.asConvexFactorization.neighborhoodInducedShading
      Z (rho : Real)).shadingDensity) :
    q <= (recomputedNeighborhoodActualTubeDatum P Z).shading.shadingDensity :=
  h

/-- Any B2 support certificate for the literal coarse family is exactly the
support certificate of the recomputed-neighborhood datum. -/
theorem recomputedNeighborhoodActualTubeDatum_B2
    (P : CoarseTubePartition fine coarse)
    (Z : Shading fine.bodyFamily)
    (hB2 : ∀ k : kappa,
      (coarse.tubes k).carrier ⊆ Metric.closedBall (0 : Space) 2) :
    ∀ k : kappa,
      ((recomputedNeighborhoodActualTubeDatum P Z).family.tubes k).carrier ⊆
        Metric.closedBall (0 : Space) 2 :=
  hB2

/-- Katz--Tao concentration belongs to the literal coarse family, hence is
unchanged by installing the recomputed neighborhood shading. -/
theorem recomputedNeighborhoodActualTubeDatum_isKatzTao
    (P : CoarseTubePartition fine coarse)
    (Z : Shading fine.bodyFamily) {C : ENNReal}
    (hKT : IsKatzTao C coarse.bodyFamily) :
    IsKatzTao C
      (recomputedNeighborhoodActualTubeDatum P Z).family.bodyFamily :=
  hKT

variable {sigma : NNReal} {alpha index : Type}
  [Fintype alpha] [DecidableEq alpha]
  [Fintype index] [DecidableEq index]
  {source : UniformTubeFamily sigma alpha}

/-- The automatic B2 support of active Sticky parents instantiates the
generic datum support on the active-fine-restricted coarse family. -/
theorem activeFineRestricted_recomputedNeighborhoodActualTubeDatum_B2
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hrho : rho <= (1 / 16 : NNReal))
    (P : CoarseTubePartition source
      (activeFineRestrictedScaleCover S).coarse)
    (Z : Shading source.bodyFamily) :
    ∀ q : Fin (activeFineRestrictedScaleCover S).coarseCard,
      ((recomputedNeighborhoodActualTubeDatum P Z).family.tubes q).carrier ⊆
        Metric.closedBall (0 : Space) 2 := by
  exact recomputedNeighborhoodActualTubeDatum_B2 P Z
    (activeFineRestrictedScaleCover_coarse_carrier_subset_closedBall_two
      D hD S hrho)

/-- The active-parent Katz--Tao theorem reindexes without loss to the same
coarse family carried by the recomputed-neighborhood datum. -/
theorem activeFineRestricted_recomputedNeighborhoodActualTubeDatum_isKatzTao
    (S : StickyScaleCover fine rho)
    (P : CoarseTubePartition source
      (activeFineRestrictedScaleCover S).coarse)
    (Z : Shading source.bodyFamily) {C : ENNReal}
    (hKT : S.IsKatzTaoAtScale C) :
    IsKatzTao C
      (recomputedNeighborhoodActualTubeDatum P Z).family.bodyFamily := by
  exact recomputedNeighborhoodActualTubeDatum_isKatzTao P Z
    (activeFineRestrictedScaleCover_coarse_isKatzTao S hKT)

#print axioms recomputedNeighborhoodActualTubeDatum
#print axioms recomputedNeighborhoodActualTubeDatum_averageMultiplicity
#print axioms recomputedNeighborhoodActualTubeDatum_density_lower
#print axioms activeFineRestricted_recomputedNeighborhoodActualTubeDatum_B2
#print axioms
  activeFineRestricted_recomputedNeighborhoodActualTubeDatum_isKatzTao

end
end Family8RecomputedNeighborhoodActualTubeDatumV2
