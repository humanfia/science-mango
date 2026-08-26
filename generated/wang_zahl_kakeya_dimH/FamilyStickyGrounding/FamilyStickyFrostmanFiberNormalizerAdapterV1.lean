import FamilyStickyGrounding.FamilyStickyAtEveryScaleCoreV1
import Submission.Kakeya.ConvexFactoring.NonConcentration

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace FamilyStickyFrostmanFiberNormalizerAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Fiberwise Katz--Tao to Frostman normalization

This module isolates the exact algebraic return step used by the random-copy
route.  A global Katz--Tao cap for each active fine fiber controls every
convex test body.  If that cap is no larger than the desired Frostman error
times the fiber's concentration in its actual parent, transitivity gives the
quotient-form Frostman condition at the scale.

The normalizer inequality is explicit: this adapter neither produces it nor
assumes the desired Frostman conclusion through a callback.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- A fiberwise Katz--Tao cap yields the scale Frostman condition once each
cap is normalized by the actual concentration of that fiber in its parent.
-/
theorem isFrostmanAtScale_of_fiberKatzTao_and_normalizer
    (S : StickyScaleCover fine rho)
    (cap : Fin S.coarseCard -> ENNReal) (error : ENNReal)
    (hKT : forall k, k ∈ S.activeCoarse ->
      IsKatzTao (cap k) (S.fiberFamily k))
    (hnormalizer : forall k, k ∈ S.activeCoarse ->
      cap k <= error *
        concentration (S.fiberFamily k) (S.coarse.tubes k).body) :
    S.IsFrostmanAtScale error := by
  intro k hk K _hK
  exact
    ((isKatzTao_iff_concentration_le.mp (hKT k hk)) K).trans
      (hnormalizer k hk)

#print axioms isFrostmanAtScale_of_fiberKatzTao_and_normalizer

end StickyScaleCover

end
end FamilyStickyFrostmanFiberNormalizerAdapterV1
