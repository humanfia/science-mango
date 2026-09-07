import Family8Grounding.Family8NormalizedFrostmanRerootedCoherentCoverV1
import Family8Grounding.Family8StickyFiberContractedJohnProxyDatumV1
import Family8Grounding.Family8StickyScaleCoverSingletonFiberV1
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8SelectedFiberJohnCanonicalCoherentFactorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedFrostmanRerootedCoherentCoverV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyScaleCoverSingletonFiberV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-!
# One selected Sticky fibre as an actual John factor with a coherent cover

This file deliberately separates two facts.

* The selected factor below is the literal fibre of the supplied active
  parent.  Its tubes and shading are moved by one common contracted-John
  affine equivalence, and the genuine equal-radius proxy datum is exactly
  the existing repository construction.
* The all-radius coherent cover placed on that actual proxy family is the
  canonical identity-radius cover.  Thus it is callback-free, but it is not
  claimed to be the affine image of the source cover's intermediate parent
  hierarchy.

The final section records the precise parent-composition statement missing
from `CoherentStickyMultiscaleCover` before a literal source-subtree
restriction can be constructed.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The actual selected fibre before applying the common John map. -/
abbrev selectedFiberSourceFamily
    (S : StickyScaleCover fine rho) (q : Fin S.coarseCard) :
    UniformTubeFamily delta {i // i ∈ S.fiber q} :=
  singletonFiberFamily S q

/-- The repository's genuine contracted-John datum on the same literal
selected subtype.  No re-selection or reindexing occurs here. -/
abbrev selectedFiberJohnDatum
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse}) :
    ActualTubeDatum (contractedJohnProxyRadius delta rho)
      {i // i ∈ S.fiber q.1} :=
  stickyFiberContractedJohnProxyDatum S Y hrho hrhoOne q

/-- A concrete all-radius coherent cover of the actual selected John factor.

It is intentionally the canonical identity-radius cover on the already
transported proxy tubes.  Consequently this definition adds no geometric
or concentration callback. -/
def selectedFiberJohnCoherentCover
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse}) :
    CoherentStickyMultiscaleCover
      (selectedFiberJohnDatum S Y hrho hrhoOne q).family :=
  identityRadiusCoherentCover
    (selectedFiberJohnDatum S Y hrho hrhoOne q).family

@[simp]
theorem selectedFiberJohnDatum_family_tubes
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse})
    (i : {i // i ∈ S.fiber q.1}) :
    (selectedFiberJohnDatum S Y hrho hrhoOne q).family.tubes i =
      contractedJohnProxyTube (S.coarse.tubes q.1) hrho
        (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne
          S hrho hrhoOne q)
        (fine.tubes i.1) :=
  rfl

@[simp]
theorem selectedFiberJohnDatum_shading_carrier
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse})
    (i : {i // i ∈ S.fiber q.1}) :
    (selectedFiberJohnDatum S Y hrho hrhoOne q).shading.carrier i =
      stickyFiberContractedJohnAffineEquiv S hrho hrhoOne q ''
        Y.carrier i.1 :=
  rfl

/-- The actual proxy factor preserves the selected source fibre average
multiplicity exactly. -/
theorem selectedFiberJohnDatum_averageMultiplicity
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse}) :
    (selectedFiberJohnDatum S Y hrho hrhoOne q).shading.averageMultiplicity =
      (stickyFiberSourceShading S Y q.1).averageMultiplicity :=
  stickyFiberContractedJohnProxyShading_averageMultiplicity
    S Y hrho hrhoOne q

/-- Every member of the actual selected factor is supported in the unit
ball, under the same nested-scale premise used by the proxy datum. -/
theorem selectedFiberJohnDatum_contained_in_unit_ball
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho)
    (q : {q // q ∈ S.activeCoarse}) :
    forall i : {i // i ∈ S.fiber q.1},
      ((selectedFiberJohnDatum S Y hrho hrhoOne q).family.tubes i).carrier ⊆
        Metric.closedBall (0 : Space) 1 :=
  stickyFiberContractedJohnProxyDatum_contained_in_unit_ball
    S Y hrho hrhoOne hdeltaRho q

/-! ## The literal interval-selected specialization -/

variable {tau : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {source : UniformTubeFamily delta sourceIndex}

/-- The split cover seen after re-rooting at `tau` is definitionally the
same actual `tau -> rho` interval cover used to choose `q`. -/
@[simp]
theorem reroot_split_cover_eq_interval
    (C : CoherentStickyMultiscaleCover source)
    (hdeltaTau : delta <= tau) (hTauRho : tau <= rho)
    (hRhoOne : rho <= 1) :
    (CoherentStickyMultiscaleCover.reroot C tau hdeltaTau
      (hTauRho.trans hRhoOne)).base.cover rho hTauRho hRhoOne =
        C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne :=
  rfl

/-- The exact staged-selector specialization: `q` is selected from the
literal interval cover, the source shading lives on the re-rooted `tau`
family, and the result is the genuine proxy datum on precisely that fibre. -/
abbrev intervalSelectedFiberJohnDatum
    (C : CoherentStickyMultiscaleCover source)
    (hdeltaTau : delta <= tau) (hTauRho : tau <= rho)
    (hRhoOne : rho <= 1)
    (Y : Shading
      (C.base.cover tau hdeltaTau
        (hTauRho.trans hRhoOne)).coarse.bodyFamily)
    (hrho : 0 < rho)
    (q : {q // q ∈ (C.intervalScaleCover tau rho hdeltaTau
      hTauRho hRhoOne).activeCoarse}) :
    ActualTubeDatum (contractedJohnProxyRadius tau rho)
      {i // i ∈ (C.intervalScaleCover tau rho hdeltaTau
        hTauRho hRhoOne).fiber q.1} :=
  selectedFiberJohnDatum
    (C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne)
    Y hrho hRhoOne q

/-- Callback-free coherent cover for the exact interval-selected factor.
The selected object is inherited from `C`; only the all-radius cover on its
already transported proxy family is canonical. -/
def intervalSelectedFiberJohnCoherentCover
    (C : CoherentStickyMultiscaleCover source)
    (hdeltaTau : delta <= tau) (hTauRho : tau <= rho)
    (hRhoOne : rho <= 1)
    (Y : Shading
      (C.base.cover tau hdeltaTau
        (hTauRho.trans hRhoOne)).coarse.bodyFamily)
    (hrho : 0 < rho)
    (q : {q // q ∈ (C.intervalScaleCover tau rho hdeltaTau
      hTauRho hRhoOne).activeCoarse}) :
    CoherentStickyMultiscaleCover
      (intervalSelectedFiberJohnDatum C hdeltaTau hTauRho hRhoOne
        Y hrho q).family :=
  selectedFiberJohnCoherentCover
    (C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne)
    Y hrho hRhoOne q

/-- Exact compositional law required to restrict an arbitrary coherent cover
to the descendants of one selected parent.  This law is not a field of the
current `CoherentStickyMultiscaleCover` structure. -/
def HasCompositionalParents
    (C : CoherentStickyMultiscaleCover source) : Prop :=
  forall (r s t : NNReal) (hdeltaR : delta <= r)
      (hRS : r <= s) (hST : s <= t) (hTOne : t <= 1)
      (k : Fin ((C.base.cover r hdeltaR
        (hRS.trans (hST.trans hTOne))).coarseCard)),
    k ∈ (C.base.cover r hdeltaR
      (hRS.trans (hST.trans hTOne))).activeCoarse ->
      C.parent s t (hdeltaR.trans hRS) hST hTOne
          (C.parent r s hdeltaR hRS (hST.trans hTOne) k) =
        C.parent r t hdeltaR (hRS.trans hST) hTOne k

/-- Parent composition is exactly what proves that an intermediate ancestor
of a selected `q`-descendant remains in the same selected subtree. -/
theorem intermediate_parent_remains_in_selected_subtree
    (C : CoherentStickyMultiscaleCover source)
    (hcomp : HasCompositionalParents C)
    (hdeltaTau : delta <= tau) (hTauRho : tau <= rho)
    (hRhoOne : rho <= 1)
    (sigma : NNReal) (hTauSigma : tau <= sigma)
    (hSigmaRho : sigma <= rho)
    (i : Fin ((C.base.cover tau hdeltaTau
      (hTauRho.trans hRhoOne)).coarseCard))
    (hi : i ∈ (C.base.cover tau hdeltaTau
      (hTauRho.trans hRhoOne)).activeCoarse)
    (q : Fin ((C.base.cover rho (hdeltaTau.trans hTauRho)
      hRhoOne).coarseCard))
    (hiq : C.parent tau rho hdeltaTau hTauRho hRhoOne i = q) :
    C.parent sigma rho (hdeltaTau.trans hTauSigma) hSigmaRho hRhoOne
        (C.parent tau sigma hdeltaTau hTauSigma
          (hSigmaRho.trans hRhoOne) i) = q := by
  rw [hcomp tau sigma rho hdeltaTau hTauSigma hSigmaRho hRhoOne i hi,
    hiq]

#print axioms selectedFiberJohnCoherentCover
#print axioms selectedFiberJohnDatum_family_tubes
#print axioms selectedFiberJohnDatum_shading_carrier
#print axioms selectedFiberJohnDatum_averageMultiplicity
#print axioms selectedFiberJohnDatum_contained_in_unit_ball
#print axioms reroot_split_cover_eq_interval
#print axioms intervalSelectedFiberJohnDatum
#print axioms intervalSelectedFiberJohnCoherentCover
#print axioms intermediate_parent_remains_in_selected_subtree

end
end Family8SelectedFiberJohnCanonicalCoherentFactorV1
