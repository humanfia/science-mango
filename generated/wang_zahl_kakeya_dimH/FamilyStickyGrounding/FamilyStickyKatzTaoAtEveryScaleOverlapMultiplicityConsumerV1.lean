import FamilyStickyGrounding.FamilyStickyFinalMultiscaleAssemblyCertificateV1
import Submission.Kakeya.ConvexFactoring.PairwiseOverlap

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace FamilyStickyKatzTaoAtEveryScaleOverlapMultiplicityConsumerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyFinalMultiscaleAssemblyCertificateV1

noncomputable section

/-!
# The first overlap-multiplicity consumer of Katz--Tao at every scale

`StickyMultiscaleCover.IsKatzTaoAtEveryScale` controls the concentration of
the literal active coarse family at every supplied radius.  Turning that
non-concentration statement into a shading multiplicity estimate needs one
additional, genuinely geometric input: each overlap row must be supported
inside a convex container whose volume is comparable with the mass of the
shaded row member.

The structure below records exactly that row geometry.  It does not contain
a second-moment, union-volume, shading-mass, or average-multiplicity bound.
The theorems then combine its data with the existing Katz--Tao finite
summation and Cordoba inequality to produce the first division-free analytic
consequence, followed by the average-multiplicity form.

No claim is made here that a hierarchy terminal family automatically
produces this row geometry.  In particular, exact-carrier terminal
multiplicity alone does not control pointwise overlap of distinct carriers.
-/

/-- Geometric data sufficient to turn Katz--Tao non-concentration into a
uniform overlap-row estimate for an actual shading. -/
structure KatzTaoOverlapRowGeometry
    {iota : Type*} [Fintype iota]
    {F : ConvexFamily iota} (Y : Shading F) where
  overlap : PairwiseOverlapBound Y
  active : iota -> Finset iota
  container : iota -> ConvexBody Space
  scaleFactor : ENNReal
  support : forall i j,
    overlap.majorant i j <=
      PairwiseOverlapBound.activeContainedVolume F (active i) (container i) j
  container_volume_le : forall i,
    volume (container i : Set Space) <=
      scaleFactor * volume (Y.carrier i)

namespace KatzTaoOverlapRowGeometry

variable {iota : Type*} [Fintype iota]
  {F : ConvexFamily iota} {Y : Shading F}
  (R : KatzTaoOverlapRowGeometry Y)

/-- A cross-multiplied Katz--Tao estimate and actual overlap-row geometry
give the division-free shading-mass inequality. -/
theorem shadingMass_le_of_isKatzTao
    {C : ENNReal} (hKT : IsKatzTao C F) :
    Y.shadingMass <=
      (C * R.scaleFactor) * volume Y.shadedUnion := by
  exact R.overlap.shadingMass_le_katzTao_mul_scale_mul_volume_shadedUnion
    C R.scaleFactor R.active R.container
      (fun i => hKT.on (R.active i)) R.support R.container_volume_le

/-- The same data give the paper's averaged multiplicity quantity directly.
This is not a callback reformulation: it is obtained through the proved
pairwise-overlap sum and Cordoba inequality. -/
theorem averageMultiplicity_le_of_isKatzTao
    {C : ENNReal} (hKT : IsKatzTao C F) :
    Y.averageMultiplicity <= C * R.scaleFactor := by
  apply averageMultiplicity_le_factor_of_overlapSum_le Y
  exact R.overlap.overlapSum_le_katzTao_mul_scale_mul_shadingMass
    C R.scaleFactor R.active R.container
      (fun i => hKT.on (R.active i)) R.support R.container_volume_le

end KatzTaoOverlapRowGeometry

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The quotient-form predicate used by the Sticky cover is exactly strong
enough to supply the cross-multiplied Katz--Tao API used by the analytic
overlap engine, including zero-volume convex bodies. -/
theorem activeCoarseFamily_isKatzTao
    (S : StickyScaleCover fine rho) {C : ENNReal}
    (hKT : S.IsKatzTaoAtScale C) :
    IsKatzTao C S.activeCoarseFamily := by
  exact isKatzTao_iff_concentration_le.mpr hKT

/-- One-scale division-free analytic consequence on the literal active
coarse family. -/
theorem shadingMass_le_of_isKatzTaoAtScale
    (S : StickyScaleCover fine rho) {C : ENNReal}
    (hKT : S.IsKatzTaoAtScale C)
    (Y : Shading S.activeCoarseFamily)
    (R : KatzTaoOverlapRowGeometry Y) :
    Y.shadingMass <=
      (C * R.scaleFactor) * volume Y.shadedUnion := by
  exact R.shadingMass_le_of_isKatzTao
    (activeCoarseFamily_isKatzTao S hKT)

/-- One-scale averaged multiplicity upper bound on the same actual coarse
family and shading. -/
theorem averageMultiplicity_le_of_isKatzTaoAtScale
    (S : StickyScaleCover fine rho) {C : ENNReal}
    (hKT : S.IsKatzTaoAtScale C)
    (Y : Shading S.activeCoarseFamily)
    (R : KatzTaoOverlapRowGeometry Y) :
    Y.averageMultiplicity <= C * R.scaleFactor := by
  exact R.averageMultiplicity_le_of_isKatzTao
    (activeCoarseFamily_isKatzTao S hKT)

end StickyScaleCover

namespace StickyMultiscaleCover

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- At every requested radius, Katz--Tao at every scale plus concrete row
geometry gives a division-free shading-mass bound. -/
theorem activeCoarse_shadingMass_le
    (M : StickyMultiscaleCover fine) {C : ENNReal}
    (hKT : M.IsKatzTaoAtEveryScale C)
    (rho : NNReal) (hdelta : delta <= rho) (hrho : rho <= 1)
    (Y : Shading (M.cover rho hdelta hrho).activeCoarseFamily)
    (R : KatzTaoOverlapRowGeometry Y) :
    Y.shadingMass <=
      (C * R.scaleFactor) * volume Y.shadedUnion := by
  exact StickyScaleCover.shadingMass_le_of_isKatzTaoAtScale
    (M.cover rho hdelta hrho) (hKT rho hdelta hrho) Y R

/-- The first Theorem 7(B)-shaped analytic consumer available from the
formal at-every-scale predicate: an explicit upper bound for the actual
shading's averaged multiplicity. -/
theorem activeCoarse_averageMultiplicity_le
    (M : StickyMultiscaleCover fine) {C : ENNReal}
    (hKT : M.IsKatzTaoAtEveryScale C)
    (rho : NNReal) (hdelta : delta <= rho) (hrho : rho <= 1)
    (Y : Shading (M.cover rho hdelta hrho).activeCoarseFamily)
    (R : KatzTaoOverlapRowGeometry Y) :
    Y.averageMultiplicity <= C * R.scaleFactor := by
  exact StickyScaleCover.averageMultiplicity_le_of_isKatzTaoAtScale
    (M.cover rho hdelta hrho) (hKT rho hdelta hrho) Y R

end StickyMultiscaleCover

/-! ## Final multiscale assembly specialization -/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry H}
  {P : FamilyStickyHierarchyPreMotionHullTestSupportV1.HierarchyPackingPlan.Plan H}
  {C : FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover
    (H.effectiveFamily 0)}
  {S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
    (H.effectiveRadius 0) depth}
  {epsilon : Real}
  {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}

/-- The final assembly certificate supplies the Katz--Tao-at-every-scale
premise automatically.  The remaining argument is precisely the actual
overlap-row geometry for the chosen coarse shading. -/
theorem finalAssembly_activeCoarse_averageMultiplicity_le
    (A : Certificate H G P C S epsilon
      massLoss bodyLoss katzTaoLoss frostmanError katzTaoError)
    (rho : NNReal) (hdelta : H.effectiveRadius 0 <= rho) (hrho : rho <= 1)
    (Y : Shading (C.base.cover rho hdelta hrho).activeCoarseFamily)
    (R : KatzTaoOverlapRowGeometry Y) :
    Y.averageMultiplicity <=
      (katzTaoLoss * katzTaoError) * R.scaleFactor := by
  exact StickyMultiscaleCover.activeCoarse_averageMultiplicity_le C.base
    A.stickyAtEveryScale.katzTao rho hdelta hrho Y R

#print axioms KatzTaoOverlapRowGeometry.shadingMass_le_of_isKatzTao
#print axioms KatzTaoOverlapRowGeometry.averageMultiplicity_le_of_isKatzTao
#print axioms StickyScaleCover.activeCoarseFamily_isKatzTao
#print axioms StickyMultiscaleCover.activeCoarse_shadingMass_le
#print axioms StickyMultiscaleCover.activeCoarse_averageMultiplicity_le
#print axioms finalAssembly_activeCoarse_averageMultiplicity_le

end

end FamilyStickyKatzTaoAtEveryScaleOverlapMultiplicityConsumerV1
