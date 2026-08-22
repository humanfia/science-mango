import Submission.Kakeya.Uniformity.TubeFamily

open Set
open scoped ENNReal NNReal

namespace FamilyStickyAtEveryScaleCoreV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity

noncomputable section

/-!
# Sticky Kakeya: the at-every-scale core

This is the first source-grounded entry for the formal `kakeya.sticky`
family.  It encodes Definition 7.1 of Guth--Wang--Zahl's streamlined proof:
at each `rho` between the fine radius `delta` and one, a supplied coarse tube
cover has

* Frostman non-concentration in every coarse fiber, and
* Katz--Tao non-concentration for the coarse family.

The predicates use the existing indexed tube families and the literal
`concentration` ratios.  No sticky theorem, volume lower bound, multiplicity
upper bound, or multiscale decomposition is assumed here.
-/

/-- A finite coarse cover of one uniform fine family at one scale.

The coarse index is `Fin coarseCard`, which bundles the varying finite index
type without importing the convex-factoring family.  The parent map and
carrier containment are explicit geometric data. -/
structure StickyScaleCover
    {delta : NNReal} {iota : Type*} [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (rho : NNReal) where
  coarseCard : Nat
  coarse : UniformTubeFamily rho (Fin coarseCard)
  activeFine : Finset iota
  activeCoarse : Finset (Fin coarseCard)
  parent : iota -> Fin coarseCard
  activeFine_eq_refined : activeFine = fine.refinement.refined
  activeCoarse_eq_refined : activeCoarse = coarse.refinement.refined
  parent_mem : forall i, i ∈ activeFine -> parent i ∈ activeCoarse
  parent_surjective : forall k, k ∈ activeCoarse ->
    exists i, i ∈ activeFine ∧ parent i = k
  carrier_subset : forall i, i ∈ activeFine ->
    (fine.tubes i).carrier ⊆ (coarse.tubes (parent i)).carrier

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Fine indices assigned to one coarse tube. -/
def fiber (S : StickyScaleCover fine rho) (k : Fin S.coarseCard) : Finset iota :=
  S.activeFine.filter fun i => S.parent i = k

@[simp] theorem mem_fiber (S : StickyScaleCover fine rho)
    (i : iota) (k : Fin S.coarseCard) :
    i ∈ S.fiber k <-> i ∈ S.activeFine ∧ S.parent i = k := by
  simp [fiber]

/-- The actual convex family in one coarse fiber. -/
def fiberFamily (S : StickyScaleCover fine rho) (k : Fin S.coarseCard) :
    ConvexFamily {i // i ∈ S.fiber k} :=
  fun i => fine.bodyFamily i.1

/-- The active coarse family, preserving repeated coarse tubes by indexing. -/
def activeCoarseFamily (S : StickyScaleCover fine rho) :
    ConvexFamily {k // k ∈ S.activeCoarse} :=
  fun k => S.coarse.bodyFamily k.1

/-- Every member of a fiber is geometrically contained in its parent tube. -/
theorem fiber_carrier_subset_parent (S : StickyScaleCover fine rho)
    (k : Fin S.coarseCard) (i : {i // i ∈ S.fiber k}) :
    (fine.tubes i.1).carrier ⊆ (S.coarse.tubes k).carrier := by
  have hi := (S.mem_fiber i.1 k).mp i.2
  simpa [hi.2] using S.carrier_subset i.1 hi.1

/-- Paper Definition 7.1(A) at one scale, in quotient form.

For every active parent and every convex sub-body of that parent, the
concentration of the fine fiber grows by at most `C`. -/
def IsFrostmanAtScale (S : StickyScaleCover fine rho) (C : ENNReal) : Prop :=
  forall k, k ∈ S.activeCoarse ->
    forall K : ConvexBody Space,
      (K : Set Space) ⊆ (S.coarse.tubes k).carrier ->
      concentration (S.fiberFamily k) K <=
        C * concentration (S.fiberFamily k) (S.coarse.tubes k).body

/-- Paper Definition 7.1(B) at one scale: the active coarse family has
Katz--Tao concentration at most `C`. -/
def IsKatzTaoAtScale (S : StickyScaleCover fine rho) (C : ENNReal) : Prop :=
  forall K : ConvexBody Space, concentration S.activeCoarseFamily K <= C

/-- The two paper conditions on the same coarse cover at one scale. -/
def IsStickyAtScale (S : StickyScaleCover fine rho)
    (frostmanError katzTaoError : ENNReal) : Prop :=
  S.IsFrostmanAtScale frostmanError ∧ S.IsKatzTaoAtScale katzTaoError

theorem isKatzTaoAtScale_iff_maximalConcentration_le
    (S : StickyScaleCover fine rho) (C : ENNReal) :
    S.IsKatzTaoAtScale C <-> maximalConcentration S.activeCoarseFamily <= C := by
  constructor
  · intro h
    exact iSup_le h
  · intro h K
    exact (concentration_le_maximalConcentration S.activeCoarseFamily K).trans h

theorem IsFrostmanAtScale.mono
    {S : StickyScaleCover fine rho} {C C' : ENNReal}
    (h : S.IsFrostmanAtScale C) (hCC' : C <= C') :
    S.IsFrostmanAtScale C' := by
  intro k hk K hK
  exact (h k hk K hK).trans (by gcongr)

theorem IsKatzTaoAtScale.mono
    {S : StickyScaleCover fine rho} {C C' : ENNReal}
    (h : S.IsKatzTaoAtScale C) (hCC' : C <= C') :
    S.IsKatzTaoAtScale C' := by
  intro K
  exact (h K).trans hCC'

end StickyScaleCover

/-- A coherent choice of an actual coarse cover at every scale in
`[delta, 1]`.  No existence claim is hidden in this bundle. -/
structure StickyMultiscaleCover
    {delta : NNReal} {iota : Type*} [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) where
  cover : forall rho : NNReal, delta <= rho -> rho <= 1 ->
    StickyScaleCover fine rho

namespace StickyMultiscaleCover

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Paper Definition 7.1(A), quantified over the full scale interval. -/
def IsFrostmanAtEveryScale (M : StickyMultiscaleCover fine)
    (C : ENNReal) : Prop :=
  forall rho (hdelta : delta <= rho) (hrho : rho <= 1),
    (M.cover rho hdelta hrho).IsFrostmanAtScale C

/-- Paper Definition 7.1(B), quantified over the full scale interval. -/
def IsKatzTaoAtEveryScale (M : StickyMultiscaleCover fine)
    (C : ENNReal) : Prop :=
  forall rho (hdelta : delta <= rho) (hrho : rho <= 1),
    (M.cover rho hdelta hrho).IsKatzTaoAtScale C

/-- The streamlined paper's finite-family notion of stickiness: both
non-concentration conditions hold on the same multiscale cover. -/
def IsStickyAtEveryScale (M : StickyMultiscaleCover fine)
    (frostmanError katzTaoError : ENNReal) : Prop :=
  M.IsFrostmanAtEveryScale frostmanError ∧
    M.IsKatzTaoAtEveryScale katzTaoError

theorem isStickyAtEveryScale_iff (M : StickyMultiscaleCover fine)
    (frostmanError katzTaoError : ENNReal) :
    M.IsStickyAtEveryScale frostmanError katzTaoError <->
      M.IsFrostmanAtEveryScale frostmanError ∧
        M.IsKatzTaoAtEveryScale katzTaoError := by
  rfl

theorem IsStickyAtEveryScale.frostman
    {M : StickyMultiscaleCover fine} {frostmanError katzTaoError : ENNReal}
    (h : M.IsStickyAtEveryScale frostmanError katzTaoError) :
    M.IsFrostmanAtEveryScale frostmanError :=
  h.1

theorem IsStickyAtEveryScale.katzTao
    {M : StickyMultiscaleCover fine} {frostmanError katzTaoError : ENNReal}
    (h : M.IsStickyAtEveryScale frostmanError katzTaoError) :
    M.IsKatzTaoAtEveryScale katzTaoError :=
  h.2

theorem IsStickyAtEveryScale.mono
    {M : StickyMultiscaleCover fine}
    {frostmanError frostmanError' katzTaoError katzTaoError' : ENNReal}
    (h : M.IsStickyAtEveryScale frostmanError katzTaoError)
    (hF : frostmanError <= frostmanError')
    (hKT : katzTaoError <= katzTaoError') :
    M.IsStickyAtEveryScale frostmanError' katzTaoError' := by
  constructor
  · intro rho hdelta hrho
    exact (h.1 rho hdelta hrho).mono hF
  · intro rho hdelta hrho
    exact (h.2 rho hdelta hrho).mono hKT

end StickyMultiscaleCover

#print axioms StickyScaleCover.fiber_carrier_subset_parent
#print axioms StickyScaleCover.isKatzTaoAtScale_iff_maximalConcentration_le
#print axioms StickyMultiscaleCover.isStickyAtEveryScale_iff
#print axioms StickyMultiscaleCover.IsStickyAtEveryScale.mono

end

end FamilyStickyAtEveryScaleCoreV1
