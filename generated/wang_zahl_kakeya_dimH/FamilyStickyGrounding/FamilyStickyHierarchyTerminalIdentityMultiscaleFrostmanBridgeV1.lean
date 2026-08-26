import FamilyStickyGrounding.FamilyStickyFrostmanFiberNormalizerAdapterV1
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1
import FamilyStickyGrounding.FamilyStickyHierarchyTerminalSourceChartBucketProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyHierarchyTerminalIdentityMultiscaleFrostmanBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1
open FamilyStickyFrostmanFiberNormalizerAdapterV1
open FamilyStickyFiniteFamilyMaximalConcentrationV1
open FamilyStickyCapturedTubeBoxWidthV1
open FamilyStickyScaleChainFirstNonLargeAdjacentCardBudgetProducerV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyTerminalEssentialDistinctAdapterV1

noncomputable section

/-!
# An honest terminal all-radius cover with automatic Frostman fibers

The hierarchy terminal output is already a finite uniform tube family, but the
same-scale terminal cover does not by itself provide the cover required by the
at-every-scale API.  We use the repository's radius-changed identity cover at
every scale.  Its active parent fibers are literal singletons, so their
Katz--Tao cap is one.  The existing parent-concentration normalizer then gives
the finite Frostman constant `capturedTubeBoxLoss delta 1`, with no cardinality
factor and with no cover, Frostman, or Katz--Tao callback.

The terminal specialization below applies this general construction to the
occurrence-indexed `terminalTubeFamily`.  It does not claim the later WZ2 union
lower bound; that endpoint additionally needs its actual shading/copy source
data.
-/

universe u

variable {delta rho : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Singleton fibers of the radius-changed identity cover -/

/-- Every active parent of the radius-changed identity cover has exactly its
canonically corresponding fine index as fiber. -/
theorem identityRadiusScaleCover_fiber_eq_singleton
    (fine : UniformTubeFamily delta iota)
    (rho : NNReal) (hdelta : delta <= rho)
    (k : Fin (Fintype.card iota))
    (hk : k ∈ (identityRadiusScaleCover fine rho hdelta).activeCoarse) :
    (identityRadiusScaleCover fine rho hdelta).fiber k =
      {(Fintype.equivFin iota).symm k} := by
  classical
  have hk' : (Fintype.equivFin iota).symm k ∈
      fine.refinement.refined := by
    change k ∈ fine.refinement.refined.map
      (Fintype.equivFin iota).toEmbedding at hk
    simpa using hk
  change fine.refinement.refined.filter
    (fun i => Fintype.equivFin iota i = k) =
      {(Fintype.equivFin iota).symm k}
  ext i
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨_hi, hik⟩
    apply (Fintype.equivFin iota).injective
    simpa using hik
  · rintro rfl
    exact ⟨hk', (Fintype.equivFin iota).apply_symm_apply k⟩

/-- Hence every active identity-cover fiber has exact finite cardinality one. -/
theorem identityRadiusScaleCover_fiber_fintypeCard_eq_one
    (fine : UniformTubeFamily delta iota)
    (rho : NNReal) (hdelta : delta <= rho)
    (k : Fin (Fintype.card iota))
    (hk : k ∈ (identityRadiusScaleCover fine rho hdelta).activeCoarse) :
    Fintype.card
        {i // i ∈ (identityRadiusScaleCover fine rho hdelta).fiber k} = 1 := by
  rw [Fintype.card_coe,
    identityRadiusScaleCover_fiber_eq_singleton fine rho hdelta k hk]
  exact Finset.card_singleton _

/-- A one-element identity-cover fiber has Katz--Tao constant one. -/
theorem identityRadiusScaleCover_fiber_isKatzTao_one
    (fine : UniformTubeFamily delta iota)
    (rho : NNReal) (hdelta : delta <= rho)
    (k : Fin (Fintype.card iota))
    (hk : k ∈ (identityRadiusScaleCover fine rho hdelta).activeCoarse) :
    IsKatzTao 1 ((identityRadiusScaleCover fine rho hdelta).fiberFamily k) := by
  apply isKatzTao_iff_concentration_le.mpr
  intro K
  calc
    concentration
          ((identityRadiusScaleCover fine rho hdelta).fiberFamily k) K <=
        maximalConcentration
          ((identityRadiusScaleCover fine rho hdelta).fiberFamily k) :=
      concentration_le_maximalConcentration _ _
    _ <=
        (Fintype.card
          {i // i ∈ (identityRadiusScaleCover fine rho hdelta).fiber k} :
            ENNReal) :=
      maximalConcentration_le_card _
    _ = 1 := by
      rw [identityRadiusScaleCover_fiber_fintypeCard_eq_one
        fine rho hdelta k hk]
      norm_num

/-! ## General all-radius identity-cover Frostman and Katz--Tao bounds -/

/-- At one radius, singleton fibers remove the cardinality factor from the
general captured-tube Frostman estimate. -/
theorem identityRadiusScaleCover_isFrostmanAtScale
    (fine : UniformTubeFamily delta iota)
    (rho : NNReal) (hdelta : delta <= rho)
    (hdeltaPos : 0 < delta) :
    (identityRadiusScaleCover fine rho hdelta).IsFrostmanAtScale
      (capturedTubeBoxLoss delta rho) := by
  apply StickyScaleCover.isFrostmanAtScale_of_fiberKatzTao_and_normalizer
    (identityRadiusScaleCover fine rho hdelta) (fun _ => 1)
  · intro k hk
    exact identityRadiusScaleCover_fiber_isKatzTao_one
      fine rho hdelta k hk
  · intro k hk
    exact one_le_capturedTubeBoxLoss_mul_parentConcentration
      (identityRadiusScaleCover fine rho hdelta) hdeltaPos
        (hdeltaPos.trans_le hdelta) k hk

/-- The canonical identity cover is Frostman at every legal radius with one
finite uniform geometric loss and no cardinality factor. -/
theorem identityRadiusCoherentCover_isFrostmanAtEveryScale
    (fine : UniformTubeFamily delta iota) (hdeltaPos : 0 < delta) :
    (identityRadiusCoherentCover fine).base.IsFrostmanAtEveryScale
      (capturedTubeBoxLoss delta 1) := by
  intro rho hdelta hRhoOne
  apply (identityRadiusScaleCover_isFrostmanAtScale
    fine rho hdelta hdeltaPos).mono
  exact capturedTubeBoxLoss_le_global hdeltaPos le_rfl hRhoOne

/-- For the identity cover, the coarse Katz--Tao constant is bounded by the
original active refined cardinality. -/
theorem identityRadiusScaleCover_isKatzTaoAtScale_refinedCard
    (fine : UniformTubeFamily delta iota)
    (rho : NNReal) (hdelta : delta <= rho) :
    (identityRadiusScaleCover fine rho hdelta).IsKatzTaoAtScale
      (fine.refinement.refined.card : ENNReal) := by
  apply (FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover.isKatzTaoAtScale_iff_coarseDeltaMax_le
    (identityRadiusScaleCover fine rho hdelta)
      (fine.refinement.refined.card : ENNReal)).mpr
  calc
    FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover.coarseDeltaMax
        (identityRadiusScaleCover fine rho hdelta) <=
      ((identityRadiusScaleCover fine rho hdelta).activeCoarse.card :
        ENNReal) :=
      StickyScaleCover.coarseDeltaMax_le_activeCoarse_card _
    _ = (fine.refinement.refined.card : ENNReal) := by
      simp [identityRadiusScaleCover]

/-- The identity cover's coarse family therefore has an automatic
Katz--Tao bound at every radius. -/
theorem identityRadiusCoherentCover_isKatzTaoAtEveryScale
    (fine : UniformTubeFamily delta iota) :
    (identityRadiusCoherentCover fine).base.IsKatzTaoAtEveryScale
      (fine.refinement.refined.card : ENNReal) := by
  intro rho hdelta _hRhoOne
  exact identityRadiusScaleCover_isKatzTaoAtScale_refinedCard
    fine rho hdelta

/-- Fully automatic every-scale Sticky data on the same honest identity cover.
The two displayed constants record the separate Frostman and coarse-family
costs. -/
theorem identityRadiusCoherentCover_isStickyAtEveryScale
    (fine : UniformTubeFamily delta iota) (hdeltaPos : 0 < delta) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
      (capturedTubeBoxLoss delta 1)
      (fine.refinement.refined.card : ENNReal) := by
  exact ⟨identityRadiusCoherentCover_isFrostmanAtEveryScale fine hdeltaPos,
    identityRadiusCoherentCover_isKatzTaoAtEveryScale fine⟩

/-! ## Specialization to the literal hierarchy terminal output -/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}

/-- The concrete coherent cover of every occurrence in one hierarchy terminal
joint output. -/
abbrev terminalIdentityCoherentCover
    (C : HierarchyJointRandomMotionCertificate H G) :
    CoherentStickyMultiscaleCover (terminalTubeFamily C) :=
  identityRadiusCoherentCover (terminalTubeFamily C)

/-- The exact `StickyMultiscaleCover (terminalTubeFamily C)` requested by the
at-every-scale API. -/
abbrev terminalIdentityMultiscaleCover
    (C : HierarchyJointRandomMotionCertificate H G) :
    StickyMultiscaleCover (terminalTubeFamily C) :=
  (terminalIdentityCoherentCover C).base

/-- Every terminal identity fiber is Frostman at every radius with the same
finite geometric constant. -/
theorem terminalIdentityMultiscaleCover_isFrostmanAtEveryScale
    (C : HierarchyJointRandomMotionCertificate H G)
    (hdelta : 0 < H.effectiveRadius 0) :
    (terminalIdentityMultiscaleCover C).IsFrostmanAtEveryScale
      (capturedTubeBoxLoss (H.effectiveRadius 0) 1) := by
  exact identityRadiusCoherentCover_isFrostmanAtEveryScale
    (terminalTubeFamily C) hdelta

/-- The occurrence-indexed terminal coarse family has its automatic finite
cardinality Katz--Tao bound at every radius. -/
theorem terminalIdentityMultiscaleCover_isKatzTaoAtEveryScale
    (C : HierarchyJointRandomMotionCertificate H G) :
    (terminalIdentityMultiscaleCover C).IsKatzTaoAtEveryScale
      (Fintype.card C.FinalIndex : ENNReal) := by
  simpa [terminalIdentityMultiscaleCover, terminalIdentityCoherentCover,
    terminalTubeFamily] using
    identityRadiusCoherentCover_isKatzTaoAtEveryScale (terminalTubeFamily C)

/-- The hierarchy terminal output now reaches the literal every-scale Sticky
interface without taking a cover, Frostman condition, or Katz--Tao condition as
input. -/
theorem terminalIdentityMultiscaleCover_isStickyAtEveryScale
    (C : HierarchyJointRandomMotionCertificate H G)
    (hdelta : 0 < H.effectiveRadius 0) :
    (terminalIdentityMultiscaleCover C).IsStickyAtEveryScale
      (capturedTubeBoxLoss (H.effectiveRadius 0) 1)
      (Fintype.card C.FinalIndex : ENNReal) := by
  exact ⟨terminalIdentityMultiscaleCover_isFrostmanAtEveryScale C hdelta,
    terminalIdentityMultiscaleCover_isKatzTaoAtEveryScale C⟩

#print axioms identityRadiusScaleCover_fiber_eq_singleton
#print axioms identityRadiusScaleCover_fiber_isKatzTao_one
#print axioms identityRadiusScaleCover_isFrostmanAtScale
#print axioms identityRadiusCoherentCover_isFrostmanAtEveryScale
#print axioms identityRadiusCoherentCover_isKatzTaoAtEveryScale
#print axioms identityRadiusCoherentCover_isStickyAtEveryScale
#print axioms terminalIdentityMultiscaleCover
#print axioms terminalIdentityMultiscaleCover_isFrostmanAtEveryScale
#print axioms terminalIdentityMultiscaleCover_isKatzTaoAtEveryScale
#print axioms terminalIdentityMultiscaleCover_isStickyAtEveryScale

end

end FamilyStickyHierarchyTerminalIdentityMultiscaleFrostmanBridgeV1
