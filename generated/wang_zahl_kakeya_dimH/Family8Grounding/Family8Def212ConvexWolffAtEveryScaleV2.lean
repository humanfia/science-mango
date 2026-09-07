import Family4GlobalExtremalUpstream
import FamilyStickyGrounding.Family6AffineConvexVolumeCoreV1
import FamilyStickyGrounding.FamilyStickyAtEveryScaleCoreV1
import FamilyStickyGrounding.JohnAxisBridge5

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Def212ConvexWolffAtEveryScaleV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family6AffineConvexVolumeCoreV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# The honest Definition 2.12 interface

This module follows Definitions 2.9--2.12 of Wang--Zahl literally at the
finite indexed-family boundary.  In particular:

* `2A` is the full dilation of a centrally symmetric parent about its center,
  not merely a radial thickening of a unit segment;
* a unit rescaling sends a circumscribing John ellipsoid to the unit ball,
  rather than pretending that an anisotropic image of a capsule is another
  Euclidean capsule; and
* the Convex Wolff bound is normalized by the cardinality of the whole
  multi-family.

No shaded-union or local-multiplicity conclusion occurs in any structure.
The last structure isolates exactly what the current `StickyMultiscaleCover`
must still produce in order to instantiate the paper definition.
-/

/-- The cardinality-normalized Convex Wolff Axioms from Definition 2.9. -/
def SatisfiesConvexWolffAxioms
    {index : Type*} [Fintype index]
    (C : ENNReal) (F : ConvexFamily index) : Prop :=
  ∀ K : ConvexBody Space,
    ((containedIndices F K).card : ENNReal) ≤
      C * volume (K : Set Space) * (Fintype.card index : ENNReal)

/-- Canonical center of the unit segment underlying a tube. -/
def tubeCenter {radius : NNReal} (T : Tube radius) : Space :=
  T.axis.base + (2 : Real)⁻¹ • T.axis.direction

/-- Full dilation about a center, matching the paper's notation `rA`. -/
def centeredDilationCarrier (center : Space) (r : Real)
    (A : Set Space) : Set Space :=
  (fun x => center + r • (x - center)) '' A

/-- The literal full two-fold dilation `2T` used in Definitions 2.10 and
2.12.  Both the length and transverse width are doubled. -/
def twoFoldTubeCarrier {radius : NNReal} (T : Tube radius) : Set Space :=
  centeredDilationCarrier (tubeCenter T) 2 T.carrier

/-- Paper-style noncontainment essential distinctness.  The public Family 8
datum currently uses the older overlap-based predicate instead; converting
between those conventions is deliberately left as a visible adapter seam. -/
def PaperEssentiallyDistinct {radius : NNReal} (T U : Tube radius) : Prop :=
  (¬ T.carrier ⊆ twoFoldTubeCarrier U) ∧
    ¬ U.carrier ⊆ twoFoldTubeCarrier T

/-- The tube center belongs to the tube carrier. -/
theorem tubeCenter_mem_carrier {radius : NNReal} (T : Tube radius) :
    tubeCenter T ∈ T.carrier := by
  apply T.axis_subset_carrier
  exact T.axis.mem_carrier_of_mem_Icc (by constructor <;> norm_num)

/-- Every tube lies in its full two-fold central dilation. -/
theorem carrier_subset_twoFoldTubeCarrier
    {radius : NNReal} (T : Tube radius) :
    T.carrier ⊆ twoFoldTubeCarrier T := by
  intro x hx
  let center := tubeCenter T
  let y := center + (2 : Real)⁻¹ • (x - center)
  have hcenter : center ∈ T.carrier := tubeCenter_mem_carrier T
  have hy : y ∈ T.carrier := by
    exact T.convex_carrier.add_smul_sub_mem hcenter hx
      ⟨by norm_num, by norm_num⟩
  refine ⟨y, hy, ?_⟩
  dsimp [centeredDilationCarrier, twoFoldTubeCarrier, y]
  module

namespace ScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Active fine tubes contained in the full doubled carrier of a parent. -/
noncomputable def doubledFiber (S : StickyScaleCover fine rho)
    (k : Fin S.coarseCard) : Finset iota := by
  classical
  exact S.activeFine.filter fun i =>
    (fine.tubes i).carrier ⊆ twoFoldTubeCarrier (S.coarse.tubes k)

@[simp]
theorem mem_doubledFiber (S : StickyScaleCover fine rho)
    (i : iota) (k : Fin S.coarseCard) :
    i ∈ doubledFiber S k ↔
      i ∈ S.activeFine ∧
        (fine.tubes i).carrier ⊆
          twoFoldTubeCarrier (S.coarse.tubes k) := by
  classical
  simp [doubledFiber]

/-- Literal `C`-uniformity of all occupied assigned fibres. -/
def IsCUniform (S : StickyScaleCover fine rho) (C : ENNReal) : Prop :=
  ∀ k, k ∈ S.activeCoarse → ∀ l, l ∈ S.activeCoarse →
    ((S.fiber k).card : ENNReal) ≤
      C * ((S.fiber l).card : ENNReal)

/-- Definition 2.10 partitioning: fibres in doubled distinct parents are
disjoint. -/
def IsDoubledParentPartitioning (S : StickyScaleCover fine rho) : Prop :=
  ∀ k, k ∈ S.activeCoarse → ∀ l, l ∈ S.activeCoarse → k ≠ l →
    Disjoint (doubledFiber S k) (doubledFiber S l)

/-- Assigned membership implies doubled-parent membership. -/
theorem fiber_subset_doubledFiber (S : StickyScaleCover fine rho)
    (k : Fin S.coarseCard) : S.fiber k ⊆ doubledFiber S k := by
  intro i hi
  have hi' := (S.mem_fiber i k).mp hi
  rw [mem_doubledFiber]
  refine ⟨hi'.1, ?_⟩
  have hparent := S.carrier_subset i hi'.1
  rw [hi'.2] at hparent
  exact hparent.trans (carrier_subset_twoFoldTubeCarrier (S.coarse.tubes k))

/-- Partitioning forces the assigned fibre to be exactly the full collection
of active fine tubes lying in the doubled parent. -/
theorem doubledFiber_eq_fiber_of_partitioning
    (S : StickyScaleCover fine rho)
    (hpartition : IsDoubledParentPartitioning S)
    (k : Fin S.coarseCard) (hk : k ∈ S.activeCoarse) :
    doubledFiber S k = S.fiber k := by
  apply Finset.Subset.antisymm
  · intro i hi
    have hiActive : i ∈ S.activeFine := (mem_doubledFiber S i k).mp hi |>.1
    let l : Fin S.coarseCard := S.parent i
    have hl : l ∈ S.activeCoarse := S.parent_mem i hiActive
    have hiFiberL : i ∈ S.fiber l :=
      (S.mem_fiber i l).mpr ⟨hiActive, rfl⟩
    have hiDoubleL : i ∈ doubledFiber S l :=
      fiber_subset_doubledFiber S l hiFiberL
    by_cases hkl : k = l
    · simpa only [← hkl] using hiFiberL
    · exact (Finset.disjoint_left.mp
        (hpartition k hk l hl hkl) hi hiDoubleL).elim
  · exact fiber_subset_doubledFiber S k

/-- Genuine John normalization data for every occupied parent.  The chosen
affine equivalence sends the displayed circumscribing axis ellipsoid to the
unit ball.  It does not assert that the image is another `Tube`. -/
structure UnitRescalingGeometry (S : StickyScaleCover fine rho) where
  johnWitness :
    ∀ k : {k // k ∈ S.activeCoarse},
      JohnAxisWitness (S.coarse.tubes k.1).body
  unitRescaling :
    ∀ _k : {k // k ∈ S.activeCoarse}, Space ≃ᵃ[Real] Space
  johnOuter_image_eq_unitBall :
    ∀ k : {k // k ∈ S.activeCoarse},
      unitRescaling k ''
          axisEllipsoid (johnWitness k).center (johnWitness k).frame
            (johnWitness k).radius 3 =
        Metric.closedBall (0 : Space) 1

variable {S : StickyScaleCover fine rho}

/-- The actual fibre after its parent's common John normalization. -/
noncomputable def UnitRescalingGeometry.rescaledFiberFamily
    (R : UnitRescalingGeometry S)
    (k : {k // k ∈ S.activeCoarse}) :
    ConvexFamily {i // i ∈ S.fiber k.1} :=
  affineImageFamily (R.unitRescaling k) (S.fiberFamily k.1)

/-- The actual parent image lies in the unit ball, derived from the John
outer containment rather than stored as a second callback. -/
theorem UnitRescalingGeometry.parent_image_subset_unitBall
    (R : UnitRescalingGeometry S)
    (k : {k // k ∈ S.activeCoarse}) :
    R.unitRescaling k '' (S.coarse.tubes k.1).carrier ⊆
      Metric.closedBall (0 : Space) 1 := by
  rw [← R.johnOuter_image_eq_unitBall k]
  exact Set.image_mono (R.johnWitness k).outer

/-- The exact rescaled-fibre condition in Definition 2.12. -/
def UnitRescalingGeometry.FibresSatisfyCWA
    (R : UnitRescalingGeometry S) (C : ENNReal) : Prop :=
  ∀ k : {k // k ∈ S.activeCoarse},
    SatisfiesConvexWolffAxioms C (R.rescaledFiberFamily k)

end ScaleCover

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- One honest cover selected in the paper window beginning at `rho0`. -/
structure Def212ScaleWitness
    (fine : UniformTubeFamily delta iota) (rho0 C : NNReal) where
  rho : NNReal
  rho0_le_rho : rho0 ≤ rho
  rho_le_one : rho ≤ 1
  rho_lt_C_mul_rho0 : rho < C * rho0
  cover : StickyScaleCover fine rho
  c_uniform : ScaleCover.IsCUniform cover (C : ENNReal)
  doubled_parent_partitioning :
    ScaleCover.IsDoubledParentPartitioning cover
  unitRescalingGeometry : ScaleCover.UnitRescalingGeometry cover
  rescaled_fibres_cwa :
    unitRescalingGeometry.FibresSatisfyCWA (C : ENNReal)

namespace Def212ScaleWitness

theorem activeFine_eq_univ
    {rho0 C : NNReal} (W : Def212ScaleWitness fine rho0 C)
    (hfull : fine.refinement.refined = Finset.univ) :
    W.cover.activeFine = Finset.univ := by
  rw [W.cover.activeFine_eq_refined, hfull]

theorem doubledFiber_eq_fiber
    {rho0 C : NNReal} (W : Def212ScaleWitness fine rho0 C)
    (k : Fin W.cover.coarseCard) (hk : k ∈ W.cover.activeCoarse) :
    ScaleCover.doubledFiber W.cover k = W.cover.fiber k :=
  ScaleCover.doubledFiber_eq_fiber_of_partitioning W.cover
    W.doubled_parent_partitioning k hk

end Def212ScaleWitness

/-- Paper-compatible Definition 2.12 package.  Its fine-family field uses
the literal full-central-dilation predicate `PaperEssentiallyDistinct`.
The overlap predicate in `ActualTubeDatum.IsAdmissible` does not construct
this field; that conversion remains an explicit adapter seam. -/
structure ConvexWolffAxiomsAtEveryScale
    (fine : UniformTubeFamily delta iota) (C : NNReal) : Prop where
  delta_pos : 0 < delta
  one_le_C : 1 ≤ C
  fine_refined_eq_univ : fine.refinement.refined = Finset.univ
  fine_pairwise_paperEssentiallyDistinct :
    Set.Pairwise (Set.univ : Set iota) fun i j =>
      PaperEssentiallyDistinct (fine.tubes i) (fine.tubes j)
  witness : ∀ rho0 : NNReal, delta ≤ rho0 → rho0 ≤ 1 →
    Nonempty (Def212ScaleWitness fine rho0 C)

/-- Exact-scale data is stronger than Definition 2.12 and is the minimal
adapter boundary for the current actual hierarchy.  Full activity is already
available, while paper full-dilation distinctness is not supplied by the
overlap-based actual datum and remains an explicit seam.  The four
per-scale fields are the remaining honest requirements: uniform branching,
doubled-parent partitioning, John normalization, and normalized rescaled
fibre CWA. -/
structure ExactScaleDef212Inputs
    (M : StickyMultiscaleCover fine) (C : NNReal) where
  delta_pos : 0 < delta
  one_lt_C : 1 < C
  fine_refined_eq_univ : fine.refinement.refined = Finset.univ
  fine_pairwise_paperEssentiallyDistinct :
    Set.Pairwise (Set.univ : Set iota) fun i j =>
      PaperEssentiallyDistinct (fine.tubes i) (fine.tubes j)
  c_uniform : ∀ rho hdelta hrho,
    ScaleCover.IsCUniform (M.cover rho hdelta hrho) (C : ENNReal)
  doubled_parent_partitioning : ∀ rho hdelta hrho,
    ScaleCover.IsDoubledParentPartitioning (M.cover rho hdelta hrho)
  unitRescalingGeometry : ∀ rho hdelta hrho,
    ScaleCover.UnitRescalingGeometry (M.cover rho hdelta hrho)
  rescaled_fibres_cwa : ∀ rho hdelta hrho,
    let R := unitRescalingGeometry rho hdelta hrho
    R.FibresSatisfyCWA (C : ENNReal)

/-- Taking `rho = rho0` turns exact-scale hierarchy data into the paper scale
window. -/
theorem ExactScaleDef212Inputs.toConvexWolffAxiomsAtEveryScale
    {M : StickyMultiscaleCover fine} {C : NNReal}
    (H : ExactScaleDef212Inputs M C) :
    ConvexWolffAxiomsAtEveryScale fine C := by
  refine
    { delta_pos := H.delta_pos
      one_le_C := H.one_lt_C.le
      fine_refined_eq_univ := H.fine_refined_eq_univ
      fine_pairwise_paperEssentiallyDistinct :=
        H.fine_pairwise_paperEssentiallyDistinct
      witness := ?_ }
  intro rho0 hdelta hrho
  let S := M.cover rho0 hdelta hrho
  let R := H.unitRescalingGeometry rho0 hdelta hrho
  have hrhoPos : 0 < rho0 := H.delta_pos.trans_le hdelta
  refine ⟨
    { rho := rho0
      rho0_le_rho := le_rfl
      rho_le_one := hrho
      rho_lt_C_mul_rho0 := ?_
      cover := S
      c_uniform := H.c_uniform rho0 hdelta hrho
      doubled_parent_partitioning :=
        H.doubled_parent_partitioning rho0 hdelta hrho
      unitRescalingGeometry := R
      rescaled_fibres_cwa := H.rescaled_fibres_cwa rho0 hdelta hrho }⟩
  exact lt_mul_of_one_lt_left hrhoPos H.one_lt_C

#print axioms carrier_subset_twoFoldTubeCarrier
#print axioms ScaleCover.doubledFiber_eq_fiber_of_partitioning
#print axioms ScaleCover.UnitRescalingGeometry.parent_image_subset_unitBall
#print axioms Def212ScaleWitness.doubledFiber_eq_fiber
#print axioms ExactScaleDef212Inputs.toConvexWolffAxiomsAtEveryScale

end


end Family8Def212ConvexWolffAtEveryScaleV2
