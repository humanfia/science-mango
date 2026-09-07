import Family8Grounding.Family8PaperConflictOwnerParentFramePhysicalBridgeV5
import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal

namespace Family8PaperConflictOwnerParentFrameCoarseCoverV6

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8PaperConflictOwnerParentFrameBoundsV2
open Family8PaperConflictOwnerParentFrameFiniteCodeV8
open Family8PaperConflictOwnerParentFramePhysicalBridgeV5
open Family8PaperEssentialDistinctOwnerClusterRetentionV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyTubeParentDirectionCoherenceV1

noncomputable section

/-!
# Honest owner-cell coarse representatives

The finite parent-frame code and its literal `5*rho` carrier containment are
assembled into a genuine finite `UniformTubeFamily`.  Every occupied code is
represented by an actual owner tube, and every owner is mapped to the coarse
tube built from the representative of its own code.  The family has the
honest `O(rho⁻¹)` code-cardinality bound.
-/

/-- The finite subtype of codes actually hit by a finite parameter type. -/
def finiteCodeIndex {parameter codeType : Type}
    [Fintype parameter] [DecidableEq parameter] [DecidableEq codeType]
    (code : parameter → codeType) :=
  {c : codeType // c ∈ (Finset.univ : Finset parameter).image code}

/-- The occupied-code label of a source parameter. -/
def finiteCodeLabel {parameter codeType : Type}
    [Fintype parameter] [DecidableEq parameter] [DecidableEq codeType]
    (code : parameter → codeType) (p : parameter) : finiteCodeIndex code :=
  ⟨code p, Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩⟩

/-- An actual source representative of every occupied code. -/
noncomputable def finiteCodeRepresentative
    {parameter codeType : Type}
    [Fintype parameter] [DecidableEq parameter] [DecidableEq codeType]
    (code : parameter → codeType) (c : finiteCodeIndex code) : parameter :=
  Classical.choose (Finset.mem_image.mp c.property)

theorem finiteCodeRepresentative_code
    {parameter codeType : Type}
    [Fintype parameter] [DecidableEq parameter] [DecidableEq codeType]
    (code : parameter → codeType) (c : finiteCodeIndex code) :
    code (finiteCodeRepresentative code c) = c.1 := by
  exact (Classical.choose_spec (Finset.mem_image.mp c.property)).2

/-- Generic coarse-cover producer from the three parent-frame bounds. -/
theorem exists_parentFrameOwnerCellCoarseCover
    {delta rho : NNReal} (hrhoPos : 0 < rho) (hdeltaRho : delta ≤ rho)
    {parameter : Type} [Fintype parameter] [DecidableEq parameter]
    (parent : Tube rho) (owner : parameter → Tube delta)
    (hlong : ∀ p,
      |parentFrameLongitudinalOffset parent (owner p)| ≤ 4)
    (hdirection : ∀ p,
      UnorientedDirectionClose (owner p).axis parent.axis
        (14 * (rho : Real)))
    (htransverse : ∀ p,
      ‖parentFrameTransverseOffset parent (owner p)‖ ≤ 94 * (rho : Real)) :
    ∃ n : Nat, ∃ representative : Fin n → parameter,
      ∃ coarse : UniformTubeFamily (5 * rho) (Fin n),
        ∃ label : parameter → Fin n,
          n ≤ parentFrameCodeCount rho ∧
          (∀ p,
            parentFrameCode hrhoPos parent owner hlong hdirection htransverse
                (representative (label p)) =
              parentFrameCode hrhoPos parent owner hlong hdirection htransverse p) ∧
          (∀ q, coarse.tubes q =
            (parentOrientedTube parent (owner (representative q))).changeRadius
              (5 * rho)) ∧
          ∀ p, (owner p).carrier ⊆ (coarse.tubes (label p)).carrier := by
  classical
  let code := parentFrameCode hrhoPos parent owner hlong hdirection htransverse
  let codes := (Finset.univ : Finset parameter).image code
  let e : {c // c ∈ codes} ≃ Fin codes.card := codes.equivFin
  let sourceCode : parameter → {c // c ∈ codes} := fun p =>
    ⟨code p, by
      dsimp only [codes]
      exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩⟩
  have hoccupied (c : {c // c ∈ codes}) : ∃ p, code p = c.1 := by
    have hc : c.1 ∈ (Finset.univ : Finset parameter).image code := by
      simpa only [codes] using c.property
    obtain ⟨p, _hp, hpc⟩ := Finset.mem_image.mp hc
    exact ⟨p, hpc⟩
  let representative : Fin codes.card → parameter := fun q =>
    Classical.choose (hoccupied (e.symm q))
  let label : parameter → Fin codes.card := fun p => e (sourceCode p)
  let coarse : UniformTubeFamily (5 * rho) (Fin codes.card) :=
    { tubes := fun q =>
        (parentOrientedTube parent (owner (representative q))).changeRadius
          (5 * rho)
      refinement := UniformRefinement.ofFinset Finset.univ }
  have hrepresentative (p : parameter) :
      code (representative (label p)) = code p := by
    change code (Classical.choose
      (hoccupied (e.symm (e (sourceCode p))))) = code p
    calc
      code (Classical.choose (hoccupied (e.symm (e (sourceCode p))))) =
          (e.symm (e (sourceCode p))).1 :=
        Classical.choose_spec (hoccupied (e.symm (e (sourceCode p))))
      _ = (sourceCode p).1 :=
        congrArg Subtype.val (e.symm_apply_apply (sourceCode p))
      _ = code p := rfl
  refine ⟨codes.card, representative, coarse, label, ?_, ?_, ?_, ?_⟩
  · simpa only [codes, code] using
      parentFrameCode_image_card_le hrhoPos parent owner hlong hdirection
        htransverse
  · exact hrepresentative
  · intro q
    rfl
  · intro p
    have hcode : code p = code (representative (label p)) :=
      (hrepresentative p).symm
    simpa only [coarse, code] using
      parentFrameCode_eq_owner_carrier_subset_five_mul hrhoPos hdeltaRho
        parent owner hlong hdirection htransverse hcode

/-- Actual specialization: for every old parent, all selected owners met by
its source fibre admit an `O(rho⁻¹)` finite family of genuine `5*rho` coarse
tubes with literal carrier coverage. -/
theorem exists_scaleCover_ownerImage_parentFrameCoarseCover
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hdeltaRho : delta ≤ rho) (hrhoPos : 0 < rho) (hrhoOne : rho ≤ 1)
    (k : Fin S.coarseCard) :
    ∃ n : Nat,
      ∃ representative : Fin n → ↥(C.sourceOwnerImage (S.fiber k)),
      ∃ coarse : UniformTubeFamily (5 * rho) (Fin n),
        ∃ label : ↥(C.sourceOwnerImage (S.fiber k)) → Fin n,
          n ≤ parentFrameCodeCount rho ∧
          (∀ q, coarse.tubes q =
            (parentOrientedTube (S.coarse.tubes k)
              (fine.tubes (representative q).1)).changeRadius (5 * rho)) ∧
          ∀ p, (fine.tubes p.1).carrier ⊆
            (coarse.tubes (label p)).carrier := by
  classical
  let Parameter := ↥(C.sourceOwnerImage (S.fiber k))
  let parent : Tube rho := S.coarse.tubes k
  let owner : Parameter → Tube delta := fun p => fine.tubes p.1
  have hbounds : ∀ p : Parameter,
      UnorientedDirectionClose (owner p).axis parent.axis
          (14 * (rho : Real)) ∧
        ‖parentFrameTransverseOffset parent (owner p)‖ ≤ 94 * (rho : Real) ∧
        |parentFrameLongitudinalOffset parent (owner p)| ≤ 4 := by
    intro p
    obtain ⟨a, ha, howner⟩ := Finset.mem_image.mp p.property
    have h := scaleCover_owner_parentFrame_bounds C S hdeltaSmall
      hdeltaRho hrhoOne k a ha
    simpa only [owner, parent, howner] using h
  let hlong : ∀ p : Parameter,
      |parentFrameLongitudinalOffset parent (owner p)| ≤ 4 :=
    fun p => (hbounds p).2.2
  let hdirection : ∀ p : Parameter,
      UnorientedDirectionClose (owner p).axis parent.axis
        (14 * (rho : Real)) := fun p => (hbounds p).1
  let htransverse : ∀ p : Parameter,
      ‖parentFrameTransverseOffset parent (owner p)‖ ≤ 94 * (rho : Real) :=
    fun p => (hbounds p).2.1
  obtain ⟨n, representative, coarse, label, hn, _hcode, hcoarse,
      hcontain⟩ :=
    exists_parentFrameOwnerCellCoarseCover hrhoPos hdeltaRho parent owner
      hlong hdirection htransverse
  refine ⟨n, representative, coarse, label, hn, ?_, ?_⟩
  · intro q
    simpa only [parent, owner] using hcoarse q
  · intro p
    simpa only [owner] using hcontain p

#print axioms finiteCodeRepresentative_code
#print axioms exists_parentFrameOwnerCellCoarseCover
#print axioms exists_scaleCover_ownerImage_parentFrameCoarseCover

end
end Family8PaperConflictOwnerParentFrameCoarseCoverV6
