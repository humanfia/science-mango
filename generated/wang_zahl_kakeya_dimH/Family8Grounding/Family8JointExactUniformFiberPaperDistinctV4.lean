import Family8Grounding.Family8CoarseTubePartitionExactUniformStickyFiberV8
import Family8Grounding.Family8JointTubeFactoringExactUniformProp66AProductV4
import Family8Grounding.Family8PaperEssentialDistinctActualDatumConstantExtractionV3
import Family8Grounding.Family8SharpKatzTaoOrGreedyHighConcentrationV1
import Mathlib.Tactic

/-!
# A paper-distinct actual subtype of one exact-uniform Joint fibre, V4

This successor uses the literal restricted `UniformTubeFamily`, while its
shading is the exact assembly's source fine-level shading on that subtype.
It produces a same-fibre paper-essentially-distinct subtype with the exact
Joint branching count and honest mass/average transport.  V1--V3 are failed
drafts and are not imported.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8JointExactUniformFiberPaperDistinctV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8CoarseTubePartitionExactUniformStickyFiberV8
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8JointTubeFactoringExactUniformProp66AProductV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperEssentialDistinctActualDatumConstantExtractionV3
open Family8PaperEssentialDistinctConstantExtractionV2
open Family8SharpKatzTaoOrGreedyHighConcentrationV1
open Family8StickyFiberContractedJohnProxyDatumV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {iota : Type} {coarseCard : Nat}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho (Fin coarseCard)}

/-- The exact source fine-level shading on the uniformly restricted literal
Joint fibre. -/
def jointSourceFineLevelFiberDatum
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {loss : Nat}
    (A : ExactAssembly P.asConvexFactorization Y loss)
    (k : Fin coarseCard) : ActualTubeDatum delta {i // i ∈ P.fiber k} where
  family := fine.restrictTo (P.fiber k)
  shading := stickyFiberSourceShading (exactPartitionStickyCover P)
    (sourceFineLevelShading A k) k

@[simp] theorem jointSourceFineLevelFiberDatum_family_tubes
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {loss : Nat}
    (A : ExactAssembly P.asConvexFactorization Y loss)
    (k : Fin coarseCard) (i : {i // i ∈ P.fiber k}) :
    (jointSourceFineLevelFiberDatum P Y A k).family.tubes i =
      fine.tubes i.1 := by
  rfl

@[simp] theorem jointSourceFineLevelFiberDatum_shading_carrier
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {loss : Nat}
    (A : ExactAssembly P.asConvexFactorization Y loss)
    (k : Fin coarseCard) (i : {i // i ∈ P.fiber k}) :
    (jointSourceFineLevelFiberDatum P Y A k).shading.carrier i =
      (sourceFineLevelShading A k).carrier i.1 := by
  rfl

/-- Tube equality with an admissible source datum supplies every geometric
admissibility field for the literal Joint fibre datum. -/
theorem jointSourceFineLevelFiberDatum_isAdmissible
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (P : CoarseTubePartition fine coarse)
    (hfineTubes : ∀ i, fine.tubes i = D.family.tubes i)
    (Y : Shading fine.bodyFamily) {loss : Nat}
    (A : ExactAssembly P.asConvexFactorization Y loss)
    (k : Fin coarseCard) :
    (jointSourceFineLevelFiberDatum P Y A k).IsAdmissible := by
  refine
    { delta_pos := hD.delta_pos
      delta_le_half := hD.delta_le_half
      contained_in_unit_ball := ?_
      pairwise_essentiallyDistinct := ?_ }
  · intro i
    rw [jointSourceFineLevelFiberDatum_family_tubes, hfineTubes i.1]
    exact hD.contained_in_unit_ball i.1
  · intro i _hi j _hj hij
    rw [jointSourceFineLevelFiberDatum_family_tubes,
      jointSourceFineLevelFiberDatum_family_tubes,
      hfineTubes i.1, hfineTubes j.1]
    apply hD.pairwise_essentiallyDistinct (Set.mem_univ i.1)
      (Set.mem_univ j.1)
    exact fun hijValue => hij (Subtype.ext hijValue)

/-- The literal fibre datum has exactly the source fine-level actual average. -/
theorem jointSourceFineLevelFiberDatum_averageMultiplicity_eq
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {loss : Nat}
    (A : ExactAssembly P.asConvexFactorization Y loss)
    (k : Fin coarseCard) :
    (jointSourceFineLevelFiberDatum P Y A k).shading.averageMultiplicity =
      (sourceFineLevelShading A k).averageMultiplicity := by
  change
    (stickyFiberSourceShading (exactPartitionStickyCover P)
      (sourceFineLevelShading A k) k).averageMultiplicity = _
  exact stickyFiber_exactPartition_sourceFineLevel_averageMultiplicity_eq
    P Y A k

/-- The corresponding exact identity for multiplicity-counted mass. -/
theorem jointSourceFineLevelFiberDatum_shadingMass_eq
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {loss : Nat}
    (A : ExactAssembly P.asConvexFactorization Y loss)
    (k : Fin coarseCard) :
    (jointSourceFineLevelFiberDatum P Y A k).shading.shadingMass =
      (sourceFineLevelShading A k).shadingMass := by
  change
    (stickyFiberSourceShading (exactPartitionStickyCover P)
      (sourceFineLevelShading A k) k).shadingMass = _
  exact stickyFiber_exactPartition_sourceFineLevel_shadingMass_eq P Y A k

/-- Constant-loss strong-distinct extraction on the same exact Joint fibre.
The residual paper-strength input is now only a thickened-plank packing
estimate for the selected actual datum. -/
theorem exists_paperEssentiallyDistinct_exactUniform_sourceFineFiber
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (P : CoarseTubePartition fine coarse)
    (hfineTubes : ∀ i, fine.tubes i = D.family.tubes i)
    (Y : Shading fine.bodyFamily) {loss : Nat}
    (A : ExactAssembly P.asConvexFactorization Y loss)
    (hloss : P.branchingLoss = 1)
    (k : {k // k ∈ P.coarseIndices}) :
    ∃ selected : Finset {i // i ∈ P.fiber k.1},
      Nonempty {i // i ∈ selected} ∧
      (restrictActualTubeDatum
        (jointSourceFineLevelFiberDatum P Y A k.1) selected).IsAdmissible ∧
      (restrictActualTubeDatum
        (jointSourceFineLevelFiberDatum P Y A k.1) selected).family.refinement.refined =
          Finset.univ ∧
      Set.Pairwise (Set.univ : Set {i // i ∈ selected}) (fun i j =>
        PaperEssentiallyDistinct
          ((restrictActualTubeDatum
            (jointSourceFineLevelFiberDatum P Y A k.1) selected).family.tubes i)
          ((restrictActualTubeDatum
            (jointSourceFineLevelFiberDatum P Y A k.1) selected).family.tubes j)) ∧
      (P.branching : ENNReal) ≤
        (paperConflictConstantCodeLoss + 1 : Nat) *
          (Fintype.card {i // i ∈ selected} : ENNReal) ∧
      (sourceFineLevelShading A k.1).shadingMass ≤
        (paperConflictConstantCodeLoss + 1 : Nat) *
          (restrictActualTubeDatum
            (jointSourceFineLevelFiberDatum P Y A k.1) selected).shading.shadingMass ∧
      (sourceFineLevelShading A k.1).averageMultiplicity ≤
        (paperConflictConstantCodeLoss + 1 : Nat) *
          (restrictActualTubeDatum
            (jointSourceFineLevelFiberDatum P Y A k.1) selected).shading.averageMultiplicity := by
  let fiberD := jointSourceFineLevelFiberDatum P Y A k.1
  have hfiberAdmissible : fiberD.IsAdmissible := by
    simpa only [fiberD] using
      jointSourceFineLevelFiberDatum_isAdmissible
        D hD P hfineTubes Y A k.1
  obtain ⟨selected, hnonempty, hselectedAdmissible, hrefined,
      hpaper, hcard, hmass⟩ :=
    exists_paperEssentiallyDistinct_actualSubtype
      fiberD hfiberAdmissible hdeltaSmall
  have hfiberNonempty : Nonempty {i // i ∈ P.fiber k.1} :=
    Finset.nonempty_coe_sort.mpr (P.fiber_nonempty k.2)
  have hselectedNonempty : Nonempty {i // i ∈ selected} :=
    hnonempty hfiberNonempty
  have hcardExact : Fintype.card {i // i ∈ P.fiber k.1} = P.branching := by
    rw [Fintype.card_coe]
    exact fiber_card_eq_branching_of_branchingLoss_eq_one P hloss k.2
  have hmassSource :
      (sourceFineLevelShading A k.1).shadingMass ≤
        (paperConflictConstantCodeLoss + 1 : Nat) *
          (restrictActualTubeDatum fiberD selected).shading.shadingMass := by
    rw [← jointSourceFineLevelFiberDatum_shadingMass_eq P Y A k.1]
    simpa only [fiberD] using hmass
  have haverageFiber :=
    source_averageMultiplicity_le_loss_mul_restrictActualTubeDatum
      fiberD selected (paperConflictConstantCodeLoss + 1 : Nat) hmass
  have haverageSource :
      (sourceFineLevelShading A k.1).averageMultiplicity ≤
        (paperConflictConstantCodeLoss + 1 : Nat) *
          (restrictActualTubeDatum fiberD selected).shading.averageMultiplicity := by
    rw [← jointSourceFineLevelFiberDatum_averageMultiplicity_eq P Y A k.1]
    exact haverageFiber
  refine ⟨selected, hselectedNonempty, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [fiberD] using hselectedAdmissible
  · simpa only [fiberD] using hrefined
  · simpa only [fiberD] using hpaper
  · rw [← hcardExact]
    exact hcard
  · simpa only [fiberD] using hmassSource
  · simpa only [fiberD] using haverageSource

#print axioms jointSourceFineLevelFiberDatum
#print axioms jointSourceFineLevelFiberDatum_family_tubes
#print axioms jointSourceFineLevelFiberDatum_shading_carrier
#print axioms jointSourceFineLevelFiberDatum_isAdmissible
#print axioms jointSourceFineLevelFiberDatum_averageMultiplicity_eq
#print axioms jointSourceFineLevelFiberDatum_shadingMass_eq
#print axioms exists_paperEssentiallyDistinct_exactUniform_sourceFineFiber

end
end Family8JointExactUniformFiberPaperDistinctV4
