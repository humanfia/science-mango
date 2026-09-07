import Family8Grounding.Family8JointExactUniformFiberPaperDistinctV4
import Family8Grounding.Family8ThinPlankFiveParameterUnorientedFrameBoxPackingV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8JointExactUniformFiberThinPlankPackingV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8CommonPointTubePackingV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperEssentialDistinctActualDatumConstantExtractionV3
open Family8JointExactUniformFiberPaperDistinctV4
open Family8PaperEssentialDistinctConstantExtractionV2
open Family8ThinPlankEssentialDistinctPackingV4
open Family8ThinPlankFiveParameterPackingV2
open Family8ThinPlankFiveParameterFrameBoxPackingV4
open Family8ThinPlankFiveParameterUnorientedFrameBoxPackingV2

noncomputable section

variable {delta rho : NNReal} {iota : Type} {coarseCard : Nat}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho (Fin coarseCard)}

/-!
# Same-Joint exact fibre with an actual quadratic thin-plank cap

The geometric hypotheses below concern the literal source fibre tubes and one
literal FrameBox.  The constant-loss paper-distinct extraction preserves those
tubes definitionally, so admissibility supplies the old overlap-based
essential distinctness required by the five-parameter packing kernel.
-/

/-- The exact-uniform Joint fibre admits a constant-retention actual subtype
whose count is quadratically bounded by the literal FrameBox aspect ratio. -/
theorem exists_paperEssentiallyDistinct_exactUniform_sourceFineFiber_with_thinPlankCap_unoriented
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (P : CoarseTubePartition fine coarse)
    (hfineTubes : ∀ i, fine.tubes i = D.family.tubes i)
    (Y : Shading fine.bodyFamily) {loss : Nat}
    (A : ExactAssembly P.asConvexFactorization Y loss)
    (hloss : P.branchingLoss = 1)
    (k : {k // k ∈ P.coarseIndices})
    (B : FrameBox) (R : Real) (hR : 0 ≤ R)
    (hsum : (∑ i, B.side i : NNReal) ≤ 4)
    (hside0 : (B.side 0 : Real) ≤ (delta : Real))
    (hside1 : (B.side 1 : Real) ≤ R * (delta : Real))
    (hthin :
      (delta : Real) ^ 2 + (R * (delta : Real)) ^ 2 ≤ (3 : Real) / 4)
    (hcontain : ∀ i : {i // i ∈ P.fiber k.1},
      (fine.tubes i.1).carrier ⊆ B.carrier) :
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
      Fintype.card {i // i ∈ selected} ≤
        thinPlankFivePackingNatCap (3 * R) ∧
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
  obtain ⟨selected, hnonempty, hselectedAdmissible, hrefined, hpaper,
      hbranching, hmass, haverage⟩ :=
    exists_paperEssentiallyDistinct_exactUniform_sourceFineFiber
      D hD hdeltaSmall P hfineTubes Y A hloss k
  let selectedD :=
    restrictActualTubeDatum
      (jointSourceFineLevelFiberDatum P Y A k.1) selected
  have hselectedContain (i : {i // i ∈ selected}) :
      (selectedD.family.tubes i).carrier ⊆ B.carrier := by
    change (fine.tubes i.1.1).carrier ⊆ B.carrier
    exact hcontain i.1
  have hselectedPairwise :
      Set.Pairwise (Set.univ : Set {i // i ∈ selected}) fun i j =>
        EssentiallyDistinct (selectedD.family.tubes i)
          (selectedD.family.tubes j) :=
    hselectedAdmissible.pairwise_essentiallyDistinct
  have hcap :
      Fintype.card {i // i ∈ selected} ≤
        thinPlankFivePackingNatCap (3 * R) :=
    card_le_thinPlankFivePackingNatCap_of_frameBox_unoriented
      B selectedD.family.tubes R hD.delta_pos hdeltaSmall hR hsum hside0 hside1
      hthin hselectedContain hselectedPairwise
  refine ⟨selected, hnonempty, hselectedAdmissible, hrefined, hpaper,
    hcap, hbranching, hmass, haverage⟩

#print axioms exists_paperEssentiallyDistinct_exactUniform_sourceFineFiber_with_thinPlankCap_unoriented

end
end Family8JointExactUniformFiberThinPlankPackingV5
