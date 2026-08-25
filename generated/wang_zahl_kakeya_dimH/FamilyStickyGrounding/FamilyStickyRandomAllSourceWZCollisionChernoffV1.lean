import FamilyStickyGrounding.FamilyStickyRandomWZSingleTranslationCapV1
import FamilyStickyGrounding.FamilyStickyActualSharedLocalFeasibilityV1
import FamilyStickyGrounding.FamilyStickyRandomPaperTailNumericsV1

open Set
open scoped BigOperators NNReal

namespace FamilyStickyRandomAllSourceWZCollisionChernoffV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomWZLineParameterGeometryV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyRandomWZSingleTranslationCapV1
open FamilyStickyRandomHundredContainerSelectionV1
open FamilyStickyRandomHundredContainerSelectionV1.MaximalSelection
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid
open FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking
open FamilyStickyActualSharedLocalFeasibilityV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Variable-cap Chernoff bound for all WZ-separated sources

No source tube is discarded.  The common-neighbour packing theorem gives the
actual single-translation load cap `C_WZ`, and the finite Chernoff theorem is
normalized by precisely that cap.

The expectation majorant is the proved local packing formula

`m = 297 * #active * k_0 * k_1 / rho^2`.

The repetition count is `1` when `m=0`, otherwise `floor(C_WZ/m)`.  Thus
`m <= C_WZ` gives `J >= 1`, while `J*m <= C_WZ` holds unconditionally.  The
tail and all box-geometry inputs are constructed internally.
-/

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [Nonempty translation]
  [DecidableEq translation] [DecidableEq tubeIndex]


/-- The literal local double-count expectation majorant for the selected
collision catalogue. -/
def allSourceWZCollisionMean
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (motionRadius : NNReal) : Real :=
  (297 * (G.tubes.card : Real) *
      (Tube.frameBoxSides (hundredRadius delta) 0 : Real) *
      (Tube.frameBoxSides (hundredRadius delta) 1 : Real)) /
    (motionRadius : Real) ^ 2

theorem allSourceWZCollisionMean_nonneg
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (motionRadius : NNReal) :
    0 <= allSourceWZCollisionMean G motionRadius := by
  unfold allSourceWZCollisionMean
  positivity

/-- Canonical nondegenerate repetition count normalized by `C_WZ`. -/
def allSourceWZCollisionRepetitions
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (motionRadius : NNReal) : Nat :=
  if allSourceWZCollisionMean G motionRadius = 0 then 1
  else Nat.floor ((commonHundredNeighbourPackingConstant : Real) /
    allSourceWZCollisionMean G motionRadius)

theorem one_le_allSourceWZCollisionRepetitions
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (motionRadius : NNReal)
    (hcap : allSourceWZCollisionMean G motionRadius <=
      (commonHundredNeighbourPackingConstant : Real)) :
    1 <= allSourceWZCollisionRepetitions G motionRadius := by
  let m := allSourceWZCollisionMean G motionRadius
  have hmnonneg : 0 <= m := allSourceWZCollisionMean_nonneg G motionRadius
  by_cases hmzero : m = 0
  · simp [allSourceWZCollisionRepetitions, m, hmzero]
  · have hmpos : 0 < m := lt_of_le_of_ne hmnonneg (Ne.symm hmzero)
    rw [allSourceWZCollisionRepetitions, if_neg hmzero]
    apply Nat.le_floor
    exact (le_div_iff₀ hmpos).2 (by simpa [m] using hcap)

theorem allSourceWZCollisionRepetitions_mul_mean_le_cap
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (motionRadius : NNReal) :
    (allSourceWZCollisionRepetitions G motionRadius : Real) *
        allSourceWZCollisionMean G motionRadius <=
      (commonHundredNeighbourPackingConstant : Real) := by
  let m := allSourceWZCollisionMean G motionRadius
  have hmnonneg : 0 <= m := allSourceWZCollisionMean_nonneg G motionRadius
  have hcapnonneg : (0 : Real) <= commonHundredNeighbourPackingConstant :=
    Nat.cast_nonneg _
  by_cases hmzero : m = 0
  · simp [allSourceWZCollisionRepetitions, m, hmzero]
  · have hmpos : 0 < m := lt_of_le_of_ne hmnonneg (Ne.symm hmzero)
    rw [allSourceWZCollisionRepetitions, if_neg hmzero]
    exact (le_div_iff₀ hmpos).mp
      (Nat.floor_le (div_nonneg hcapnonneg hmpos.le))

/-- Canonical strict union-bound threshold for every all-source WZ collision
candidate. -/
def allSourceWZCollisionTail
    (G : ActualTubeTranslationGrid delta translation tubeIndex) : Real :=
  Real.log ((((collisionGrid G).activeTests.card : Real) *
    Real.exp (Real.exp 1 - 1)) + 1)

theorem allSourceWZCollisionTailRoom
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    ((collisionGrid G).activeTests.card : Real) *
        Real.exp (Real.exp 1 - 1) <
      Real.exp (allSourceWZCollisionTail G) := by
  let x : Real :=
    ((collisionGrid G).activeTests.card : Real) *
      Real.exp (Real.exp 1 - 1)
  have hx : 0 <= x :=
    mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hx1 : 0 < x + 1 := by linarith
  rw [allSourceWZCollisionTail, show
    ((collisionGrid G).activeTests.card : Real) *
      Real.exp (Real.exp 1 - 1) = x by rfl, Real.exp_log hx1]
  linarith

theorem allSourceWZCollision_explicit_297
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    {motionRadius : NNReal} (hRadius : 0 < motionRadius)
    (K : Fin (collisionGrid G).testCard) :
    297 * ((collisionGrid G).tubes.card : Real) *
        (collisionSide G K 0 : Real) *
        (collisionSide G K 1 : Real) <=
      (motionRadius : Real) ^ 2 *
        allSourceWZCollisionMean G motionRadius := by
  unfold allSourceWZCollisionMean collisionSide
  have hRadiusReal : (0 : Real) < (motionRadius : Real) := by
    exact_mod_cast hRadius
  have hsq : (motionRadius : Real) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hRadiusReal.ne'
  change 297 * (G.tubes.card : Real) *
        (Tube.frameBoxSides (hundredRadius delta) 0 : Real) *
        (Tube.frameBoxSides (hundredRadius delta) 1 : Real) <= _
  rw [mul_comm ((motionRadius : Real) ^ 2), div_mul_cancel₀ _ hsq]

/-- One common finite outcome, with direct `C_WZ` collision control and the
motion-radius conclusion retained for that same outcome. -/
structure AllSourceWZCollisionOutput
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (motionRadius : NNReal) where
  omega : Fin (allSourceWZCollisionRepetitions G motionRadius) -> translation
  repetitions_one_le : 1 <= allSourceWZCollisionRepetitions G motionRadius
  vector_norm_le : forall j,
    ‖G.gridVector (omega j)‖ <= (motionRadius : Real)
  allCandidateLoad : forall a : ModelCandidate G,
    (∑ j, candidateCollisionLoad G a (omega j)) <=
      Nat.ceil (allSourceWZCollisionTail G *
        commonHundredNeighbourPackingConstant)
  sourceCarrier_motionRadius : forall j
      (i : ActiveSource G),
    (translateTube (G.tube i)
      (G.gridVector (omega j))).carrier ⊆
      Metric.cthickening (motionRadius : Real)
        (G.tube i).carrier

/-- Geometry-complete all-source variable-cap Chernoff adapter.  The sole remaining analytic
scale input is the transparent inequality `allSourceWZCollisionMean <= C_WZ`; the
packing, point counts, balance, nonzero repetition count, and strict tail
room are all constructed internally. -/
theorem exists_allSourceWZCollisionOutput
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    {mesh motionRadius : NNReal}
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (G.tubes : Set tubeIndex) fun i j =>
      WZEndpointParameterSeparated (G.tube i) (G.tube j))
    (hRadius : 0 < motionRadius)
    (hsmall : hundredRadius delta <= (2 : NNReal)⁻¹)
    (hmeshDelta : mesh <= delta) (hmeshRadius : mesh <= motionRadius)
    (hcap : allSourceWZCollisionMean G motionRadius <=
      (commonHundredNeighbourPackingConstant : Real)) :
    Nonempty (AllSourceWZCollisionOutput G motionRadius) := by
  let C := collisionGrid G
  let PC : IsSharedTranslationPacking C mesh motionRadius :=
    FamilyStickyRandomModelTubeCollisionGridV1.IsSharedTranslationPacking.collisionGrid P
  have hdim : forall K, HasBoxDimensions 2 (collisionSide G K)
      (C.testBody K) := by
    intro K
    exact collisionGrid_hasBoxDimensions G hsmall K
  let outerBox : Fin C.testCard -> FrameBox :=
    FamilyStickyFrameBoxCertificateExtractionV1.ActualTubeTranslationGrid.testOuterBox
      C hdim
  have houterSide (K : Fin C.testCard) :
      (outerBox K).side = collisionSide G K := by
    exact FamilyStickyFrameBoxCertificateExtractionV1.ActualTubeTranslationGrid.testOuterBox_side
      C hdim K
  have hloadCap : forall K, K ∈ C.activeTests -> forall g,
      (C.singleLoad K g : Real) <=
        commonHundredNeighbourPackingConstant := by
    intro K _hK g
    let a := modelCandidateOfIndex G K
    have hindex : modelCandidateIndex G a = K := by
      exact (modelCandidateEquivFin G).apply_symm_apply K
    rw [← hindex]
    exact_mod_cast collisionGrid_singleLoad_le_WZConstant G hdelta hpair a g
  obtain ⟨omega, hload⟩ :=
    FamilyStickyRandomPaperTailNumericsV1.ActualTubeTranslationGrid.exists_grid_translations_singleLoad_le_A_mul_cap
      C (fun K =>
        FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localPointBudget
          PC (outerBox K))
      (allSourceWZCollisionRepetitions G motionRadius)
      (cap := (commonHundredNeighbourPackingConstant : Real))
      (mean := allSourceWZCollisionMean G motionRadius)
      (A := allSourceWZCollisionTail G)
      (by exact_mod_cast commonHundredNeighbourPackingConstant_pos)
      (allSourceWZCollisionMean_nonneg G motionRadius)
      (allSourceWZCollisionRepetitions_mul_mean_le_cap G motionRadius)
      hloadCap
      (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.tubeHitCount_le_localPointBudget_of_boxDimensions
        PC hdim)
      (fun K hK => by
        apply FamilyStickyActualSharedLocalFeasibilityV1.balance_of_explicit_297
          PC (outerBox K)
        · rw [houterSide K]
          exact hmeshDelta.trans (delta_le_collisionSide_zero G K)
        · rw [houterSide K]
          exact hmeshDelta.trans (delta_le_collisionSide_one G K)
        · exact hmeshRadius
        · exact allSourceWZCollisionMean_nonneg G motionRadius
        · rw [houterSide K]
          exact allSourceWZCollision_explicit_297 G hRadius K)
      (allSourceWZCollisionTailRoom G)
  refine ⟨{
    omega := omega
    repetitions_one_le := one_le_allSourceWZCollisionRepetitions
      G motionRadius hcap
    vector_norm_le := fun j => P.gridVector_norm_le (omega j)
    allCandidateLoad := ?_
    sourceCarrier_motionRadius := ?_ }⟩
  · intro a
    let K := modelCandidateIndex G a
    have hreal := hload K (by exact Finset.mem_univ K)
    have hreal' :
        ((∑ j, candidateCollisionLoad G a (omega j) : Nat) : Real) <=
          allSourceWZCollisionTail G *
            commonHundredNeighbourPackingConstant := by
      rw [Nat.cast_sum]
      simpa only [K, C, collisionGrid_singleLoad_candidate]
        using hreal
    have hceil :
        ((∑ j, candidateCollisionLoad G a (omega j) : Nat) : Real) <=
          (Nat.ceil (allSourceWZCollisionTail G *
            commonHundredNeighbourPackingConstant) : Nat) :=
      hreal'.trans (Nat.le_ceil _)
    exact_mod_cast hceil
  · intro j i
    exact
      FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.translateTube_carrier_subset_cthickening
        P i (omega j)

#print axioms allSourceWZCollisionMean_nonneg
#print axioms one_le_allSourceWZCollisionRepetitions
#print axioms allSourceWZCollisionRepetitions_mul_mean_le_cap
#print axioms allSourceWZCollisionTailRoom
#print axioms allSourceWZCollision_explicit_297
#print axioms exists_allSourceWZCollisionOutput

end
end FamilyStickyRandomAllSourceWZCollisionChernoffV1
