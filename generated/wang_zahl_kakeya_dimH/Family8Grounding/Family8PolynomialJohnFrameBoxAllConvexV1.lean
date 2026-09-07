import Family8Grounding.Family8PolynomialJohnFrameBoxVolumeV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8PolynomialJohnFrameBoxAllConvexV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8PolynomialJohnFrameBoxContainmentV1
open Family8PolynomialJohnFrameBoxVolumeV2

noncomputable section

/-!
# Polynomial John-box tests control all convex containers

For a convex body containing at least one source tube, choose that tube and
clip the body to the unit ball before taking its John certificate.  Every
other captured unit-ball tube lies in the same clipped body, hence in the
single representative catalogue test.  The representative test volume is
bounded by the explicit universal John constant times the original body
volume.  Empty captured sets are handled directly.
-/

@[simp] theorem coe_ofCapturedTube_body
    {delta : NNReal} (hdelta : 0 < delta)
    (K : ConvexBody Space) (T : Tube delta)
    (hTK : T.carrier ⊆ (K : Set Space))
    (hTU : T.carrier ⊆ Metric.closedBall (0 : Space) 1) :
    ((CapturedJohnParameter.ofCapturedTube hdelta K T hTK hTU).body :
      Set Space) = (K : Set Space) ∩ Metric.closedBall (0 : Space) 1 := by
  rfl

theorem capturedTube_subset_catalogueTest
    {delta : NNReal} (hdelta : 0 < delta)
    (K : ConvexBody Space) (witness : Tube delta)
    (hwitnessK : witness.carrier ⊆ (K : Set Space))
    (hwitnessUnit : witness.carrier ⊆ Metric.closedBall (0 : Space) 1)
    (T : Tube delta) (hTK : T.carrier ⊆ (K : Set Space))
    (hTUnit : T.carrier ⊆ Metric.closedBall (0 : Space) 1) :
    let p := CapturedJohnParameter.ofCapturedTube hdelta K witness
      hwitnessK hwitnessUnit
    T.carrier ⊆
      (representativeTestBody delta hdelta (parameterCode hdelta p) :
        Set Space) := by
  let p := CapturedJohnParameter.ofCapturedTube hdelta K witness
    hwitnessK hwitnessUnit
  apply tube_subset_representativeTestBody hdelta p T
  intro x hx
  rw [coe_ofCapturedTube_body]
  exact ⟨hTK hx, hTUnit hx⟩

theorem catalogueTest_volume_le_originalBody
    {delta : NNReal} (hdelta : 0 < delta)
    (K : ConvexBody Space) (witness : Tube delta)
    (hwitnessK : witness.carrier ⊆ (K : Set Space))
    (hwitnessUnit : witness.carrier ⊆ Metric.closedBall (0 : Space) 1) :
    let p := CapturedJohnParameter.ofCapturedTube hdelta K witness
      hwitnessK hwitnessUnit
    volume (representativeTestBody delta hdelta (parameterCode hdelta p) :
      Set Space) ≤ johnCatalogueVolumeConstant * volume (K : Set Space) := by
  let p := CapturedJohnParameter.ofCapturedTube hdelta K witness
    hwitnessK hwitnessUnit
  calc
    volume (representativeTestBody delta hdelta (parameterCode hdelta p) :
        Set Space) ≤ johnCatalogueVolumeConstant * volume (p.body : Set Space) :=
      representativeTestBody_volume_le_johnCatalogueVolumeConstant hdelta p
    _ ≤ johnCatalogueVolumeConstant * volume (K : Set Space) := by
      gcongr
      intro x hx
      change x ∈ (K : Set Space) ∩ Metric.closedBall (0 : Space) 1 at hx
      exact hx.1

/-- Convex family underlying an actual indexed tube family. -/
def tubeBodyFamily {delta : NNReal} {index : Type*}
    (T : index → Tube delta) : ConvexFamily index :=
  fun i => (T i).body

@[simp] theorem coe_tubeBodyFamily
    {delta : NNReal} {index : Type*} (T : index → Tube delta) (i : index) :
    (tubeBodyFamily T i : Set Space) = (T i).carrier := rfl

/-- Fixed control on the polynomial occupied catalogue implies control on
every convex body, at the explicit universal John loss.  This replaces the
exponential canonical-hull test list in the finite-test reduction. -/
theorem isKatzTao_of_polynomialJohnCatalogue
    {delta : NNReal} (hdelta : 0 < delta)
    {index : Type*} [Fintype index] [DecidableEq index]
    (T : index → Tube delta)
    (hunit : ∀ i, (T i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (A : ENNReal)
    (hfinite : ∀ q : CatalogueIndex delta hdelta,
      IsKatzTaoAt A (tubeBodyFamily T)
        (representativeTestBody delta hdelta q)) :
    IsKatzTao (A * johnCatalogueVolumeConstant) (tubeBodyFamily T) := by
  classical
  intro K
  let captured := containedIndices (tubeBodyFamily T) K
  by_cases hcaptured : captured.Nonempty
  · obtain ⟨i, hi⟩ := hcaptured
    have hiK : (T i).carrier ⊆ (K : Set Space) := by
      have hi' : i ∈ containedIndices (tubeBodyFamily T) K := hi
      rw [mem_containedIndices] at hi'
      simpa only [coe_tubeBodyFamily] using hi'
    let p := CapturedJohnParameter.ofCapturedTube hdelta K (T i) hiK (hunit i)
    let q : CatalogueIndex delta hdelta := parameterCode hdelta p
    have hmass :
        containedMass (tubeBodyFamily T) K ≤
          containedMass (tubeBodyFamily T)
            (representativeTestBody delta hdelta q) := by
      unfold containedMass
      apply Finset.sum_le_sum_of_subset
      intro j hj
      rw [mem_containedIndices] at hj ⊢
      rw [coe_tubeBodyFamily] at hj ⊢
      exact capturedTube_subset_catalogueTest hdelta K (T i) hiK
        (hunit i) (T j) hj (hunit j)
    have htestVolume :
        volume (representativeTestBody delta hdelta q : Set Space) ≤
          johnCatalogueVolumeConstant * volume (K : Set Space) := by
      exact catalogueTest_volume_le_originalBody hdelta K (T i) hiK (hunit i)
    calc
      containedMass (tubeBodyFamily T) K ≤
          containedMass (tubeBodyFamily T)
            (representativeTestBody delta hdelta q) := hmass
      _ ≤ A * volume (representativeTestBody delta hdelta q : Set Space) :=
        hfinite q
      _ ≤ A * (johnCatalogueVolumeConstant * volume (K : Set Space)) := by
        gcongr
      _ = (A * johnCatalogueVolumeConstant) * volume (K : Set Space) := by
        ring
  · have hcapturedEmpty : captured = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hcaptured
    unfold IsKatzTaoAt containedMass
    rw [show containedIndices (tubeBodyFamily T) K = ∅ from hcapturedEmpty]
    simp

#print axioms coe_ofCapturedTube_body
#print axioms capturedTube_subset_catalogueTest
#print axioms catalogueTest_volume_le_originalBody
#print axioms isKatzTao_of_polynomialJohnCatalogue

end
end Family8PolynomialJohnFrameBoxAllConvexV1
