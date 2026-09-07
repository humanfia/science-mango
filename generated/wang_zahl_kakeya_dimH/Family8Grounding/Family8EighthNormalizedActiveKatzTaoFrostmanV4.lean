import Family8Grounding.Family8EighthNormalizedKatzTaoAmbientFrostmanV2
import Family8Grounding.Family8GeneralizedKatzTaoMultiplicityV1
import Family8Grounding.Family8NormalizedLongIntervalFrostmanInheritanceV1
import Mathlib.Tactic

/-!
# Eighth-normalized Frostman control on one literal active family, V4

V2 attempted to close the final proof-dependent family transport by broad
simplification.  V3 had a namespace typo and is not imported.  This clean
successor records the pointwise family equality explicitly before
transporting the Frostman certificate.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EighthNormalizedActiveKatzTaoFrostmanV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8EighthNormalizedKatzTaoAmbientFrostmanV2
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1

noncomputable section

/-- The exact normalized ambient Frostman constant for a literal active
subtype of an actual datum. -/
def eighthNormalizedActiveKatzTaoFrostmanConstant
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (C : ENNReal) (D : ActualTubeDatum delta iota)
    (active : Finset iota) : ENNReal :=
  eighthNormalizedKatzTaoAmbientFrostmanConstant C
    (restrictActualTubeDatum D active)

/-- Katz--Tao control of an active source graph becomes unit-ball Frostman
control of its honest eighth normalization on exactly the same graph. -/
theorem eighthNormalizedActive_isFrostmanOn_of_isKatzTao
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    (active : Finset iota) (hactive : active.Nonempty)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hB2 : ∀ i, i ∈ active →
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2)
    {C : ENNReal}
    (hKT : IsKatzTao C (activeSubtypeFamily D.family.bodyFamily active)) :
    IsFrostmanOn
      (eighthNormalizedActiveKatzTaoFrostmanConstant C D active)
      (eighthNormalizedDatum D).family.bodyFamily active unitBallBody := by
  let _ : Nonempty {i // i ∈ active} :=
    Finset.nonempty_coe_sort.mpr hactive
  let DA := restrictActualTubeDatum D active
  have hB2A : ∀ i,
      (DA.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2 := by
    intro i
    change (D.family.tubes i.1).carrier ⊆
      Metric.closedBall (0 : Space) 2
    exact hB2 i.1 i.2
  have hKTA : IsKatzTao C DA.family.bodyFamily := by
    change IsKatzTao C (activeSubtypeFamily D.family.bodyFamily active)
    exact hKT
  have hFA := eighthNormalizedDatum_isFrostmanIn_of_isKatzTao
    DA hdeltaPos hdeltaHalf hB2A hKTA
  apply (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
    (eighthNormalizedDatum D).family.bodyFamily active unitBallBody).2
  have hfamily :
      (eighthNormalizedDatum DA).family.bodyFamily =
        activeSubtypeFamily
          (eighthNormalizedDatum D).family.bodyFamily active := by
    funext i
    rfl
  rw [← hfamily]
  simpa only [eighthNormalizedActiveKatzTaoFrostmanConstant, DA] using hFA

#print axioms eighthNormalizedActiveKatzTaoFrostmanConstant
#print axioms eighthNormalizedActive_isFrostmanOn_of_isKatzTao

end
end Family8EighthNormalizedActiveKatzTaoFrostmanV4
