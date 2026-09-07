import Family8Grounding.Family8SameQSingletonExactRResidualV1
import Mathlib.Tactic

/-!
# Source Frostman normalization on one fixed greedy occurrence

For a fixed occurrence `q`, its literal block density normalizes the global
source Katz--Tao estimate on exactly the fine fibre of `q`.  The retained set
is the singleton `{q}` and the density depth is zero.  No membership in the
canonical Proposition 5.1 bucket, and no density-covering hypothesis, is
used.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SameQSingletonFineBlockDensityNormalizedFrostmanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8Prop51SelectedFineBlockDensityNormalizedFrostmanV1
open Family8Prop51SelectedOccurrenceSourceFrostmanV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SameQSingletonExactRResidualV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- Global source Katz--Tao normalizes on the literal fine fibre of one fixed
greedy occurrence.  The only geometric input is containment of that fibre in
the ambient body.  The four scalar side conditions are exactly those needed
to cancel the two inverses displayed in the conclusion. -/
theorem sameQ_singletonFine_isFrostmanOn_of_sourceKatzTao
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (q : Fin (blocks F P).length)
    (ambient : ConvexBody Space) (A : ENNReal)
    (hKT : IsKatzTao A F)
    (hcontained : ∀ i ∈ selectedOccurrenceFineIndices P {q},
      (F i : Set Space) ⊆ (ambient : Set Space))
    (hd0 : blockDensity F (blockAt F P q) ≠ 0)
    (hdTop : blockDensity F (blockAt F P q) ≠ ∞)
    (hbodyVolume0 : volume ((blockAt F P q).body : Set Space) ≠ 0)
    (hbodyVolumeTop : volume ((blockAt F P q).body : Set Space) ≠ ∞) :
    let d := blockDensity F (blockAt F P q)
    IsFrostmanOn
      (prop51SubselectedFineBlockDensityFrostmanConstant
        A P Y d 0 {q} ambient)
      F (selectedOccurrenceFineIndices P {q}) ambient := by
  dsimp only
  let selected := selectedOccurrenceFineIndices P {q}
  let d := blockDensity F (blockAt F P q)
  let bodyVolume := volume ((blockAt F P q).body : Set Space)
  let C := prop51SubselectedFineBlockDensityFrostmanConstant
    A P Y d 0 {q} ambient
  have hlower : prop51SelectedLowerDensity P Y d 0 = d := by
    exact prop51SelectedLowerDensity_zero_eq P Y d
  have hsubselectedBodyVolume :
      prop51SubselectedBodyVolume P {q} = bodyVolume := by
    dsimp only [bodyVolume]
    simp [prop51SubselectedBodyVolume]
  have hKTselected : IsKatzTao A (activeSubtypeFamily F selected) := by
    change IsKatzTao A (selectedCoarseFamily F selected)
    exact isKatzTao_selectedCoarseFamily_of_isKatzTaoOn (hKT.on selected)
  have hmass : d * bodyVolume ≤ containedMassOn F selected ambient := by
    rw [containedMassOn_eq_bodyMassOn_of_contained F selected ambient
      hcontained]
    dsimp only [selected, d, bodyVolume]
    unfold selectedOccurrenceFineIndices bodyMassOn
    simpa [blockMass] using
      lower_mul_volume_le_blockMass F (blockAt F P q)
        (blockDensity F (blockAt F P q)) le_rfl
  have hbase : A * volume (ambient : Set Space) ≤
      C * containedMass (activeSubtypeFamily F selected) ambient := by
    rw [containedMass_activeSubtypeFamily]
    calc
      A * volume (ambient : Set Space) = C * (d * bodyVolume) := by
        dsimp only [C]
        unfold prop51SubselectedFineBlockDensityFrostmanConstant
        rw [hlower, hsubselectedBodyVolume]
        symm
        calc
          (A * volume (ambient : Set Space) * d⁻¹ * bodyVolume⁻¹) *
                (d * bodyVolume) =
              A * volume (ambient : Set Space) * (d⁻¹ * d) *
                (bodyVolume⁻¹ * bodyVolume) := by ac_rfl
          _ = A * volume (ambient : Set Space) := by
            rw [ENNReal.inv_mul_cancel hd0 hdTop,
              ENNReal.inv_mul_cancel hbodyVolume0 hbodyVolumeTop]
            simp
      _ ≤ C * containedMassOn F selected ambient :=
        mul_le_mul' le_rfl hmass
  apply (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
    F selected ambient).2
  apply IsKatzTao.isFrostmanIn hKTselected
  · intro i
    exact hcontained i.1 i.2
  · exact hbase

end

end Family8SameQSingletonFineBlockDensityNormalizedFrostmanV1
