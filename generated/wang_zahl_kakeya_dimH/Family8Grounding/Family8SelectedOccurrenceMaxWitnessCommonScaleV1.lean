import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1
import Family8Grounding.Family8SelectedOccurrenceMaxOwnerAverageRetentionV3
import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullUniqueOwnerV2
import Submission.Kakeya.ConvexFactoring.TubeFrameBoxDimensions
import Mathlib.Tactic

/-!
# Common-scale max-witness tube refinement

The original max-owner hull need not fit an `a x b x 1` box with `b <= rho`.
This successor therefore performs the smallest literal refinement that has
uniform geometry: in each occurrence it keeps the complete fine tube of the
already constructed maximal-shading witness and its actual shading.

All witness tubes have the same radius.  The single scalar
`(1 + 2*delta)^(-1)` sends their exact outer side vector
`(2*delta,2*delta,1+2*delta)` to `(w,w,1)`, where
`w = 2*delta/(1+2*delta)`.  Thus every member is an actual `2`-plank in one
common coordinate system.  The additional refinement costs at most one more
literal occurrence-fibre cardinality factor, and common affine transport
preserves average multiplicity exactly.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedOccurrenceMaxWitnessCommonScaleV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8SelectedOccurrenceActiveParentOwnerV7
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerAverageRetentionV3
open Family8SelectedOccurrenceMaxOwnerHullAggregateV2
open Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1
open Family8SelectedOccurrenceMaxOwnerHullFrostmanProducerV3
open Family8SelectedOccurrenceMaxOwnerHullQualityV3
open Family8SelectedOccurrenceMaxOwnerHullUniqueOwnerV2
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8UniqueOwnerLocalDeltaMaxThickControlV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-! ## Exact common normalization of one fine tube -/

def maxWitnessCommonScale (delta : NNReal) : NNReal :=
  (1 + 2 * delta)⁻¹

def maxWitnessCommonWidth (delta : NNReal) : NNReal :=
  maxWitnessCommonScale delta * (2 * delta)

theorem maxWitnessCommonScale_pos (delta : NNReal) :
    0 < maxWitnessCommonScale delta := by
  exact inv_pos.mpr (by positivity)

theorem maxWitnessCommonWidth_pos {delta : NNReal} (hdelta : 0 < delta) :
    0 < maxWitnessCommonWidth delta := by
  exact mul_pos (maxWitnessCommonScale_pos delta)
    (mul_pos (by norm_num) hdelta)

theorem maxWitnessCommonWidth_le_one (delta : NNReal) :
    maxWitnessCommonWidth delta ≤ 1 := by
  have hden : 0 < 1 + 2 * delta := by positivity
  calc
    maxWitnessCommonWidth delta = (1 + 2 * delta)⁻¹ * (2 * delta) := rfl
    _ ≤ (1 + 2 * delta)⁻¹ * (1 + 2 * delta) := by gcongr; simp
    _ = 1 := inv_mul_cancel₀ hden.ne'

def maxWitnessCommonScaleEquiv (delta : NNReal) : Space ≃ᵃ[Real] Space :=
  scalarDilationAffineEquiv (maxWitnessCommonScale delta)
    (maxWitnessCommonScale_pos delta)

def commonScaleTubeBody {delta : NNReal} (T : Tube delta) :
    ConvexBody Space :=
  affineImageConvexBody (maxWitnessCommonScaleEquiv delta) T.body

noncomputable def commonScaleTubeCertificate
    {delta : NNReal} (T : Tube delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    BoxDimensionsCertificate 2
      (plankSides (maxWitnessCommonWidth delta) (maxWitnessCommonWidth delta))
      (commonScaleTubeBody T) := by
  let cert : BoxDimensionsCertificate 2 (Tube.frameBoxSides delta) T.body :=
    Classical.choice
      (T.hasBoxDimensions_frameBoxSides hdeltaHalf).nonempty_boxDimensionsCertificate
  let cert' := scalarDilationBoxDimensionsCertificate cert
    (maxWitnessCommonScale delta) (maxWitnessCommonScale_pos delta)
  have hside :
      (fun i ↦ maxWitnessCommonScale delta * Tube.frameBoxSides delta i) =
        plankSides (maxWitnessCommonWidth delta)
          (maxWitnessCommonWidth delta) := by
    have hden : 1 + 2 * delta ≠ 0 := by positivity
    funext i
    fin_cases i <;>
      simp [maxWitnessCommonScale, maxWitnessCommonWidth,
        Tube.frameBoxSides, plankSides, hden]
  exact hside ▸ cert'

theorem commonScaleTube_isPlank
    {delta : NNReal} (T : Tube delta) (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    IsPlank 2 (maxWitnessCommonWidth delta) (maxWitnessCommonWidth delta)
      (commonScaleTubeBody T) := by
  let cert := commonScaleTubeCertificate T hdeltaHalf
  exact ⟨maxWitnessCommonWidth_pos hdelta, le_rfl,
    maxWitnessCommonWidth_le_one delta, cert.one_le, cert.box,
    cert.side_eq, cert.inner_le, cert.outer_le⟩

/-! ## Actual selected witness family and shading -/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  {P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine}

/-- The actual max-witness shading before the common affine map. -/
def selectedOccurrenceMaxWitnessShading
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    Shading (selectedOccurrenceMaxWitnessFamily C Y R) where
  carrier q := Y.carrier (occurrenceMaxShadedWitness C P Y
    (selectedOccurrencePosition C R q))
  measurable_carrier q := Y.measurable_carrier
    (occurrenceMaxShadedWitness C P Y (selectedOccurrencePosition C R q))
  carrier_subset q := Y.carrier_subset
    (occurrenceMaxShadedWitness C P Y (selectedOccurrencePosition C R q))

/-- All actual witness tubes transported by the same scalar. -/
abbrev selectedOccurrenceMaxWitnessCommonScaleFamily
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    ConvexFamily {q // q ∈ selectedOccurrenceIndices P R} :=
  affineImageFamily (maxWitnessCommonScaleEquiv delta)
    (selectedOccurrenceMaxWitnessFamily C Y R)

def selectedOccurrenceMaxWitnessCommonScaleShading
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    Shading (selectedOccurrenceMaxWitnessCommonScaleFamily C Y R) :=
  affineImageShading (maxWitnessCommonScaleEquiv delta)
    (selectedOccurrenceMaxWitnessShading C Y R)

@[simp] theorem selectedOccurrenceMaxWitnessCommonScaleFamily_apply
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    selectedOccurrenceMaxWitnessCommonScaleFamily C Y R q =
      commonScaleTubeBody (fine.tubes (occurrenceMaxShadedWitness C P Y
        (selectedOccurrencePosition C R q))) := rfl

theorem selectedOccurrenceMaxWitnessCommonScale_all_isPlank
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    IsPlank 2 (maxWitnessCommonWidth delta) (maxWitnessCommonWidth delta)
      (selectedOccurrenceMaxWitnessCommonScaleFamily C Y R q) := by
  rw [selectedOccurrenceMaxWitnessCommonScaleFamily_apply]
  exact commonScaleTube_isPlank _ hdelta hdeltaHalf

theorem selectedOccurrenceMaxWitnessCommonScale_averageMultiplicity
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    (selectedOccurrenceMaxWitnessCommonScaleShading C Y R).averageMultiplicity =
      (selectedOccurrenceMaxWitnessShading C Y R).averageMultiplicity :=
  affineImageShading_averageMultiplicity (maxWitnessCommonScaleEquiv delta)
    (selectedOccurrenceMaxWitnessShading C Y R)

/-! ## The explicit additional fibre-cardinality loss -/

theorem occurrenceMaxOwnerCarrier_volume_le_card_mul_maxWitness
    (Y : Shading fine.bodyFamily)
    (k : Fin (blocks fine.bodyFamily P).length) :
    volume (occurrenceMaxOwnerCarrier C P Y k) ≤
      (((blockAt fine.bodyFamily P k).fiber.card : Nat) : ENNReal) *
        volume (Y.carrier (occurrenceMaxShadedWitness C P Y k)) := by
  let B := (blockAt fine.bodyFamily P k).fiber
  have hsubset : occurrenceMaxOwnerCarrier C P Y k ⊆
      ⋃ i : {i // i ∈ B}, Y.carrier i.1 := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    have hiB := (mem_occurrenceMaxOwnerSubfiber C P Y k i.1).1 i.2 |>.1
    exact Set.mem_iUnion.mpr ⟨⟨i.1, hiB⟩, hxi⟩
  calc
    volume (occurrenceMaxOwnerCarrier C P Y k) ≤
        volume (⋃ i : {i // i ∈ B}, Y.carrier i.1) := measure_mono hsubset
    _ ≤ ∑ i : {i // i ∈ B}, volume (Y.carrier i.1) :=
      measure_iUnion_fintype_le volume fun i : {i // i ∈ B} ↦ Y.carrier i.1
    _ = ∑ i ∈ B, volume (Y.carrier i) := by
      symm
      exact Finset.sum_subtype _ (fun _i ↦ Iff.rfl) _
    _ ≤ B.card • volume (Y.carrier (occurrenceMaxShadedWitness C P Y k)) :=
      Finset.sum_le_card_nsmul B (fun i ↦ volume (Y.carrier i))
        (volume (Y.carrier (occurrenceMaxShadedWitness C P Y k)))
        (fun i hi ↦ occurrenceShadedVolume_le_maxWitness C P Y k i hi)
    _ = ((B.card : Nat) : ENNReal) *
        volume (Y.carrier (occurrenceMaxShadedWitness C P Y k)) := by
      simp [nsmul_eq_mul]

theorem selectedOccurrenceMaxWitnessShading_mass_eq_sum
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    (selectedOccurrenceMaxWitnessShading C Y R).shadingMass =
      ∑ k ∈ R, volume (Y.carrier (occurrenceMaxShadedWitness C P Y k)) := by
  classical
  unfold Shading.shadingMass
  calc
    (∑ q, volume ((selectedOccurrenceMaxWitnessShading C Y R).carrier q)) =
        ∑ k : {k // k ∈ R},
          volume (Y.carrier (occurrenceMaxShadedWitness C P Y k.1)) := by
      symm
      apply Fintype.sum_equiv (selectedOccurrencePositionEquiv C P R)
        (fun k : {k // k ∈ R} ↦
          volume (Y.carrier (occurrenceMaxShadedWitness C P Y k.1)))
        (fun q ↦ volume ((selectedOccurrenceMaxWitnessShading C Y R).carrier q))
      intro k
      have hpos : selectedOccurrencePosition C R
          (selectedOccurrenceIndexOf P R k.1 k.2) = k.1 :=
        Option.some.inj (some_selectedOccurrencePosition_eq C R
          (selectedOccurrenceIndexOf P R k.1 k.2))
      change volume (Y.carrier (occurrenceMaxShadedWitness C P Y k.1)) =
        volume (Y.carrier (occurrenceMaxShadedWitness C P Y
          (selectedOccurrencePosition C R
            (selectedOccurrenceIndexOf P R k.1 k.2))))
      exact congrArg (fun t ↦
        volume (Y.carrier (occurrenceMaxShadedWitness C P Y t))) hpos |>.symm
    _ = ∑ k ∈ R,
        volume (Y.carrier (occurrenceMaxShadedWitness C P Y k)) := by
      symm
      exact Finset.sum_subtype _ (fun _k ↦ Iff.rfl) _

theorem selectedOccurrenceMaxOwnerHullShading_mass_le_card_mul_maxWitness
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (M : Nat)
    (hcard : ∀ k ∈ R, (blockAt fine.bodyFamily P k).fiber.card ≤ M) :
    (selectedOccurrenceMaxOwnerHullShading C P Y R).shadingMass ≤
      (M : ENNReal) * (selectedOccurrenceMaxWitnessShading C Y R).shadingMass := by
  rw [selectedOccurrenceMaxOwnerHullShading_mass_eq_sum,
    selectedOccurrenceMaxWitnessShading_mass_eq_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  exact (occurrenceMaxOwnerCarrier_volume_le_card_mul_maxWitness C Y k).trans
    (by gcongr; exact_mod_cast hcard k hk)

theorem selectedOccurrenceMaxWitnessShading_shadedUnion_subset_maxOwner
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    (selectedOccurrenceMaxWitnessShading C Y R).shadedUnion ⊆
      (selectedOccurrenceMaxOwnerHullShading C P Y R).shadedUnion := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨q, hxq⟩
  apply Set.mem_iUnion.mpr
  refine ⟨q, ?_⟩
  exact maxWitnessCarrier_subset_occurrenceMaxOwnerCarrier C P Y
    (selectedOccurrencePosition C R q) hxq

/-- The additional one-witness refinement costs exactly one more uniform
fibre-cardinality factor at the average-multiplicity level. -/
theorem selectedOccurrenceMaxOwnerHull_average_le_card_mul_maxWitness
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (M : Nat)
    (hcard : ∀ k ∈ R, (blockAt fine.bodyFamily P k).fiber.card ≤ M) :
    (selectedOccurrenceMaxOwnerHullShading C P Y R).averageMultiplicity ≤
      (M : ENNReal) *
        (selectedOccurrenceMaxWitnessCommonScaleShading C Y R).averageMultiplicity := by
  have hmass := selectedOccurrenceMaxOwnerHullShading_mass_le_card_mul_maxWitness
    C Y R M hcard
  have hunion := selectedOccurrenceMaxWitnessShading_shadedUnion_subset_maxOwner
    C Y R
  rw [selectedOccurrenceMaxWitnessCommonScale_averageMultiplicity]
  unfold Shading.averageMultiplicity
  calc
    (selectedOccurrenceMaxOwnerHullShading C P Y R).shadingMass /
          volume (selectedOccurrenceMaxOwnerHullShading C P Y R).shadedUnion ≤
        ((M : ENNReal) *
          (selectedOccurrenceMaxWitnessShading C Y R).shadingMass) /
          volume (selectedOccurrenceMaxOwnerHullShading C P Y R).shadedUnion :=
      ENNReal.div_le_div_right hmass _
    _ ≤ ((M : ENNReal) *
          (selectedOccurrenceMaxWitnessShading C Y R).shadingMass) /
          volume (selectedOccurrenceMaxWitnessShading C Y R).shadedUnion := by
      exact ENNReal.div_le_div_left (measure_mono hunion) _
    _ = (M : ENNReal) *
        ((selectedOccurrenceMaxWitnessShading C Y R).shadingMass /
          volume (selectedOccurrenceMaxWitnessShading C Y R).shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Source average through conflict selection and both actual refinements.
The loss is the previous `M * conflictLoss` times one additional `M`. -/
theorem selectedOccurrenceOuter_average_le_card_conflict_card_mul_witness
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMaxOwnerMass C P Y R0) loss)
    (M : Nat)
    (hcard : ∀ k ∈ R0, (blockAt fine.bodyFamily P k).fiber.card ≤ M) :
    (selectedOccurrenceOuterShading P Y R0).averageMultiplicity ≤
      (((M : ENNReal) * loss) * (M : ENNReal)) *
        (selectedOccurrenceMaxWitnessCommonScaleShading C Y
          (occurrencesMaxOwnedBy C P Y R0 W.selected)).averageMultiplicity := by
  let R := occurrencesMaxOwnedBy C P Y R0 W.selected
  have hcardR : ∀ k ∈ R, (blockAt fine.bodyFamily P k).fiber.card ≤ M := by
    intro k hk
    exact hcard k ((mem_occurrencesMaxOwnedBy C P Y R0 W.selected k).1 hk).1
  exact (selectedOccurrenceOuterShading_average_le_card_mul_conflict_mul_maxOwner
    C P Y R0 M hcard loss W).trans (by
      calc
        ((M : ENNReal) * loss) *
            (selectedOccurrenceMaxOwnerHullShading C P Y R).averageMultiplicity ≤
          ((M : ENNReal) * loss) *
            ((M : ENNReal) *
              (selectedOccurrenceMaxWitnessCommonScaleShading C Y R).averageMultiplicity) := by
                gcongr
                exact selectedOccurrenceMaxOwnerHull_average_le_card_mul_maxWitness
                  C Y R M hcardR
        _ = (((M : ENNReal) * loss) * (M : ENNReal)) *
            (selectedOccurrenceMaxWitnessCommonScaleShading C Y R).averageMultiplicity := by
              ac_rfl)

/-! ## Callback-free Frostman transport and the actual plank datum -/

theorem selectedOccurrenceMaxWitnessCommonScale_isFrostmanIn
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (M : Nat)
    (hcard : ∀ k ∈ R, (blockAt fine.bodyFamily P k).fiber.card ≤ M)
    (ambient : ConvexBody Space) {CF : ENNReal}
    (hsource : IsFrostmanOn CF fine.bodyFamily
      (selectedOccurrenceFineIndices P R) ambient)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    IsFrostmanIn (CF * (16 * (M : ENNReal)))
      (selectedOccurrenceMaxWitnessCommonScaleFamily C Y R)
      (affineImageConvexBody (maxWitnessCommonScaleEquiv delta) ambient) := by
  apply IsFrostmanIn.affineImage (maxWitnessCommonScaleEquiv delta)
  exact selectedOccurrenceMaxWitness_isFrostmanIn C Y R M hcard ambient
    hsource hdeltaHalf

def selectedOccurrenceMaxWitnessCommonScaleDatum
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (ambient : ConvexBody Space) (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1
      (affineImageConvexBody (maxWitnessCommonScaleEquiv delta) ambient))
    (contained_in_ambient : ∀ q,
      (selectedOccurrenceMaxWitnessFamily C Y R q : Set Space) ⊆
        (ambient : Set Space)) :
    ShadedConvexPlankFamily {q // q ∈ selectedOccurrenceIndices P R}
      (maxWitnessCommonWidth delta) (maxWitnessCommonWidth delta) where
  family := selectedOccurrenceMaxWitnessCommonScaleFamily C Y R
  shading := selectedOccurrenceMaxWitnessCommonScaleShading C Y R
  comparisonConstant := 2
  all_isPlank := selectedOccurrenceMaxWitnessCommonScale_all_isPlank
    C Y R hdelta hdeltaHalf
  ambient := affineImageConvexBody (maxWitnessCommonScaleEquiv delta) ambient
  ambientComparisonConstant := ambientComparisonConstant
  ambient_is_unit_scale := ambient_is_unit_scale
  contained_in_ambient q := Set.image_mono (contained_in_ambient q)

#print axioms commonScaleTubeCertificate
#print axioms commonScaleTube_isPlank
#print axioms selectedOccurrenceMaxWitnessCommonScale_all_isPlank
#print axioms occurrenceMaxOwnerCarrier_volume_le_card_mul_maxWitness
#print axioms selectedOccurrenceMaxOwnerHull_average_le_card_mul_maxWitness
#print axioms selectedOccurrenceOuter_average_le_card_conflict_card_mul_witness
#print axioms selectedOccurrenceMaxWitnessCommonScale_isFrostmanIn
#print axioms selectedOccurrenceMaxWitnessCommonScaleDatum

end
end Family8SelectedOccurrenceMaxWitnessCommonScaleV1
