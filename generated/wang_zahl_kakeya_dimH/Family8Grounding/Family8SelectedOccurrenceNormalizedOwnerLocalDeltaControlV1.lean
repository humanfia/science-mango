import Family8Grounding.Family8SameSelectedQFibreCrossingValueTransportV1
import Family8Grounding.Family8SelectedOccurrenceActiveParentOwnerV9
import Family8Grounding.Family8SelectedOccurrenceNormalizedOuterDatumV1
import Mathlib.Tactic

/-!
# Direct owner/local-Delta control on the normalized selected outer datum

The raw winning hulls do not need to be packaged as an `IsPlank` family.
Instead, containment in a normalized closed thickening is pulled back through
the one positive scalar dilation used by the normalized datum.  Unique
ownership is then checked on the literal raw winning bodies, while local
maximal concentration is transported exactly by affine invariance.

No occurrence is selected or removed in this file.  The index type, owner,
and local `Delta` are unchanged, and the resulting comparison constant is the
actual normalized constant `576`.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedOccurrenceNormalizedOwnerLocalDeltaControlV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8DoubledParentConflictClusteringV2.ScaleCover
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8GreedyWinnerNormalizedPlankBucketV1
open Family8SameSelectedQFibreCrossingValueTransportV1
open Family8SelectedOccurrenceActiveParentOwnerV5
open Family8SelectedOccurrenceActiveParentOwnerV7
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceNormalizedOuterDatumV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8UniqueOwnerLocalDeltaMaxThickControlV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe v

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {active : Finset iota}

variable
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates active) (hullContainer fine.bodyFamily) active)

/-! ## Closed thickenings under the normalization scalar -/

/-- Pull a closed-thickening containment back through a positive scalar
dilation.  This is kept local to the normalized-outer route, so it does not
import any max-witness datum. -/
theorem normalizedOuter_scalarDilation_preimage_cthickening_subset
    {s r : NNReal} (hs : 0 < s) {A B : Set Space} (hB : IsCompact B)
    (h : scalarDilationAffineEquiv s hs '' A ⊆
      Metric.cthickening (r : Real)
        (scalarDilationAffineEquiv s hs '' B)) :
    A ⊆ Metric.cthickening (((r / s : NNReal) : Real)) B := by
  let d := scalarDilationAffineEquiv s hs
  intro x hx
  have hdx : d x ∈ Metric.cthickening (r : Real) (d '' B) :=
    h ⟨x, hx, rfl⟩
  have hdCompact : IsCompact (d '' B) :=
    hB.image d.continuous_of_finiteDimensional
  rw [hdCompact.cthickening_eq_biUnion_closedBall (by positivity)] at hdx
  simp only [mem_iUnion, Metric.mem_closedBall] at hdx
  obtain ⟨y, hyImage, hdist⟩ := hdx
  obtain ⟨z, hz, rfl⟩ := hyImage
  apply Metric.mem_cthickening_of_dist_le x z
    (((r / s : NNReal) : Real)) B hz
  have hsReal : (0 : Real) < (s : Real) := by exact_mod_cast hs
  have hscaled : (s : Real) * dist x z ≤ (r : Real) := by
    simpa only [d, scalarDilationAffineEquiv_apply, dist_smul₀,
      Real.norm_eq_abs, abs_of_pos hsReal] using hdist
  rw [NNReal.coe_div]
  exact (le_div_iff₀ hsReal).2 (by simpa [mul_comm] using hscaled)

/-! ## The two exact raw-family premises -/

/-- The literal raw owner fibre, without any raw `IsPlank` packaging. -/
abbrev selectedOccurrenceRawOwnerFiberFamily
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    {ownerIndex : Type v} [DecidableEq ownerIndex]
    (owner : {q // q ∈ selectedOccurrenceIndices P Rside} → ownerIndex)
    (p : ownerIndex) :
    ConvexFamily
      {q // q ∈ ownerFiberIndices owner p} :=
  selectedCoarseFamily (selectedOccurrenceOuterFamily P Rside)
    (ownerFiberIndices owner p)

/-- The weakest owner premise seen after pulling a normalized thickening back
through the scalar dilation.  It mentions the raw family but no raw plank
datum or raw comparison constant. -/
def NormalizedOuterPullbackUniqueOwner
    (labelOuter : Fin 3 → Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    {ownerIndex : Type v} [DecidableEq ownerIndex]
    (owner : {q // q ∈ selectedOccurrenceIndices P Rside} → ownerIndex) :
    Prop :=
  ∀ theta : NNReal,
    bucketShortA labelOuter / bucketShortB labelOuter ≤ theta →
    theta ≤ 1 →
    ∀ i j,
      (selectedOccurrenceOuterFamily P Rside j : Set Space) ⊆
          Metric.cthickening
            (((theta * bucketShortB labelOuter /
              (sideShapeUpper labelOuter 2)⁻¹ : NNReal) : Real))
            (selectedOccurrenceOuterFamily P Rside i : Set Space) →
        owner j = owner i

/-! ## Direct transport to the normalized datum -/

/-- Pullback uniqueness gives unique ownership on the actual normalized
selected-occurrence datum. -/
theorem thickenedPlankUniqueOwner_normalizedOuter_of_pullback
    (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta)
    (labelOuter : Fin 3 → Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (hlabel : ∀ k, k ∈ Rside →
      sideShapeLabel (winnerLongSide P hdelta k) = labelOuter)
    (ambient : ConvexBody Space)
    (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1
      (affineImageConvexBody
        (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter) ambient))
    (contained_in_ambient : ∀ q,
      (selectedOccurrenceOuterFamily P Rside q : Set Space) ⊆
        (ambient : Set Space))
    {ownerIndex : Type v} [DecidableEq ownerIndex]
    (owner : {q // q ∈ selectedOccurrenceIndices P Rside} → ownerIndex)
    (hpullback : NormalizedOuterPullbackUniqueOwner
      P labelOuter Rside owner) :
    ThickenedPlankUniqueOwner
      (selectedOccurrenceNormalizedOuterDatum P Y hdelta labelOuter Rside
        hlabel ambient ambientComparisonConstant ambient_is_unit_scale
        contained_in_ambient)
      owner := by
  intro theta hthetaLower hthetaUpper i j hj
  have hjContainedDatum :
      ((selectedOccurrenceNormalizedOuterDatum P Y hdelta labelOuter Rside
          hlabel ambient ambientComparisonConstant ambient_is_unit_scale
          contained_in_ambient).family j : Set Space) ⊆
        Metric.cthickening
          (((theta * bucketShortB labelOuter : NNReal) : Real))
          ((selectedOccurrenceNormalizedOuterDatum P Y hdelta labelOuter Rside
            hlabel ambient ambientComparisonConstant ambient_is_unit_scale
            contained_in_ambient).family i : Set Space) := by
    simpa [thickenedPlankIndices,
      Family6AffinePlankAnalyticHypothesesStableV1.containedIndices] using
        (Finset.mem_filter.mp hj).2
  have hjContained :
      (selectedOccurrenceNormalizedOuterFamily P labelOuter Rside j :
          Set Space) ⊆
        Metric.cthickening
          (((theta * bucketShortB labelOuter : NNReal) : Real))
          (selectedOccurrenceNormalizedOuterFamily P labelOuter Rside i :
            Set Space) := by
    exact hjContainedDatum
  have himage :
      scalarDilationAffineEquiv (sideShapeUpper labelOuter 2)⁻¹
          (inv_pos.mpr (sideShapeUpper_pos labelOuter 2)) ''
            (selectedOccurrenceOuterFamily P Rside j : Set Space) ⊆
        Metric.cthickening
          (((theta * bucketShortB labelOuter : NNReal) : Real))
          (scalarDilationAffineEquiv (sideShapeUpper labelOuter 2)⁻¹
            (inv_pos.mpr (sideShapeUpper_pos labelOuter 2)) ''
              (selectedOccurrenceOuterFamily P Rside i : Set Space)) := by
    simpa only [selectedOccurrenceNormalizedOuterFamily,
      selectedOccurrenceNormalizedOuterAffineEquiv,
      affineImageFamily_apply, coe_affineImageConvexBody] using hjContained
  have hpulled :=
    normalizedOuter_scalarDilation_preimage_cthickening_subset
        (s := (sideShapeUpper labelOuter 2)⁻¹)
        (r := theta * bucketShortB labelOuter)
        (inv_pos.mpr (sideShapeUpper_pos labelOuter 2))
        (selectedOccurrenceOuterFamily P Rside i).isCompact himage
  exact hpullback theta hthetaLower hthetaUpper i j hpulled

/-- Affine invariance of maximal concentration transports the literal raw
owner-fibre `Delta` bound to the normalized datum. -/
theorem ownerFiberDeltaMax_normalizedOuter_le_of_raw
    (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta)
    (labelOuter : Fin 3 → Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (hlabel : ∀ k, k ∈ Rside →
      sideShapeLabel (winnerLongSide P hdelta k) = labelOuter)
    (ambient : ConvexBody Space)
    (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1
      (affineImageConvexBody
        (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter) ambient))
    (contained_in_ambient : ∀ q,
      (selectedOccurrenceOuterFamily P Rside q : Set Space) ⊆
        (ambient : Set Space))
    {ownerIndex : Type v} [DecidableEq ownerIndex]
    (owner : {q // q ∈ selectedOccurrenceIndices P Rside} → ownerIndex)
    {Delta : NNReal}
    (hDelta : ∀ p,
      maximalConcentration
        (selectedOccurrenceRawOwnerFiberFamily P Rside owner p) ≤
          (Delta : ENNReal)) :
    ownerFiberDeltaMax
      (selectedOccurrenceNormalizedOuterDatum P Y hdelta labelOuter Rside
        hlabel ambient ambientComparisonConstant ambient_is_unit_scale
        contained_in_ambient)
      owner ≤ (Delta : ENNReal) := by
  unfold ownerFiberDeltaMax
  apply iSup_le
  intro p
  change maximalConcentration
      (affineImageFamily
        (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter)
        (selectedOccurrenceRawOwnerFiberFamily P Rside owner p)) ≤
      (Delta : ENNReal)
  calc
    maximalConcentration
        (affineImageFamily
          (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter)
          (selectedOccurrenceRawOwnerFiberFamily P Rside owner p)) =
      maximalConcentration
        (selectedOccurrenceRawOwnerFiberFamily P Rside owner p) :=
      maximalConcentration_affineImageFamily
          (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter)
          (selectedOccurrenceRawOwnerFiberFamily P Rside owner p)
    _ ≤ (Delta : ENNReal) := hDelta p

/-- The direct normalized Eq. (45) control theorem.  Its only owner premise
is the exact inverse-dilation pullback statement, and its only local-density
premise is maximal concentration on the literal raw owner fibres. -/
theorem frostmanThickenedPlankControl_normalizedOuter_of_pullbackOwnerLocalDelta
    (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta)
    (labelOuter : Fin 3 → Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (hlabel : ∀ k, k ∈ Rside →
      sideShapeLabel (winnerLongSide P hdelta k) = labelOuter)
    (ambient : ConvexBody Space)
    (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1
      (affineImageConvexBody
        (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter) ambient))
    (contained_in_ambient : ∀ q,
      (selectedOccurrenceOuterFamily P Rside q : Set Space) ⊆
        (ambient : Set Space))
    {ownerIndex : Type v} [DecidableEq ownerIndex]
    (owner : {q // q ∈ selectedOccurrenceIndices P Rside} → ownerIndex)
    (hpullback : NormalizedOuterPullbackUniqueOwner
      P labelOuter Rside owner)
    {Delta : NNReal}
    (hDelta : ∀ p,
      maximalConcentration
        (selectedOccurrenceRawOwnerFiberFamily P Rside owner p) ≤
          (Delta : ENNReal)) :
    FrostmanThickenedPlankControl
      (selectedOccurrenceNormalizedOuterDatum P Y hdelta labelOuter Rside
        hlabel ambient ambientComparisonConstant ambient_is_unit_scale
        contained_in_ambient)
      (uniqueOwnerLocalDeltaThickM 576 Delta
        (bucketShortA labelOuter) (bucketShortB labelOuter)) := by
  apply frostmanThickenedPlankControl_of_uniqueOwner_localDeltaMax
    (selectedOccurrenceNormalizedOuterDatum P Y hdelta labelOuter Rside
      hlabel ambient ambientComparisonConstant ambient_is_unit_scale
      contained_in_ambient)
    owner
  · exact thickenedPlankUniqueOwner_normalizedOuter_of_pullback
      P Y hdelta labelOuter Rside hlabel ambient ambientComparisonConstant
      ambient_is_unit_scale contained_in_ambient owner hpullback
  · exact ownerFiberDeltaMax_normalizedOuter_le_of_raw
      P Y hdelta labelOuter Rside hlabel ambient ambientComparisonConstant
      ambient_is_unit_scale contained_in_ambient owner hDelta

/-! ## Actual active-parent producer -/

variable {rho : NNReal}
  (C : StickyScaleCover fine rho)
  {Pactive : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine}

/-- The exact geometric premise left after inverse normalization: each raw
winner thickened by the pulled-back normalized radius stays in its actual
doubled sticky parent. -/
def NormalizedOuterPullbackThickeningInsideActiveParent
    (labelOuter : Fin 3 → Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily Pactive).length)) : Prop :=
  ∀ theta : NNReal,
    bucketShortA labelOuter / bucketShortB labelOuter ≤ theta →
    theta ≤ 1 →
    ∀ q,
      Metric.cthickening
          (((theta * bucketShortB labelOuter /
            (sideShapeUpper labelOuter 2)⁻¹ : NNReal) : Real))
          (selectedOccurrenceOuterFamily Pactive Rside q : Set Space) ⊆
        twoFoldTubeCarrier
          (C.coarse.tubes (selectedOccurrenceActiveParent C Rside q))

/-- Conflict-free actual parents turn the exact pulled-back body inclusion
into the owner premise needed by the normalized datum. -/
theorem normalizedOuterPullbackUniqueOwner_of_actualSelectedParents
    (hpure : ParentPure C Pactive)
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily Pactive).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMassByActiveParent C Pactive Y R0) loss)
    (Rside : Finset (Fin (blocks fine.bodyFamily Pactive).length))
    (hRside : ∀ k, k ∈ Rside →
      occurrenceActiveParent C Pactive k ∈ W.selected)
    (labelOuter : Fin 3 → Int)
    (hinside : NormalizedOuterPullbackThickeningInsideActiveParent
      C labelOuter Rside) :
    NormalizedOuterPullbackUniqueOwner Pactive labelOuter Rside
      (selectedOccurrenceActiveParent C Rside) := by
  intro theta hthetaLower hthetaUpper i j hjContained
  by_contra hne
  have hiOwner : selectedOccurrenceActiveParent C Rside i ∈ W.selected :=
    hRside _ (selectedOccurrencePosition_mem C Rside i)
  have hjOwner : selectedOccurrenceActiveParent C Rside j ∈ W.selected :=
    hRside _ (selectedOccurrencePosition_mem C Rside j)
  let witness := occurrenceFineWitness C Pactive
    (selectedOccurrencePosition C Rside j)
  have hwitnessMem : witness ∈
      (blockAt fine.bodyFamily Pactive
        (selectedOccurrencePosition C Rside j)).fiber :=
    occurrenceFineWitness_mem C Pactive _
  have hwitnessActive : witness ∈ C.activeFine :=
    occurrenceFineWitness_mem_active C Pactive _
  have hwitnessBody : (fine.tubes witness).carrier ⊆
      (selectedOccurrenceOuterFamily Pactive Rside j : Set Space) :=
    selectedOccurrenceFineWitness_carrier_subset_body C Rside j
  have hiDouble : (fine.tubes witness).carrier ⊆
      twoFoldTubeCarrier
        (C.coarse.tubes (selectedOccurrenceActiveParent C Rside i)) :=
    hwitnessBody.trans (hjContained.trans
      (hinside theta hthetaLower hthetaUpper i))
  have hwitnessParent : C.parent witness =
      selectedOccurrenceActiveParent C Rside j :=
    parent_eq_selectedOccurrenceActiveParent_of_mem C hpure Rside j witness
      hwitnessMem
  have hjParent : (fine.tubes witness).carrier ⊆
      (C.coarse.tubes (selectedOccurrenceActiveParent C Rside j)).carrier := by
    have hparent := C.carrier_subset witness hwitnessActive
    rw [hwitnessParent] at hparent
    exact hparent
  have hjDouble : (fine.tubes witness).carrier ⊆
      twoFoldTubeCarrier
        (C.coarse.tubes (selectedOccurrenceActiveParent C Rside j)) :=
    hjParent.trans (carrier_subset_twoFoldTubeCarrier
      (C.coarse.tubes (selectedOccurrenceActiveParent C Rside j)))
  exact W.selected_pairwise hiOwner hjOwner (fun h => hne h.symm)
    ⟨witness, hwitnessActive, hiDouble, hjDouble⟩

/-- The main actual-parent entry point.  It constructs neither a raw plank
datum nor a raw thick-control certificate. -/
theorem frostmanThickenedPlankControl_normalizedOuter_actualSelectedParents
    (hpure : ParentPure C Pactive)
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily Pactive).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMassByActiveParent C Pactive Y R0) loss)
    (Rside : Finset (Fin (blocks fine.bodyFamily Pactive).length))
    (hRside : ∀ k, k ∈ Rside →
      occurrenceActiveParent C Pactive k ∈ W.selected)
    (hdelta : 0 < delta)
    (labelOuter : Fin 3 → Int)
    (hlabel : ∀ k, k ∈ Rside →
      sideShapeLabel (winnerLongSide Pactive hdelta k) = labelOuter)
    (ambient : ConvexBody Space)
    (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1
      (affineImageConvexBody
        (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter) ambient))
    (contained_in_ambient : ∀ q,
      (selectedOccurrenceOuterFamily Pactive Rside q : Set Space) ⊆
        (ambient : Set Space))
    (hinside : NormalizedOuterPullbackThickeningInsideActiveParent
      C labelOuter Rside)
    {Delta : NNReal}
    (hDelta : ∀ p : Fin C.coarseCard,
      maximalConcentration
        (selectedOccurrenceRawOwnerFiberFamily Pactive Rside
          (selectedOccurrenceActiveParent C Rside) p) ≤
        (Delta : ENNReal)) :
    FrostmanThickenedPlankControl
      (selectedOccurrenceNormalizedOuterDatum Pactive Y hdelta labelOuter
        Rside hlabel ambient ambientComparisonConstant ambient_is_unit_scale
        contained_in_ambient)
      (uniqueOwnerLocalDeltaThickM 576 Delta
        (bucketShortA labelOuter) (bucketShortB labelOuter)) := by
  apply frostmanThickenedPlankControl_normalizedOuter_of_pullbackOwnerLocalDelta
    Pactive Y hdelta labelOuter Rside hlabel ambient ambientComparisonConstant
      ambient_is_unit_scale contained_in_ambient
      (selectedOccurrenceActiveParent C Rside)
  · exact normalizedOuterPullbackUniqueOwner_of_actualSelectedParents
      C hpure Y R0 loss W Rside hRside labelOuter hinside
  · exact hDelta

#print axioms thickenedPlankUniqueOwner_normalizedOuter_of_pullback
#print axioms normalizedOuter_scalarDilation_preimage_cthickening_subset
#print axioms ownerFiberDeltaMax_normalizedOuter_le_of_raw
#print axioms
  frostmanThickenedPlankControl_normalizedOuter_of_pullbackOwnerLocalDelta
#print axioms normalizedOuterPullbackUniqueOwner_of_actualSelectedParents
#print axioms
  frostmanThickenedPlankControl_normalizedOuter_actualSelectedParents

end

end Family8SelectedOccurrenceNormalizedOwnerLocalDeltaControlV1
