import Family8Grounding.Family8SelectedOccurrenceNormalizedOuterDatumV1
import Family8Grounding.Family8OwnerFiberKatzTaoFromAmbientFrostmanV2
import Family8Grounding.Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
import FamilyStickyGrounding.Family6AffineKatzTaoTransportV3
import Submission.Kakeya.ConvexFactoring.GreedyLateTailRestart
import Mathlib.Tactic

/-!
# Direct source Katz--Tao control for the selected occurrence outer family

A lower mass density on every retained greedy block converts source
Katz--Tao control directly into Katz--Tao control on the exact selected
occurrence outer family.  The coefficient is exactly `sourceKT * d⁻¹`:
there is no ambient-density normalization and no retained-cardinality loss.

The same coefficient survives the common affine normalization.  A constant
`Unit` owner then turns this global estimate into the Family 6 thick-plank
control used in Equation (45), without a geometric owner-containment premise.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceDirectSourceKatzTaoEq45ControlV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.GreedyLateTailRestart
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family6AffineKatzTaoTransportV3
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8OwnerFiberKatzTaoFromAmbientFrostmanV2
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceNormalizedOuterDatumV1
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8UniqueOwnerLocalDeltaMaxThickControlV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u v

/-! ## Direct source-to-occurrence Katz--Tao transport -/

/-- A common lower block density transfers global source Katz--Tao control
to the literal retained occurrence positions with the exact reciprocal
density loss. -/
theorem occurrenceFamily_isKatzTaoOn_of_sourceKatzTao_and_blockMass_lower
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota} {kappa : Type v}
    {candidates : Finset kappa} {container : kappa -> ConvexBody Space}
    {active : Finset iota}
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length))
    (sourceKT d : ENNReal)
    (hKT : IsKatzTao sourceKT F)
    (hblockMassLower : forall k, k ∈ R ->
      d * volume ((blockAt F P k).body : Set Space) <=
        blockMass F (blockAt F P k))
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞) :
    IsKatzTaoOn (sourceKT * d⁻¹) (occurrenceFamily F P) R := by
  intro K
  rw [containedMassOn_occurrenceFamily_eq F P R K]
  have hcross :
      (∑ k ∈ containedOccurrences F P R K,
          volume ((blockAt F P k).body : Set Space)) * d <=
        sourceKT * volume (K : Set Space) := by
    calc
      (∑ k ∈ containedOccurrences F P R K,
          volume ((blockAt F P k).body : Set Space)) * d =
          ∑ k ∈ containedOccurrences F P R K,
            d * volume ((blockAt F P k).body : Set Space) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _hk
        ac_rfl
      _ <= ∑ k ∈ containedOccurrences F P R K,
          blockMass F (blockAt F P k) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hblockMassLower k
          ((mem_containedOccurrences F P R K k).mp hk).1
      _ <= massInside F active K :=
        sum_blockMass_le_activeMassInside F P R K
      _ = containedMassOn F active K :=
        massInside_eq_containedMassOn F active K
      _ <= sourceKT * volume (K : Set Space) := hKT.on active K
  rw [show (sourceKT * d⁻¹) * volume (K : Set Space) =
      (sourceKT * volume (K : Set Space)) / d by
    simp only [div_eq_mul_inv]
    ac_rfl]
  exact (ENNReal.le_div_iff_mul_le
    (Or.inl hd0) (Or.inl hdTop)).2 hcross

/-- The exact selected outer subtype inherits the preceding occurrence
estimate.  The `Option.some` reindexing is injective and introduces no loss. -/
theorem selectedOccurrenceOuterFamily_isKatzTao_of_sourceKatzTao_and_blockMass_lower
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota} {kappa : Type v}
    {candidates : Finset kappa} {container : kappa -> ConvexBody Space}
    {active : Finset iota}
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length))
    (sourceKT d : ENNReal)
    (hKT : IsKatzTao sourceKT F)
    (hblockMassLower : forall k, k ∈ R ->
      d * volume ((blockAt F P k).body : Set Space) <=
        blockMass F (blockAt F P k))
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞) :
    IsKatzTao (sourceKT * d⁻¹)
      (selectedOccurrenceOuterFamily P R) := by
  let e : Fin (blocks F P).length ↪
      Option (Fin (blocks F P).length) :=
    ⟨some, fun _ _ h => Option.some.inj h⟩
  have hocc : IsKatzTaoOn (sourceKT * d⁻¹)
      (occurrenceFamily F P) R :=
    occurrenceFamily_isKatzTaoOn_of_sourceKatzTao_and_blockMass_lower
      P R sourceKT d hKT hblockMassLower hd0 hdTop
  have hmapped : IsKatzTaoOn (sourceKT * d⁻¹)
      (coarseFamily F P) (R.map e) := by
    apply isKatzTaoOn_map_embedding e (coarseFamily F P) R
    change IsKatzTaoOn (sourceKT * d⁻¹)
      (fun k => coarseFamily F P (some k)) R
    exact hocc
  have hselected : R.map e = selectedOccurrenceIndices P R := by
    ext q
    simp only [e, selectedOccurrenceIndices, Finset.mem_map,
      Finset.mem_image]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, rfl⟩
  apply isKatzTao_selectedCoarseFamily_of_isKatzTaoOn
  simpa only [hselected] using hmapped

/-! ## Affine normalization and constant-owner Equation (45) -/

/-- The exact direct coefficient is unchanged by the common outer affine
normalization. -/
theorem selectedOccurrenceNormalizedOuterFamily_isKatzTao_of_sourceKatzTao_and_blockMass_lower
    {delta : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota} {active : Finset iota}
    (P : GreedyDensityPartition fine.bodyFamily
      (hullCandidates active) (hullContainer fine.bodyFamily) active)
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (sourceKT d : ENNReal)
    (hKT : IsKatzTao sourceKT fine.bodyFamily)
    (hblockMassLower : forall k, k ∈ Rside ->
      d * volume ((blockAt fine.bodyFamily P k).body : Set Space) <=
        blockMass fine.bodyFamily (blockAt fine.bodyFamily P k))
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞) :
    IsKatzTao (sourceKT * d⁻¹)
      (selectedOccurrenceNormalizedOuterFamily P labelOuter Rside) := by
  exact isKatzTao_affineImageFamily
    (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter)
    (selectedOccurrenceOuterFamily P Rside)
    (selectedOccurrenceOuterFamily_isKatzTao_of_sourceKatzTao_and_blockMass_lower
      P Rside sourceKT d hKT hblockMassLower hd0 hdTop)

/-- Any global Katz--Tao estimate gives the honest Family 6 thick-count
certificate through the constant `Unit` owner. -/
theorem frostmanThickenedPlankControl_of_globalKatzTao
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b Delta : NNReal}
    (D : ShadedConvexPlankFamily index a b)
    (hKT : IsKatzTao (Delta : ENNReal) D.family) :
    FrostmanThickenedPlankControl D
      (uniqueOwnerLocalDeltaThickM
        D.comparisonConstant Delta a b) := by
  let owner : index -> Unit := fun _ => ()
  have hownerDelta : ownerFiberDeltaMax D owner <=
      (Delta : ENNReal) := by
    unfold ownerFiberDeltaMax
    apply iSup_le
    intro p
    exact
      Family6PlankKatzTaoFrostmanActualAdaptersV1.isKatzTao_iff_maximalConcentration_le.mp
        (isKatzTao_ownerFiberFamily_of_global D owner hKT p)
  apply frostmanThickenedPlankControl_of_uniqueOwner_localDeltaMax
    D owner
  · intro _theta _hthetaLower _hthetaUpper _i _j _hj
    rfl
  · exact hownerDelta

/-- The finite `NNReal` representative of the exact direct coefficient. -/
def selectedOccurrenceDirectSourceKatzTaoDelta
    (sourceKT d : ENNReal) : NNReal :=
  (sourceKT * d⁻¹).toNNReal

theorem selectedOccurrenceDirectSourceKatzTaoDelta_coe
    (sourceKT d : ENNReal) (hsourceKTTop : sourceKT ≠ ∞)
    (hd0 : d ≠ 0) :
    (selectedOccurrenceDirectSourceKatzTaoDelta sourceKT d : ENNReal) =
      sourceKT * d⁻¹ := by
  unfold selectedOccurrenceDirectSourceKatzTaoDelta
  rw [ENNReal.coe_toNNReal]
  exact ENNReal.mul_ne_top hsourceKTTop (ENNReal.inv_ne_top.mpr hd0)

/-- Exact selected-occurrence specialization of the direct route.  The
ambient hypotheses occur only in the normalized datum constructor; the
Eq. (45) coefficient itself is the source Katz--Tao constant divided by the
actual common block-density lower bound. -/
theorem selectedOccurrenceNormalizedOuter_frostmanThickenedPlankControl_of_sourceKatzTao
    {delta : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota} {active : Finset iota}
    (P : GreedyDensityPartition fine.bodyFamily
      (hullCandidates active) (hullContainer fine.bodyFamily) active)
    (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta)
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (hlabel : forall k, k ∈ Rside ->
      sideShapeLabel (winnerLongSide P hdelta k) = labelOuter)
    (ambient : ConvexBody Space)
    (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1
      (affineImageConvexBody
        (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter) ambient))
    (contained_in_ambient : forall q,
      (selectedOccurrenceOuterFamily P Rside q : Set Space) ⊆
        (ambient : Set Space))
    (sourceKT d : ENNReal)
    (hKT : IsKatzTao sourceKT fine.bodyFamily)
    (hsourceKTTop : sourceKT ≠ ∞)
    (hblockMassLower : forall k, k ∈ Rside ->
      d * volume ((blockAt fine.bodyFamily P k).body : Set Space) <=
        blockMass fine.bodyFamily (blockAt fine.bodyFamily P k))
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞) :
    FrostmanThickenedPlankControl
      (selectedOccurrenceNormalizedOuterDatum P Y hdelta labelOuter Rside
        hlabel ambient ambientComparisonConstant ambient_is_unit_scale
        contained_in_ambient)
      (uniqueOwnerLocalDeltaThickM 576
        (selectedOccurrenceDirectSourceKatzTaoDelta sourceKT d)
        (bucketShortA labelOuter) (bucketShortB labelOuter)) := by
  let Delta := selectedOccurrenceDirectSourceKatzTaoDelta sourceKT d
  let D := selectedOccurrenceNormalizedOuterDatum P Y hdelta labelOuter Rside
    hlabel ambient ambientComparisonConstant ambient_is_unit_scale
    contained_in_ambient
  have hnormalized : IsKatzTao (sourceKT * d⁻¹)
      (selectedOccurrenceNormalizedOuterFamily P labelOuter Rside) :=
    selectedOccurrenceNormalizedOuterFamily_isKatzTao_of_sourceKatzTao_and_blockMass_lower
      P labelOuter Rside sourceKT d hKT hblockMassLower hd0 hdTop
  have hnormalizedDelta : IsKatzTao (Delta : ENNReal)
      (selectedOccurrenceNormalizedOuterFamily P labelOuter Rside) := by
    rw [selectedOccurrenceDirectSourceKatzTaoDelta_coe
      sourceKT d hsourceKTTop hd0]
    exact hnormalized
  simpa only [D, Delta, selectedOccurrenceNormalizedOuterDatum] using
    (frostmanThickenedPlankControl_of_globalKatzTao D hnormalizedDelta)

#print axioms
  occurrenceFamily_isKatzTaoOn_of_sourceKatzTao_and_blockMass_lower
#print axioms
  selectedOccurrenceOuterFamily_isKatzTao_of_sourceKatzTao_and_blockMass_lower
#print axioms
  selectedOccurrenceNormalizedOuterFamily_isKatzTao_of_sourceKatzTao_and_blockMass_lower
#print axioms frostmanThickenedPlankControl_of_globalKatzTao
#print axioms
  selectedOccurrenceNormalizedOuter_frostmanThickenedPlankControl_of_sourceKatzTao

end

end Family8SelectedOccurrenceDirectSourceKatzTaoEq45ControlV1
