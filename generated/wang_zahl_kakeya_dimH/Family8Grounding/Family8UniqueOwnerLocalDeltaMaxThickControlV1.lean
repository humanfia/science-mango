import Family8Grounding.Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
import Submission.Kakeya.ConvexFactoring.JointTubeFactoring
import Family6Grounding.Family6AffinePlankAnalyticHypothesesStableV1
import FamilyStickyGrounding.FamilyStickyAdjacentTestBodyGeometryV1
import FamilyStickyGrounding.FamilyStickyConvexClosedThickeningBoxGrowthV1
import Mathlib.Tactic

/-!
# Thick-plank control from a unique owner and actual local Delta-max

This file formalizes the counting mechanism used before Equation (45).
Every plank receives an owner.  If every plank contained in the relevant
closed thickening has the same owner as the central plank, the count reduces
to that one owner fibre.  Its *actual* `maximalConcentration`, together with
the certified plank volume lower bound and an explicitly proved thickening
volume upper bound, gives the desired cardinal estimate.

The constants are intentionally honest.  With the current `IsPlank C a b`
API the direct estimate is

`card <= 27 * C^3 * Delta * (b/a) * theta`.

Thus the exact stable-family input `M = b/a` follows when the scalar
comparison loss satisfies `27 * C^3 * Delta <= 1`.  Without an absorption or
renormalization of this fixed comparison loss, the library cannot erase it
definitionally.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8UniqueOwnerLocalDeltaMaxThickControlV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6PlankKatzTaoFrostmanActualAdaptersV1
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open FamilyStickyAdjacentTestBodyGeometryV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

universe u v

variable {index : Type u} [Fintype index] [DecidableEq index]
  {ownerIndex : Type v} [DecidableEq ownerIndex]
  {a b : NNReal} {D : ShadedConvexPlankFamily index a b}

/-- The literal finite fibre of one owner. -/
def ownerFiberIndices (owner : index -> ownerIndex) (p : ownerIndex) :
    Finset index :=
  Finset.univ.filter fun i => owner i = p

omit [DecidableEq index] in
@[simp] theorem mem_ownerFiberIndices
    (owner : index -> ownerIndex) (p : ownerIndex) (i : index) :
    i ∈ ownerFiberIndices owner p ↔ owner i = p := by
  simp [ownerFiberIndices]

/-- The actual convex subfamily belonging to one owner. -/
abbrev ownerFiberFamily
    (D : ShadedConvexPlankFamily index a b)
    (owner : index -> ownerIndex) (p : ownerIndex) :
    ConvexFamily {i // i ∈ ownerFiberIndices owner p} :=
  selectedCoarseFamily D.family (ownerFiberIndices owner p)

/-- The actual worst local `Delta_max`, defined from the genuine owner-fibre
convex families. -/
def ownerFiberDeltaMax
    (D : ShadedConvexPlankFamily index a b)
    (owner : index -> ownerIndex) : ENNReal :=
  ⨆ p : ownerIndex, maximalConcentration (ownerFiberFamily D owner p)

/-- Every genuine local concentration is bounded by the actual owner-fibre
`Delta_max`. -/
theorem maximalConcentration_ownerFiber_le_ownerFiberDeltaMax
    (D : ShadedConvexPlankFamily index a b)
    (owner : index -> ownerIndex) (p : ownerIndex) :
    maximalConcentration (ownerFiberFamily D owner p) ≤
      ownerFiberDeltaMax D owner := by
  exact le_iSup
    (fun q : ownerIndex =>
      maximalConcentration (ownerFiberFamily D owner q)) p

/-- Paper's unique-parent input in the precise form used by the count: every
member contained in an admissible thickening of `i` has the same owner as
`i`. -/
def ThickenedPlankUniqueOwner
    (D : ShadedConvexPlankFamily index a b)
    (owner : index -> ownerIndex) : Prop :=
  ∀ theta : NNReal, a / b ≤ theta -> theta ≤ 1 ->
    ∀ i j : index, j ∈ thickenedPlankIndices D theta i ->
      owner j = owner i

/-! ## Certified geometry of one thickened plank -/

/-- A certified `a x b x 1` plank has closed `theta*b` thickening volume at
most `27 * theta * b^2` on the admissible theta range.  This is proved from
the actual outer witness box of `IsPlank`; it is not a volume callback. -/
theorem IsPlank.volume_theta_mul_b_closedThickening_le
    {C a b theta : NNReal} {K : ConvexBody Space}
    (h : IsPlank C a b K) (hthetaLower : a / b ≤ theta)
    (hthetaUpper : theta ≤ 1) :
    volume (Metric.cthickening (((theta * b : NNReal) : Real))
      (K : Set Space)) ≤
        27 * (theta : ENNReal) * (b : ENNReal) ^ 2 := by
  rcases h with ⟨ha, hab, hb1, hbox⟩
  have hb : 0 < b := ha.trans_le hab
  have habtheta : a ≤ theta * b :=
    (div_le_iff₀ hb).mp hthetaLower
  rcases hbox with ⟨_hC, B, hBside, _hinner, houter⟩
  have hraw :=
    FamilyStickyConvexClosedThickeningBoxGrowthV1.FrameBox.volume_cthickening_le_prod_side_add_two_mul
      B (K : Set Space) K.isCompact houter (theta * b)
  rw [hBside] at hraw
  have hrb : theta * b ≤ b := by nlinarith
  have hrone : theta * b ≤ 1 := hrb.trans hb1
  have hshort : a + 2 * (theta * b) ≤ 3 * (theta * b) := by nlinarith
  have hmiddle : b + 2 * (theta * b) ≤ 3 * b := by nlinarith
  have hlong : 1 + 2 * (theta * b) ≤ 3 := by nlinarith
  calc
    volume (Metric.cthickening (((theta * b : NNReal) : Real))
        (K : Set Space)) ≤
        ((a : ENNReal) + 2 * ((theta * b : NNReal) : ENNReal)) *
          (((b : ENNReal) + 2 * ((theta * b : NNReal) : ENNReal)) *
            ((1 : ENNReal) + 2 * ((theta * b : NNReal) : ENNReal))) := by
      simpa [plankSides, Fin.prod_univ_succ] using hraw
    _ ≤ (3 * ((theta : ENNReal) * (b : ENNReal))) *
        ((3 * (b : ENNReal)) * 3) := by
      gcongr
      · exact_mod_cast hshort
      · exact_mod_cast hmiddle
      · exact_mod_cast hlong
    _ = 27 * (theta : ENNReal) * (b : ENNReal) ^ 2 := by ring

/-! ## Unique owner plus local Delta-max gives the count -/

/-- Before cancelling the common certified member-volume lower bound, the
thickened cardinality is controlled by the actual owner-fibre concentration. -/
theorem thickenedPlank_card_mul_lowerVolume_le
    (D : ShadedConvexPlankFamily index a b)
    (owner : index -> ownerIndex)
    (hunique : ThickenedPlankUniqueOwner D owner)
    {Delta : NNReal}
    (hDelta : ownerFiberDeltaMax D owner ≤ (Delta : ENNReal))
    (theta : NNReal) (hthetaLower : a / b ≤ theta)
    (hthetaUpper : theta ≤ 1) (i : index) :
    ((thickenedPlankIndices D theta i).card : ENNReal) *
        ((((D.comparisonConstant)⁻¹ : NNReal) : ENNReal) ^ 3 *
          ((a : ENNReal) * (b : ENNReal))) ≤
      (Delta : ENNReal) *
        (27 * (theta : ENNReal) * (b : ENNReal) ^ 2) := by
  classical
  let A := thickenedPlankIndices D theta i
  let K := closedThickeningBody (D.family i) (theta * b)
  let ownerSet := ownerFiberIndices owner (owner i)
  have hownerSubset : A ⊆ ownerSet := by
    intro j hj
    exact (mem_ownerFiberIndices owner (owner i) j).2
      (hunique theta hthetaLower hthetaUpper i j hj)
  have hcontainedSubset : A ⊆
      Submission.Kakeya.ConvexGeometry.containedIndices D.family K := by
    intro j hj
    have hj' : (D.family j : Set Space) ⊆
        Metric.cthickening (((theta * b : NNReal) : Real))
          (D.family i : Set Space) := by
      simpa [A, thickenedPlankIndices,
        Family6AffinePlankAnalyticHypothesesStableV1.containedIndices] using
          (Finset.mem_filter.mp hj).2
    exact (mem_containedIndices D.family K j).2 (by
      simpa [K, closedThickeningBody] using hj')
  have hsum_le :
      (∑ j ∈ A, volume (D.family j : Set Space)) ≤
        containedMassOn D.family ownerSet K := by
    change bodyMassOn D.family A ≤ containedMassOn D.family ownerSet K
    rw [← containedMassOn_eq_bodyMassOn_of_contained D.family A K]
    · exact containedMassOn_mono hownerSubset K
    · intro j hj
      exact (mem_containedIndices D.family K j).1 (hcontainedSubset hj)
  have hlocalKT : IsKatzTao (Delta : ENNReal)
      (ownerFiberFamily D owner (owner i)) := by
    apply isKatzTao_iff_maximalConcentration_le.mpr
    exact (maximalConcentration_ownerFiber_le_ownerFiberDeltaMax
      D owner (owner i)).trans hDelta
  have hlocalMass : containedMassOn D.family ownerSet K ≤
      (Delta : ENNReal) * volume (K : Set Space) := by
    have h := hlocalKT K
    change containedMass (ownerFiberFamily D owner (owner i)) K ≤
      (Delta : ENNReal) * volume (K : Set Space) at h
    rw [containedMass_selectedCoarseFamily_eq_containedMassOn] at h
    simpa [ownerSet] using h
  calc
    ((A.card : Nat) : ENNReal) *
        ((((D.comparisonConstant)⁻¹ : NNReal) : ENNReal) ^ 3 *
          ((a : ENNReal) * (b : ENNReal))) =
      ∑ _j ∈ A,
        ((((D.comparisonConstant)⁻¹ : NNReal) : ENNReal) ^ 3 *
          ((a : ENNReal) * (b : ENNReal))) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ A, volume (D.family j : Set Space) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact (D.all_isPlank j).volume_lower_bound
    _ ≤ containedMassOn D.family ownerSet K := hsum_le
    _ ≤ (Delta : ENNReal) * volume (K : Set Space) := hlocalMass
    _ ≤ (Delta : ENNReal) *
        (27 * (theta : ENNReal) * (b : ENNReal) ^ 2) := by
      gcongr
      simpa [K, closedThickeningBody] using
        Family8UniqueOwnerLocalDeltaMaxThickControlV1.IsPlank.volume_theta_mul_b_closedThickening_le
          (D.all_isPlank i) hthetaLower hthetaUpper

/-- Exact ENNReal cancellation identity for the comparison-volume lower bound. -/
theorem localDeltaFactor_mul_plankLowerVolume
    {C Delta a b theta : NNReal} (hC : 0 < C) (ha : 0 < a) :
    (Delta : ENNReal) *
        (27 * (theta : ENNReal) * (b : ENNReal) ^ 2) =
      ((27 * C ^ 3 * Delta * (b / a) * theta : NNReal) : ENNReal) *
        ((((C⁻¹ : NNReal) : ENNReal) ^ 3) *
          ((a : ENNReal) * (b : ENNReal))) := by
  norm_cast
  field_simp

/-- The honest raw local-Delta count after cancelling the certified member
volume. -/
theorem thickenedPlank_card_le_localDeltaFactor
    (D : ShadedConvexPlankFamily index a b)
    (owner : index -> ownerIndex)
    (hunique : ThickenedPlankUniqueOwner D owner)
    {Delta : NNReal}
    (hDelta : ownerFiberDeltaMax D owner ≤ (Delta : ENNReal)) :
    ∀ theta : NNReal, a / b ≤ theta -> theta ≤ 1 ->
      ∀ i : index,
        ((thickenedPlankIndices D theta i).card : ENNReal) ≤
          ((27 * D.comparisonConstant ^ 3 * Delta * (b / a) : NNReal) :
            ENNReal) * (theta : ENNReal) := by
  intro theta hthetaLower hthetaUpper i
  have hplank := D.all_isPlank i
  have ha : 0 < a := hplank.1
  have hC : 0 < D.comparisonConstant :=
    zero_lt_one.trans_le hplank.2.2.2.1
  have hb : 0 < b := ha.trans_le hplank.2.1
  let v0 : ENNReal :=
    ((((D.comparisonConstant)⁻¹ : NNReal) : ENNReal) ^ 3 *
      ((a : ENNReal) * (b : ENNReal)))
  have hv0 : v0 ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero 3 (ENNReal.coe_ne_zero.mpr (inv_pos.mpr hC).ne')
    · exact mul_ne_zero
        (ENNReal.coe_ne_zero.mpr ha.ne') (ENNReal.coe_ne_zero.mpr hb.ne')
  have hvTop : v0 ≠ ∞ := by
    exact (ENNReal.mul_lt_top
      (ENNReal.pow_lt_top ENNReal.coe_lt_top)
      (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top)).ne
  have hmass := thickenedPlank_card_mul_lowerVolume_le
    D owner hunique hDelta theta hthetaLower hthetaUpper i
  have hscalar :
      (Delta : ENNReal) *
          (27 * (theta : ENNReal) * (b : ENNReal) ^ 2) =
        ((27 * D.comparisonConstant ^ 3 * Delta * (b / a) * theta : NNReal) :
            ENNReal) * v0 := by
    simpa [v0] using
      (localDeltaFactor_mul_plankLowerVolume
        (C := D.comparisonConstant) (Delta := Delta)
        (a := a) (b := b) (theta := theta) hC ha)
  have hcancel :
      ((thickenedPlankIndices D theta i).card : ENNReal) * v0 ≤
        ((27 * D.comparisonConstant ^ 3 * Delta * (b / a) * theta : NNReal) :
            ENNReal) * v0 := by
    exact hmass.trans_eq hscalar
  have hcancelled := (ENNReal.mul_le_mul_iff_left hv0 hvTop).mp hcancel
  simpa only [ENNReal.coe_mul] using hcancelled

/-- The resulting stable thick-control constant with no hidden comparison
loss.  The `max 1` is forced by the Family 6 predicate's normalization. -/
def uniqueOwnerLocalDeltaThickM
    (C Delta a b : NNReal) : NNReal :=
  max 1 (27 * C ^ 3 * Delta * (b / a))

/-- Unique owner and actual local `Delta_max` produce a stable Family 6
thick-plank certificate with the honest comparison-dependent constant. -/
theorem frostmanThickenedPlankControl_of_uniqueOwner_localDeltaMax
    (D : ShadedConvexPlankFamily index a b)
    (owner : index -> ownerIndex)
    (hunique : ThickenedPlankUniqueOwner D owner)
    {Delta : NNReal}
    (hDelta : ownerFiberDeltaMax D owner ≤ (Delta : ENNReal)) :
    FrostmanThickenedPlankControl D
      (uniqueOwnerLocalDeltaThickM D.comparisonConstant Delta a b) := by
  refine ⟨le_max_left _ _, ?_⟩
  intro theta hthetaLower hthetaUpper i
  have hraw := thickenedPlank_card_le_localDeltaFactor
    D owner hunique hDelta theta hthetaLower hthetaUpper i
  have hmax :
      27 * D.comparisonConstant ^ 3 * Delta * (b / a) ≤
        uniqueOwnerLocalDeltaThickM D.comparisonConstant Delta a b :=
    le_max_right _ _
  have hmaxE :
      ((27 * D.comparisonConstant ^ 3 * Delta * (b / a) : NNReal) :
          ENNReal) ≤
        (uniqueOwnerLocalDeltaThickM D.comparisonConstant Delta a b :
          ENNReal) :=
    ENNReal.coe_le_coe.mpr hmax
  exact hraw.trans (mul_le_mul hmaxE le_rfl bot_le bot_le)

/-- Paper-normalized exact ratio.  This isolates the precise scalar
absorption needed to turn the honest comparison-dependent count into the
Bundle V2 field `M = b/a`. -/
theorem frostmanThickenedPlankControl_ratio_of_uniqueOwner_localDeltaMax
    (D : ShadedConvexPlankFamily index a b)
    (owner : index -> ownerIndex)
    (hunique : ThickenedPlankUniqueOwner D owner)
    {Delta : NNReal}
    (hDelta : ownerFiberDeltaMax D owner ≤ (Delta : ENNReal))
    (ha : 0 < a) (hab : a ≤ b)
    (hcomparisonAbsorb :
      27 * D.comparisonConstant ^ 3 * Delta ≤ 1) :
    FrostmanThickenedPlankControl D (b / a) := by
  have hratioOne : 1 ≤ b / a := by
    exact (le_div_iff₀ ha).2 (by simpa using hab)
  refine ⟨hratioOne, ?_⟩
  intro theta hthetaLower hthetaUpper i
  have hraw := thickenedPlank_card_le_localDeltaFactor
    D owner hunique hDelta theta hthetaLower hthetaUpper i
  have hfactor :
      27 * D.comparisonConstant ^ 3 * Delta * (b / a) ≤ b / a := by
    calc
      27 * D.comparisonConstant ^ 3 * Delta * (b / a) ≤
          1 * (b / a) := by gcongr
      _ = b / a := one_mul _
  have hfactorE :
      ((27 * D.comparisonConstant ^ 3 * Delta * (b / a) : NNReal) :
          ENNReal) ≤ ((b / a : NNReal) : ENNReal) :=
    ENNReal.coe_le_coe.mpr hfactor
  exact hraw.trans (mul_le_mul hfactorE le_rfl bot_le bot_le)

#print axioms maximalConcentration_ownerFiber_le_ownerFiberDeltaMax
#print axioms IsPlank.volume_theta_mul_b_closedThickening_le
#print axioms thickenedPlank_card_mul_lowerVolume_le
#print axioms thickenedPlank_card_le_localDeltaFactor
#print axioms frostmanThickenedPlankControl_of_uniqueOwner_localDeltaMax
#print axioms frostmanThickenedPlankControl_ratio_of_uniqueOwner_localDeltaMax

end

end Family8UniqueOwnerLocalDeltaMaxThickControlV1
