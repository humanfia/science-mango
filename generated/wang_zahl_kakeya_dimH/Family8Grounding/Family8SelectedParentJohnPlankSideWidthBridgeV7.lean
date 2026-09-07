import Family8Grounding.Family8SelectedParentJohnPlankSideWidthBridgeV5
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnLongAxisRelabelV4
import FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentJohnPlankSideWidthBridgeV7

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8FiniteRandomRigidMotionPaperFixedJohnLongAxisRelabelV4
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

noncomputable section

/-! ## Carrier-preserving relabeling of an arbitrary box certificate -/

/-- The side vector obtained by permuting the axes of a frame box. -/
def relabeledSide (side : Fin 3 → NNReal) (e : Equiv.Perm (Fin 3)) :
    Fin 3 → NNReal :=
  fun i ↦ side (e.symm i)

@[simp] theorem relabeledSide_apply
    (side : Fin 3 → NNReal) (e : Equiv.Perm (Fin 3)) (i : Fin 3) :
    relabeledSide side e i = side (e.symm i) := rfl

/-- Relabeling axes changes neither the certified body nor the comparison
constant.  In particular, this is not a geometric replacement of a parent. -/
def relabelBoxDimensionsCertificate
    {C : NNReal} {side : Fin 3 → NNReal} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K) (e : Equiv.Perm (Fin 3)) :
    BoxDimensionsCertificate C (relabeledSide side e) K where
  one_le := cert.one_le
  box := relabelFrameBox cert.box e
  side_eq := by
    funext i
    simp only [relabelFrameBox_side, relabeledSide_apply]
    exact congrFun cert.side_eq (e.symm i)
  inner_le := by
    intro x hx
    apply cert.inner_le
    change x ∈ ((relabelFrameBox cert.box e).rescale C⁻¹).carrier at hx
    change x ∈ (cert.box.rescale C⁻¹).carrier
    have hrescale :
        (relabelFrameBox cert.box e).rescale C⁻¹ =
          relabelFrameBox (cert.box.rescale C⁻¹) e := by
      rfl
    rw [hrescale, relabelFrameBox_carrier] at hx
    exact hx
  outer_le := by
    intro x hx
    change x ∈ (relabelFrameBox cert.box e).carrier
    rw [relabelFrameBox_carrier]
    exact cert.outer_le hx

/-! ## A canonical longest-axis choice -/

/-- A concrete longest coordinate among the three sides. -/
def longestSideIndex (side : Fin 3 → NNReal) : Fin 3 :=
  if side 0 ≤ side 1 then
    if side 1 ≤ side 2 then 2 else 1
  else if side 0 ≤ side 2 then 2 else 0

theorem side_le_longestSideIndex
    (side : Fin 3 → NNReal) (i : Fin 3) :
    side i ≤ side (longestSideIndex side) := by
  unfold longestSideIndex
  by_cases h01 : side 0 ≤ side 1
  · rw [if_pos h01]
    by_cases h12 : side 1 ≤ side 2
    · rw [if_pos h12]
      fin_cases i
      · exact h01.trans h12
      · exact h12
      · exact le_rfl
    · rw [if_neg h12]
      have h21 : side 2 ≤ side 1 := (lt_of_not_ge h12).le
      fin_cases i
      · exact h01
      · exact le_rfl
      · exact h21
  · rw [if_neg h01]
    have h10 : side 1 ≤ side 0 := (lt_of_not_ge h01).le
    by_cases h02 : side 0 ≤ side 2
    · rw [if_pos h02]
      fin_cases i
      · exact h02
      · exact h10.trans h02
      · exact le_rfl
    · rw [if_neg h02]
      have h20 : side 2 ≤ side 0 := (lt_of_not_ge h02).le
      fin_cases i
      · exact le_rfl
      · exact h10
      · exact h20

/-- Move the chosen longest side to coordinate `2`. -/
def longAxisPermutation (side : Fin 3 → NNReal) : Equiv.Perm (Fin 3) :=
  Equiv.swap 2 (longestSideIndex side)

/-- The relabeled coordinate `2` is at least every relabeled coordinate. -/
theorem relabeledSide_le_two
    (side : Fin 3 → NNReal) (i : Fin 3) :
    relabeledSide side (longAxisPermutation side) i ≤
      relabeledSide side (longAxisPermutation side) 2 := by
  rw [relabeledSide_apply, relabeledSide_apply]
  simp only [longAxisPermutation, Equiv.symm_swap, Equiv.swap_apply_left]
  exact side_le_longestSideIndex side _

/-! ## Three-coordinate dyadic shape labels -/

/-- The three independent ceil-log labels of a positive side vector. -/
def sideShapeLabel (side : Fin 3 → NNReal) : Fin 3 → Int :=
  fun i ↦ dyadicCeilBucket (side i : Real)

/-- The target upper endpoint attached to a three-coordinate shape label. -/
def sideShapeUpper (label : Fin 3 → Int) : Fin 3 → NNReal :=
  fun i ↦ ⟨dyadicCeilUpper (label i), by
    exact (Real.rpow_pos_of_pos (by norm_num : (0 : Real) < 2) _).le⟩

theorem sideShapeUpper_pos (label : Fin 3 → Int) (i : Fin 3) :
    0 < sideShapeUpper label i := by
  change 0 < dyadicCeilUpper (label i)
  exact Real.rpow_pos_of_pos (by norm_num) _

/-- A positive side lies in the factor-two band attached to its label. -/
theorem sideShapeUpper_half_lt_and_le
    {side : Fin 3 → NNReal} (hside : ∀ i, 0 < side i) (i : Fin 3) :
    sideShapeUpper (sideShapeLabel side) i / 2 < side i ∧
      side i ≤ sideShapeUpper (sideShapeLabel side) i := by
  have h := dyadicCeilUpper_half_lt_and_le
    (show (0 : Real) < (side i : Real) by exact_mod_cast hside i)
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

/-- The ceil-log upper endpoint preserves coordinate ordering. -/
theorem sideShapeUpper_le_of_side_le
    {side : Fin 3 → NNReal} (hside : ∀ i, 0 < side i)
    {i j : Fin 3} (hij : side i ≤ side j) :
    sideShapeUpper (sideShapeLabel side) i ≤
      sideShapeUpper (sideShapeLabel side) j := by
  have hlabel := dyadicCeilBucket_mono
    (show (0 : Real) < (side i : Real) by exact_mod_cast hside i)
    (show (side i : Real) ≤ (side j : Real) by exact_mod_cast hij)
  change (⟨dyadicCeilUpper (dyadicCeilBucket (side i : Real)), _⟩ : NNReal) ≤
    ⟨dyadicCeilUpper (dyadicCeilBucket (side j : Real)), _⟩
  exact_mod_cast Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : Real) ≤ 2) (by exact_mod_cast hlabel)

/-- Literal fiber of members having one common three-coordinate side label. -/
def sideShapeBucket {item : Type*} [DecidableEq item]
    (items : Finset item) (side : item → Fin 3 → NNReal)
    (label : Fin 3 → Int) : Finset item :=
  items.filter fun x ↦ sideShapeLabel (side x) = label

@[simp] theorem mem_sideShapeBucket_iff
    {item : Type*} [DecidableEq item]
    (items : Finset item) (side : item → Fin 3 → NNReal)
    (label : Fin 3 → Int) (x : item) :
    x ∈ sideShapeBucket items side label ↔
      x ∈ items ∧ sideShapeLabel (side x) = label := by
  simp [sideShapeBucket]

/-- Honest finite weighted three-side pigeonholing.  The loss is the exact
number of occupied shape labels, not an assumed global comparability factor. -/
theorem exists_sideShapeBucket_weight_retention
    {item : Type*} [DecidableEq item]
    (items : Finset item) (hitems : items.Nonempty)
    (side : item → Fin 3 → NNReal) (hside : ∀ x i, 0 < side x i)
    (weight : item → Real) :
    ∃ label : Fin 3 → Int,
      label ∈ occupiedWeightBuckets items (fun x ↦ sideShapeLabel (side x)) ∧
      (∑ x ∈ items, weight x) ≤
        (occupiedWeightBuckets items
          (fun x ↦ sideShapeLabel (side x))).card *
          (∑ x ∈ sideShapeBucket items side label, weight x) ∧
      ∀ x, x ∈ sideShapeBucket items side label → ∀ i,
        sideShapeUpper label i / 2 < side x i ∧
          side x i ≤ sideShapeUpper label i := by
  obtain ⟨label, hlabel, hweight⟩ :=
    exists_totalWeight_le_card_mul_bucketWeight
      (items := items) (bucket := fun x ↦ sideShapeLabel (side x))
      weight hitems
  refine ⟨label, hlabel, ?_, ?_⟩
  · simpa [bucketWeight, sideShapeBucket] using hweight
  · intro x hx i
    have hxLabel := (mem_sideShapeBucket_iff items side label x).mp hx |>.2
    have hband := sideShapeUpper_half_lt_and_le (hside x) i
    simpa only [hxLabel] using hband

/-! ## Normalizing one occupied shape bucket to literal plank sides -/

/-- A single common transverse swap orders the two short dyadic upper
endpoints. It fixes the already selected long coordinate `2`. -/
def transverseOrderPermutation (label : Fin 3 → Int) :
    Equiv.Perm (Fin 3) :=
  if sideShapeUpper label 0 ≤ sideShapeUpper label 1 then
    Equiv.refl (Fin 3)
  else Equiv.swap 0 1

/-- Divide every oriented side by the common long dyadic upper endpoint. -/
def normalizedBucketSide (source : Fin 3 → NNReal)
    (label : Fin 3 → Int) : Fin 3 → NNReal :=
  fun i ↦ relabeledSide source (transverseOrderPermutation label) i /
    sideShapeUpper label 2

/-- The similarly oriented and long-normalized common target vector. -/
def normalizedBucketTarget (label : Fin 3 → Int) : Fin 3 → NNReal :=
  fun i ↦
    relabeledSide (sideShapeUpper label) (transverseOrderPermutation label) i /
      sideShapeUpper label 2

def bucketShortA (label : Fin 3 → Int) : NNReal :=
  if sideShapeUpper label 0 ≤ sideShapeUpper label 1 then
    sideShapeUpper label 0 / sideShapeUpper label 2
  else sideShapeUpper label 1 / sideShapeUpper label 2

def bucketShortB (label : Fin 3 → Int) : NNReal :=
  if sideShapeUpper label 0 ≤ sideShapeUpper label 1 then
    sideShapeUpper label 1 / sideShapeUpper label 2
  else sideShapeUpper label 0 / sideShapeUpper label 2

theorem normalizedBucketTarget_eq_plankSides (label : Fin 3 → Int) :
    normalizedBucketTarget label =
      plankSides (bucketShortA label) (bucketShortB label) := by
  have htwo : sideShapeUpper label 2 ≠ 0 :=
    (sideShapeUpper_pos label 2).ne'
  funext i
  by_cases h : sideShapeUpper label 0 ≤ sideShapeUpper label 1
  · fin_cases i <;>
      simp [normalizedBucketTarget, transverseOrderPermutation,
        bucketShortA, bucketShortB, relabeledSide, plankSides, h, htwo]
  · have hswap2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    fin_cases i <;>
      simp [normalizedBucketTarget, transverseOrderPermutation,
        bucketShortA, bucketShortB, relabeledSide, plankSides, h, hswap2, htwo]

theorem bucketShortA_pos (label : Fin 3 → Int) :
    0 < bucketShortA label := by
  by_cases h : sideShapeUpper label 0 ≤ sideShapeUpper label 1
  · simp only [bucketShortA, if_pos h]
    exact div_pos (sideShapeUpper_pos label 0) (sideShapeUpper_pos label 2)
  · simp only [bucketShortA, if_neg h]
    exact div_pos (sideShapeUpper_pos label 1) (sideShapeUpper_pos label 2)

theorem bucketShortA_le_bucketShortB (label : Fin 3 → Int) :
    bucketShortA label ≤ bucketShortB label := by
  by_cases h : sideShapeUpper label 0 ≤ sideShapeUpper label 1
  · simp only [bucketShortA, bucketShortB, if_pos h]
    simp only [div_eq_mul_inv]
    simpa [mul_comm] using
      mul_le_mul_right h (sideShapeUpper label 2)⁻¹
  · simp only [bucketShortA, bucketShortB, if_neg h]
    simp only [div_eq_mul_inv]
    simpa [mul_comm] using
      mul_le_mul_right (le_of_not_ge h) (sideShapeUpper label 2)⁻¹

theorem bucketShortB_le_one
    (label : Fin 3 → Int)
    (h02 : sideShapeUpper label 0 ≤ sideShapeUpper label 2)
    (h12 : sideShapeUpper label 1 ≤ sideShapeUpper label 2) :
    bucketShortB label ≤ 1 := by
  have htwo : 0 < sideShapeUpper label 2 := sideShapeUpper_pos label 2
  by_cases h : sideShapeUpper label 0 ≤ sideShapeUpper label 1
  · simp only [bucketShortB, if_pos h]
    exact (div_le_iff₀ htwo).2 (by simpa using h12)
  · simp only [bucketShortB, if_neg h]
    exact (div_le_iff₀ htwo).2 (by simpa using h02)

/-- The factor-two dyadic bands give a literal `SideWidthEnvelope` after
one common long normalization and one common transverse ordering. -/
theorem normalizedBucketSide_sideWidthEnvelope
    {source : Fin 3 → NNReal} {label : Fin 3 → Int}
    (hband : ∀ i, sideShapeUpper label i / 2 < source i ∧
      source i ≤ sideShapeUpper label i) :
    SideWidthEnvelope (normalizedBucketSide source label)
      (plankSides (bucketShortA label) (bucketShortB label)) 2 := by
  rw [← normalizedBucketTarget_eq_plankSides label]
  refine ⟨by norm_num, ?_, ?_⟩
  · intro i
    simp only [normalizedBucketSide, normalizedBucketTarget,
      relabeledSide_apply, div_eq_mul_inv]
    simpa [mul_comm] using mul_le_mul_right
      (hband ((transverseOrderPermutation label).symm i)).2
      (sideShapeUpper label 2)⁻¹
  · intro i
    simp only [normalizedBucketSide, normalizedBucketTarget,
      relabeledSide_apply, div_eq_mul_inv]
    have htwo :
        sideShapeUpper label ((transverseOrderPermutation label).symm i) ≤
          2 * source ((transverseOrderPermutation label).symm i) := by
      nlinarith [
        (hband ((transverseOrderPermutation label).symm i)).1]
    calc
      sideShapeUpper label ((transverseOrderPermutation label).symm i) *
          (sideShapeUpper label 2)⁻¹ ≤
        (2 * source ((transverseOrderPermutation label).symm i)) *
          (sideShapeUpper label 2)⁻¹ := by
            simpa [mul_comm] using
              mul_le_mul_right htwo (sideShapeUpper label 2)⁻¹
      _ = 2 * (source ((transverseOrderPermutation label).symm i) *
          (sideShapeUpper label 2)⁻¹) := by ac_rfl

/-! ## Specialization to actual selected parents in the common John frame -/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The actual memberwise John side vector after carrier-preserving longest
axis relabeling. -/
noncomputable def selectedParentLongRelabeledSide
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (p : {p // p ∈ B}) : Fin 3 → NNReal :=
  let side := selectedParentAffineJohnSide e S B hrho p
  relabeledSide side (longAxisPermutation side)

/-- The actual certificate behind `selectedParentLongRelabeledSide`; its box
has exactly the same carrier as the automatically selected John box. -/
noncomputable def selectedParentLongRelabeledCertificate
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (p : {p // p ∈ B}) :
    BoxDimensionsCertificate 288
      (selectedParentLongRelabeledSide e S B hrho p)
      (selectedParentAffineFamily e S B p) :=
  relabelBoxDimensionsCertificate
    (selectedParentAffineJohnCertificate e S B hrho p)
    (longAxisPermutation (selectedParentAffineJohnSide e S B hrho p))

theorem selectedParentLongRelabeledSide_pos
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (p : {p // p ∈ B}) (i : Fin 3) :
    0 < selectedParentLongRelabeledSide e S B hrho p i := by
  exact selectedParentAffineJohnSide_pos e S B hrho p _

theorem selectedParentLongRelabeledSide_le_two
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (p : {p // p ∈ B}) (i : Fin 3) :
    selectedParentLongRelabeledSide e S B hrho p i ≤
      selectedParentLongRelabeledSide e S B hrho p 2 := by
  exact relabeledSide_le_two
    (selectedParentAffineJohnSide e S B hrho p) i

/-- In the common contracted winning-hull frame, all three relabeled actual
member sides retain the explicit automatic upper bound. -/
theorem selectedParentContractedLongRelabeledSide_le
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
    (i : Fin 3) :
    selectedParentLongRelabeledSide
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho p i ≤
      1728 * r := by
  exact selectedParentContractedJohnSide_le S hrho P k r hr p _

/-- A genuine weighted dyadic shape bucket for the actual selected parents.
Every retained member has all three sides within factor two of one common
upper vector, with the long side still in coordinate `2`. -/
theorem exists_selectedParentLongSideShapeBucket_weight_retention
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (weight :
      {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber} → Real) :
    let parent := {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}
    let side : parent → Fin 3 → NNReal := fun p ↦
      selectedParentLongRelabeledSide
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho p
    ∃ label : Fin 3 → Int,
      label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
        (fun p ↦ sideShapeLabel (side p)) ∧
      (∑ p : parent, weight p) ≤
        (occupiedWeightBuckets (Finset.univ : Finset parent)
          (fun p ↦ sideShapeLabel (side p))).card *
          (∑ p ∈ sideShapeBucket Finset.univ side label, weight p) ∧
      ∀ p, p ∈ sideShapeBucket Finset.univ side label → ∀ i,
        sideShapeUpper label i / 2 < side p i ∧
          side p i ≤ sideShapeUpper label i := by
  dsimp only
  let p₀ : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber} :=
    ⟨Classical.choose (blockAt S.activeCoarseFamily P k).fiber_nonempty,
      Classical.choose_spec (blockAt S.activeCoarseFamily P k).fiber_nonempty⟩
  have huniv : (Finset.univ : Finset
      {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}).Nonempty :=
    ⟨p₀, Finset.mem_univ _⟩
  apply exists_sideShapeBucket_weight_retention
    (items := Finset.univ) huniv
  intro p i
  exact selectedParentLongRelabeledSide_pos _ S _ hrho p i

/-- The selected occupied bucket supplies literal anisotropic plank parameters
`a ≤ b ≤ 1` and a factor-two side envelope for every retained actual parent,
after the common long-scale normalization and common transverse ordering. -/
theorem exists_selectedParentNormalizedPlankBucket_weight_retention
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (weight :
      {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber} → Real) :
    let parent := {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}
    let side : parent → Fin 3 → NNReal := fun p ↦
      selectedParentLongRelabeledSide
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho p
    ∃ label : Fin 3 → Int,
      label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
        (fun p ↦ sideShapeLabel (side p)) ∧
      (∑ p : parent, weight p) ≤
        (occupiedWeightBuckets (Finset.univ : Finset parent)
          (fun p ↦ sideShapeLabel (side p))).card *
          (∑ p ∈ sideShapeBucket Finset.univ side label, weight p) ∧
      0 < bucketShortA label ∧
      bucketShortA label ≤ bucketShortB label ∧
      bucketShortB label ≤ 1 ∧
      ∀ p, p ∈ sideShapeBucket Finset.univ side label →
        SideWidthEnvelope (normalizedBucketSide (side p) label)
          (plankSides (bucketShortA label) (bucketShortB label)) 2 := by
  dsimp only
  have hbucket :=
    exists_selectedParentLongSideShapeBucket_weight_retention
      S hrho P k r hr weight
  dsimp only at hbucket
  obtain ⟨label, hoccupied, hweight, hband⟩ := hbucket
  rcases mem_occupiedWeightBuckets_iff.mp hoccupied with
    ⟨p, _hp, hpLabel⟩
  have hpos : ∀ i, 0 < selectedParentLongRelabeledSide
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho p i := by
    intro i
    exact selectedParentLongRelabeledSide_pos _ S _ hrho p i
  have h02 := sideShapeUpper_le_of_side_le hpos
    (selectedParentLongRelabeledSide_le_two
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho p 0)
  have h12 := sideShapeUpper_le_of_side_le hpos
    (selectedParentLongRelabeledSide_le_two
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho p 1)
  rw [hpLabel] at h02 h12
  refine ⟨label, hoccupied, hweight, bucketShortA_pos label,
    bucketShortA_le_bucketShortB label,
    bucketShortB_le_one label h02 h12, ?_⟩
  intro q hq
  exact normalizedBucketSide_sideWidthEnvelope (hband q hq)

#print axioms relabelBoxDimensionsCertificate
#print axioms side_le_longestSideIndex
#print axioms relabeledSide_le_two
#print axioms sideShapeUpper_half_lt_and_le
#print axioms sideShapeUpper_le_of_side_le
#print axioms normalizedBucketSide_sideWidthEnvelope
#print axioms exists_sideShapeBucket_weight_retention
#print axioms selectedParentLongRelabeledCertificate
#print axioms selectedParentContractedLongRelabeledSide_le
#print axioms exists_selectedParentLongSideShapeBucket_weight_retention
#print axioms exists_selectedParentNormalizedPlankBucket_weight_retention

end
end Family8SelectedParentJohnPlankSideWidthBridgeV7
