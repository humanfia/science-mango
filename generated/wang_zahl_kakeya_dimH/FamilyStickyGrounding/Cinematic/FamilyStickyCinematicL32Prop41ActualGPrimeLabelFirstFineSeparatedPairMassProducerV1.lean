import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstBilateralSupportBoundaryV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

namespace FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1

open scoped BigOperators

open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32Lemma57FiniteTwoEndsMaximizerV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstBilateralSupportBoundaryV1
open FamilyStickyCinematicL32Prop41ActualY1ExactCFiberPairSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CanonicalSeparatedBallPairV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41SeparatedCoefficientBallPairV1

noncomputable section

universe u v

/-!
# Fine-label-first separated-pair mass

The coarse G-prime count does not imply that the two sampled sides share a
fine label. Here the order of summation is reversed: first restrict to the
retained indices at one literal fine label, subtract the canonical near
pairs in that fibre, and only then sum over labels. A Fubini identity turns
this into a weighted sum over separated centre pairs.
-/

noncomputable def actualGPrimeRetainedFineActiveFiber
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (r : fineLabel) : Finset iota :=
  retainedY1IndicesAtFine D keep r ∩ N.family

@[simp]
theorem mem_actualGPrimeRetainedFineActiveFiber_iff
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (r : fineLabel) (i : iota) :
    i ∈ actualGPrimeRetainedFineActiveFiber N D keep r ↔
      (i, r) ∈ D.retainedGoodPairs keep ∧ i ∈ N.family := by
  classical
  simp [actualGPrimeRetainedFineActiveFiber,
    mem_retainedY1IndicesAtFine_iff]

noncomputable def actualGPrimeFineSeparatedPairsAt
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (r : fineLabel) : Finset (iota × iota) := by
  classical
  exact ((actualGPrimeRetainedFineActiveFiber N D keep r) ×ˢ
    (actualGPrimeRetainedFineActiveFiber N D keep r)).filter fun pair =>
      canonicalTenRadiusSeparated N ballRadius pair.1 pair.2

noncomputable def actualGPrimeFineNearRightFiber
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (r : fineLabel) (left : iota) : Finset iota := by
  classical
  exact (actualGPrimeRetainedFineActiveFiber N D keep r).filter fun right =>
    ¬canonicalTenRadiusSeparated N ballRadius left right

noncomputable def actualGPrimeFineNearPairsAt
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (r : fineLabel) : Finset (iota × iota) := by
  classical
  exact ((actualGPrimeRetainedFineActiveFiber N D keep r) ×ˢ
    (actualGPrimeRetainedFineActiveFiber N D keep r)).filter fun pair =>
      ¬canonicalTenRadiusSeparated N ballRadius pair.1 pair.2

noncomputable def actualGPrimeFineSeparatedPairMass
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real) : Nat :=
  ∑ r ∈ D.fineLabels,
    (actualGPrimeFineSeparatedPairsAt N D keep ballRadius r).card

noncomputable def actualGPrimeCommonFineCenterLabels
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota) :
    Finset fineLabel := by
  classical
  exact D.fineLabels.filter fun r =>
    left ∈ actualGPrimeRetainedFineActiveFiber N D keep r ∧
    right ∈ actualGPrimeRetainedFineActiveFiber N D keep r

@[simp]
theorem mem_actualGPrimeCommonFineCenterLabels_iff
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (r : fineLabel) :
    r ∈ actualGPrimeCommonFineCenterLabels N D keep left right ↔
      r ∈ D.fineLabels ∧
      left ∈ actualGPrimeRetainedFineActiveFiber N D keep r ∧
      right ∈ actualGPrimeRetainedFineActiveFiber N D keep r := by
  classical
  simp [actualGPrimeCommonFineCenterLabels, and_assoc]

noncomputable def actualGPrimeFineSeparatedCenterPairMass
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real) : Nat :=
  richSeparatedPairCountTotal N.family
    (canonicalTenRadiusSeparated N ballRadius) (fun _ _ => True)
    (fun left right =>
      (actualGPrimeCommonFineCenterLabels N D keep left right).card)

theorem actualGPrimeFineNearRightFiber_subset_tenRadiusBall
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (r : fineLabel)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (left : iota) :
    actualGPrimeFineNearRightFiber N D keep ballRadius r left ⊆
      finiteFamilyMetricBall N.family N.distance (10 * ballRadius) left := by
  intro right hright
  have hrightData :
      right ∈ actualGPrimeRetainedFineActiveFiber N D keep r ∧
        ¬canonicalTenRadiusSeparated N ballRadius left right := by
    simpa only [actualGPrimeFineNearRightFiber, Finset.mem_filter] using hright
  have hrightN : right ∈ N.family :=
    (mem_actualGPrimeRetainedFineActiveFiber_iff
      N D keep r right).mp hrightData.1 |>.2
  have hnotSeparated :
      ¬10 * ballRadius <= N.distance left right := by
    simpa only [canonicalTenRadiusSeparated] using hrightData.2
  have hdistance : N.distance right left <= 10 * ballRadius := by
    calc
      N.distance right left = N.distance left right := hsymm right left
      _ <= 10 * ballRadius := (lt_of_not_ge hnotSeparated).le
  simpa only [finiteFamilyMetricBall, Finset.mem_filter] using
    And.intro hrightN hdistance

theorem actualGPrimeFineNearRightFiber_card_le_automatic
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (r : fineLabel)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (hnearRadiusLower : N.delta <= 10 * ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= N.ceiling)
    (left : iota)
    (hleft : left ∈ actualGPrimeRetainedFineActiveFiber N D keep r) :
    (actualGPrimeFineNearRightFiber N D keep ballRadius r left).card <=
      automaticCanonicalNearCap N ballRadius := by
  have hleftN := (mem_actualGPrimeRetainedFineActiveFiber_iff
    N D keep r left).mp hleft |>.2
  have hsubset := actualGPrimeFineNearRightFiber_subset_tenRadiusBall
    N D keep ballRadius r hsymm left
  have hnearNat :
      (actualGPrimeFineNearRightFiber N D keep ballRadius r left).card <=
        (finiteFamilyMetricBall N.family N.distance
          (10 * ballRadius) left).card :=
    Finset.card_le_card hsubset
  have hballReal :
      ((finiteFamilyMetricBall N.family N.distance
        (10 * ballRadius) left).card : Real) <=
      ((10 * ballRadius) / N.criticalScale) ^ N.exponent *
        ((N.criticalBall.card : Nat) : Real) := by
    simpa only [finiteBallCount, finiteFamilyMetricBall] using
      N.card_le_ratio_rpow hnearRadiusLower hnearRadiusUpper left hleftN
  have hnearReal :
      ((actualGPrimeFineNearRightFiber
        N D keep ballRadius r left).card : Real) <=
        (automaticCanonicalNearCap N ballRadius : Nat) := by
    have hcast :
        ((actualGPrimeFineNearRightFiber
          N D keep ballRadius r left).card : Real) <=
          ((finiteFamilyMetricBall N.family N.distance
            (10 * ballRadius) left).card : Real) := by
      exact_mod_cast hnearNat
    exact hcast.trans (hballReal.trans (Nat.le_ceil _))
  exact_mod_cast hnearReal

theorem actualGPrimeFineNearPairsAt_card_eq_sum_nearRightFiber
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (r : fineLabel) :
    (actualGPrimeFineNearPairsAt N D keep ballRadius r).card =
      ∑ left ∈ actualGPrimeRetainedFineActiveFiber N D keep r,
        (actualGPrimeFineNearRightFiber
          N D keep ballRadius r left).card := by
  classical
  rw [Finset.card_eq_sum_ones]
  simp only [actualGPrimeFineNearPairsAt, Finset.sum_filter]
  rw [Finset.sum_product
    (actualGPrimeRetainedFineActiveFiber N D keep r)
    (actualGPrimeRetainedFineActiveFiber N D keep r)
    (fun pair => if
      ¬canonicalTenRadiusSeparated N ballRadius pair.1 pair.2 then 1 else 0)]
  apply Finset.sum_congr rfl
  intro left hleft
  change
    (∑ right ∈ actualGPrimeRetainedFineActiveFiber N D keep r,
      if ¬canonicalTenRadiusSeparated N ballRadius left right then 1 else 0) =
    ((actualGPrimeRetainedFineActiveFiber N D keep r).filter fun right =>
      ¬canonicalTenRadiusSeparated N ballRadius left right).card
  rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter]

theorem actualGPrimeFineSeparated_card_add_near_card
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (r : fineLabel) :
    (actualGPrimeFineSeparatedPairsAt N D keep ballRadius r).card +
        (actualGPrimeFineNearPairsAt N D keep ballRadius r).card =
      (actualGPrimeRetainedFineActiveFiber N D keep r).card *
        (actualGPrimeRetainedFineActiveFiber N D keep r).card := by
  classical
  simpa only [actualGPrimeFineSeparatedPairsAt,
    actualGPrimeFineNearPairsAt, Finset.card_product] using
    ((actualGPrimeRetainedFineActiveFiber N D keep r) ×ˢ
      (actualGPrimeRetainedFineActiveFiber N D keep r)
    ).card_filter_add_card_filter_not
      (fun pair => canonicalTenRadiusSeparated N ballRadius pair.1 pair.2)

theorem actualGPrimeFineActive_card_mul_tsub_nearCap_le_separated_card
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (r : fineLabel) (nearCap : Nat)
    (hcap : forall left,
      left ∈ actualGPrimeRetainedFineActiveFiber N D keep r ->
      (actualGPrimeFineNearRightFiber
        N D keep ballRadius r left).card <= nearCap) :
    (actualGPrimeRetainedFineActiveFiber N D keep r).card *
        ((actualGPrimeRetainedFineActiveFiber N D keep r).card - nearCap) <=
      (actualGPrimeFineSeparatedPairsAt N D keep ballRadius r).card := by
  have hnear :
      (actualGPrimeFineNearPairsAt N D keep ballRadius r).card <=
        (actualGPrimeRetainedFineActiveFiber N D keep r).card * nearCap := by
    rw [actualGPrimeFineNearPairsAt_card_eq_sum_nearRightFiber]
    calc
      (∑ left ∈ actualGPrimeRetainedFineActiveFiber N D keep r,
          (actualGPrimeFineNearRightFiber
            N D keep ballRadius r left).card) <=
        ∑ _left ∈ actualGPrimeRetainedFineActiveFiber N D keep r,
          nearCap :=
        Finset.sum_le_sum fun left hleft => hcap left hleft
      _ = (actualGPrimeRetainedFineActiveFiber N D keep r).card *
          nearCap := by simp
  have hpartition := actualGPrimeFineSeparated_card_add_near_card
    N D keep ballRadius r
  rw [Nat.mul_sub_left_distrib]
  have hsub := Nat.sub_le_sub_left hnear
    ((actualGPrimeRetainedFineActiveFiber N D keep r).card *
      (actualGPrimeRetainedFineActiveFiber N D keep r).card)
  omega

theorem fineLabels_mul_degreeLower_mul_tsub_nearCap_le_mass
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (degreeLower nearCap : Nat)
    (hdegree : forall r, r ∈ D.fineLabels ->
      degreeLower <=
        (actualGPrimeRetainedFineActiveFiber N D keep r).card)
    (hcap : forall r, r ∈ D.fineLabels -> forall left,
      left ∈ actualGPrimeRetainedFineActiveFiber N D keep r ->
      (actualGPrimeFineNearRightFiber
        N D keep ballRadius r left).card <= nearCap) :
    D.fineLabels.card * (degreeLower * (degreeLower - nearCap)) <=
      actualGPrimeFineSeparatedPairMass N D keep ballRadius := by
  unfold actualGPrimeFineSeparatedPairMass
  calc
    D.fineLabels.card * (degreeLower * (degreeLower - nearCap)) =
        ∑ _r ∈ D.fineLabels,
          degreeLower * (degreeLower - nearCap) := by simp
    _ <= ∑ r ∈ D.fineLabels,
        (actualGPrimeRetainedFineActiveFiber N D keep r).card *
          ((actualGPrimeRetainedFineActiveFiber N D keep r).card -
            nearCap) := by
      apply Finset.sum_le_sum
      intro r hr
      exact Nat.mul_le_mul (hdegree r hr)
        (Nat.sub_le_sub_right (hdegree r hr) nearCap)
    _ <= ∑ r ∈ D.fineLabels,
        (actualGPrimeFineSeparatedPairsAt
          N D keep ballRadius r).card :=
      Finset.sum_le_sum fun r hr =>
        actualGPrimeFineActive_card_mul_tsub_nearCap_le_separated_card
          N D keep ballRadius r nearCap (hcap r hr)

theorem fineLabels_mul_degreeLower_mul_tsub_automaticNearCap_le_mass
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (degreeLower : Nat)
    (hdegree : forall r, r ∈ D.fineLabels ->
      degreeLower <=
        (actualGPrimeRetainedFineActiveFiber N D keep r).card)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (hnearRadiusLower : N.delta <= 10 * ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= N.ceiling) :
    D.fineLabels.card *
        (degreeLower *
          (degreeLower - automaticCanonicalNearCap N ballRadius)) <=
      actualGPrimeFineSeparatedPairMass N D keep ballRadius := by
  apply fineLabels_mul_degreeLower_mul_tsub_nearCap_le_mass
    N D keep ballRadius degreeLower
      (automaticCanonicalNearCap N ballRadius) hdegree
  intro r hr left hleft
  exact actualGPrimeFineNearRightFiber_card_le_automatic
    N D keep ballRadius r hsymm hnearRadiusLower hnearRadiusUpper left hleft

/-- With the trivial retention predicate, a fine active fibre is exactly the
projected active-at-point fibre as soon as that fibre lies in the canonical
family. -/
theorem actualGPrimeRetainedFineActiveFiber_true_eq_activeAtPoint
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (r : fineLabel) (hr : r ∈ D.fineLabels)
    (hsubset :
      D.shading.activeAtPoint (D.pointAt r) ⊆ N.family) :
    actualGPrimeRetainedFineActiveFiber N D (fun _ _ => True) r =
      D.shading.activeAtPoint (D.pointAt r) := by
  classical
  ext i
  constructor
  · intro hi
    have hiData := (mem_actualGPrimeRetainedFineActiveFiber_iff
      N D (fun _ _ => True) r i).mp hi
    have hgood := (D.mem_retainedGoodPairs_iff
      (fun _ _ => True)).mp hiData.1 |>.1
    exact (D.shading.mem_activeAtPoint (D.pointAt r) i).mpr
      ⟨hgood.1, hgood.2.2⟩
  · intro hi
    have hiData := (D.shading.mem_activeAtPoint
      (D.pointAt r) i).mp hi
    apply (mem_actualGPrimeRetainedFineActiveFiber_iff
      N D (fun _ _ => True) r i).mpr
    constructor
    · apply (D.mem_retainedGoodPairs_iff (fun _ _ => True)).mpr
      exact ⟨⟨hiData.1, hr, hiData.2⟩, trivial⟩
    · exact hsubset hi

/-- The literal E2 dyadic degree lower transfers without loss to the
label-first active fibre under the same canonical-family inclusion. -/
theorem pyzE2DegreeLower_le_actualGPrimeRetainedFineActiveFiber_true
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (label : Int) (r : fineLabel) (hr : r ∈ D.fineLabels)
    (hcell : D.pointAt r ∈
      projectedPositiveMultiplicityDyadicCell D.shading label)
    (hactive :
      (D.shading.activeAtPoint (D.pointAt r)).Nonempty)
    (hsubset :
      D.shading.activeAtPoint (D.pointAt r) ⊆ N.family) :
    pyzE2DegreeLower label <=
      (actualGPrimeRetainedFineActiveFiber
        N D (fun _ _ => True) r).card := by
  rw [actualGPrimeRetainedFineActiveFiber_true_eq_activeAtPoint
    N D r hr hsubset]
  exact pyzE2DegreeLower_le_active_card_of_mem_cell
    D.shading label (D.pointAt r) hcell hactive
/-- The active-product definition is the same as filtering the ambient
canonical square by common fine-label membership. -/
theorem actualGPrimeFineSeparatedPairsAt_eq_family_filter
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (r : fineLabel) :
    actualGPrimeFineSeparatedPairsAt N D keep ballRadius r =
      (by
        classical
        exact (N.family.product N.family).filter fun pair : iota × iota =>
          canonicalTenRadiusSeparated N ballRadius pair.1 pair.2 ∧
          pair.1 ∈ actualGPrimeRetainedFineActiveFiber N D keep r ∧
          pair.2 ∈ actualGPrimeRetainedFineActiveFiber N D keep r) := by
  classical
  ext pair
  constructor
  · intro hpair
    have hdata := Finset.mem_filter.mp hpair
    have hactive := Finset.mem_product.mp hdata.1
    have hleftN := (mem_actualGPrimeRetainedFineActiveFiber_iff
      N D keep r pair.1).mp hactive.1 |>.2
    have hrightN := (mem_actualGPrimeRetainedFineActiveFiber_iff
      N D keep r pair.2).mp hactive.2 |>.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hleftN, hrightN⟩,
        hdata.2, hactive.1, hactive.2⟩
  · intro hpair
    have hdata := Finset.mem_filter.mp hpair
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hdata.2.2.1, hdata.2.2.2⟩,
        hdata.2.1⟩

/-- Exact Fubini identity: summing separated pairs label first equals summing,
over separated centre pairs, their number of common retained fine labels. -/
theorem actualGPrimeFineSeparatedPairMass_eq_centerPairMass
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real) :
    actualGPrimeFineSeparatedPairMass N D keep ballRadius =
      actualGPrimeFineSeparatedCenterPairMass N D keep ballRadius := by
  classical
  symm
  unfold actualGPrimeFineSeparatedCenterPairMass
  unfold richSeparatedPairCountTotal
  simp only [richSeparatedCenterPairs, and_true, Finset.sum_filter]
  calc
    (∑ pair ∈ N.family.product N.family,
        if canonicalTenRadiusSeparated N ballRadius pair.1 pair.2 then
          (actualGPrimeCommonFineCenterLabels
            N D keep pair.1 pair.2).card else 0) =
      ∑ pair ∈ N.family.product N.family,
        ∑ r ∈ D.fineLabels,
          if canonicalTenRadiusSeparated N ballRadius pair.1 pair.2 ∧
              pair.1 ∈ actualGPrimeRetainedFineActiveFiber N D keep r ∧
              pair.2 ∈ actualGPrimeRetainedFineActiveFiber N D keep r
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro pair hpair
      by_cases hsep :
          canonicalTenRadiusSeparated N ballRadius pair.1 pair.2
      · simp only [hsep, if_true, true_and]
        rw [Finset.card_eq_sum_ones]
        simp only [actualGPrimeCommonFineCenterLabels, Finset.sum_filter]
      · simp [hsep]
    _ = ∑ r ∈ D.fineLabels,
        ∑ pair ∈ N.family.product N.family,
          if canonicalTenRadiusSeparated N ballRadius pair.1 pair.2 ∧
              pair.1 ∈ actualGPrimeRetainedFineActiveFiber N D keep r ∧
              pair.2 ∈ actualGPrimeRetainedFineActiveFiber N D keep r
          then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ D.fineLabels,
        (actualGPrimeFineSeparatedPairsAt
          N D keep ballRadius r).card := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [actualGPrimeFineSeparatedPairsAt_eq_family_filter,
        Finset.card_eq_sum_ones]
      simp only [Finset.sum_filter]
    _ = actualGPrimeFineSeparatedPairMass N D keep ballRadius := rfl

/-- Common fine labels already present at the two centres inject into the
same-fine cross-edge mass of their radius balls. -/
theorem commonFineCenterLabels_card_le_commonFineEdgeMass
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) (hballRadiusLower : N.delta <= ballRadius) :
    (actualGPrimeCommonFineCenterLabels N D keep left right).card <=
      actualGPrimeCommonFineEdgeMass
        N D keep left right ballRadius := by
  classical
  rw [Finset.card_eq_sum_ones]
  unfold actualGPrimeCommonFineEdgeMass
  calc
    (∑ r ∈ actualGPrimeCommonFineCenterLabels N D keep left right, 1) <=
      ∑ r ∈ actualGPrimeCommonFineCenterLabels N D keep left right,
        (actualGPrimeRetainedFineMetricNeighbors
          N D keep left ballRadius r).card *
        (actualGPrimeRetainedFineMetricNeighbors
          N D keep right ballRadius r).card := by
      apply Finset.sum_le_sum
      intro r hr
      have hrData := (mem_actualGPrimeCommonFineCenterLabels_iff
        N D keep left right r).mp hr
      have hleftData := (mem_actualGPrimeRetainedFineActiveFiber_iff
        N D keep r left).mp hrData.2.1
      have hrightData := (mem_actualGPrimeRetainedFineActiveFiber_iff
        N D keep r right).mp hrData.2.2
      let leftInFamily : N.family := ⟨left, hleftData.2⟩
      let rightInFamily : N.family := ⟨right, hrightData.2⟩
      have hleftMem : leftInFamily ∈
          actualGPrimeRetainedFineMetricNeighbors
            N D keep left ballRadius r := by
        apply (mem_actualGPrimeRetainedFineMetricNeighbors_iff
          N D keep left ballRadius r leftInFamily).mpr
        exact ⟨hleftData.1,
          (N.self_le_delta left hleftData.2).trans hballRadiusLower⟩
      have hrightMem : rightInFamily ∈
          actualGPrimeRetainedFineMetricNeighbors
            N D keep right ballRadius r := by
        apply (mem_actualGPrimeRetainedFineMetricNeighbors_iff
          N D keep right ballRadius r rightInFamily).mpr
        exact ⟨hrightData.1,
          (N.self_le_delta right hrightData.2).trans hballRadiusLower⟩
      have hleftPos : 0 < (actualGPrimeRetainedFineMetricNeighbors
          N D keep left ballRadius r).card :=
        Finset.card_pos.mpr ⟨leftInFamily, hleftMem⟩
      have hrightPos : 0 < (actualGPrimeRetainedFineMetricNeighbors
          N D keep right ballRadius r).card :=
        Finset.card_pos.mpr ⟨rightInFamily, hrightMem⟩
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
        (Nat.ne_of_gt hleftPos) (Nat.ne_of_gt hrightPos))
    _ <= ∑ r ∈ D.fineLabels,
        (actualGPrimeRetainedFineMetricNeighbors
          N D keep left ballRadius r).card *
        (actualGPrimeRetainedFineMetricNeighbors
          N D keep right ballRadius r).card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr
        exact (mem_actualGPrimeCommonFineCenterLabels_iff
          N D keep left right r).mp hr |>.1
      · intro r hr hnot
        exact Nat.zero_le _

/-- Output of the fine-label-first mass selector. The average inequality is
denominator-free and the selected canonical balls already have genuine
bilateral same-fine support. -/
structure ActualGPrimeFineSeparatedBallPairOutcome
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (degreeLower : Nat) where
  left : iota
  right : iota
  left_mem : left ∈ N.family
  right_mem : right ∈ N.family
  centers_separated :
    canonicalTenRadiusSeparated N ballRadius left right
  average_edge_mass :
    D.fineLabels.card *
        (degreeLower *
          (degreeLower - automaticCanonicalNearCap N ballRadius)) <=
      (richSeparatedCenterPairs N.family
        (canonicalTenRadiusSeparated N ballRadius)
        (fun _ _ => True)).card *
      actualGPrimeCommonFineEdgeMass
        N D keep left right ballRadius
  bilateral :
    (actualGPrimeBilateralRetainedFineLabels
      N D keep left right ballRadius).Nonempty
  cross_separated :
    FiniteFamiliesCrossSeparated N.distance (8 * ballRadius)
      (finiteFamilyMetricBall N.family N.distance ballRadius left)
      (finiteFamilyMetricBall N.family N.distance ballRadius right)
  left_ball_card :
    ((finiteFamilyMetricBall N.family N.distance
      ballRadius left).card : Real) <=
      (ballRadius / N.criticalScale) ^ N.exponent *
        ((N.criticalBall.card : Nat) : Real)
  right_ball_card :
    ((finiteFamilyMetricBall N.family N.distance
      ballRadius right).card : Real) <=
      (ballRadius / N.criticalScale) ^ N.exponent *
        ((N.criticalBall.card : Nat) : Real)

/-- Active degree strictly above the automatic near cap produces a separated
canonical ball pair with positive same-fine edge mass and exact finite-average
control. -/
theorem exists_actualGPrimeFineSeparatedBallPairOutcome
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (degreeLower : Nat)
    (hfineLabels : D.fineLabels.Nonempty)
    (hdegree : forall r, r ∈ D.fineLabels ->
      degreeLower <=
        (actualGPrimeRetainedFineActiveFiber N D keep r).card)
    (hroom : automaticCanonicalNearCap N ballRadius < degreeLower)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (htriangle : forall x center y,
      N.distance x y <= N.distance x center + N.distance center y)
    (hnearRadiusLower : N.delta <= 10 * ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= N.ceiling)
    (hballRadiusLower : N.delta <= ballRadius)
    (hballRadiusUpper : ballRadius <= N.ceiling) :
    Nonempty (ActualGPrimeFineSeparatedBallPairOutcome
      N D keep ballRadius degreeLower) := by
  let lowerBound := D.fineLabels.card *
    (degreeLower *
      (degreeLower - automaticCanonicalNearCap N ballRadius))
  have hlowerBound : 0 < lowerBound := by
    unfold lowerBound
    exact Nat.mul_pos (Finset.card_pos.mpr hfineLabels)
      (Nat.mul_pos (Nat.zero_lt_of_lt hroom)
        (Nat.sub_pos_of_lt hroom))
  have hlabelMass : lowerBound <=
      actualGPrimeFineSeparatedPairMass N D keep ballRadius := by
    exact fineLabels_mul_degreeLower_mul_tsub_automaticNearCap_le_mass
      N D keep ballRadius degreeLower hdegree hsymm
        hnearRadiusLower hnearRadiusUpper
  have hcenterMass : lowerBound <=
      actualGPrimeFineSeparatedCenterPairMass N D keep ballRadius := by
    rw [← actualGPrimeFineSeparatedPairMass_eq_centerPairMass]
    exact hlabelMass
  obtain ⟨left, hleft, right, hright, hseparated, _htrue, havg⟩ :=
    exists_richSeparated_pair_of_pos_totalCount_lower
      N.family (canonicalTenRadiusSeparated N ballRadius)
      (fun _ _ => True)
      (fun x y =>
        (actualGPrimeCommonFineCenterLabels N D keep x y).card)
      hlowerBound (by
        simpa only [actualGPrimeFineSeparatedCenterPairMass] using
          hcenterMass)
  have hcenterEdge :
      (actualGPrimeCommonFineCenterLabels N D keep left right).card <=
        actualGPrimeCommonFineEdgeMass
          N D keep left right ballRadius :=
    commonFineCenterLabels_card_le_commonFineEdgeMass
      N D keep left right ballRadius hballRadiusLower
  have havgEdge : lowerBound <=
      (richSeparatedCenterPairs N.family
        (canonicalTenRadiusSeparated N ballRadius)
        (fun _ _ => True)).card *
      actualGPrimeCommonFineEdgeMass
        N D keep left right ballRadius :=
    havg.trans (Nat.mul_le_mul_left _ hcenterEdge)
  have hedgePos : 0 < actualGPrimeCommonFineEdgeMass
      N D keep left right ballRadius := by
    by_contra hedge
    have hedgeZero : actualGPrimeCommonFineEdgeMass
        N D keep left right ballRadius = 0 := Nat.eq_zero_of_not_pos hedge
    rw [hedgeZero, Nat.mul_zero] at havgEdge
    exact (Nat.not_succ_le_zero 0) (hlowerBound.trans_le havgEdge)
  have hbilateral :=
    (actualGPrimeCommonFineEdgeMass_pos_iff_bilateral_nonempty
      N D keep left right ballRadius).mp hedgePos
  have hballs := canonicalMetricBallPair_crossSeparated_and_card_bounds
    N hsymm htriangle hballRadiusLower hballRadiusUpper
      left right hleft hright hseparated
  exact ⟨{
    left := left
    right := right
    left_mem := hleft
    right_mem := hright
    centers_separated := hseparated
    average_edge_mass := by simpa only [lowerBound] using havgEdge
    bilateral := hbilateral
    cross_separated := hballs.1
    left_ball_card := hballs.2.1
    right_ball_card := hballs.2.2
  }⟩

/-- E2-ready endpoint: uniform membership in one positive multiplicity cell,
together with the actual canonical-family inclusion, supplies every degree
input of the fine-label separated-ball selector. -/
theorem exists_actualGPrimeFineSeparatedBallPairOutcome_of_E2
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (label : Int) (ballRadius : Real)
    (hfineLabels : D.fineLabels.Nonempty)
    (hcell : forall r, r ∈ D.fineLabels ->
      D.pointAt r ∈
        projectedPositiveMultiplicityDyadicCell D.shading label)
    (hactive : forall r, r ∈ D.fineLabels ->
      (D.shading.activeAtPoint (D.pointAt r)).Nonempty)
    (hsubset : forall r, r ∈ D.fineLabels ->
      D.shading.activeAtPoint (D.pointAt r) ⊆ N.family)
    (hroom :
      automaticCanonicalNearCap N ballRadius <
        pyzE2DegreeLower label)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (htriangle : forall x center y,
      N.distance x y <= N.distance x center + N.distance center y)
    (hnearRadiusLower : N.delta <= 10 * ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= N.ceiling)
    (hballRadiusLower : N.delta <= ballRadius)
    (hballRadiusUpper : ballRadius <= N.ceiling) :
    Nonempty (ActualGPrimeFineSeparatedBallPairOutcome
      N D (fun _ _ => True) ballRadius (pyzE2DegreeLower label)) := by
  apply exists_actualGPrimeFineSeparatedBallPairOutcome
    N D (fun _ _ => True) ballRadius (pyzE2DegreeLower label)
      hfineLabels
  · intro r hr
    exact pyzE2DegreeLower_le_actualGPrimeRetainedFineActiveFiber_true
      N D label r hr (hcell r hr) (hactive r hr) (hsubset r hr)
  · exact hroom
  · exact hsymm
  · exact htriangle
  · exact hnearRadiusLower
  · exact hnearRadiusUpper
  · exact hballRadiusLower
  · exact hballRadiusUpper

#print axioms actualGPrimeRetainedFineActiveFiber_true_eq_activeAtPoint
#print axioms pyzE2DegreeLower_le_actualGPrimeRetainedFineActiveFiber_true
#print axioms exists_actualGPrimeFineSeparatedBallPairOutcome_of_E2
#print axioms actualGPrimeFineSeparatedPairMass_eq_centerPairMass
#print axioms commonFineCenterLabels_card_le_commonFineEdgeMass
#print axioms exists_actualGPrimeFineSeparatedBallPairOutcome
#print axioms actualGPrimeFineNearRightFiber_card_le_automatic
#print axioms actualGPrimeFineActive_card_mul_tsub_nearCap_le_separated_card
#print axioms fineLabels_mul_degreeLower_mul_tsub_automaticNearCap_le_mass

end

end FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
