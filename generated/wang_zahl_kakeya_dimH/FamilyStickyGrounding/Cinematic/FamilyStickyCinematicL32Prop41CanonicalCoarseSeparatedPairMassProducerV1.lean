import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassLowerV1

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassProducerV1

open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32Lemma57FiniteTwoEndsMaximizerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassLowerV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1

open scoped BigOperators

noncomputable section

universe u v w

/-!
# Actual producer for the global separated-pair mass

This module joins the exact pair subtraction from the companion `MassLower`
module to two genuine sources: canonical norm non-concentration and retained
`G'` incidence mass with the paper's `q`-degree upper window.

The output is the literal `canonicalCoarseRichSeparatedPairCountTotal` lower
bound required by the existing rich-ball consumer.  No separated total or
equivalent callback is an input.
-/

/-- On a selected rectangle whose literal coarse fibre lies in the canonical
family, the active fibre is exactly the literal `F(R)`. -/
theorem canonicalCoarseActiveFiber_eq_coarseCurveIndexFiber_of_subset
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (hsubset : D.coarseCurveIndexFiber keep R ⊆ N.family) :
    canonicalCoarseActiveFiber N D keep R =
      D.coarseCurveIndexFiber keep R := by
  exact Finset.inter_eq_left.mpr hsubset

/-- Every non-separated right endpoint lies in the closed canonical
`10 * ballRadius` ball around the fixed left endpoint.  The strict complement
of `10r <= distance` is deliberately weakened to closed-ball membership. -/
theorem canonicalCoarseNearRightFiber_subset_tenRadiusBall
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (R : C2GraphRectangle)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (left : iota) :
    canonicalCoarseNearRightFiber N D keep ballRadius R left ⊆
      finiteFamilyMetricBall N.family N.distance (10 * ballRadius) left := by
  intro right hright
  have hrightData :
      right ∈ canonicalCoarseActiveFiber N D keep R ∧
        ¬canonicalTenRadiusSeparated N ballRadius left right := by
    simpa only [canonicalCoarseNearRightFiber, Finset.mem_filter] using hright
  have hrightN : right ∈ N.family :=
    (Finset.mem_inter.mp hrightData.1).2
  have hnotSeparated :
      ¬10 * ballRadius <= N.distance left right := by
    simpa only [canonicalTenRadiusSeparated] using hrightData.2
  have hdistance : N.distance right left <= 10 * ballRadius := by
    calc
      N.distance right left = N.distance left right := hsymm right left
      _ <= 10 * ballRadius := (lt_of_not_ge hnotSeparated).le
  simpa only [finiteFamilyMetricBall, Finset.mem_filter] using
    And.intro hrightN hdistance

/-- The canonical maximizer's genuine non-concentration estimate supplies a
uniform natural-number cap for every coarse near-right fibre.  The only new
quantitative input is the scalar comparison of its explicit rpow upper bound
with `nearCap`. -/
theorem canonicalCoarseNearRightFiber_card_le_of_nonconcentration
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (R : C2GraphRectangle)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (hnearRadiusLower : N.delta <= 10 * ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= N.ceiling)
    (nearCap : Nat)
    (hnumeric :
      ((10 * ballRadius) / N.criticalScale) ^ N.exponent *
          ((N.criticalBall.card : Nat) : Real) <= (nearCap : Real))
    (left : iota) (hleft : left ∈ N.family) :
    (canonicalCoarseNearRightFiber N D keep ballRadius R left).card <=
      nearCap := by
  have hsubset := canonicalCoarseNearRightFiber_subset_tenRadiusBall
    N D keep ballRadius R hsymm left
  have hnearNat :
      (canonicalCoarseNearRightFiber N D keep ballRadius R left).card <=
        (finiteFamilyMetricBall N.family N.distance
          (10 * ballRadius) left).card :=
    Finset.card_le_card hsubset
  have hballReal :
      ((finiteFamilyMetricBall N.family N.distance
        (10 * ballRadius) left).card : Real) <=
      ((10 * ballRadius) / N.criticalScale) ^ N.exponent *
        ((N.criticalBall.card : Nat) : Real) := by
    simpa only [finiteBallCount, finiteFamilyMetricBall] using
      N.card_le_ratio_rpow hnearRadiusLower hnearRadiusUpper left hleft
  have hnearReal :
      ((canonicalCoarseNearRightFiber N D keep ballRadius R left).card : Real) <=
        (nearCap : Real) := by
    have hnearCast :
        ((canonicalCoarseNearRightFiber N D keep ballRadius R left).card : Real) <=
          ((finiteFamilyMetricBall N.family N.distance
            (10 * ballRadius) left).card : Real) := by
      exact_mod_cast hnearNat
    exact hnearCast.trans (hballReal.trans hnumeric)
  exact_mod_cast hnearReal

/-- The upper half of the paper's `q`-uniform degree window bounds the number
of retained incidences over one coarse rectangle by `qUpper * #F(R)`. -/
theorem coarseIncidencePairs_card_le_curveFiber_card_mul_degreeUpper
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (degreeUpper : Nat)
    (hdegree : forall i, i ∈ D.coarseCurveIndexFiber keep R ->
      ((D.coarseIncidencePairs keep R).filter fun pair =>
        pair.1 = i).card <= degreeUpper) :
    (D.coarseIncidencePairs keep R).card <=
      (D.coarseCurveIndexFiber keep R).card * degreeUpper := by
  rw [D.coarseIncidencePairs_card_eq_sum_curve keep R]
  calc
    (∑ i ∈ D.coarseCurveIndexFiber keep R,
        ((D.coarseIncidencePairs keep R).filter fun pair =>
          pair.1 = i).card) <=
      ∑ _i ∈ D.coarseCurveIndexFiber keep R, degreeUpper :=
        Finset.sum_le_sum fun i hi => hdegree i hi
    _ = (D.coarseCurveIndexFiber keep R).card * degreeUpper := by
      simp

/-- Selected retained `G'` mass and the degree upper bound give an actual
lower bound for the total curve-fibre membership, with exactly one integer
division by `degreeUpper`. -/
theorem retainedMass_div_degreeUpper_le_sum_coarseCurveFiber_card
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (massLower degreeUpper : Nat)
    (hmass : massLower <= (retainedGoodPairsOver D keep rectangles).card)
    (hdegree : forall R, R ∈ rectangles -> forall i,
      i ∈ D.coarseCurveIndexFiber keep R ->
        ((D.coarseIncidencePairs keep R).filter fun pair =>
          pair.1 = i).card <= degreeUpper) :
    massLower / degreeUpper <=
      ∑ R ∈ rectangles, (D.coarseCurveIndexFiber keep R).card := by
  apply Nat.div_le_of_le_mul
  calc
    massLower <= (retainedGoodPairsOver D keep rectangles).card := hmass
    _ = ∑ R ∈ rectangles, (D.coarseIncidencePairs keep R).card :=
      retainedGoodPairsOver_card_eq_sum_coarseIncidencePairs D keep rectangles
    _ <= ∑ R ∈ rectangles,
        (D.coarseCurveIndexFiber keep R).card * degreeUpper :=
      Finset.sum_le_sum fun R hR =>
        coarseIncidencePairs_card_le_curveFiber_card_mul_degreeUpper
          D keep R degreeUpper (hdegree R hR)
    _ = (∑ R ∈ rectangles,
        (D.coarseCurveIndexFiber keep R).card) * degreeUpper := by
      rw [Finset.sum_mul]
    _ = degreeUpper * (∑ R ∈ rectangles,
        (D.coarseCurveIndexFiber keep R).card) := Nat.mul_comm _ _

/-- Summing the fibrewise near-pair subtraction.  This is where the loss from
all pairs to separated pairs appears explicitly as `richness - nearCap`. -/
theorem richness_tsub_nearCap_mul_sum_activeFiber_card_le_sum_separated
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (rectangles : Finset C2GraphRectangle) (richness nearCap : Nat)
    (hrichness : forall R, R ∈ rectangles ->
      richness <= (canonicalCoarseActiveFiber N D keep R).card)
    (hcap : forall R, R ∈ rectangles -> forall left,
      left ∈ canonicalCoarseActiveFiber N D keep R ->
        (canonicalCoarseNearRightFiber N D keep ballRadius R left).card <=
          nearCap) :
    (richness - nearCap) *
        (∑ R ∈ rectangles, (canonicalCoarseActiveFiber N D keep R).card) <=
      ∑ R ∈ rectangles,
        (canonicalCoarseSeparatedPairsAt N D keep ballRadius R).card := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun R hR => by
    have hgap : richness - nearCap <=
        (canonicalCoarseActiveFiber N D keep R).card - nearCap :=
      Nat.sub_le_sub_right (hrichness R hR) nearCap
    calc
      (richness - nearCap) *
          (canonicalCoarseActiveFiber N D keep R).card =
        (canonicalCoarseActiveFiber N D keep R).card *
          (richness - nearCap) := Nat.mul_comm _ _
      _ <= (canonicalCoarseActiveFiber N D keep R).card *
          ((canonicalCoarseActiveFiber N D keep R).card - nearCap) :=
        Nat.mul_le_mul_left _ hgap
      _ <= (canonicalCoarseSeparatedPairsAt N D keep ballRadius R).card :=
        activeFiber_card_mul_tsub_nearCap_le_separatedPairsAt_card
          N D keep ballRadius R nearCap (hcap R hR)

/-- The explicit lower bound produced from the paper-level mass, degree, and
near-pair inputs. -/
def canonicalCoarseSeparatedPairProducedLower
    (richness nearCap massLower degreeUpper : Nat) : Nat :=
  (richness - nearCap) * (massLower / degreeUpper)

/-- Main producer: source-level retained mass, q-uniform degree, richness,
and canonical non-concentration imply the actual global separated-pair sum
lower bound consumed by `exists_canonical_coarse_richSeparated_ballPair`. -/
theorem canonicalCoarseSeparatedPairProducedLower_le_total
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (rectangles : Finset C2GraphRectangle)
    (richness nearCap massLower degreeUpper : Nat)
    (hrectangles : rectangles ⊆ D.coarseRectangleFamily)
    (hfiberSubset : forall R, R ∈ rectangles ->
      D.coarseCurveIndexFiber keep R ⊆ N.family)
    (hmass : massLower <= (retainedGoodPairsOver D keep rectangles).card)
    (hdegree : forall R, R ∈ rectangles -> forall i,
      i ∈ D.coarseCurveIndexFiber keep R ->
        ((D.coarseIncidencePairs keep R).filter fun pair =>
          pair.1 = i).card <= degreeUpper)
    (hrichness : forall R, R ∈ rectangles ->
      richness <= (D.coarseCurveIndexFiber keep R).card)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (hnearRadiusLower : N.delta <= 10 * ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= N.ceiling)
    (hnumeric :
      ((10 * ballRadius) / N.criticalScale) ^ N.exponent *
          ((N.criticalBall.card : Nat) : Real) <= (nearCap : Real)) :
    canonicalCoarseSeparatedPairProducedLower
        richness nearCap massLower degreeUpper <=
      canonicalCoarseRichSeparatedPairCountTotal N D keep ballRadius := by
  have hcurveMass :=
    retainedMass_div_degreeUpper_le_sum_coarseCurveFiber_card
      D keep rectangles massLower degreeUpper hmass hdegree
  have hactiveEq : forall R, R ∈ rectangles ->
      canonicalCoarseActiveFiber N D keep R =
        D.coarseCurveIndexFiber keep R := fun R hR =>
    canonicalCoarseActiveFiber_eq_coarseCurveIndexFiber_of_subset
      N D keep R (hfiberSubset R hR)
  have hactiveMass : massLower / degreeUpper <=
      ∑ R ∈ rectangles, (canonicalCoarseActiveFiber N D keep R).card := by
    calc
      massLower / degreeUpper <=
          ∑ R ∈ rectangles, (D.coarseCurveIndexFiber keep R).card := hcurveMass
      _ = ∑ R ∈ rectangles,
          (canonicalCoarseActiveFiber N D keep R).card := by
        apply Finset.sum_congr rfl
        intro R hR
        exact congrArg Finset.card (hactiveEq R hR).symm
  have hactiveRichness : forall R, R ∈ rectangles ->
      richness <= (canonicalCoarseActiveFiber N D keep R).card := by
    intro R hR
    rw [hactiveEq R hR]
    exact hrichness R hR
  have hnearCaps : forall R, R ∈ rectangles -> forall left,
      left ∈ canonicalCoarseActiveFiber N D keep R ->
        (canonicalCoarseNearRightFiber N D keep ballRadius R left).card <=
          nearCap := by
    intro R hR left hleft
    exact canonicalCoarseNearRightFiber_card_le_of_nonconcentration
      N D keep ballRadius R hsymm hnearRadiusLower hnearRadiusUpper
        nearCap hnumeric left (Finset.mem_inter.mp hleft).2
  have hselected :=
    richness_tsub_nearCap_mul_sum_activeFiber_card_le_sum_separated
      N D keep ballRadius rectangles richness nearCap
        hactiveRichness hnearCaps
  have hselectedLeFull :
      (∑ R ∈ rectangles,
          (canonicalCoarseSeparatedPairsAt N D keep ballRadius R).card) <=
        ∑ R ∈ D.coarseRectangleFamily,
          (canonicalCoarseSeparatedPairsAt N D keep ballRadius R).card :=
    Finset.sum_le_sum_of_subset hrectangles
  unfold canonicalCoarseSeparatedPairProducedLower
  calc
    (richness - nearCap) * (massLower / degreeUpper) <=
        (richness - nearCap) *
          (∑ R ∈ rectangles,
            (canonicalCoarseActiveFiber N D keep R).card) :=
      Nat.mul_le_mul_left _ hactiveMass
    _ <= ∑ R ∈ rectangles,
        (canonicalCoarseSeparatedPairsAt N D keep ballRadius R).card := hselected
    _ <= ∑ R ∈ D.coarseRectangleFamily,
        (canonicalCoarseSeparatedPairsAt N D keep ballRadius R).card :=
      hselectedLeFull
    _ = canonicalCoarseRichSeparatedPairCountTotal N D keep ballRadius :=
      (canonicalCoarseRichSeparatedPairCountTotal_eq_sum_separatedPairsAt
        N D keep ballRadius).symm

/-- Positivity is not hidden: it requires strict room after near-pair
subtraction and at least one full degree block of retained mass. -/
theorem canonicalCoarseSeparatedPairProducedLower_pos
    (richness nearCap massLower degreeUpper : Nat)
    (hnear : nearCap < richness)
    (hdegreePos : 0 < degreeUpper)
    (hdegreeMass : degreeUpper <= massLower) :
    0 < canonicalCoarseSeparatedPairProducedLower
      richness nearCap massLower degreeUpper := by
  exact Nat.mul_pos (Nat.sub_pos_iff_lt.mpr hnear)
    (Nat.div_pos hdegreeMass hdegreePos)

#print axioms canonicalCoarseActiveFiber_eq_coarseCurveIndexFiber_of_subset
#print axioms canonicalCoarseNearRightFiber_subset_tenRadiusBall
#print axioms canonicalCoarseNearRightFiber_card_le_of_nonconcentration
#print axioms coarseIncidencePairs_card_le_curveFiber_card_mul_degreeUpper
#print axioms retainedMass_div_degreeUpper_le_sum_coarseCurveFiber_card
#print axioms richness_tsub_nearCap_mul_sum_activeFiber_card_le_sum_separated
#print axioms canonicalCoarseSeparatedPairProducedLower_le_total
#print axioms canonicalCoarseSeparatedPairProducedLower_pos

end

end FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassProducerV1
