import FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
import FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
import FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyPyzActualPositiveCenterHighPairCarrierV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1

noncomputable section

universe u v

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# The genuine finite pair carrier in the positive-centre high branch

The canonical payload stores a literal point of its selected `E₂` cell.
This module exposes the active indices at that point, transports them
losslessly to actual tubes under the already available essential-distinctness
input, and selects every unordered distinct pair of those tubes.

This is deliberately only the finite selection boundary before the PYZ
shift lemma.  It does not manufacture the two shifted intersections,
rectangles, or `PairLocalActualLensRectangleData` certificates required by
the Proposition 4.1 consumer.
-/

/-- An orientation of one unordered non-diagonal first-generation pair. -/
structure FirstGenerationPairOrientation
    {curve : Type*} [DecidableEq curve] (curves : Finset curve)
    (p : FirstGenerationCurvePair curves) where
  first : FirstGenerationCurve curves
  second : FirstGenerationCurve curves
  pair_eq : p.1 = s(first, second)
  first_ne_second : first ≠ second

/-- Every unordered non-diagonal pair admits an orientation. -/
theorem nonempty_firstGenerationPairOrientation
    {curve : Type*} [DecidableEq curve] (curves : Finset curve)
    (p : FirstGenerationCurvePair curves) :
    Nonempty (FirstGenerationPairOrientation curves p) := by
  have hrepresentative : ∃ first second : FirstGenerationCurve curves,
      p.1 = s(first, second) := by
    refine Sym2.inductionOn p.1 ?_
    intro first second
    exact ⟨first, second, rfl⟩
  obtain ⟨first, second, hpair⟩ := hrepresentative
  have hne : first ≠ second := by
    intro heq
    apply p.2
    rw [hpair, Sym2.mk_isDiag_iff]
    exact heq
  exact ⟨{
    first := first
    second := second
    pair_eq := hpair
    first_ne_second := hne }⟩

/-- A fixed classical orientation, used only to feed the oriented pair API
of the tracked Proposition 4.1 consumer. -/
noncomputable def canonicalFirstGenerationPairOrientation
    {curve : Type*} [DecidableEq curve] (curves : Finset curve)
    (p : FirstGenerationCurvePair curves) :
    FirstGenerationPairOrientation curves p :=
  Classical.choice (nonempty_firstGenerationPairOrientation curves p)

/-- The full finite pair carrier has the expected binomial cardinality. -/
theorem allFirstGenerationPairs_card
    {curve : Type*} [DecidableEq curve] (curves : Finset curve) :
    (Finset.univ : Finset (FirstGenerationCurvePair curves)).card =
      Nat.choose curves.card 2 := by
  rw [Finset.card_univ]
  simpa only [FirstGenerationCurvePair, FirstGenerationCurve,
    Fintype.card_coe] using
    (Sym2.card_subtype_not_diag
      (α := FirstGenerationCurve curves))

/-- At the canonical payload point, the lower endpoint of the selected
`E₂` degree window is a genuine lower bound for the literal active fibre. -/
theorem degreeLower_le_payload_active_card
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure point) (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyExponent : Real)
    (payload : ActualPositiveCenterCanonicalPayload mu base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      tangencyExponent) :
    let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
      outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
      payload.tangencyLabel
    pyzE2DegreeLower payload.finalLabel ≤
      (Y1.activeAtPoint payload.q).card := by
  dsimp only
  obtain ⟨_hfinalLabel, hq, _hmeasure, _hEtPos, _hEtSubset,
      _htangencyBin, _hE2Pos, _hE2Measurable, _hE2Subset, hactive⟩ :=
    payload.certificate
  let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
    outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
    payload.tangencyLabel
  have hq' : payload.q ∈ projectedPositiveMultiplicityDyadicCell Y1
      payload.finalLabel := by
    simpa only [positiveCenterE2, Y1] using hq
  exact pyzE2DegreeLower_le_active_card_of_mem_cell Y1 payload.finalLabel
    payload.q hq' (hactive payload.q hq)

/-- A high payload produces an actual tube family of the same cardinality,
all of its unordered distinct pairs, a canonical orientation of every pair,
and the corresponding binomial pair-count lower bound. -/
theorem exists_highPayload_actualTubePairCarrier
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure point) (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyExponent : Real)
    (payload : ActualPositiveCenterCanonicalPayload mu base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      tangencyExponent)
    (degreeThreshold : Nat)
    (hhigh : degreeThreshold ≤ pyzE2DegreeLower payload.finalLabel)
    (hradius : 0 < radius)
    (hpair :
      let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
        outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
        payload.tangencyLabel
      Set.Pairwise (Y1.activeAtPoint payload.q : Set iota) (fun i j =>
        EssentiallyDistinct (fine.tubes i) (fine.tubes j))) :
    ∃ curves : Finset (Tube radius),
      curves = activeTubeImage fine
        ((positiveCenterY1 base hbase fine physical f f1 f2 outerA outerB
          hOuter hf hf1 globalScale globalCenter tangencyExponent
          payload.tangencyLabel).activeAtPoint payload.q) ∧
      degreeThreshold ≤ curves.card ∧
      Nat.choose degreeThreshold 2 ≤
        (Finset.univ : Finset (FirstGenerationCurvePair curves)).card ∧
      (Finset.univ : Finset (FirstGenerationCurvePair curves)).card =
        Nat.choose curves.card 2 ∧
      (∀ p : FirstGenerationCurvePair curves,
        p.1 = s((canonicalFirstGenerationPairOrientation curves p).first,
          (canonicalFirstGenerationPairOrientation curves p).second)) ∧
      (∀ p : FirstGenerationCurvePair curves,
        (canonicalFirstGenerationPairOrientation curves p).first ≠
          (canonicalFirstGenerationPairOrientation curves p).second) := by
  let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
    outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
    payload.tangencyLabel
  let active := Y1.activeAtPoint payload.q
  let curves := activeTubeImage fine active
  have hactiveLower : pyzE2DegreeLower payload.finalLabel ≤ active.card := by
    simpa only [Y1, active] using
      degreeLower_le_payload_active_card mu base hbase fine physical f f1 f2
        outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent payload
  have hcurvesCard : curves.card = active.card := by
    exact activeTubeImage_card fine active hradius (by
      simpa only [Y1, active] using hpair)
  have hthreshold : degreeThreshold ≤ curves.card := by
    rw [hcurvesCard]
    exact hhigh.trans hactiveLower
  have hpairsCard := allFirstGenerationPairs_card curves
  have hpairsLower : Nat.choose degreeThreshold 2 ≤
      (Finset.univ : Finset (FirstGenerationCurvePair curves)).card := by
    rw [hpairsCard]
    exact Nat.choose_le_choose 2 hthreshold
  refine ⟨curves, rfl, hthreshold, hpairsLower, hpairsCard, ?_, ?_⟩
  · intro p
    exact (canonicalFirstGenerationPairOrientation curves p).pair_eq
  · intro p
    exact (canonicalFirstGenerationPairOrientation curves p).first_ne_second

#print axioms FirstGenerationPairOrientation
#print axioms nonempty_firstGenerationPairOrientation
#print axioms canonicalFirstGenerationPairOrientation
#print axioms allFirstGenerationPairs_card
#print axioms degreeLower_le_payload_active_card
#print axioms exists_highPayload_actualTubePairCarrier

end

end FamilyStickyPyzActualPositiveCenterHighPairCarrierV1
