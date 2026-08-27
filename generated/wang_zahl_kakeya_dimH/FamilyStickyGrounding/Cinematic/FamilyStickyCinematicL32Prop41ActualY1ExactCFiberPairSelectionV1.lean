import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftPerturbationReadyV1

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualY1ExactCFiberPairSelectionV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftPerturbationReadyV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u v w

/-!
# Exact graph-`c` refinement for retained actual Y1 incidences

The positive-width graph-`c` buckets already present in the repository only
give an estimate `|c(T) - c(U)| <= eta`.  That estimate cannot supply the
literal equality consumed by `ActualTwoFamilyRectangleTangencyData`.

This module performs the honest finite refinement by the exact real value of
`tubeGraphC`.  It first records a reusable exact-fibre counting lemma.  It
then specializes that lemma both to retained incidences at one fine label and
to retained incidences over one coarse rectangle.  Pair producers filter an
exact fibre by the required coefficient separation; in the coarse version
they additionally filter for a common fine label.  No nonemptiness or
cardinality of these pair filters is asserted without the corresponding
witnesses.
-/

/-! ## Generic finite exact-value fibres -/

/-- Values actually attained by a finite source. -/
noncomputable def occupiedExactValues
    {alpha : Type u} {beta : Type v} [DecidableEq alpha]
    (source : Finset alpha) (value : alpha -> beta) : Finset beta := by
  classical
  exact source.image value

/-- The literal fibre of a finite source over one exact value. -/
noncomputable def exactValueFiber
    {alpha : Type u} {beta : Type v} [DecidableEq alpha]
    (source : Finset alpha) (value : alpha -> beta) (b : beta) :
    Finset alpha := by
  classical
  exact source.filter fun a => value a = b

@[simp]
theorem mem_occupiedExactValues_iff
    {alpha : Type u} {beta : Type v} [DecidableEq alpha]
    (source : Finset alpha) (value : alpha -> beta) (b : beta) :
    b ∈ occupiedExactValues source value <->
      ∃ a, a ∈ source ∧ value a = b := by
  classical
  simp [occupiedExactValues]

@[simp]
theorem mem_exactValueFiber_iff
    {alpha : Type u} {beta : Type v} [DecidableEq alpha]
    (source : Finset alpha) (value : alpha -> beta) (b : beta) (a : alpha) :
    a ∈ exactValueFiber source value b <->
      a ∈ source ∧ value a = b := by
  classical
  simp [exactValueFiber]

/-- Exact values partition the source with no loss. -/
theorem card_eq_sum_exactValueFiber
    {alpha : Type u} {beta : Type v} [DecidableEq alpha]
    (source : Finset alpha) (value : alpha -> beta) :
    source.card =
      ∑ b ∈ occupiedExactValues source value,
        (exactValueFiber source value b).card := by
  classical
  exact Finset.card_eq_sum_card_fiberwise (fun a ha => by
    exact (mem_occupiedExactValues_iff source value (value a)).mpr
      ⟨a, ha, rfl⟩)

/-- A largest occupied exact fibre retains the reciprocal of the number of
exact values actually present.  There is deliberately no fixed numerical
bound on that number for a real-valued map. -/
theorem exists_cardinalRetaining_exactValueFiber
    {alpha : Type u} {beta : Type v} [DecidableEq alpha]
    (source : Finset alpha) (value : alpha -> beta)
    (hsource : source.Nonempty) :
    exists b, b ∈ occupiedExactValues source value ∧
      (exactValueFiber source value b).Nonempty ∧
      source.card <=
        (occupiedExactValues source value).card *
          (exactValueFiber source value b).card := by
  classical
  let labels := occupiedExactValues source value
  let fiberCard : beta -> Nat := fun b =>
    (exactValueFiber source value b).card
  have hlabels : labels.Nonempty := by
    obtain ⟨a, ha⟩ := hsource
    exact ⟨value a, (mem_occupiedExactValues_iff source value (value a)).mpr
      ⟨a, ha, rfl⟩⟩
  obtain ⟨b, hb, hmax⟩ :=
    Finset.exists_max_image labels fiberCard hlabels
  have hfiber : (exactValueFiber source value b).Nonempty := by
    obtain ⟨a, ha, hab⟩ :=
      (mem_occupiedExactValues_iff source value b).mp hb
    exact ⟨a, (mem_exactValueFiber_iff source value b a).mpr ⟨ha, hab⟩⟩
  have hcard : source.card <= labels.card * fiberCard b := by
    calc
      source.card = ∑ c ∈ labels, fiberCard c := by
        simpa [labels, fiberCard] using
          card_eq_sum_exactValueFiber source value
      _ <= ∑ _c ∈ labels, fiberCard b := by
        apply Finset.sum_le_sum
        intro c hc
        exact hmax c hc
      _ = labels.card * fiberCard b := by simp
  exact ⟨b, hb, hfiber, by
    simpa [labels, fiberCard] using hcard⟩

/-- Exact-`b` provenance makes the refinement literally lossless. -/
theorem exactValueFiber_eq_source_of_constant
    {alpha : Type u} {beta : Type v} [DecidableEq alpha]
    (source : Finset alpha) (value : alpha -> beta) (b : beta)
    (hconstant : forall a, a ∈ source -> value a = b) :
    exactValueFiber source value b = source := by
  classical
  ext a
  simp only [mem_exactValueFiber_iff]
  constructor
  · exact And.left
  · intro ha
    exact ⟨ha, hconstant a ha⟩

/-! ## Exact graph-c fibres at a retained fine label -/

/-- Actual curve indices retained at one literal fine rectangle. -/
noncomputable def retainedY1IndicesAtFine
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (r : fineLabel) : Finset iota := by
  classical
  exact D.shading.ambient.filter fun i =>
    (i, r) ∈ D.retainedGoodPairs keep

@[simp]
theorem mem_retainedY1IndicesAtFine_iff
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (r : fineLabel) (i : iota) :
    i ∈ retainedY1IndicesAtFine D keep r <->
      (i, r) ∈ D.retainedGoodPairs keep := by
  classical
  simp only [retainedY1IndicesAtFine, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hretained
    have hgood := ((D.mem_retainedGoodPairs_iff keep).mp hretained).1
    exact ⟨hgood.1, hretained⟩

/-- Exact graph-`c` values occupied at one retained fine label. -/
noncomputable def retainedY1ExactCValuesAtFine
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (r : fineLabel) : Finset Real :=
  occupiedExactValues (retainedY1IndicesAtFine D keep r) fun i =>
    tubeGraphC (D.fine.tubes i)

/-- The retained indices at one fine label with literal graph-`c` value
equal to `c`. -/
noncomputable def retainedY1ExactCFiberAtFine
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (r : fineLabel) (c : Real) :
    Finset iota :=
  exactValueFiber (retainedY1IndicesAtFine D keep r)
    (fun i => tubeGraphC (D.fine.tubes i)) c

@[simp]
theorem mem_retainedY1ExactCFiberAtFine_iff
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (r : fineLabel) (c : Real)
    (i : iota) :
    i ∈ retainedY1ExactCFiberAtFine D keep r c <->
      (i, r) ∈ D.retainedGoodPairs keep ∧
        tubeGraphC (D.fine.tubes i) = c := by
  classical
  simp [retainedY1ExactCFiberAtFine]

/-- Quantitative exact-`c` refinement of a nonempty retained fine fibre. -/
theorem exists_cardinalRetaining_retainedY1ExactCFiberAtFine
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (r : fineLabel)
    (hsource : (retainedY1IndicesAtFine D keep r).Nonempty) :
    exists c, c ∈ retainedY1ExactCValuesAtFine D keep r ∧
      (retainedY1ExactCFiberAtFine D keep r c).Nonempty ∧
      (retainedY1IndicesAtFine D keep r).card <=
        (retainedY1ExactCValuesAtFine D keep r).card *
          (retainedY1ExactCFiberAtFine D keep r c).card := by
  simpa [retainedY1ExactCValuesAtFine, retainedY1ExactCFiberAtFine] using
    exists_cardinalRetaining_exactValueFiber
      (retainedY1IndicesAtFine D keep r)
      (fun i => tubeGraphC (D.fine.tubes i)) hsource

/-- Ordered pairs from one retained exact-`c` fine fibre, filtered by the
literal coefficient lower bound needed by `choiceOfShift`. -/
noncomputable def retainedY1ExactCSeparatedPairsAtFine
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (r : fineLabel)
    (c pairScale : Real) : Finset (iota × iota) := by
  classical
  exact ((retainedY1ExactCFiberAtFine D keep r c).product
    (retainedY1ExactCFiberAtFine D keep r c)).filter fun pair =>
      2 * pairScale <= tubePairCoefficientDistance
        (D.fine.tubes pair.1) (D.fine.tubes pair.2)

@[simp]
theorem mem_retainedY1ExactCSeparatedPairsAtFine_iff
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (r : fineLabel)
    (c pairScale : Real) (pair : iota × iota) :
    pair ∈ retainedY1ExactCSeparatedPairsAtFine D keep r c pairScale <->
      (pair.1 ∈ retainedY1ExactCFiberAtFine D keep r c ∧
        pair.2 ∈ retainedY1ExactCFiberAtFine D keep r c) ∧
      2 * pairScale <= tubePairCoefficientDistance
        (D.fine.tubes pair.1) (D.fine.tubes pair.2) := by
  classical
  simp [retainedY1ExactCSeparatedPairsAtFine]

/-- The exact-`c`, coefficient-separated actual pair set directly produces
the complete upstream selection record.  In particular, both
`common_c` and `coefficient_lower` are conclusions of membership filters. -/
theorem retainedY1ExactCSeparatedPairsAtFine_selection
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (r : fineLabel)
    (c pairScale : Real) :
    ActualRetainedY1PairSelection D
      (retainedY1ExactCSeparatedPairsAtFine D keep r c pairScale)
      Prod.fst Prod.snd (fun _ : iota × iota => r) keep pairScale := by
  constructor
  · intro pair hpair
    exact ((mem_retainedY1ExactCFiberAtFine_iff D keep r c pair.1).mp
      ((mem_retainedY1ExactCSeparatedPairsAtFine_iff
        D keep r c pairScale pair).mp hpair).1.1).1
  · intro pair hpair
    exact ((mem_retainedY1ExactCFiberAtFine_iff D keep r c pair.2).mp
      ((mem_retainedY1ExactCSeparatedPairsAtFine_iff
        D keep r c pairScale pair).mp hpair).1.2).1
  · intro pair hpair
    have hp := (mem_retainedY1ExactCSeparatedPairsAtFine_iff
      D keep r c pairScale pair).mp hpair
    have hleft :=
      (mem_retainedY1ExactCFiberAtFine_iff D keep r c pair.1).mp hp.1.1 |>.2
    have hright :=
      (mem_retainedY1ExactCFiberAtFine_iff D keep r c pair.2).mp hp.1.2 |>.2
    exact hleft.trans hright.symm
  · intro pair hpair
    exact ((mem_retainedY1ExactCSeparatedPairsAtFine_iff
      D keep r c pairScale pair).mp hpair).2

/-- A concrete separated pair witnesses that the produced item family is
nonempty; no such witness is fabricated by exact-value pigeonholing alone. -/
theorem retainedY1ExactCSeparatedPairsAtFine_nonempty
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (r : fineLabel)
    (c pairScale : Real) {left right : iota}
    (hleft : left ∈ retainedY1ExactCFiberAtFine D keep r c)
    (hright : right ∈ retainedY1ExactCFiberAtFine D keep r c)
    (hseparated : 2 * pairScale <= tubePairCoefficientDistance
      (D.fine.tubes left) (D.fine.tubes right)) :
    (retainedY1ExactCSeparatedPairsAtFine D keep r c pairScale).Nonempty := by
  exact ⟨(left, right),
    (mem_retainedY1ExactCSeparatedPairsAtFine_iff
      D keep r c pairScale (left, right)).mpr
      ⟨⟨hleft, hright⟩, hseparated⟩⟩

/-! ## Exact graph-c refinement over one actual coarse rectangle -/

/-- Retained coarse incidences with one literal graph-`c` value.  Keeping
the fine label in the source avoids an unjustified choice of a common label. -/
noncomputable def retainedY1ExactCIncidencesOverCoarse
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle) (c : Real) :
    Finset (iota × fineLabel) :=
  exactValueFiber (D.coarseIncidencePairs keep R)
    (fun incidence => tubeGraphC (D.fine.tubes incidence.1)) c

@[simp]
theorem mem_retainedY1ExactCIncidencesOverCoarse_iff
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle) (c : Real)
    (incidence : iota × fineLabel) :
    incidence ∈ retainedY1ExactCIncidencesOverCoarse D keep R c <->
      incidence ∈ D.coarseIncidencePairs keep R ∧
        tubeGraphC (D.fine.tubes incidence.1) = c := by
  classical
  simp [retainedY1ExactCIncidencesOverCoarse]

/-- Exact values occupied by the retained incidences over `R`. -/
noncomputable def retainedY1ExactCValuesOverCoarse
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle) : Finset Real :=
  occupiedExactValues (D.coarseIncidencePairs keep R) fun incidence =>
    tubeGraphC (D.fine.tubes incidence.1)

/-- A largest exact-`c` coarse-incidence fibre retains the exact reciprocal
of the number of graph-`c` values actually occupied over `R`. -/
theorem exists_cardinalRetaining_retainedY1ExactCIncidencesOverCoarse
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (hsource : (D.coarseIncidencePairs keep R).Nonempty) :
    exists c, c ∈ retainedY1ExactCValuesOverCoarse D keep R ∧
      (retainedY1ExactCIncidencesOverCoarse D keep R c).Nonempty ∧
      (D.coarseIncidencePairs keep R).card <=
        (retainedY1ExactCValuesOverCoarse D keep R).card *
          (retainedY1ExactCIncidencesOverCoarse D keep R c).card := by
  simpa [retainedY1ExactCValuesOverCoarse,
    retainedY1ExactCIncidencesOverCoarse] using
    exists_cardinalRetaining_exactValueFiber
      (D.coarseIncidencePairs keep R)
      (fun incidence => tubeGraphC (D.fine.tubes incidence.1)) hsource

/-- Honest coarse pairing: both retained incidences lie over the same coarse
rectangle and in one exact-`c` fibre; the additional filters require the
same fine label and the coefficient lower used downstream. -/
noncomputable def retainedY1ExactCSeparatedIncidencePairsOverCoarse
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (c pairScale : Real) :
    Finset ((iota × fineLabel) × (iota × fineLabel)) := by
  classical
  exact ((retainedY1ExactCIncidencesOverCoarse D keep R c).product
    (retainedY1ExactCIncidencesOverCoarse D keep R c)).filter fun pair =>
      pair.1.2 = pair.2.2 ∧
        2 * pairScale <= tubePairCoefficientDistance
          (D.fine.tubes pair.1.1) (D.fine.tubes pair.2.1)

/-- The coarse exact-`c` pair filter produces the same downstream selection
record.  The common fine label is obtained from the explicit equality
filter, not from common coarse-rectangle membership. -/
theorem retainedY1ExactCSeparatedIncidencePairsOverCoarse_selection
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (c pairScale : Real) :
    ActualRetainedY1PairSelection D
      (retainedY1ExactCSeparatedIncidencePairsOverCoarse
        D keep R c pairScale)
      (fun pair => pair.1.1) (fun pair => pair.2.1)
      (fun pair => pair.1.2) keep pairScale := by
  constructor
  · intro pair hpair
    have hproduct := (Finset.mem_filter.mp hpair).1
    have hleft := (Finset.mem_product.mp hproduct).1
    have hcoarse :=
      (mem_retainedY1ExactCIncidencesOverCoarse_iff
        D keep R c pair.1).mp hleft |>.1
    have hactual := (D.mem_coarseIncidencePairs_iff keep).mp hcoarse
    exact (D.mem_retainedGoodPairs_iff keep).mpr
      ⟨hactual.1, hactual.2.1⟩
  · intro pair hpair
    have hproduct := (Finset.mem_filter.mp hpair).1
    have hright := (Finset.mem_product.mp hproduct).2
    have hcoarse :=
      (mem_retainedY1ExactCIncidencesOverCoarse_iff
        D keep R c pair.2).mp hright |>.1
    have hactual := (D.mem_coarseIncidencePairs_iff keep).mp hcoarse
    have hretained : (pair.2.1, pair.2.2) ∈
        D.retainedGoodPairs keep :=
      (D.mem_retainedGoodPairs_iff keep).mpr
        ⟨hactual.1, hactual.2.1⟩
    have hlabel := (Finset.mem_filter.mp hpair).2.1
    simpa only [hlabel] using hretained
  · intro pair hpair
    have hproduct := (Finset.mem_filter.mp hpair).1
    have hleft := (Finset.mem_product.mp hproduct).1
    have hright := (Finset.mem_product.mp hproduct).2
    have hcLeft :=
      (mem_retainedY1ExactCIncidencesOverCoarse_iff
        D keep R c pair.1).mp hleft |>.2
    have hcRight :=
      (mem_retainedY1ExactCIncidencesOverCoarse_iff
        D keep R c pair.2).mp hright |>.2
    exact hcLeft.trans hcRight.symm
  · intro pair hpair
    exact (Finset.mem_filter.mp hpair).2.2

#print axioms card_eq_sum_exactValueFiber
#print axioms exists_cardinalRetaining_exactValueFiber
#print axioms exactValueFiber_eq_source_of_constant
#print axioms exists_cardinalRetaining_retainedY1ExactCFiberAtFine
#print axioms retainedY1ExactCSeparatedPairsAtFine_selection
#print axioms exists_cardinalRetaining_retainedY1ExactCIncidencesOverCoarse
#print axioms retainedY1ExactCSeparatedIncidencePairsOverCoarse_selection

end

end FamilyStickyCinematicL32Prop41ActualY1ExactCFiberPairSelectionV1
