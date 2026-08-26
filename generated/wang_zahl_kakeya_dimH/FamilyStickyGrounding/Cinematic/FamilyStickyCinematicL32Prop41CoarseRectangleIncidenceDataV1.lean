import Submission.Kakeya.Uniformity.TubeFamily
import FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TubeC2GraphRectangleV1RepoV2

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1

noncomputable section

universe u v w

/-!
# Honest finite incidence data for the paper's coarse rectangles

The paper defines `F(Ṙ)` from a retained good-pair relation `G'`: a curve is
in `F(Ṙ)` exactly when it has a retained good incidence with some fine
rectangle assigned to `Ṙ`.  This module records that definition for the
actual projected shading and actual tube family already present in the
repository.

The input `keep` below is deliberately an explicit parameter.  It represents
the later dyadic subrelation `G'`; no size, uniformity, non-concentration,
rich-ball, or global lower-bound property is attached to it here.

The current repository does not produce the fine rectangle `R_x`, its
coarse dilation, or the fine-to-coarse clustering.  Consequently those maps
are the minimal identification interface in `CoarseRectangleIncidenceData`.
No tangency theorem is asserted from them.
-/

/-- Actual finite source for the combinatorial definition of `F(Ṙ)`.

`pointAt r` is the paper's `x(r)`.  A good incidence is then the literal
projected-shading statement `pointAt r ∈ shading.carrier i`.  The two
rectangle maps retain the missing geometric identification without assuming
that either rectangle is tangent to a tube or contains the other. -/
structure CoarseRectangleIncidenceData
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    (fineLabel : Type w) [DecidableEq fineLabel] where
  fine : UniformTubeFamily radius iota
  shading : FiniteProjectedShading point iota
  fineLabels : Finset fineLabel
  pointAt : fineLabel -> point
  fineRectangleAt : fineLabel -> C2GraphRectangle
  coarseRectangleAt : fineLabel -> C2GraphRectangle

/-- Literal good pair `(tube index, fine rectangle)`: the fine rectangle's
source point lies in that tube's actual projected `Y₁` carrier. -/
def CoarseRectangleIncidenceData.GoodPair
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (i : iota) (r : fineLabel) : Prop :=
  i ∈ D.shading.ambient ∧ r ∈ D.fineLabels ∧
    D.pointAt r ∈ D.shading.carrier i

/-- All literal good pairs. -/
noncomputable def CoarseRectangleIncidenceData.goodPairs
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel) :
    Finset (iota × fineLabel) := by
  classical
  exact (D.shading.ambient.product D.fineLabels).filter fun p =>
    D.pointAt p.2 ∈ D.shading.carrier p.1

@[simp]
theorem CoarseRectangleIncidenceData.mem_goodPairs_iff
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    {i : iota} {r : fineLabel} :
    (i, r) ∈ D.goodPairs ↔ D.GoodPair i r := by
  classical
  simp [CoarseRectangleIncidenceData.goodPairs,
    CoarseRectangleIncidenceData.GoodPair, and_assoc]

/-- Explicit retained good pairs `G'`, obtained only by filtering genuine
good pairs with the supplied selection predicate. -/
noncomputable def CoarseRectangleIncidenceData.retainedGoodPairs
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) : Finset (iota × fineLabel) := by
  classical
  exact D.goodPairs.filter fun p => keep p.1 p.2

@[simp]
theorem CoarseRectangleIncidenceData.mem_retainedGoodPairs_iff
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) {i : iota} {r : fineLabel} :
    (i, r) ∈ D.retainedGoodPairs keep ↔ D.GoodPair i r ∧ keep i r := by
  classical
  simp [CoarseRectangleIncidenceData.retainedGoodPairs]

/-- The literal finite family of coarse `C2` rectangles appearing as an
assigned coarse enlargement of a fine rectangle. -/
noncomputable def CoarseRectangleIncidenceData.coarseRectangleFamily
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel) :
    Finset C2GraphRectangle := by
  classical
  exact D.fineLabels.image D.coarseRectangleAt

@[simp]
theorem CoarseRectangleIncidenceData.mem_coarseRectangleFamily_iff
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    {R : C2GraphRectangle} :
    R ∈ D.coarseRectangleFamily ↔
      ∃ r ∈ D.fineLabels, D.coarseRectangleAt r = R := by
  classical
  simp [CoarseRectangleIncidenceData.coarseRectangleFamily]

/-- The paper's cluster `R(Ṙ)` of fine rectangle labels assigned to one
literal coarse rectangle. -/
noncomputable def CoarseRectangleIncidenceData.fineRectangleFiber
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (R : C2GraphRectangle) : Finset fineLabel := by
  classical
  exact D.fineLabels.filter fun r => D.coarseRectangleAt r = R

@[simp]
theorem CoarseRectangleIncidenceData.mem_fineRectangleFiber_iff
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    {R : C2GraphRectangle} {r : fineLabel} :
    r ∈ D.fineRectangleFiber R ↔
      r ∈ D.fineLabels ∧ D.coarseRectangleAt r = R := by
  classical
  simp [CoarseRectangleIncidenceData.fineRectangleFiber]

theorem CoarseRectangleIncidenceData.fineRectangleFiber_nonempty
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    {R : C2GraphRectangle} (hR : R ∈ D.coarseRectangleFamily) :
    (D.fineRectangleFiber R).Nonempty := by
  rcases D.mem_coarseRectangleFamily_iff.mp hR with ⟨r, hr, hcoarse⟩
  exact ⟨r, D.mem_fineRectangleFiber_iff.mpr ⟨hr, hcoarse⟩⟩

/-- Retained good incidences whose fine rectangle lies over `R`. -/
noncomputable def CoarseRectangleIncidenceData.coarseIncidencePairs
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle) :
    Finset (iota × fineLabel) := by
  classical
  exact (D.retainedGoodPairs keep).filter fun p =>
    D.coarseRectangleAt p.2 = R

@[simp]
theorem CoarseRectangleIncidenceData.mem_coarseIncidencePairs_iff
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) {R : C2GraphRectangle}
    {i : iota} {r : fineLabel} :
    (i, r) ∈ D.coarseIncidencePairs keep R ↔
      D.GoodPair i r ∧ keep i r ∧ D.coarseRectangleAt r = R := by
  classical
  simp [CoarseRectangleIncidenceData.coarseIncidencePairs, and_assoc]

/-- Index-level version of the paper's `F(Ṙ)`: first-coordinate image of
the retained incidences over `Ṙ`. -/
noncomputable def CoarseRectangleIncidenceData.coarseCurveIndexFiber
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle) :
    Finset iota := by
  classical
  exact (D.coarseIncidencePairs keep R).image Prod.fst

@[simp]
theorem CoarseRectangleIncidenceData.mem_coarseCurveIndexFiber_iff
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) {R : C2GraphRectangle} {i : iota} :
    i ∈ D.coarseCurveIndexFiber keep R ↔
      ∃ r, D.GoodPair i r ∧ keep i r ∧
        D.coarseRectangleAt r = R := by
  classical
  simp [CoarseRectangleIncidenceData.coarseCurveIndexFiber]

/-- Actual tube-valued `F(Ṙ)`.  Using an image is essential: no injectivity
of the ambient tube map is assumed by this data layer. -/
noncomputable def CoarseRectangleIncidenceData.coarseTubeFiber
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle) :
    Finset (Tube radius) := by
  classical
  exact (D.coarseCurveIndexFiber keep R).image D.fine.tubes

@[simp]
theorem CoarseRectangleIncidenceData.mem_coarseTubeFiber_iff
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) {R : C2GraphRectangle}
    {T : Tube radius} :
    T ∈ D.coarseTubeFiber keep R ↔
      ∃ i ∈ D.coarseCurveIndexFiber keep R, D.fine.tubes i = T := by
  classical
  simp [CoarseRectangleIncidenceData.coarseTubeFiber]

theorem CoarseRectangleIncidenceData.coarseTubeFiber_card_le
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle) :
    (D.coarseTubeFiber keep R).card <=
      (D.coarseCurveIndexFiber keep R).card := by
  classical
  exact Finset.card_image_le

/-- Retained incidences at one fine rectangle. -/
noncomputable def CoarseRectangleIncidenceData.retainedPairsAtFine
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (r : fineLabel) :
    Finset (iota × fineLabel) := by
  classical
  exact (D.retainedGoodPairs keep).filter fun p => p.2 = r

/-- Exact partition of `G'` by fine rectangles. -/
theorem CoarseRectangleIncidenceData.retainedGoodPairs_card_eq_sum_fine
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) :
    (D.retainedGoodPairs keep).card =
      ∑ r ∈ D.fineLabels, (D.retainedPairsAtFine keep r).card := by
  classical
  exact Finset.card_eq_sum_card_fiberwise (fun p hp => by
    have hgood := ((D.mem_retainedGoodPairs_iff keep).mp hp).1
    exact hgood.2.1)

/-- Exact partition of `G'` by literal coarse rectangles. -/
theorem CoarseRectangleIncidenceData.retainedGoodPairs_card_eq_sum_coarse
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) :
    (D.retainedGoodPairs keep).card =
      ∑ R ∈ D.coarseRectangleFamily,
        (D.coarseIncidencePairs keep R).card := by
  classical
  exact Finset.card_eq_sum_card_fiberwise (fun p hp => by
    have hgood := ((D.mem_retainedGoodPairs_iff keep).mp hp).1
    exact D.mem_coarseRectangleFamily_iff.mpr
      ⟨p.2, hgood.2.1, rfl⟩)

/-- Exact curve-side degree formula inside one coarse rectangle. -/
theorem CoarseRectangleIncidenceData.coarseIncidencePairs_card_eq_sum_curve
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle) :
    (D.coarseIncidencePairs keep R).card =
      ∑ i ∈ D.coarseCurveIndexFiber keep R,
        ((D.coarseIncidencePairs keep R).filter fun p => p.1 = i).card := by
  classical
  simpa [CoarseRectangleIncidenceData.coarseCurveIndexFiber] using
    (Finset.card_eq_sum_card_image Prod.fst
      (D.coarseIncidencePairs keep R))

/-- Exact fine-rectangle-side degree formula inside one coarse rectangle. -/
theorem CoarseRectangleIncidenceData.coarseIncidencePairs_card_eq_sum_fine
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle) :
    (D.coarseIncidencePairs keep R).card =
      ∑ r ∈ D.fineRectangleFiber R,
        ((D.coarseIncidencePairs keep R).filter fun p => p.2 = r).card := by
  classical
  exact Finset.card_eq_sum_card_fiberwise (fun p hp => by
    have hpair := (D.mem_coarseIncidencePairs_iff keep).mp hp
    exact D.mem_fineRectangleFiber_iff.mpr
      ⟨hpair.1.2.1, hpair.2.2⟩)

/-- The two ways of summing retained incidences over a fixed coarse
rectangle agree exactly. -/
theorem CoarseRectangleIncidenceData.sum_curve_degrees_eq_sum_fine_degrees
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle) :
    (∑ i ∈ D.coarseCurveIndexFiber keep R,
        ((D.coarseIncidencePairs keep R).filter fun p => p.1 = i).card) =
      ∑ r ∈ D.fineRectangleFiber R,
        ((D.coarseIncidencePairs keep R).filter fun p => p.2 = r).card := by
  rw [← D.coarseIncidencePairs_card_eq_sum_curve keep R,
    D.coarseIncidencePairs_card_eq_sum_fine keep R]

/-- Coarse rectangles incident to both curve indices.  This is a concrete
candidate for the `goodPair` predicate consumed by a later separated-centre
selection; it contains no richness assertion. -/
noncomputable def CoarseRectangleIncidenceData.commonCoarseRectangleFiber
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota) :
    Finset C2GraphRectangle := by
  classical
  exact D.coarseRectangleFamily.filter fun R =>
    left ∈ D.coarseCurveIndexFiber keep R ∧
      right ∈ D.coarseCurveIndexFiber keep R

/-- Two curve indices form a coarse good pair exactly when some literal
coarse rectangle is incident to both. -/
def CoarseRectangleIncidenceData.CoarseGoodPair
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota) : Prop :=
  (D.commonCoarseRectangleFiber keep left right).Nonempty

@[simp]
theorem CoarseRectangleIncidenceData.mem_commonCoarseRectangleFiber_iff
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) {left right : iota}
    {R : C2GraphRectangle} :
    R ∈ D.commonCoarseRectangleFiber keep left right ↔
      R ∈ D.coarseRectangleFamily ∧
        left ∈ D.coarseCurveIndexFiber keep R ∧
        right ∈ D.coarseCurveIndexFiber keep R := by
  classical
  simp [CoarseRectangleIncidenceData.commonCoarseRectangleFiber]

/-- Literal common coarse-incidence count. -/
noncomputable def CoarseRectangleIncidenceData.coarseCrossIncidenceCount
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota) : Nat :=
  (D.commonCoarseRectangleFiber keep left right).card

theorem CoarseRectangleIncidenceData.coarseGoodPair_iff_crossIncidence_pos
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota) :
    D.CoarseGoodPair keep left right ↔
      0 < D.coarseCrossIncidenceCount keep left right := by
  classical
  exact Finset.card_pos.symm

#print axioms CoarseRectangleIncidenceData
#print axioms CoarseRectangleIncidenceData.mem_goodPairs_iff
#print axioms CoarseRectangleIncidenceData.mem_retainedGoodPairs_iff
#print axioms CoarseRectangleIncidenceData.mem_coarseRectangleFamily_iff
#print axioms CoarseRectangleIncidenceData.mem_coarseCurveIndexFiber_iff
#print axioms CoarseRectangleIncidenceData.mem_coarseTubeFiber_iff
#print axioms CoarseRectangleIncidenceData.retainedGoodPairs_card_eq_sum_fine
#print axioms CoarseRectangleIncidenceData.retainedGoodPairs_card_eq_sum_coarse
#print axioms CoarseRectangleIncidenceData.sum_curve_degrees_eq_sum_fine_degrees
#print axioms CoarseRectangleIncidenceData.coarseGoodPair_iff_crossIncidence_pos

end

end FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
