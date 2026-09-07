import Family8Grounding.Family8PlankThickControlRetainedOwnerFamilyV3
import Family6Grounding.Family6CanonicalCertifiedPlankSlabIncidenceCoreV3
import Submission.Kakeya.ConvexFactoring.FrameBoxCoordinateWindowEquiv
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankCanonicalUnitSlabIncidenceV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6FaithfulPlankSlabIncidenceCoreV9
open Family6CanonicalCertifiedPlankSlabIncidenceCoreV3
open Family8PlankThickControlActualClusterV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# A canonical certified unit slab through every actual plank

Every `IsPlank C a b K` certificate supplies a fixed framed plank.  Enlarging
its certified outer frame box coordinatewise to side vector `1 x 1 x 1`
produces a genuine certified slab at `theta = 1` which contains `K`.

At this endpoint scale no coherence between different slab certificates is
needed: the sine of any angle is at most one.  Consequently the fixed
one-certificate-per-query selector from
`CanonicalCertifiedPlankSlabIncidence` gives honest selected tangent coverage.
This removes the frame/selector/coverage construction seam without asserting
the still-missing nontrivial member-count estimate at intermediate angles.
-/

/-- The frame certificate selected from the actual `IsPlank` witness. -/
noncomputable def canonicalFramedPlank
    (D : ShadedConvexPlankFamily iota a b) (i : iota) :
    FramedPlank D.comparisonConstant a b (D.family i) := by
  have hbox : HasBoxDimensions D.comparisonConstant
      (plankSides a b) (D.family i) := (D.all_isPlank i).2.2.2
  exact
    { toBoxDimensionsCertificate :=
        Classical.choice hbox.nonempty_boxDimensionsCertificate }

/-- Reuse the center and frame of a plank certificate with unit side vector. -/
def unitSlabBox
    {C a b : NNReal} {K : ConvexBody Space}
    (P : FramedPlank C a b K) : FrameBox where
  center := P.box.center
  frame := P.box.frame
  side := slabSides 1

/-- The actual convex body of the unit slab attached to a framed plank. -/
def unitSlabBody
    {C a b : NNReal} {K : ConvexBody Space}
    (P : FramedPlank C a b K) : ConvexBody Space :=
  (unitSlabBox P).body

/-- Coordinatewise enlargement with fixed center and frame enlarges a frame
box carrier. -/
theorem frameBox_carrier_subset_of_same_center_frame_side
    (B E : FrameBox) (hcenter : B.center = E.center)
    (hframe : B.frame = E.frame) (hside : forall i, B.side i <= E.side i) :
    B.carrier <= E.carrier := by
  intro x hx
  rw [E.carrier_eq_centeredCoordinateWindow,
    mem_centeredCoordinateWindow_iff]
  intro i
  have hcoord := B.centeredCoordinate_abs_le_halfSide hx i
  simp only [FrameBox.coordinateCenter, FrameBox.coordinateHalf]
  rw [← hcenter, ← hframe]
  have hs : (B.side i : Real) <= (E.side i : Real) := by
    exact_mod_cast hside i
  exact hcoord.trans (by
    norm_num [NNReal.coe_div]
    linarith)

/-- The certified plank outer box lies in its attached unit slab box. -/
theorem canonicalFramedPlank_box_subset_unitSlabBox
    (D : ShadedConvexPlankFamily iota a b) (i : iota) :
    (canonicalFramedPlank D i).box.carrier <=
      (unitSlabBox (canonicalFramedPlank D i)).carrier := by
  apply frameBox_carrier_subset_of_same_center_frame_side
  · rfl
  · rfl
  · intro k
    rw [(canonicalFramedPlank D i).side_eq]
    have hab : a <= b := (D.all_isPlank i).2.1
    have hb : b <= 1 := (D.all_isPlank i).2.2.1
    fin_cases k
    · simpa [plankSides, unitSlabBox, slabSides] using hab.trans hb
    · simpa [plankSides, unitSlabBox, slabSides] using hb
    · simp [plankSides, unitSlabBox, slabSides]

/-- The unit reboxing is a literal comparison-one certified slab. -/
theorem unitSlabBody_isSlab
    {C a b : NNReal} {K : ConvexBody Space}
    (P : FramedPlank C a b K) :
    IsSlab 1 1 (unitSlabBody P) := by
  refine ⟨by norm_num, le_rfl, le_rfl, unitSlabBox P, rfl, ?_, le_rfl⟩
  intro x hx
  change x ∈ ((unitSlabBox P).rescale 1⁻¹).carrier at hx
  change x ∈ (unitSlabBox P).carrier
  simpa [FrameBox.rescale] using hx

/-- The source plank is tangent, at the endpoint scale, to whichever fixed
certificate the canonical selector chooses for its attached unit slab. -/
theorem canonicalFramedPlank_tangent_selected_unitSlab
    (D : ShadedConvexPlankFamily iota a b) (i : iota)
    (hS : IsSlab 1 1
      (unitSlabBody (canonicalFramedPlank D i))) :
    FrameTangent 1 (canonicalFramedPlank D i)
      ((classicalChoiceSlabCertificateSelector 1).select hS) := by
  constructor
  · exact (canonicalFramedPlank D i).outer_le |>.trans
      (canonicalFramedPlank_box_subset_unitSlabBox D i)
  · simpa [planeSine] using Real.sin_le_one
      (InnerProductGeometry.angle
        ((canonicalFramedPlank D i).box.frame 0)
        (((classicalChoiceSlabCertificateSelector 1).select hS).box.frame 0))

/-- A genuine canonical certified slab incidence on any nonempty actual plank
family.  Its members remain the derived fixed-frame tangent filter. -/
noncomputable def canonicalUnitSlabIncidence
    (D : ShadedConvexPlankFamily iota a b) (hindex : Nonempty iota) :
    CanonicalCertifiedPlankSlabIncidence iota iota D 1 1 where
  one_le_tangentComparisonConstant := le_rfl
  index_nonempty := hindex
  sourceToIndex := id
  indexToSource := id
  source_leftInverse := fun _ => rfl
  index_rightInverse := fun _ => rfl
  plank := canonicalFramedPlank D
  selector := classicalChoiceSlabCertificateSelector 1
  selected_tangent_coverage := by
    intro i
    let S := unitSlabBody (canonicalFramedPlank D i)
    have hS : IsSlab 1 1 S := unitSlabBody_isSlab _
    have ha : 0 < a := (D.all_isPlank i).1
    have hab : a <= b := (D.all_isPlank i).2.1
    have hbpos : 0 < b := ha.trans_le hab
    refine ⟨1, S, hS, (div_le_one hbpos).2 hab, le_rfl, ?_⟩
    exact canonicalFramedPlank_tangent_selected_unitSlab D i hS

/-- The positive-mass retained owner family from the M-aware clustering line
therefore carries the canonical incidence on exactly the same restricted
source objects. -/
theorem exists_retainedOwner_canonicalUnitSlabIncidence
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0) :
    Nonempty
      (CanonicalCertifiedPlankSlabIncidence
        {i // i ∈ retainedOwnerSourceIndices C q}
        {i // i ∈ retainedOwnerSourceIndices C q}
        (retainedOwnerPlankFamily D C q) 1 1) := by
  have hfin := retainedOwnerSourceIndices_nonempty_of_mass_ne_zero
    D C q hmass
  let hindex : Nonempty {i // i ∈ retainedOwnerSourceIndices C q} :=
    ⟨⟨hfin.choose, hfin.choose_spec⟩⟩
  exact ⟨canonicalUnitSlabIncidence
    (retainedOwnerPlankFamily D C q) hindex⟩

#print axioms canonicalFramedPlank
#print axioms frameBox_carrier_subset_of_same_center_frame_side
#print axioms canonicalFramedPlank_box_subset_unitSlabBox
#print axioms unitSlabBody_isSlab
#print axioms canonicalFramedPlank_tangent_selected_unitSlab
#print axioms canonicalUnitSlabIncidence
#print axioms exists_retainedOwner_canonicalUnitSlabIncidence

end
end Family8PlankCanonicalUnitSlabIncidenceV5
