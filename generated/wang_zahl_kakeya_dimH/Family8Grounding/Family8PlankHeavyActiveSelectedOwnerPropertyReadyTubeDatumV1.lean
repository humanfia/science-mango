import Family8Grounding.Family8PlankHeavyActiveSelectedOwnerRowMassEndpointV2
import Family8Grounding.Family8PlankLongTubeCenteredFreshV4
import Family8Grounding.Family8ActiveCoarseCanonicalFrostmanXLowerV3
import FamilyStickyGrounding.FamilyStickyFiniteFamilyMaximalConcentrationV1
import Submission.Kakeya.ConvexFactoring.BoxDimensionsMeasure
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
set_option linter.style.haveILetI false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalFrostmanConstantCoreV1
open Family8ActiveCoarseCanonicalFrostmanXLowerV3
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankHeavyRetainedOwnerActualDatumV2
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankHeavyRetainedOwnerActiveCertifiedOwnerIncidenceV1
open Family8PlankHeavyActiveSelectedOwnerRepresentativeDatumV2
open Family8PlankHeavyActiveSelectedOwnerRowMassEndpointV2
open Family8PlankThickControlActualClusterV1
open Family8PlankCertificateLongTubeCoverV2
open Family8PlankLongTubeCenteredFreshV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8PlankLongTubeGlobalKatzTaoV3
open FamilyStickyFiniteFamilyMaximalConcentrationV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe v

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# A property-ready tube datum on one literal heavy-owner row

The coarse row carrier is only known to have volume *at most* the complete
owner-fibre mass.  It therefore cannot honestly carry the already proved
rowwise mass floor.  Instead this module indexes every complete source fibre
by its owner in the final active certified row.  The sigma index is injective
back to the original source because owner fibres are disjoint.  Thus no mass,
cardinality, plank certificate, or thick-control information is invented or
duplicated.

The resulting shaded plank family feeds the genuine long-tube cover and the
existing centered/fresh normalization.  The later power density and global
Frostman base budgets remain scalar analytic inputs; they are deliberately
not fields of this structural package.
-/

/-- The literal subtype of heavy selected owners in one certified row. -/
abbrev ActiveSelectedOwnerRow
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space) :=
  {s // s ∈ activeSelectedOwnersInCertifiedSlab
    D C q cell hcell selected hmass hactive thetaScale S}

/-- Every occurrence in the row is one literal source index in the complete
fibre of one final heavy owner. -/
abbrev ActiveSelectedOwnerRowOccurrence
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space) :=
  Σ s : ActiveSelectedOwnerRow
      D C q cell hcell selected hmass hactive thetaScale S,
    {i // i ∈ ownerFiber C s.1.1}

/-- The complete-fibre row as an actual shaded `a × b × 1` plank family. -/
def activeSelectedOwnerRowPlankDatum
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space) :
    ShadedConvexPlankFamily
      (ActiveSelectedOwnerRowOccurrence
        D C q cell hcell selected hmass hactive thetaScale S) a b where
  family p := D.family p.2.1
  shading := {
    carrier := fun p => D.shading.carrier p.2.1
    measurable_carrier := fun p => D.shading.measurable_carrier p.2.1
    carrier_subset := fun p => D.shading.carrier_subset p.2.1 }
  comparisonConstant := D.comparisonConstant
  all_isPlank p := D.all_isPlank p.2.1
  ambient := D.ambient
  ambientComparisonConstant := D.ambientComparisonConstant
  ambient_is_unit_scale := D.ambient_is_unit_scale
  contained_in_ambient p := D.contained_in_ambient p.2.1

@[simp] theorem activeSelectedOwnerRowPlankDatum_family_apply
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space)
    (p : ActiveSelectedOwnerRowOccurrence
      D C q cell hcell selected hmass hactive thetaScale S) :
    (activeSelectedOwnerRowPlankDatum
      D C q cell hcell selected hmass hactive thetaScale S).family p =
        D.family p.2.1 := rfl

@[simp] theorem activeSelectedOwnerRowPlankDatum_shading_carrier
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space)
    (p : ActiveSelectedOwnerRowOccurrence
      D C q cell hcell selected hmass hactive thetaScale S) :
    (activeSelectedOwnerRowPlankDatum
      D C q cell hcell selected hmass hactive thetaScale S).shading.carrier p =
        D.shading.carrier p.2.1 := rfl

/-- The sigma datum's mass is exactly the sum of the complete owner-fibre
masses on the same final row. -/
theorem activeSelectedOwnerRowPlankDatum_shadingMass
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space) :
    (activeSelectedOwnerRowPlankDatum
      D C q cell hcell selected hmass hactive thetaScale S).shading.shadingMass =
      ∑ s : ActiveSelectedOwnerRow
          D C q cell hcell selected hmass hactive thetaScale S,
        ownerFiberMass C s.1.1 := by
  classical
  change (∑ p : ActiveSelectedOwnerRowOccurrence
      D C q cell hcell selected hmass hactive thetaScale S,
        volume (D.shading.carrier p.2.1)) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s _hs
  unfold ownerFiberMass
  symm
  exact Finset.sum_subtype _ (fun _i => Iff.rfl) _

/-- Its occurrence cardinality is exactly the sum of the literal owner-fibre
cardinalities on the row. -/
theorem activeSelectedOwnerRowOccurrence_card
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space) :
    Fintype.card (ActiveSelectedOwnerRowOccurrence
      D C q cell hcell selected hmass hactive thetaScale S) =
      ∑ s : ActiveSelectedOwnerRow
          D C q cell hcell selected hmass hactive thetaScale S,
        (ownerFiber C s.1.1).card := by
  classical
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro s _hs
  exact Fintype.card_coe _

/-- The endpoint's common half-average floor is a genuine lower bound for the
mass of this same complete-fibre row datum. -/
theorem activeSelectedOwnerRow_card_mul_floor_le_shadingMass
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space) :
    ((activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selected hmass hactive thetaScale S).card : ENNReal) *
        retainedOwnerHalfAverageFloor C q ≤
      (activeSelectedOwnerRowPlankDatum
        D C q cell hcell selected hmass hactive thetaScale S).shading.shadingMass := by
  rw [activeSelectedOwnerRowPlankDatum_shadingMass]
  calc
    ((activeSelectedOwnersInCertifiedSlab
          D C q cell hcell selected hmass hactive thetaScale S).card : ENNReal) *
          retainedOwnerHalfAverageFloor C q =
        ∑ _s : ActiveSelectedOwnerRow
            D C q cell hcell selected hmass hactive thetaScale S,
          retainedOwnerHalfAverageFloor C q := by
            simp [mul_comm]
    _ ≤ ∑ s : ActiveSelectedOwnerRow
          D C q cell hcell selected hmass hactive thetaScale S,
        ownerFiberMass C s.1.1 := by
      apply Finset.sum_le_sum
      intro s _hs
      exact activeSelectedOwner_halfAverageFloor_le_ownerFiberMass
        D C q cell hcell selected hmass hactive thetaScale S s

/-- The common log-bucket branching number controls the total occurrence
cardinality on both sides.  The strict per-fibre upper bound is weakened only
to a non-strict aggregate bound. -/
theorem activeSelectedOwnerRowOccurrence_card_bounds
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space) :
    (activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selected hmass hactive thetaScale S).card *
          ownerBucketBranching q ≤
        Fintype.card (ActiveSelectedOwnerRowOccurrence
          D C q cell hcell selected hmass hactive thetaScale S) ∧
    Fintype.card (ActiveSelectedOwnerRowOccurrence
        D C q cell hcell selected hmass hactive thetaScale S) ≤
      (activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selected hmass hactive thetaScale S).card *
          (2 * ownerBucketBranching q) := by
  rw [activeSelectedOwnerRowOccurrence_card]
  constructor
  · calc
      (activeSelectedOwnersInCertifiedSlab
          D C q cell hcell selected hmass hactive thetaScale S).card *
            ownerBucketBranching q =
          ∑ _s : ActiveSelectedOwnerRow
              D C q cell hcell selected hmass hactive thetaScale S,
            ownerBucketBranching q := by simp
      _ ≤ ∑ s : ActiveSelectedOwnerRow
            D C q cell hcell selected hmass hactive thetaScale S,
          (ownerFiber C s.1.1).card := by
        apply Finset.sum_le_sum
        intro s _hs
        have hsBucket : s.1.1 ∈ selectedOwnerLogBucket C q :=
          (mem_heavyRetainedOwners C q s.1.1).1 s.1.2 |>.1
        exact (selectedOwnerLogBucket_card_bounds C q hsBucket).1
  · calc
      (∑ s : ActiveSelectedOwnerRow
            D C q cell hcell selected hmass hactive thetaScale S,
          (ownerFiber C s.1.1).card) ≤
          ∑ _s : ActiveSelectedOwnerRow
              D C q cell hcell selected hmass hactive thetaScale S,
            (2 * ownerBucketBranching q) := by
        apply Finset.sum_le_sum
        intro s _hs
        have hsBucket : s.1.1 ∈ selectedOwnerLogBucket C q :=
          (mem_heavyRetainedOwners C q s.1.1).1 s.1.2 |>.1
        exact Nat.le_of_lt
          (selectedOwnerLogBucket_card_bounds C q hsBucket).2
      _ = (activeSelectedOwnersInCertifiedSlab
          D C q cell hcell selected hmass hactive thetaScale S).card *
            (2 * ownerBucketBranching q) := by simp

/-- A specified row must be nonempty to feed APIs requiring a nonempty index
type.  This follows mechanically once a row owner is supplied, since every
selected owner owns itself. -/
theorem activeSelectedOwnerRowOccurrence_nonempty
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space)
    (hrow : (activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive thetaScale S).Nonempty) :
    Nonempty (ActiveSelectedOwnerRowOccurrence
      D C q cell hcell selected hmass hactive thetaScale S) := by
  obtain ⟨s, hsRow⟩ := hrow
  have hsBucket : s.1 ∈ selectedOwnerLogBucket C q :=
    (mem_heavyRetainedOwners C q s.1).1 s.2 |>.1
  have hsSelected : s.1 ∈ C.selected :=
    (mem_selectedOwnerLogBucket C q s.1).1 hsBucket |>.1
  obtain ⟨i, hi⟩ := ownerFiber_nonempty_of_selected C hsSelected
  exact ⟨⟨⟨s, hsRow⟩, ⟨i, hi⟩⟩⟩

/-- Complete owner fibres are disjoint: forgetting the row owner and keeping
only the literal source index is injective on occurrences. -/
theorem activeSelectedOwnerRowOccurrence_source_injective
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space) :
    Function.Injective (fun p : ActiveSelectedOwnerRowOccurrence
      D C q cell hcell selected hmass hactive thetaScale S => p.2.1) := by
  rintro ⟨ps, pi⟩ ⟨rs, ri⟩ hsource
  have hpOwner : C.owner pi.1 = ps.1.1 :=
    (mem_ownerFiber C ps.1.1 pi.1).1 pi.2
  have hrOwner : C.owner ri.1 = rs.1.1 :=
    (mem_ownerFiber C rs.1.1 ri.1).1 ri.2
  have howners : ps.1.1 = rs.1.1 := by
    calc
      ps.1.1 = C.owner pi.1 := hpOwner.symm
      _ = C.owner ri.1 := congrArg C.owner hsource
      _ = rs.1.1 := hrOwner
  have hrow : ps = rs := by
    apply Subtype.ext
    exact Subtype.ext howners
  subst rs
  have hpi : pi = ri := Subtype.ext hsource
  subst ri
  rfl

/-- The original M-aware thickened-plank control passes to the complete-fibre
row with no loss: the occurrence projection is injective and every row
containment is the identical source-plank containment. -/
theorem activeSelectedOwnerRowPlankDatum_frostmanThickenedPlankControl
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space)
    (M : NNReal) (hthick : FrostmanThickenedPlankControl D M) :
    FrostmanThickenedPlankControl
      (activeSelectedOwnerRowPlankDatum
        D C q cell hcell selected hmass hactive thetaScale S) M := by
  let rowD := activeSelectedOwnerRowPlankDatum
    D C q cell hcell selected hmass hactive thetaScale S
  let sourceEmbedding :
      ActiveSelectedOwnerRowOccurrence
        D C q cell hcell selected hmass hactive thetaScale S ↪ iota :=
    ⟨fun p => p.2.1,
      activeSelectedOwnerRowOccurrence_source_injective
        D C q cell hcell selected hmass hactive thetaScale S⟩
  refine ⟨hthick.1, ?_⟩
  intro scale hratio hscale p
  have hsubset :
      (thickenedPlankIndices rowD scale p).map sourceEmbedding ⊆
        thickenedPlankIndices D scale p.2.1 := by
    intro i hi
    rw [Finset.mem_map] at hi
    obtain ⟨r, hr, hir⟩ := hi
    subst i
    rw [mem_thickenedPlankIndices_iff] at hr ⊢
    change (D.family r.2.1 : Set Space) ⊆
      Metric.cthickening ((scale * b : NNReal) : Real)
        (D.family p.2.1 : Set Space) at hr
    change (D.family r.2.1 : Set Space) ⊆
      Metric.cthickening ((scale * b : NNReal) : Real)
        (D.family p.2.1 : Set Space)
    exact hr
  calc
    ((thickenedPlankIndices rowD scale p).card : ENNReal) =
        (((thickenedPlankIndices rowD scale p).map sourceEmbedding).card :
          ENNReal) := by simp
    _ ≤ ((thickenedPlankIndices D scale p.2.1).card : ENNReal) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ (M : ENNReal) * (scale : ENNReal) :=
      hthick.2 scale hratio hscale p.2.1

/-- On every nonempty final row, the common branching number retains its
literal M times theta cap from the original thick-control datum. -/
theorem activeSelectedOwnerRow_branching_le_M_mul_theta
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (S : ConvexBody Space)
    (hrow : (activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive theta S).Nonempty)
    (M : NNReal) (hthick : FrostmanThickenedPlankControl D M)
    (hratio : a / b ≤ theta) (htheta : theta ≤ 1) :
    (ownerBucketBranching q : ENNReal) ≤
      (M : ENNReal) * (theta : ENNReal) := by
  obtain ⟨s, hsRow⟩ := hrow
  have hsBucket : s.1 ∈ selectedOwnerLogBucket C q :=
    (mem_heavyRetainedOwners C q s.1).1 s.2 |>.1
  calc
    (ownerBucketBranching q : ENNReal) ≤
        ((ownerFiber C s.1).card : ENNReal) := by
      exact_mod_cast (selectedOwnerLogBucket_card_bounds C q hsBucket).1
    _ ≤ (M : ENNReal) * (theta : ENNReal) :=
      ownerFiber_card_le D M theta C hthick hratio htheta s.1

/-- A nonempty complete-fibre row has positive actual plank family volume. -/
theorem activeSelectedOwnerRowPlankDatum_familyVolume_pos
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space)
    (hrow : (activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive thetaScale S).Nonempty) :
    0 < familyVolume (activeSelectedOwnerRowPlankDatum
      D C q cell hcell selected hmass hactive thetaScale S).family := by
  let rowD := activeSelectedOwnerRowPlankDatum
    D C q cell hcell selected hmass hactive thetaScale S
  let p : ActiveSelectedOwnerRowOccurrence
      D C q cell hcell selected hmass hactive thetaScale S :=
    Classical.choice (activeSelectedOwnerRowOccurrence_nonempty
      D C q cell hcell selected hmass hactive thetaScale S hrow)
  have hp : 0 < volume (rowD.family p : Set Space) :=
    (rowD.all_isPlank p).volume_pos
  have hsingle :
      volume (rowD.family p : Set Space) ≤ familyVolume rowD.family := by
    unfold familyVolume
    exact Finset.single_le_sum
      (fun j _ => show (0 : ENNReal) ≤ volume (rowD.family j : Set Space) from bot_le)
      (Finset.mem_univ p)
  exact hp.trans_le hsingle

/-- The canonical finite-row constant automatically certifies Frostman
non-concentration for the same complete-fibre row and ambient body. -/
theorem activeSelectedOwnerRowPlankDatum_isFrostmanIn_canonical
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space)
    (hrow : (activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive thetaScale S).Nonempty) :
    let rowD := activeSelectedOwnerRowPlankDatum
      D C q cell hcell selected hmass hactive thetaScale S
    IsFrostmanIn
      (canonicalFrostmanConstant rowD.family rowD.ambient)
      rowD.family rowD.ambient := by
  dsimp only
  let rowD := activeSelectedOwnerRowPlankDatum
    D C q cell hcell selected hmass hactive thetaScale S
  apply canonicalFrostmanConstant_isFrostmanIn
    rowD.family rowD.ambient rowD.contained_in_ambient
  · rw [containedMass_eq_familyVolume_of_contained
      rowD.family rowD.ambient rowD.contained_in_ambient]
    exact (activeSelectedOwnerRowPlankDatum_familyVolume_pos
      D C q cell hcell selected hmass hactive thetaScale S hrow).ne'
  · rw [containedMass_eq_familyVolume_of_contained
      rowD.family rowD.ambient rowD.contained_in_ambient]
    exact familyVolume_ne_top rowD.family

/-- The same canonical Frostman constant is finite, with no callback or
external scalar bound required. -/
theorem activeSelectedOwnerRowPlankDatum_canonicalFrostmanConstant_ne_top
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space)
    (hrow : (activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive thetaScale S).Nonempty) :
    let rowD := activeSelectedOwnerRowPlankDatum
      D C q cell hcell selected hmass hactive thetaScale S
    canonicalFrostmanConstant rowD.family rowD.ambient ≠ ∞ := by
  dsimp only
  let rowD := activeSelectedOwnerRowPlankDatum
    D C q cell hcell selected hmass hactive thetaScale S
  have hmass0 : containedMass rowD.family rowD.ambient ≠ 0 := by
    rw [containedMass_eq_familyVolume_of_contained
      rowD.family rowD.ambient rowD.contained_in_ambient]
    exact (activeSelectedOwnerRowPlankDatum_familyVolume_pos
      D C q cell hcell selected hmass hactive thetaScale S hrow).ne'
  unfold canonicalFrostmanConstant
  exact ENNReal.div_ne_top
    (ENNReal.mul_ne_top
      (maximalConcentration_lt_top rowD.family).ne
      rowD.ambient.isCompact.measure_lt_top.ne)
    hmass0

/-- The genuine same-index radius-b tube cover of the complete-fibre row. -/
def activeSelectedOwnerRowLongTubeDatum
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space) :
    ActualTubeDatum b (ActiveSelectedOwnerRowOccurrence
      D C q cell hcell selected hmass hactive thetaScale S) :=
  plankLongTubeActualDatum (activeSelectedOwnerRowPlankDatum
    D C q cell hcell selected hmass hactive thetaScale S)

/-- A nonempty row at radius at most one half automatically produces a
centered, eighth-normalized, fresh admissible subtype.  The output includes
the exact card, mass, Katz--Tao, and row-average retention statements from
the existing callback-free long-tube theorem. -/
theorem exists_activeSelectedOwnerRow_fresh_admissible
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space)
    (hrow : (activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selectedCells hmass hactive thetaScale S).Nonempty)
    (hbHalf : b ≤ (2 : NNReal)⁻¹) :
    let occurrence := ActiveSelectedOwnerRowOccurrence
      D C q cell hcell selectedCells hmass hactive thetaScale S
    let rowD := activeSelectedOwnerRowPlankDatum
      D C q cell hcell selectedCells hmass hactive thetaScale S
    let source := centeredPlankLongTubeActualDatum rowD
    let CF := canonicalFrostmanConstant rowD.family rowD.ambient
    let Csource := plankLongTubeGlobalKatzTaoConstant rowD CF
    let threshold := Nat.ceil ((480000 * (128 * Csource) : ENNReal).toReal)
    ∃ selected : Finset (Unit × occurrence),
      selected.Nonempty ∧
      (restrictActualTubeDatum
        (eighthNormalizedDatum source) selected).IsAdmissible ∧
      (Fintype.card (Unit × occurrence) : ENNReal) ≤
        (threshold + 1 : Nat) * (selected.card : ENNReal) ∧
      (eighthNormalizedDatum source).shading.shadingMass ≤
        (threshold + 1 : Nat) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum source) selected).shading.shadingMass ∧
      IsKatzTao (128 * Csource)
        (restrictActualTubeDatum
          (eighthNormalizedDatum source) selected).family.bodyFamily ∧
      rowD.shading.averageMultiplicity ≤
        (threshold + 1 : Nat) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum source) selected).shading.averageMultiplicity := by
  dsimp only
  let occurrence := ActiveSelectedOwnerRowOccurrence
    D C q cell hcell selectedCells hmass hactive thetaScale S
  let rowD := activeSelectedOwnerRowPlankDatum
    D C q cell hcell selectedCells hmass hactive thetaScale S
  let hocc : Nonempty occurrence :=
    activeSelectedOwnerRowOccurrence_nonempty
      D C q cell hcell selectedCells hmass hactive thetaScale S hrow
  let p : occurrence := Classical.choice hocc
  have hbPos : 0 < b :=
    (rowD.all_isPlank p).1.trans_le (rowD.all_isPlank p).2.1
  let CF := canonicalFrostmanConstant rowD.family rowD.ambient
  have hCF : CF ≠ ∞ := by
    exact activeSelectedOwnerRowPlankDatum_canonicalFrostmanConstant_ne_top
      D C q cell hcell selectedCells hmass hactive thetaScale S hrow
  have hF : IsFrostmanIn CF rowD.family rowD.ambient := by
    exact activeSelectedOwnerRowPlankDatum_isFrostmanIn_canonical
      D C q cell hcell selectedCells hmass hactive thetaScale S hrow
  haveI : Nonempty occurrence := hocc
  exact exists_centeredPlankLongTube_fresh_admissible
    rowD hbPos hbHalf hCF hF

#print axioms activeSelectedOwnerRowPlankDatum_shadingMass
#print axioms activeSelectedOwnerRowOccurrence_card
#print axioms activeSelectedOwnerRow_card_mul_floor_le_shadingMass
#print axioms activeSelectedOwnerRowOccurrence_card_bounds
#print axioms activeSelectedOwnerRowOccurrence_nonempty
#print axioms activeSelectedOwnerRowOccurrence_source_injective
#print axioms
  activeSelectedOwnerRowPlankDatum_frostmanThickenedPlankControl
#print axioms activeSelectedOwnerRow_branching_le_M_mul_theta
#print axioms activeSelectedOwnerRowPlankDatum_familyVolume_pos
#print axioms activeSelectedOwnerRowPlankDatum_isFrostmanIn_canonical
#print axioms
  activeSelectedOwnerRowPlankDatum_canonicalFrostmanConstant_ne_top
#print axioms activeSelectedOwnerRowLongTubeDatum
#print axioms exists_activeSelectedOwnerRow_fresh_admissible

end
end Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1
