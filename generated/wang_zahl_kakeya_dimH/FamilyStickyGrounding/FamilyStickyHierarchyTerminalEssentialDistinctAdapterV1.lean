import FamilyStickyGrounding.FamilyStickyHierarchyTerminalCarrierDedupV1
import Family4GlobalExtremalUpstream

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal

namespace FamilyStickyHierarchyTerminalEssentialDistinctAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomHundredContainerSelectionV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1.HierarchyJointRandomMotionCertificate
open FamilyStickyHierarchyTerminalCarrierDedupV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Terminal strong separation and paper essential distinctness

The repository has one concrete predicate named `EssentiallyDistinct`: the
Family4 half-volume overlap condition.  The random-motion terminal selection,
on the other hand, supplies `NoCommonHundredContainer`.  These notions cannot
be identified without further geometry.  In particular, longitudinally
shifted, almost coincident unit tubes can overlap in more than half their
volume while failing to fit in one unit-length `100 delta` tube when `delta`
is sufficiently small.

WZ2 uses a different literal definition: neither tube is contained in the
two-fold radial enlargement of the other.  This module records that relation
and proves that terminal strong representatives satisfy it.  It also packages
the representatives as a uniform tube family and isolates the exact local
seam required by downstream modules that specifically demand the Family4
volume-overlap predicate.
-/

/-! ## The WZ2 two-fold noncontainment relation -/

/-- Twice the certified tube radius. -/
def twoRadius (delta : NNReal) : NNReal := 2 * delta

/-- The two-fold radial enlargement, with the same unit axis. -/
def twoTube {delta : NNReal} (T : Tube delta) : Tube (twoRadius delta) :=
  T.changeRadius (twoRadius delta)

@[simp]
theorem twoTube_axis {delta : NNReal} (T : Tube delta) :
    (twoTube T).axis = T.axis :=
  rfl

theorem radius_le_twoRadius (delta : NNReal) : delta <= twoRadius delta := by
  unfold twoRadius
  nlinarith [delta.2]

theorem twoRadius_le_hundredRadius (delta : NNReal) :
    twoRadius delta <= hundredRadius delta := by
  unfold twoRadius hundredRadius
  nlinarith [delta.2]

/-- Every tube is contained in its two-fold radial enlargement. -/
theorem carrier_subset_twoTube {delta : NNReal} (T : Tube delta) :
    T.carrier ⊆ (twoTube T).carrier := by
  exact T.carrier_subset_changeRadius (radius_le_twoRadius delta)

/-- The two-fold enlargement is contained in the corresponding `100`-fold
enlargement. -/
theorem twoTube_carrier_subset_hundredTube {delta : NNReal} (T : Tube delta) :
    (twoTube T).carrier ⊆ (hundredTube T).carrier := by
  rw [twoTube, hundredTube, Tube.changeRadius_carrier, Tube.changeRadius_carrier]
  exact Metric.cthickening_mono
    (by exact_mod_cast twoRadius_le_hundredRadius delta) T.axis.carrier

/-- WZ2-style essential distinctness: neither tube lies in the two-fold
radial enlargement of the other. -/
def WZ2EssentiallyDistinct {delta : NNReal} (T U : Tube delta) : Prop :=
  (¬ T.carrier ⊆ (twoTube U).carrier) ∧
    ¬ U.carrier ⊆ (twoTube T).carrier

theorem wz2EssentiallyDistinct_symm {delta : NNReal} {T U : Tube delta} :
    WZ2EssentiallyDistinct T U -> WZ2EssentiallyDistinct U T := by
  rintro ⟨hTU, hUT⟩
  exact ⟨hUT, hTU⟩

theorem WZ2EssentiallyDistinct.carrier_ne
    {delta : NNReal} {T U : Tube delta}
    (h : WZ2EssentiallyDistinct T U) :
    T.carrier ≠ U.carrier := by
  intro hcarrier
  exact h.1 (hcarrier.subset.trans (carrier_subset_twoTube U))

theorem WZ2EssentiallyDistinct.tube_ne
    {delta : NNReal} {T U : Tube delta}
    (h : WZ2EssentiallyDistinct T U) :
    T ≠ U := by
  intro htube
  exact h.carrier_ne (congrArg Tube.carrier htube)

/-- One-sided containment in a two-fold enlargement already gives a common
`100`-fold container. -/
theorem commonHundredContainer_of_left_subset_twoTube
    {delta : NNReal} {T U : Tube delta}
    (hTU : T.carrier ⊆ (twoTube U).carrier) :
    CommonHundredContainer T U := by
  refine ⟨U, hTU.trans (twoTube_carrier_subset_hundredTube U), ?_⟩
  exact carrier_subset_hundredTube U

theorem commonHundredContainer_of_right_subset_twoTube
    {delta : NNReal} {T U : Tube delta}
    (hUT : U.carrier ⊆ (twoTube T).carrier) :
    CommonHundredContainer T U := by
  refine ⟨T, carrier_subset_hundredTube T, ?_⟩
  exact hUT.trans (twoTube_carrier_subset_hundredTube T)

/-- Strong common-container separation implies the literal WZ2 relation. -/
theorem wz2EssentiallyDistinct_of_noCommonHundredContainer
    {delta : NNReal} {T U : Tube delta}
    (h : NoCommonHundredContainer T U) :
    WZ2EssentiallyDistinct T U := by
  constructor
  · intro hTU
    exact h (commonHundredContainer_of_left_subset_twoTube hTU)
  · intro hUT
    exact h (commonHundredContainer_of_right_subset_twoTube hUT)

/-! ## Connection to terminal carrier deduplication -/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  (C : HierarchyJointRandomMotionCertificate H G)

/-- The strong terminal representatives satisfy the WZ2 relation with no
additional geometric input. -/
theorem terminalStrongRepresentatives_pairwise_wz2EssentiallyDistinct :
    Set.Pairwise
      (terminalStrongRepresentatives C : Set C.FinalIndex)
      fun a b => WZ2EssentiallyDistinct (C.finalTube a) (C.finalTube b) := by
  intro a ha b hb hab
  exact wz2EssentiallyDistinct_of_noCommonHundredContainer
    (terminalStrongRepresentatives_pairwise_noCommonHundredContainer C
      ha hb hab)

/-- The occurrence-indexed terminal tubes, with a loss-one scale-empty
refinement used only to expose the standard `UniformTubeFamily` interface. -/
def terminalTubeFamily :
    UniformTubeFamily (H.effectiveRadius 0) C.FinalIndex where
  tubes := C.finalTube
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp]
theorem terminalTubeFamily_tubes (a : C.FinalIndex) :
    (terminalTubeFamily C).tubes a = C.finalTube a :=
  rfl

/-- Index type of the canonical strong terminal representative family. -/
abbrev TerminalStrongIndex :=
  {a : C.FinalIndex // a ∈ terminalStrongRepresentatives C}

/-- The canonical terminal strong representatives as a standard uniform tube
family.  Its refinement contains every subtype index. -/
def terminalStrongTubeFamily :
    UniformTubeFamily (H.effectiveRadius 0) (TerminalStrongIndex C) :=
  (terminalTubeFamily C).restrictTo (terminalStrongRepresentatives C)

@[simp]
theorem terminalStrongTubeFamily_tubes (a : TerminalStrongIndex C) :
    (terminalStrongTubeFamily C).tubes a = C.finalTube a.1 :=
  rfl

@[simp]
theorem terminalStrongTubeFamily_refined :
    (terminalStrongTubeFamily C).refinement.refined = Finset.univ :=
  rfl

theorem terminalStrongTubeFamily_pairwise_wz2EssentiallyDistinct :
    Set.Pairwise (Set.univ : Set (TerminalStrongIndex C)) fun a b =>
      WZ2EssentiallyDistinct
        ((terminalStrongTubeFamily C).tubes a)
        ((terminalStrongTubeFamily C).tubes b) := by
  intro a _ha b _hb hab
  simpa only [terminalStrongTubeFamily_tubes] using
    (terminalStrongRepresentatives_pairwise_wz2EssentiallyDistinct C
      a.2 b.2 (Subtype.coe_ne_coe.mpr hab))

/-- WZ2 separation already makes the tube map injective, independently of
the volume-overlap predicate and without a positive-radius premise. -/
theorem terminalStrongTubeFamily_tubes_injective :
    Function.Injective (terminalStrongTubeFamily C).tubes := by
  intro a b htube
  by_contra hab
  have hsep := terminalStrongTubeFamily_pairwise_wz2EssentiallyDistinct C
    (Set.mem_univ a) (Set.mem_univ b) hab
  exact hsep.tube_ne htube

/-- Concrete image of the terminal strong representative tubes. -/
noncomputable def terminalStrongTubeImage : Finset (Tube (H.effectiveRadius 0)) := by
  classical
  exact Finset.univ.image (terminalStrongTubeFamily C).tubes

theorem terminalStrongTubeImage_card :
    (terminalStrongTubeImage C).card =
      (terminalStrongRepresentatives C).card := by
  classical
  rw [terminalStrongTubeImage,
    Finset.card_image_of_injective _
      (terminalStrongTubeFamily_tubes_injective C),
    Finset.card_univ, Fintype.card_coe]

/-! ## Exact seam to the repository's volume-overlap predicate -/

/-- The minimal extra geometric input needed only by downstream results that
specifically require Family4's half-volume-overlap notion.  It is local to the
already selected finite family; no generally false implication between the
two global notions is asserted. -/
def TerminalWZ2ToVolumeEssentiallyDistinctSeam : Prop :=
  forall a b : TerminalStrongIndex C, a ≠ b ->
    WZ2EssentiallyDistinct
      ((terminalStrongTubeFamily C).tubes a)
      ((terminalStrongTubeFamily C).tubes b) ->
    EssentiallyDistinct
      ((terminalStrongTubeFamily C).tubes a)
      ((terminalStrongTubeFamily C).tubes b)

/-- Under precisely the local seam above, the packaged terminal family meets
the pairwise volume-overlap hypothesis consumed by the Cinematic modules. -/
theorem terminalStrongTubeFamily_pairwise_volumeEssentiallyDistinct
    (hseam : TerminalWZ2ToVolumeEssentiallyDistinctSeam C) :
    Set.Pairwise (Set.univ : Set (TerminalStrongIndex C)) fun a b =>
      EssentiallyDistinct
        ((terminalStrongTubeFamily C).tubes a)
        ((terminalStrongTubeFamily C).tubes b) := by
  intro a _ha b _hb hab
  exact hseam a b hab
    (terminalStrongTubeFamily_pairwise_wz2EssentiallyDistinct C
      (Set.mem_univ a) (Set.mem_univ b) hab)

theorem terminalStrongRepresentatives_pairwise_volumeEssentiallyDistinct
    (hseam : TerminalWZ2ToVolumeEssentiallyDistinctSeam C) :
    Set.Pairwise
      (terminalStrongRepresentatives C : Set C.FinalIndex)
      fun a b => EssentiallyDistinct (C.finalTube a) (C.finalTube b) := by
  intro a ha b hb hab
  let a' : TerminalStrongIndex C := ⟨a, ha⟩
  let b' : TerminalStrongIndex C := ⟨b, hb⟩
  have hab' : a' ≠ b' := by
    intro hEq
    exact hab (congrArg Subtype.val hEq)
  simpa only [terminalStrongTubeFamily_tubes] using
    (terminalStrongTubeFamily_pairwise_volumeEssentiallyDistinct C hseam
      (Set.mem_univ a') (Set.mem_univ b') hab')

#print axioms wz2EssentiallyDistinct_of_noCommonHundredContainer
#print axioms terminalStrongRepresentatives_pairwise_wz2EssentiallyDistinct
#print axioms terminalStrongTubeFamily_tubes_injective
#print axioms terminalStrongTubeImage_card
#print axioms terminalStrongTubeFamily_pairwise_volumeEssentiallyDistinct

end

end FamilyStickyHierarchyTerminalEssentialDistinctAdapterV1
