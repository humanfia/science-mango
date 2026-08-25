import FamilyStickyGrounding.FamilyStickyRandomModelTubeCollisionGridV1
import FamilyStickyRandomFiniteMaximalCellCodeV1
import Submission.Kakeya.ConvexFactoring.TubeCommonSegment

open Set
open scoped NNReal

namespace FamilyStickyRandomHundredContainerSelectionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomFiniteMaximalCellCodeV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Maximal selection by a common `100`-tube container

This module isolates a deliberately strong geometric separation relation.
Two `delta`-tubes conflict when both carriers lie in one literal `100 W`.
A finite maximal selection is pairwise conflict-free and every original tube
conflicts with a selected centre (or is itself a centre).  The card loss is
not hidden: it is the maximum finite common-container neighbourhood size.

Source audit.  GWZ `260115_kakeyadetailedproofv3.tex`, random-motion lines
2655--2677, tests `100 T_0` and only concludes `X_j \lesssim 1` at line 2659.
The paper does not define `essentially distinct` there.  WZ1
`251007_sticky_kakeya_final.tex`, line 217, defines it using the line-space
metric `|p-p'| + angle(v,v')`; WZ2 `2401.12337v2`, lines 213--215, defines it
by mutual noncontainment in two-fold dilates.  Thus the relation below is a
stronger refinement device, not a renaming of the cited source definition.

In particular, the repository's Family4 volume-overlap predicate is
insufficient here.  For small `delta`, two collinear unit segments shifted by
about `0.4` have overlap about `0.6`, so they can violate the half-volume
overlap threshold while an endpoint remains much farther than `100 delta`
from the other segment.  Hence volume-overlap essential distinctness cannot
produce the containment bridge or a collision cap by itself.
-/

/-- Two equal-radius tubes have one literal paper-style `100 W` container. -/
def CommonHundredContainer {delta : NNReal} (T U : Tube delta) : Prop :=
  exists W : Tube delta,
    T.carrier ⊆ (hundredTube W).carrier ∧
    U.carrier ⊆ (hundredTube W).carrier

/-- Strong separation used only after the finite maximal refinement. -/
def NoCommonHundredContainer {delta : NNReal} (T U : Tube delta) : Prop :=
  ¬ CommonHundredContainer T U

theorem commonHundredContainer_symm {delta : NNReal} {T U : Tube delta} :
    CommonHundredContainer T U -> CommonHundredContainer U T := by
  rintro ⟨W, hT, hU⟩
  exact ⟨W, hU, hT⟩

theorem noCommonHundredContainer_symm {delta : NNReal} {T U : Tube delta} :
    NoCommonHundredContainer T U -> NoCommonHundredContainer U T := by
  intro h hUT
  exact h (commonHundredContainer_symm hUT)

@[simp] theorem translateTube_hundredTube {delta : NNReal}
    (T : Tube delta) (v : Space) :
    translateTube (hundredTube T) v =
      hundredTube (translateTube T v) := rfl

theorem translate_carrier_subset_translate_carrier
    {r R : NNReal} {T : Tube r} {U : Tube R} {v : Space}
    (h : T.carrier ⊆ U.carrier) :
    (translateTube T v).carrier ⊆ (translateTube U v).carrier := by
  rw [translateTube_carrier, translateTube_carrier]
  exact Set.image_mono h

/-- A common container transports forward under a common translation. -/
theorem CommonHundredContainer.translate {delta : NNReal}
    {T U : Tube delta} (h : CommonHundredContainer T U) (v : Space) :
    CommonHundredContainer (translateTube T v) (translateTube U v) := by
  obtain ⟨W, hT, hU⟩ := h
  refine ⟨translateTube W v, ?_, ?_⟩
  · simpa only [← translateTube_hundredTube] using
      (translate_carrier_subset_translate_carrier (v := v) hT)
  · simpa only [← translateTube_hundredTube] using
      (translate_carrier_subset_translate_carrier (v := v) hU)

/-- Translating a common container back by the inverse vector recovers a
container for the untranslated tubes.  The witness need not itself have been
presented as a translate. -/
theorem commonHundredContainer_of_translate {delta : NNReal}
    {T U : Tube delta} {v : Space}
    (h : CommonHundredContainer (translateTube T v) (translateTube U v)) :
    CommonHundredContainer T U := by
  obtain ⟨W, hT, hU⟩ := h
  refine ⟨translateTube W (-v), ?_, ?_⟩
  · intro x hx
    rw [← translateTube_hundredTube, translateTube_carrier]
    refine ⟨v + x, hT ?_, ?_⟩
    · rw [translateTube_carrier]
      exact ⟨x, hx, rfl⟩
    · simp
  · intro x hx
    rw [← translateTube_hundredTube, translateTube_carrier]
    refine ⟨v + x, hU ?_, ?_⟩
    · rw [translateTube_carrier]
      exact ⟨x, hx, rfl⟩
    · simp

/-- Strong separation is invariant under a common translation. -/
theorem NoCommonHundredContainer.translate {delta : NNReal}
    {T U : Tube delta} (h : NoCommonHundredContainer T U) (v : Space) :
    NoCommonHundredContainer (translateTube T v) (translateTube U v) := by
  intro htranslated
  exact h (commonHundredContainer_of_translate htranslated)

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]

/-- Active source occurrences retain the original finite index, including
geometrically repeated tubes if the input grid contains them. -/
abbrev ActiveSource
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :=
  {i // i ∈ G.tubes}

def sourceNoCommonRelation
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (a b : ActiveSource G) : Prop :=
  NoCommonHundredContainer (G.tube a.1) (G.tube b.1)

theorem sourceNoCommonRelation_symm
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    Std.Symm (sourceNoCommonRelation G) := by
  constructor
  intro a b hab
  exact noCommonHundredContainer_symm hab

/-- Canonical finite maximal conflict-free source selection. -/
def maximalNoCommonSelection
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    MaximalSeparatedCells (sourceNoCommonRelation G) :=
  Classical.choice
    (exists_maximalSeparatedCells (sourceNoCommonRelation G)
      (sourceNoCommonRelation_symm G))

namespace MaximalSelection

variable (G : ActualTubeTranslationGrid delta translation tubeIndex)

abbrev selection := maximalNoCommonSelection G

abbrev SelectedSource := (selection G).Cell

/-- Each original is its selected centre or shares a literal `100 W`
container with that centre.  This is produced by maximality, not assumed. -/
theorem eq_or_commonHundredContainer_code (a : ActiveSource G) :
    a = ((selection G).code a).1 ∨
      CommonHundredContainer (G.tube a.1)
        (G.tube ((selection G).code a).1.1) := by
  rcases (selection G).eq_or_not_separated_code a with heq | hnot
  · exact Or.inl heq
  · right
    exact Classical.not_not.mp hnot

/-- Selected centres are pairwise strongly separated. -/
theorem pairwise_noCommonHundredContainer :
    Set.Pairwise (Set.univ : Set (SelectedSource G)) fun a b =>
      NoCommonHundredContainer (G.tube a.1.1) (G.tube b.1.1) := by
  simpa only [sourceNoCommonRelation] using
    (selection G).pairwise_cell_centres

/-- Literal finite neighbourhood controlling the loss of the maximal
selection. -/
def commonHundredNeighbourFinset (b : ActiveSource G) :
    Finset (ActiveSource G) := by
  classical
  exact Finset.univ.filter fun a =>
    a = b ∨ CommonHundredContainer (G.tube a.1) (G.tube b.1)

/-- Exact quantified card-loss source.  A paper-level `O(1)` conclusion must
bound this number using the WZ line/tube metric packing; it is never supplied
as an unnamed callback. -/
def commonHundredNeighbourMultiplicity : Nat :=
  Finset.univ.sup fun b : ActiveSource G =>
    (commonHundredNeighbourFinset G b).card

theorem code_fiber_subset_neighbour (b : SelectedSource G) :
    (Finset.univ.filter fun a : ActiveSource G =>
      (selection G).code a = b) ⊆
      commonHundredNeighbourFinset G b.1 := by
  classical
  intro a ha
  have hcode := (Finset.mem_filter.mp ha).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases eq_or_commonHundredContainer_code G a with heq | hcommon
  · left
    exact heq.trans (congrArg Subtype.val hcode)
  · right
    simpa only [congrArg Subtype.val hcode] using hcommon

theorem code_fiber_card_le_neighbour (b : SelectedSource G) :
    (Finset.univ.filter fun a : ActiveSource G =>
      (selection G).code a = b).card <=
      (commonHundredNeighbourFinset G b.1).card :=
  Finset.card_le_card (code_fiber_subset_neighbour G b)

theorem neighbour_card_le_multiplicity (b : ActiveSource G) :
    (commonHundredNeighbourFinset G b).card <=
      commonHundredNeighbourMultiplicity G := by
  exact Finset.le_sup (s := Finset.univ)
    (f := fun c : ActiveSource G =>
      (commonHundredNeighbourFinset G c).card) (Finset.mem_univ b)

/-- Exact finite card loss of the automatically produced selection. -/
theorem active_card_le_multiplicity_mul_selected_card :
    Fintype.card (ActiveSource G) <=
      commonHundredNeighbourMultiplicity G *
        Fintype.card (SelectedSource G) := by
  apply (selection G).card_le_of_fiber_bound
  intro b
  exact (code_fiber_card_le_neighbour G b).trans
    (neighbour_card_le_multiplicity G b.1)

end MaximalSelection

/-- If the active source family is already pairwise strongly separated, then
every literal translated `100 T_0` collision cell contains at most one source
tube under any common translation. -/
theorem candidateCollisionLoad_le_one
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (hpair : Set.Pairwise (G.tubes : Set tubeIndex) fun i j =>
      NoCommonHundredContainer (G.tube i) (G.tube j))
    (a : ModelCandidate G) (g : translation) :
    candidateCollisionLoad G a g <= 1 := by
  classical
  unfold candidateCollisionLoad
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  have hi' := (mem_candidateCollisionFinset G a g i).mp hi
  have hj' := (mem_candidateCollisionFinset G a g j).mp hj
  have hsource : NoCommonHundredContainer (G.tube i) (G.tube j) :=
    hpair hi'.1 hj'.1 hij
  have htranslated := hsource.translate (G.gridVector g)
  exact htranslated ⟨modelCandidateTube G a, hi'.2, hj'.2⟩

/-- The same cap stated as the actual collision-grid single load. -/
theorem collisionGrid_singleLoad_le_one
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (hpair : Set.Pairwise (G.tubes : Set tubeIndex) fun i j =>
      NoCommonHundredContainer (G.tube i) (G.tube j))
    (a : ModelCandidate G) (g : translation) :
    (collisionGrid G).singleLoad (modelCandidateIndex G a) g <= 1 := by
  rw [collisionGrid_singleLoad_candidate]
  exact candidateCollisionLoad_le_one G hpair a g

/-- Restrict the source index to the automatically selected centres while
keeping the shared translation packing and the old auxiliary test suite.
The collision catalogue built later is regenerated from this selected source
family, so no unselected tube is smuggled into a `100 T_0` test. -/
def selectedGrid
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    ActualTubeTranslationGrid delta translation
      (MaximalSelection.SelectedSource G) where
  gridVector := G.gridVector
  tubes := Finset.univ
  tube := fun a => G.tube a.1.1
  testCard := G.testCard
  testBody := G.testBody
  activeTests := G.activeTests

@[simp] theorem selectedGrid_gridVector
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    (selectedGrid G).gridVector = G.gridVector := rfl

@[simp] theorem selectedGrid_tubes
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    (selectedGrid G).tubes = Finset.univ := rfl

theorem selectedGrid_pairwise_noCommonHundredContainer
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    Set.Pairwise ((selectedGrid G).tubes :
      Set (MaximalSelection.SelectedSource G)) fun a b =>
        NoCommonHundredContainer
          ((selectedGrid G).tube a) ((selectedGrid G).tube b) := by
  intro a _ha b _hb hab
  change NoCommonHundredContainer
    (G.tube a.1.1) (G.tube b.1.1)
  exact (MaximalSelection.pairwise_noCommonHundredContainer G)
    (Set.mem_univ a) (Set.mem_univ b) hab

/-- The maximal producer discharges the strong-separation input, yielding an
automatic strict cap one for every single translation and every regenerated
collision cell. -/
theorem selectedCollisionGrid_singleLoad_le_one
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (a : ModelCandidate (selectedGrid G)) (g : translation) :
    (collisionGrid (selectedGrid G)).singleLoad
      (modelCandidateIndex (selectedGrid G) a) g <= 1 := by
  exact collisionGrid_singleLoad_le_one (selectedGrid G)
    (selectedGrid_pairwise_noCommonHundredContainer G) a g

#print axioms CommonHundredContainer.translate
#print axioms commonHundredContainer_of_translate
#print axioms NoCommonHundredContainer.translate
#print axioms MaximalSelection.eq_or_commonHundredContainer_code
#print axioms MaximalSelection.pairwise_noCommonHundredContainer
#print axioms MaximalSelection.active_card_le_multiplicity_mul_selected_card
#print axioms candidateCollisionLoad_le_one
#print axioms collisionGrid_singleLoad_le_one
#print axioms selectedCollisionGrid_singleLoad_le_one

end
end FamilyStickyRandomHundredContainerSelectionV1
