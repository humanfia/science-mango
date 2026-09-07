import Family8Grounding.Family8PlankThickControlActualClusterV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55FiniteMaximalIncomparableClusteringV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankThickControlMutualContainmentClusteringV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlActualClusterV1
open FamilyStickyCinematicL32Lemma55FiniteMaximalIncomparableClusteringV1

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Lossless clustering by actual mutual plank thickening

At one fixed admissible scale, two source planks are declared comparable
exactly when each belongs to the other's literal `theta * b` thickening
cluster.  A maximal independent set gives genuine selected seeds and an
owner map.  Every owner fibre lies in its selected seed's actual thickening,
so `FrostmanThickenedPlankControl` bounds that fibre by `M * theta`.

V1 failed only the strict unused-section-variable linter and is not imported.\n+\n+The owner fibres partition both source cardinality and source shaded mass
exactly.  This is the finite construction behind the `N <= M * theta` part
of paper Lemma 6.13; it does not assert the later slab/tangency refinement or
any multiplicity conclusion.
-/

/-- Symmetric comparability witnessed by the two literal source-plank
containments at the fixed thickening scale. -/
def MutualThickeningComparable
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal)
    (i j : iota) : Prop :=
  j ∈ thickenedPlankIndices D theta i ∧
    i ∈ thickenedPlankIndices D theta j

theorem mutualThickeningComparable_symm
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    Std.Symm (MutualThickeningComparable D theta) := by
  constructor
  intro i j hij
  exact ⟨hij.2, hij.1⟩

/-- A lossless actual owner clustering of all source planks. -/
structure MutualThickeningClustering
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) where
  selected : Finset iota
  owner : iota → iota
  selected_nonempty : selected.Nonempty
  selected_pairwise : Set.Pairwise (selected : Set iota)
    (fun i j ↦ ¬ MutualThickeningComparable D theta i j)
  owner_selected : ∀ i, owner i ∈ selected
  owner_eq_or_comparable : ∀ i,
    owner i = i ∨ MutualThickeningComparable D theta (owner i) i
  card_partition : Fintype.card iota =
    ∑ s ∈ selected, (Finset.univ.filter fun i ↦ owner i = s).card
  mass_partition : D.shading.shadingMass =
    ∑ s ∈ selected,
      ∑ i ∈ Finset.univ.filter (fun i ↦ owner i = s),
        volume (D.shading.carrier i)

/-- The actual source indices assigned to one selected thickening seed. -/
def ownerFiber
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta) (s : iota) : Finset iota :=
  Finset.univ.filter fun i ↦ C.owner i = s

@[simp] theorem mem_ownerFiber
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta) (s i : iota) :
    i ∈ ownerFiber C s ↔ C.owner i = s := by
  simp [ownerFiber]

/-- Maximal finite clustering with the exact source shading weights. -/
theorem exists_mutualThickeningClustering
    [Nonempty iota]
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    Nonempty (MutualThickeningClustering D theta) := by
  classical
  obtain ⟨selected, owner, _hsubset, hnonempty, hpairwise,
      hownerSelected, hownerComparable, hcard, hmass⟩ :=
    exists_maximal_pairwise_not_relation_clustering
      (Finset.univ : Finset iota)
      (MutualThickeningComparable D theta)
      (mutualThickeningComparable_symm D theta)
      (fun i ↦ volume (D.shading.carrier i))
  have hselectedNonempty : selected.Nonempty :=
    hnonempty Finset.univ_nonempty
  refine ⟨{
    selected := selected
    owner := owner
    selected_nonempty := hselectedNonempty
    selected_pairwise := hpairwise
    owner_selected := fun i ↦ hownerSelected i (Finset.mem_univ i)
    owner_eq_or_comparable := fun i ↦
      hownerComparable i (Finset.mem_univ i)
    card_partition := ?_
    mass_partition := ?_ }⟩
  · simpa only [Finset.card_univ] using hcard
  · simpa only [Shading.shadingMass] using hmass

/-- A selected seed owns itself.  Otherwise two distinct selected seeds
would be comparable, contradicting maximal independence. -/
theorem owner_eq_self_of_selected
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta) {s : iota}
    (hs : s ∈ C.selected) :
    C.owner s = s := by
  rcases C.owner_eq_or_comparable s with h | h
  · exact h
  · by_contra hne
    exact (C.selected_pairwise (C.owner_selected s) hs hne) h

/-- Every selected owner fibre is genuinely occupied. -/
theorem ownerFiber_nonempty_of_selected
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta) {s : iota}
    (hs : s ∈ C.selected) :
    (ownerFiber C s).Nonempty := by
  exact ⟨s, (mem_ownerFiber C s s).2 (owner_eq_self_of_selected C hs)⟩

/-- Each literal owner fibre lies inside the selected seed's actual source
thickening cluster. -/
theorem ownerFiber_subset_thickenedPlankIndices
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta) (s : iota) :
    ownerFiber C s ⊆ thickenedPlankIndices D theta s := by
  intro i hi
  have howner : C.owner i = s := (mem_ownerFiber C s i).1 hi
  rcases C.owner_eq_or_comparable i with heq | hcomp
  · have his : i = s := by simpa [howner] using heq.symm
    subst i
    exact source_mem_thickenedPlankIndices D theta s
  · simpa only [howner] using hcomp.1

/-- The paper's `N <= M * theta` bound on every selected owner fibre,
derived from the genuine thick-control field. -/
theorem ownerFiber_card_le
    (D : ShadedConvexPlankFamily iota a b) (M theta : NNReal)
    (C : MutualThickeningClustering D theta)
    (hthick : FrostmanThickenedPlankControl D M)
    (hatheta : a / b ≤ theta) (htheta : theta ≤ 1)
    (s : iota) :
    ((ownerFiber C s).card : ENNReal) ≤
      (M : ENNReal) * (theta : ENNReal) := by
  calc
    ((ownerFiber C s).card : ENNReal) ≤
        ((thickenedPlankIndices D theta s).card : ENNReal) := by
      exact_mod_cast Finset.card_le_card
        (ownerFiber_subset_thickenedPlankIndices C s)
    _ ≤ (M : ENNReal) * (theta : ENNReal) :=
      hthick.2 theta hatheta htheta s

/-- Exact source cardinality partition in owner-fibre notation. -/
theorem card_eq_sum_ownerFiber_card
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta) :
    Fintype.card iota =
      ∑ s ∈ C.selected, (ownerFiber C s).card := by
  simpa only [ownerFiber] using C.card_partition

/-- Exact source shaded-mass partition in owner-fibre notation. -/
theorem shadingMass_eq_sum_ownerFiber_mass
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta) :
    D.shading.shadingMass =
      ∑ s ∈ C.selected,
        ∑ i ∈ ownerFiber C s, volume (D.shading.carrier i) := by
  simpa only [ownerFiber] using C.mass_partition

#print axioms mutualThickeningComparable_symm
#print axioms exists_mutualThickeningClustering
#print axioms owner_eq_self_of_selected
#print axioms ownerFiber_nonempty_of_selected
#print axioms ownerFiber_subset_thickenedPlankIndices
#print axioms ownerFiber_card_le
#print axioms card_eq_sum_ownerFiber_card
#print axioms shadingMass_eq_sum_ownerFiber_mass

end
end Family8PlankThickControlMutualContainmentClusteringV2
