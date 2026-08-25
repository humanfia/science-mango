import FamilyStickyGrounding.FamilyStickyLatticeBoxPointCountV1

open Set
open scoped BigOperators NNReal InnerProductSpace

namespace FamilyStickyLatticeMultiBoxPointCountV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyLatticeBoxPointCountV1

noncomputable section

/-!
# A simultaneous finite lattice for finitely many oriented boxes

Each test box gets its own three-coordinate lattice block, in its own
orthonormal frame.  A global translation is the sum of one choice from every
block.  When all blocks except the one belonging to a fixed test are frozen,
the one-box separation theorem gives at most one successful choice.  Hence
the point-hit count is bounded by the number of choices in the other blocks.
This is a finite product/fibre count, not a probabilistic callback.
-/

/-- Box-specific lattice data for a finite collection of oriented tests. -/
structure MultiBoxLattice (test : Type*) [Fintype test] [DecidableEq test] where
  box : test -> FrameBox
  spacing : test -> Fin 3 -> NNReal
  siteCount : test -> Fin 3 -> Nat
  side_lt_spacing : forall K i, (box K).side i < spacing K i

/-- The coordinate-lattice block belonging to one test. -/
abbrev MultiBoxLattice.Block {test : Type*} [Fintype test] [DecidableEq test]
    (L : MultiBoxLattice test) (K : test) :=
  BoxLatticeSites (L.siteCount K)

/-- A global finite translation choice, one lattice block per test. -/
abbrev MultiBoxLattice.Choice {test : Type*} [Fintype test] [DecidableEq test]
    (L : MultiBoxLattice test) :=
  forall K, L.Block K

/-- Choices in every block except the distinguished test block. -/
abbrev MultiBoxLattice.OtherChoice
    {test : Type*} [Fintype test] [DecidableEq test]
    (L : MultiBoxLattice test) (K : test) :=
  forall J : {J // J ≠ K}, L.Block J.1

namespace MultiBoxLattice

variable {test : Type*} [Fintype test] [DecidableEq test]

/-- The actual ambient translation vector of a global product choice. -/
def choiceVector (L : MultiBoxLattice test) (omega : L.Choice) : Space :=
  ∑ K, boxLatticeVector (L.box K) (L.spacing K) (omega K)

/-- Forget the block of one distinguished test. -/
def dropChoice (L : MultiBoxLattice test) (K : test)
    (omega : L.Choice) : L.OtherChoice K :=
  (Equiv.piSplitAt K (fun J => L.Block J) omega).2

/-- The global product cardinality splits into the distinguished block and
all other blocks. -/
theorem card_choice_eq_card_block_mul_card_other
    (L : MultiBoxLattice test) (K : test) :
    Fintype.card L.Choice =
      Fintype.card (L.Block K) * Fintype.card (L.OtherChoice K) := by
  simpa using Fintype.card_congr (Equiv.piSplitAt K (fun J => L.Block J))

/-- One distinguished block has exactly the product of its three explicit coordinate counts. -/
theorem card_block_eq_prod_siteCount
    (L : MultiBoxLattice test) (K : test) :
    Fintype.card (L.Block K) = ∏ i, L.siteCount K i := by
  simp [MultiBoxLattice.Block, BoxLatticeSites, Fintype.card_pi]

/-- The sum of all product-block vectors splits into the distinguished
vector plus the sum over the remaining test indices. -/
theorem choiceVector_eq_block_add_erase
    (L : MultiBoxLattice test) (K : test) (omega : L.Choice) :
    L.choiceVector omega =
      boxLatticeVector (L.box K) (L.spacing K) (omega K) +
        ∑ J ∈ Finset.univ.erase K,
          boxLatticeVector (L.box J) (L.spacing J) (omega J) := by
  exact (Finset.add_sum_erase Finset.univ
    (fun J => boxLatticeVector (L.box J) (L.spacing J) (omega J))
    (Finset.mem_univ K)).symm

/-- Equal dropped choices give equal remaining-vector sums. -/
theorem sum_erase_eq_of_dropChoice_eq
    (L : MultiBoxLattice test) (K : test) {omega eta : L.Choice}
    (hdrop : L.dropChoice K omega = L.dropChoice K eta) :
    (∑ J ∈ Finset.univ.erase K,
        boxLatticeVector (L.box J) (L.spacing J) (omega J)) =
      ∑ J ∈ Finset.univ.erase K,
        boxLatticeVector (L.box J) (L.spacing J) (eta J) := by
  apply Finset.sum_congr rfl
  intro J hJ
  have hJK : J ≠ K := Finset.ne_of_mem_erase hJ
  have hvalue := congrFun hdrop (⟨J, hJK⟩ : {J // J ≠ K})
  change omega J = eta J at hvalue
  rw [hvalue]

/-- On the point-hit fibre for one box, dropping its own lattice block is
injective. -/
theorem choice_eq_of_dropChoice_eq_of_add_mem_box
    (L : MultiBoxLattice test) (K : test) (x : Space)
    {omega eta : L.Choice}
    (homega : x + L.choiceVector omega ∈ (L.box K).carrier)
    (heta : x + L.choiceVector eta ∈ (L.box K).carrier)
    (hdrop : L.dropChoice K omega = L.dropChoice K eta) :
    omega = eta := by
  let remainder : Space :=
    ∑ J ∈ Finset.univ.erase K,
      boxLatticeVector (L.box J) (L.spacing J) (omega J)
  have hremainder :
      remainder = ∑ J ∈ Finset.univ.erase K,
        boxLatticeVector (L.box J) (L.spacing J) (eta J) := by
    exact L.sum_erase_eq_of_dropChoice_eq K hdrop
  have homega' :
      (x + remainder) +
          boxLatticeVector (L.box K) (L.spacing K) (omega K) ∈
        (L.box K).carrier := by
    rw [L.choiceVector_eq_block_add_erase K omega] at homega
    simpa only [remainder, add_assoc, add_left_comm, add_comm] using homega
  have heta' :
      (x + remainder) +
          boxLatticeVector (L.box K) (L.spacing K) (eta K) ∈
        (L.box K).carrier := by
    rw [L.choiceVector_eq_block_add_erase K eta] at heta
    rw [hremainder]
    simpa only [add_assoc, add_left_comm, add_comm] using heta
  have hK : omega K = eta K :=
    boxLatticeSites_eq_of_add_mem_carrier
      (L.box K) (L.spacing K) (L.side_lt_spacing K)
      (x + remainder) (omega K) (eta K) homega' heta'
  funext J
  by_cases hJK : J = K
  · subst J
    exact hK
  · have hvalue := congrFun hdrop (⟨J, hJK⟩ : {J // J ≠ K})
    exact hvalue

/-- Literal number of global product choices moving one point into one
distinguished test box. -/
def pointHitCount (L : MultiBoxLattice test) (K : test) (x : Space) : Nat := by
  classical
  exact (Finset.univ.filter fun omega : L.Choice =>
    x + L.choiceVector omega ∈ (L.box K).carrier).card

/-- Fibre count for the simultaneous product lattice: the hit count for a
fixed test is at most the cardinality of all other blocks. -/
theorem pointHitCount_le_card_other
    (L : MultiBoxLattice test) (K : test) (x : Space) :
    L.pointHitCount K x <= Fintype.card (L.OtherChoice K) := by
  classical
  let hits : Finset L.Choice := Finset.univ.filter fun omega =>
    x + L.choiceVector omega ∈ (L.box K).carrier
  let drop : ↥hits -> L.OtherChoice K :=
    fun omega => L.dropChoice K omega.1
  have hdrop : Function.Injective drop := by
    intro omega eta heq
    apply Subtype.ext
    apply L.choice_eq_of_dropChoice_eq_of_add_mem_box K x
    · exact (Finset.mem_filter.mp omega.2).2
    · exact (Finset.mem_filter.mp eta.2).2
    · exact heq
  have hcard := Fintype.card_le_of_injective drop hdrop
  simpa only [pointHitCount, hits, Fintype.card_coe] using hcard

#print axioms card_choice_eq_card_block_mul_card_other
#print axioms card_block_eq_prod_siteCount
#print axioms choiceVector_eq_block_add_erase
#print axioms sum_erase_eq_of_dropChoice_eq
#print axioms choice_eq_of_dropChoice_eq_of_add_mem_box
#print axioms pointHitCount_le_card_other

end MultiBoxLattice

end

end FamilyStickyLatticeMultiBoxPointCountV1
