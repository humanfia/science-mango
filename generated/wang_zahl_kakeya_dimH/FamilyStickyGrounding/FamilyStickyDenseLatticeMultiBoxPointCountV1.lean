import FamilyStickyGrounding.FamilyStickyDenseLatticeBoxPointCountV1

open Set
open scoped BigOperators NNReal InnerProductSpace

namespace FamilyStickyDenseLatticeMultiBoxPointCountV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyLatticeBoxPointCountV1
open FamilyStickyDenseLatticeBoxPointCountV1

noncomputable section

/-!
# Simultaneous dense product lattice for oriented test boxes

Every test gets an arbitrarily fine positive-spacing coordinate block.  Its
canonical coordinate hit budgets are `ceil(side / spacing) + 1`.  For a fixed
test, a hit is encoded by all other blocks together with the three residues of
its own block.  This gives the exact enlarged fibre cap

`card(other blocks) * prod_i (ceil(side_i / spacing_i) + 1)`.
-/

/-- Dense box-specific lattice data.  Unlike the earlier one-hit structure,
no spacing-versus-side separation is imposed. -/
structure DenseMultiBoxLattice (test : Type*) [Fintype test] [DecidableEq test] where
  box : test -> FrameBox
  spacing : test -> Fin 3 -> NNReal
  siteCount : test -> Fin 3 -> Nat
  spacing_pos : forall K i, 0 < spacing K i

namespace DenseMultiBoxLattice

variable {test : Type*} [Fintype test] [DecidableEq test]

abbrev Block (L : DenseMultiBoxLattice test) (K : test) :=
  BoxLatticeSites (L.siteCount K)

abbrev Choice (L : DenseMultiBoxLattice test) :=
  forall K, L.Block K

abbrev OtherChoice (L : DenseMultiBoxLattice test) (K : test) :=
  forall J : {J // J ≠ K}, L.Block J.1

/-- Canonical per-coordinate dense hit budget. -/
def hitBudget (L : DenseMultiBoxLattice test) (K : test) (i : Fin 3) : Nat :=
  ceilHitBudget (L.box K) (L.spacing K) i

/-- Product of the three canonical coordinate hit budgets. -/
def blockHitBudget (L : DenseMultiBoxLattice test) (K : test) : Nat :=
  ∏ i, L.hitBudget K i

theorem hitBudget_pos (L : DenseMultiBoxLattice test) (K : test) (i : Fin 3) :
    0 < L.hitBudget K i :=
  ceilHitBudget_pos (L.box K) (L.spacing K) i

theorem side_lt_hitBudget_mul_spacing
    (L : DenseMultiBoxLattice test) (K : test) (i : Fin 3) :
    ((L.box K).side i : Real) <
      (L.hitBudget K i : Real) * (L.spacing K i : Real) :=
  side_lt_ceilHitBudget_mul_spacing
    (L.box K) (L.spacing K) (L.spacing_pos K) i

/-- Actual ambient sum of all dense lattice blocks. -/
def choiceVector (L : DenseMultiBoxLattice test) (omega : L.Choice) : Space :=
  ∑ K, boxLatticeVector (L.box K) (L.spacing K) (omega K)

def dropChoice (L : DenseMultiBoxLattice test) (K : test)
    (omega : L.Choice) : L.OtherChoice K :=
  (Equiv.piSplitAt K (fun J => L.Block J) omega).2

theorem card_choice_eq_card_block_mul_card_other
    (L : DenseMultiBoxLattice test) (K : test) :
    Fintype.card L.Choice =
      Fintype.card (L.Block K) * Fintype.card (L.OtherChoice K) := by
  simpa using Fintype.card_congr (Equiv.piSplitAt K (fun J => L.Block J))

theorem card_block_eq_prod_siteCount
    (L : DenseMultiBoxLattice test) (K : test) :
    Fintype.card (L.Block K) = ∏ i, L.siteCount K i := by
  simp [DenseMultiBoxLattice.Block, BoxLatticeSites, Fintype.card_pi]

theorem card_residues_eq_blockHitBudget
    (L : DenseMultiBoxLattice test) (K : test) :
    Fintype.card (BoxLatticeResidues (L.hitBudget K)) =
      L.blockHitBudget K := by
  simp [BoxLatticeResidues, blockHitBudget, Fintype.card_pi]

theorem choiceVector_eq_block_add_erase
    (L : DenseMultiBoxLattice test) (K : test) (omega : L.Choice) :
    L.choiceVector omega =
      boxLatticeVector (L.box K) (L.spacing K) (omega K) +
        ∑ J ∈ Finset.univ.erase K,
          boxLatticeVector (L.box J) (L.spacing J) (omega J) := by
  exact (Finset.add_sum_erase Finset.univ
    (fun J => boxLatticeVector (L.box J) (L.spacing J) (omega J))
    (Finset.mem_univ K)).symm

theorem sum_erase_eq_of_dropChoice_eq
    (L : DenseMultiBoxLattice test) (K : test) {omega eta : L.Choice}
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

/-- A dense hit is determined by the other blocks and the residue vector of
the distinguished block. -/
theorem choice_eq_of_dropChoice_eq_of_residue_eq_of_add_mem_box
    (L : DenseMultiBoxLattice test) (K : test) (x : Space)
    {omega eta : L.Choice}
    (homega : x + L.choiceVector omega ∈ (L.box K).carrier)
    (heta : x + L.choiceVector eta ∈ (L.box K).carrier)
    (hdrop : L.dropChoice K omega = L.dropChoice K eta)
    (hresidue :
      boxLatticeResidue (L.hitBudget_pos K) (omega K) =
        boxLatticeResidue (L.hitBudget_pos K) (eta K)) :
    omega = eta := by
  let remainder : Space :=
    ∑ J ∈ Finset.univ.erase K,
      boxLatticeVector (L.box J) (L.spacing J) (omega J)
  have hremainder :
      remainder = ∑ J ∈ Finset.univ.erase K,
        boxLatticeVector (L.box J) (L.spacing J) (eta J) :=
    L.sum_erase_eq_of_dropChoice_eq K hdrop
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
    boxLatticeSites_eq_of_residue_eq_of_add_mem_carrier
      (L.box K) (L.spacing K) (L.hitBudget_pos K)
      (L.side_lt_hitBudget_mul_spacing K) (x + remainder)
      (omega K) (eta K) homega' heta' hresidue
  funext J
  by_cases hJK : J = K
  · subst J
    exact hK
  · exact congrFun hdrop (⟨J, hJK⟩ : {J // J ≠ K})

/-- Literal number of global dense choices translating one point into the
distinguished oriented box. -/
def pointHitCount (L : DenseMultiBoxLattice test) (K : test) (x : Space) : Nat := by
  classical
  exact (Finset.univ.filter fun omega : L.Choice =>
    x + L.choiceVector omega ∈ (L.box K).carrier).card

/-- Exact enlarged dense-grid fibre cap. -/
theorem pointHitCount_le_card_other_mul_blockHitBudget
    (L : DenseMultiBoxLattice test) (K : test) (x : Space) :
    L.pointHitCount K x <=
      Fintype.card (L.OtherChoice K) * L.blockHitBudget K := by
  classical
  let hits : Finset L.Choice := Finset.univ.filter fun omega =>
    x + L.choiceVector omega ∈ (L.box K).carrier
  let encode : ↥hits ->
      L.OtherChoice K × BoxLatticeResidues (L.hitBudget K) :=
    fun omega =>
      (L.dropChoice K omega.1,
        boxLatticeResidue (L.hitBudget_pos K) (omega.1 K))
  have hencode : Function.Injective encode := by
    intro omega eta heq
    apply Subtype.ext
    apply L.choice_eq_of_dropChoice_eq_of_residue_eq_of_add_mem_box K x
    · exact (Finset.mem_filter.mp omega.2).2
    · exact (Finset.mem_filter.mp eta.2).2
    · exact congrArg Prod.fst heq
    · exact congrArg Prod.snd heq
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa only [pointHitCount, hits, Fintype.card_coe, Fintype.card_prod,
    L.card_residues_eq_blockHitBudget K] using hcard

#print axioms side_lt_hitBudget_mul_spacing
#print axioms card_choice_eq_card_block_mul_card_other
#print axioms card_block_eq_prod_siteCount
#print axioms choice_eq_of_dropChoice_eq_of_residue_eq_of_add_mem_box
#print axioms pointHitCount_le_card_other_mul_blockHitBudget

end DenseMultiBoxLattice

end

end FamilyStickyDenseLatticeMultiBoxPointCountV1
