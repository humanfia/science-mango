import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32FiniteNestedValueFibresClosedNeighbourCodeSumV1

open FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1

noncomputable section

universe u v

/-!
# Closed-neighbour summation over code-tagged candidates

The third-stage candidate family is a dependent disjoint union over local
cover codes.  This module records the exact decomposition of a closed
comparison neighbourhood into its code slices.  No disjointness of the
underlying untagged items is assumed: the code tag itself is retained.
-/

/-- The slice in code `k` of the closed comparison neighbourhood of the
tagged pivot `q`. -/
noncomputable def finiteClosedComparableCodeSlice
    {code : Type v} {item : Type u}
    (selectedAt : code -> Finset item)
    (comparable : CodeSelectedCandidate code item ->
      CodeSelectedCandidate code item -> Prop)
    (q : CodeSelectedCandidate code item) (k : code) : Finset item := by
  classical
  exact (selectedAt k).filter fun b =>
    (⟨k, b⟩ : CodeSelectedCandidate code item) = q ∨
      comparable q ⟨k, b⟩

@[simp]
theorem mem_finiteClosedComparableCodeSlice_iff
    {code : Type v} {item : Type u}
    (selectedAt : code -> Finset item)
    (comparable : CodeSelectedCandidate code item ->
      CodeSelectedCandidate code item -> Prop)
    (q : CodeSelectedCandidate code item) (k : code) (b : item) :
    b ∈ finiteClosedComparableCodeSlice selectedAt comparable q k <->
      b ∈ selectedAt k ∧
        ((⟨k, b⟩ : CodeSelectedCandidate code item) = q ∨
          comparable q ⟨k, b⟩) := by
  classical
  simp [finiteClosedComparableCodeSlice]

/-- The closed neighbourhood in the tagged sigma family is literally the
sigma of its code slices. -/
theorem finiteClosedComparableNeighbour_codeSelectedCandidates_eq_sigma
    {code : Type v} {item : Type u}
    (codes : Finset code) (selectedAt : code -> Finset item)
    (comparable : CodeSelectedCandidate code item ->
      CodeSelectedCandidate code item -> Prop)
    (q : CodeSelectedCandidate code item) :
    finiteClosedComparableNeighbour
        (codeSelectedCandidates codes selectedAt) comparable q =
      codes.sigma
        (finiteClosedComparableCodeSlice selectedAt comparable q) := by
  classical
  ext r
  rcases r with ⟨k, b⟩
  simp only [finiteClosedComparableNeighbour, codeSelectedCandidates,
    finiteClosedComparableCodeSlice, Finset.mem_filter,
    Finset.mem_sigma]
  constructor
  · rintro ⟨⟨hk, hb⟩, hclosed⟩
    exact ⟨hk, hb, hclosed⟩
  · rintro ⟨hk, hb, hclosed⟩
    exact ⟨⟨hk, hb⟩, hclosed⟩

/-- Exact cardinal decomposition of a tagged closed neighbourhood. -/
theorem finiteClosedComparableNeighbour_codeSelectedCandidates_card_eq_sum
    {code : Type v} {item : Type u}
    (codes : Finset code) (selectedAt : code -> Finset item)
    (comparable : CodeSelectedCandidate code item ->
      CodeSelectedCandidate code item -> Prop)
    (q : CodeSelectedCandidate code item) :
    ((finiteClosedComparableNeighbour
        (codeSelectedCandidates codes selectedAt) comparable q).card :
          ENNReal) =
      ∑ k ∈ codes,
        ((finiteClosedComparableCodeSlice selectedAt comparable q k).card :
          ENNReal) := by
  classical
  rw [finiteClosedComparableNeighbour_codeSelectedCandidates_eq_sigma,
    Finset.card_sigma]
  norm_cast

/-- A uniform per-code slice cap gives the honest product by the number of
occupied codes. -/
theorem finiteClosedComparableNeighbour_codeSelectedCandidates_card_le
    {code : Type v} {item : Type u}
    (codes : Finset code) (selectedAt : code -> Finset item)
    (comparable : CodeSelectedCandidate code item ->
      CodeSelectedCandidate code item -> Prop)
    (q : CodeSelectedCandidate code item) (perCodeBound : ENNReal)
    (hslice : forall k, k ∈ codes ->
      ((finiteClosedComparableCodeSlice selectedAt comparable q k).card :
        ENNReal) <= perCodeBound) :
    ((finiteClosedComparableNeighbour
        (codeSelectedCandidates codes selectedAt) comparable q).card :
          ENNReal) <=
      (codes.card : ENNReal) * perCodeBound := by
  rw [finiteClosedComparableNeighbour_codeSelectedCandidates_card_eq_sum]
  calc
    (∑ k ∈ codes,
        ((finiteClosedComparableCodeSlice selectedAt comparable q k).card :
          ENNReal)) <= ∑ _k ∈ codes, perCodeBound := by
      exact Finset.sum_le_sum fun k hk => hslice k hk
    _ = (codes.card : ENNReal) * perCodeBound := by
      simp [nsmul_eq_mul]

/-- The same estimate after replacing the literal occupied-code cardinality
by any external cover-code packing bound. -/
theorem finiteClosedComparableNeighbour_codeSelectedCandidates_card_le_of_codeBound
    {code : Type v} {item : Type u}
    (codes : Finset code) (selectedAt : code -> Finset item)
    (comparable : CodeSelectedCandidate code item ->
      CodeSelectedCandidate code item -> Prop)
    (q : CodeSelectedCandidate code item)
    (codeBound perCodeBound : ENNReal)
    (hcodes : (codes.card : ENNReal) <= codeBound)
    (hslice : forall k, k ∈ codes ->
      ((finiteClosedComparableCodeSlice selectedAt comparable q k).card :
        ENNReal) <= perCodeBound) :
    ((finiteClosedComparableNeighbour
        (codeSelectedCandidates codes selectedAt) comparable q).card :
          ENNReal) <=
      codeBound * perCodeBound := by
  calc
    ((finiteClosedComparableNeighbour
        (codeSelectedCandidates codes selectedAt) comparable q).card :
          ENNReal) <=
        (codes.card : ENNReal) * perCodeBound :=
      finiteClosedComparableNeighbour_codeSelectedCandidates_card_le
        codes selectedAt comparable q perCodeBound hslice
    _ <= codeBound * perCodeBound := by
      gcongr

#print axioms finiteClosedComparableNeighbour_codeSelectedCandidates_eq_sigma
#print axioms finiteClosedComparableNeighbour_codeSelectedCandidates_card_eq_sum
#print axioms finiteClosedComparableNeighbour_codeSelectedCandidates_card_le
#print axioms finiteClosedComparableNeighbour_codeSelectedCandidates_card_le_of_codeBound

end

end FamilyStickyCinematicL32FiniteNestedValueFibresClosedNeighbourCodeSumV1
