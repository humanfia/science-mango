import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosForbiddenTripleV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1

/-!
# Forbidden cyclic triples in the five-pseudo-circle step

Marcus--Tardos Lemma 10 proves that, for each fixed lens class, two cyclic
neighbor lists cannot contain three common curves in the same cyclic order.
This module makes that source obligation literal and separates it from the
pure finite theorem saying that absence of such a triple forces reversed
cyclic order.

`TripleCharacterizationCore` is intentionally marked as an unresolved
finite-combinatorial producer interface.  It contains no cardinal estimate,
and no Family6-complete wrapper may import a value of this structure until a
proof producer is supplied.
-/

/-- The three-symbol support used to restrict a cyclic sequence. -/
def tripleSupport {symbol : Type*} [DecidableEq symbol]
    (x y z : symbol) : Finset symbol :=
  {x, y, z}

/-- The order induced by a cyclic sequence on three specified symbols. -/
def tripleOrder {symbol : Type*} [DecidableEq symbol]
    (A : DistinctCyclicSequence symbol) (x y z : symbol) : List symbol :=
  A.order.filter fun a => a ∈ tripleSupport x y z

/-- `x,y,z` occur counterclockwise in this order, modulo the choice of cut. -/
def CyclicallyOrdered {symbol : Type*} [DecidableEq symbol]
    (A : DistinctCyclicSequence symbol) (x y z : symbol) : Prop :=
  tripleOrder A x y z ~r [x, y, z]

/-- A literal forbidden triple: three distinct common symbols have the same
cyclic orientation in both lists. -/
def SameCyclicTriple {symbol : Type*} [DecidableEq symbol]
    (A B : DistinctCyclicSequence symbol) (x y z : symbol) : Prop :=
  x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
    x ∈ A.support ∩ B.support ∧
    y ∈ A.support ∩ B.support ∧
    z ∈ A.support ∩ B.support ∧
    CyclicallyOrdered A x y z ∧ CyclicallyOrdered B x y z

def HasSameCyclicTriple {symbol : Type*} [DecidableEq symbol]
    (A B : DistinctCyclicSequence symbol) : Prop :=
  ∃ x y z, SameCyclicTriple A B x y z

def NoSameCyclicTriple {symbol : Type*} [DecidableEq symbol]
    (A B : DistinctCyclicSequence symbol) : Prop :=
  ¬ HasSameCyclicTriple A B

theorem cyclicallyOrdered_of_rotated
    {symbol : Type*} [DecidableEq symbol]
    {A A' : DistinctCyclicSequence symbol} {x y z : symbol}
    (hrot : A.order ~r A'.order)
    (h : CyclicallyOrdered A x y z) :
    CyclicallyOrdered A' x y z := by
  have hfilter : tripleOrder A x y z ~r tripleOrder A' x y z :=
    IsRotated.filterByFinset (tripleSupport x y z) hrot
  exact hfilter.symm.trans h

theorem sameCyclicTriple_comm
    {symbol : Type*} [DecidableEq symbol]
    (A B : DistinctCyclicSequence symbol) (x y z : symbol) :
    SameCyclicTriple A B x y z ↔ SameCyclicTriple B A x y z := by
  simp only [SameCyclicTriple, Finset.mem_inter]
  aesop

theorem hasSameCyclicTriple_comm
    {symbol : Type*} [DecidableEq symbol]
    (A B : DistinctCyclicSequence symbol) :
    HasSameCyclicTriple A B ↔ HasSameCyclicTriple B A := by
  constructor
  · rintro ⟨x, y, z, h⟩
    exact ⟨x, y, z, (sameCyclicTriple_comm A B x y z).mp h⟩
  · rintro ⟨x, y, z, h⟩
    exact ⟨x, y, z, (sameCyclicTriple_comm B A x y z).mp h⟩

theorem noSameCyclicTriple_comm
    {symbol : Type*} [DecidableEq symbol]
    (A B : DistinctCyclicSequence symbol) :
    NoSameCyclicTriple A B ↔ NoSameCyclicTriple B A := by
  simp only [NoSameCyclicTriple, hasSameCyclicTriple_comm A B]

/-- With at most two common symbols there cannot even be a forbidden
triple.  This is independent of cyclic order. -/
theorem noSameCyclicTriple_of_common_card_le_two
    {symbol : Type*} [DecidableEq symbol]
    (A B : DistinctCyclicSequence symbol)
    (hcard : (A.support ∩ B.support).card ≤ 2) :
    NoSameCyclicTriple A B := by
  rintro ⟨x, y, z, hxy, hyz, hzx, hx, hy, hz, _, _⟩
  have hsub : ({x, y, z} : Finset symbol) ⊆ A.support ∩ B.support := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  have hthree : ({x, y, z} : Finset symbol).card = 3 := by
    simp [hxy, hyz, Ne.symm hzx]
  have := Finset.card_le_card hsub
  omega

/-- Fixed-kind source output of the planar five-curve case analysis. -/
def FixedKindForbidsSameTriple
    {curve : Type*} [DecidableEq curve]
    (lists : curve → DistinctCyclicSequence curve) : Prop :=
  Pairwise fun c d => NoSameCyclicTriple (lists c) (lists d)

/-- **UNRESOLVED_MT_FINITE_CORE.**  This is a named producer interface for
the pure theorem “no common equally-oriented triple implies opposite cyclic
orders”.  It must eventually be constructed, not assumed by a final
Family6 theorem. -/
structure TripleCharacterizationCore (symbol : Type*) [DecidableEq symbol] : Prop where
  noSame_implies_intersectionReverse :
    ∀ A B : DistinctCyclicSequence symbol,
      NoSameCyclicTriple A B → IntersectionReverse A B

/-- Once the pure triple characterization is available, the fixed-kind
five-curve obligation mechanically gives pairwise intersection reversal. -/
theorem fixedKind_pairwiseIntersectionReverse
    {curve : Type*} [DecidableEq curve]
    (core : TripleCharacterizationCore curve)
    (lists : curve → DistinctCyclicSequence curve)
    (hforbidden : FixedKindForbidsSameTriple lists) :
    PairwiseIntersectionReverse lists := by
  intro c d hcd
  exact core.noSame_implies_intersectionReverse _ _ (hforbidden hcd)

/-- All three lens kinds are handled separately, exactly as required in the
Marcus--Tardos proof. -/
theorem lensListEncoding_pairwiseIntersectionReverse
    {curve lens : Type*} [Fintype curve] [DecidableEq curve]
    (core : TripleCharacterizationCore curve)
    (E : LensListEncoding curve lens)
    (hforbidden : ∀ k, FixedKindForbidsSameTriple (E.lists k)) :
    E.ListsPairwiseIntersectionReverse := by
  intro k
  exact fixedKind_pairwiseIntersectionReverse core (E.lists k) (hforbidden k)

#print axioms cyclicallyOrdered_of_rotated
#print axioms sameCyclicTriple_comm
#print axioms hasSameCyclicTriple_comm
#print axioms noSameCyclicTriple_comm
#print axioms noSameCyclicTriple_of_common_card_le_two
#print axioms FixedKindForbidsSameTriple
#print axioms TripleCharacterizationCore
#print axioms fixedKind_pairwiseIntersectionReverse
#print axioms lensListEncoding_pairwiseIntersectionReverse

end FamilyStickyCinematicL32Prop41MarcusTardosForbiddenTripleV1
