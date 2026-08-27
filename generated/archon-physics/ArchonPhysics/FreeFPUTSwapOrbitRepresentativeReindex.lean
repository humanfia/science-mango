import ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
import Mathlib.Data.Fintype.EquivFin

/-!
# Canonical swap-orbit reindexing of the free FPUT coherent gain

The ordered quadratic first-Picard expansion contains both orders of its two
input legs.  This module chooses one canonical representative from every
input-swap orbit and reindexes the exact orbit-internal Haar contribution.

There are two different, equally necessary cardinality factors:

* with an outer sum over every ordered left term, summing its right swap
  partner contributes one factor `swapOrbit.card`;
* after the outer terms are themselves deduplicated to one representative per
  orbit, the complete coherent ordered-pair contribution carries
  `swapOrbit.card ^ 2`.

Thus a repeated-input fixed point has multiplicity one, while a genuine
two-element orbit has coherent multiplicity four.  No cross-orbit term is
dropped: the final full-sum formula retains the existing coherent remainder.
-/

namespace ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion

noncomputable section

/-- A deterministic finite rank used only to choose one of the two ordered
members of a swap orbit. -/
def quadraticPhaseTermRank
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    Fin (Fintype.card (QuadraticPhaseTerm N)) :=
  Fintype.equivFin (QuadraticPhaseTerm N) term

/-- The lower-ranked member of an input-swap orbit. -/
def canonicalQuadraticSwapRepresentative
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    QuadraticPhaseTerm N :=
  if quadraticPhaseTermRank term ≤
      quadraticPhaseTermRank (swapQuadraticPhaseTerm term) then
    term
  else
    swapQuadraticPhaseTerm term

/-- The finite set containing exactly one canonical member of every
input-swap orbit. -/
def quadraticSwapOrbitRepresentatives (N : Nat) [NeZero N] :
    Finset (QuadraticPhaseTerm N) :=
  Finset.univ.image canonicalQuadraticSwapRepresentative

theorem quadraticPhaseTermRank_injective
    {N : Nat} [NeZero N] :
    Function.Injective
      (quadraticPhaseTermRank : QuadraticPhaseTerm N →
        Fin (Fintype.card (QuadraticPhaseTerm N))) :=
  (Fintype.equivFin (QuadraticPhaseTerm N)).injective

/-- The canonical choice is literally one of the two ordered members of the
input-swap orbit. -/
theorem canonicalQuadraticSwapRepresentative_mem_swapOrbit
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    canonicalQuadraticSwapRepresentative term ∈ quadraticSwapOrbit term := by
  classical
  unfold canonicalQuadraticSwapRepresentative quadraticSwapOrbit
  split <;> simp

/-- Swapping the ordered inputs does not change the canonical representative. -/
@[simp] theorem canonicalQuadraticSwapRepresentative_swap
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    canonicalQuadraticSwapRepresentative (swapQuadraticPhaseTerm term) =
      canonicalQuadraticSwapRepresentative term := by
  classical
  by_cases hforward :
      quadraticPhaseTermRank term ≤
        quadraticPhaseTermRank (swapQuadraticPhaseTerm term)
  · by_cases hback :
        quadraticPhaseTermRank (swapQuadraticPhaseTerm term) ≤
          quadraticPhaseTermRank term
    · have hrank :
          quadraticPhaseTermRank term =
            quadraticPhaseTermRank (swapQuadraticPhaseTerm term) :=
        le_antisymm hforward hback
      have hfixed : term = swapQuadraticPhaseTerm term :=
        quadraticPhaseTermRank_injective hrank
      exact congrArg canonicalQuadraticSwapRepresentative hfixed.symm
    · simp [canonicalQuadraticSwapRepresentative, hforward, hback]
  · have hback :
        quadraticPhaseTermRank (swapQuadraticPhaseTerm term) ≤
          quadraticPhaseTermRank term :=
      le_of_not_ge hforward
    simp [canonicalQuadraticSwapRepresentative, hforward, hback]

/-- Every member of one swap orbit has the same canonical representative. -/
theorem canonicalQuadraticSwapRepresentative_eq_of_mem_swapOrbit
    {N : Nat} [NeZero N] {candidate term : QuadraticPhaseTerm N}
    (hmem : candidate ∈ quadraticSwapOrbit term) :
    canonicalQuadraticSwapRepresentative candidate =
      canonicalQuadraticSwapRepresentative term := by
  rcases (mem_quadraticSwapOrbit_iff candidate term).mp hmem with h | h
  · rw [h]
  · rw [h, canonicalQuadraticSwapRepresentative_swap]

/-- Canonicalization is idempotent. -/
@[simp] theorem canonicalQuadraticSwapRepresentative_idempotent
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    canonicalQuadraticSwapRepresentative
        (canonicalQuadraticSwapRepresentative term) =
      canonicalQuadraticSwapRepresentative term := by
  exact canonicalQuadraticSwapRepresentative_eq_of_mem_swapOrbit
    (canonicalQuadraticSwapRepresentative_mem_swapOrbit term)

/-- Membership in the representative finset is equivalent to being fixed by
canonicalization. -/
theorem mem_quadraticSwapOrbitRepresentatives_iff
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    term ∈ quadraticSwapOrbitRepresentatives N ↔
      canonicalQuadraticSwapRepresentative term = term := by
  classical
  constructor
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨source, _hsource, hsource⟩
    rw [← hsource, canonicalQuadraticSwapRepresentative_idempotent]
  · intro hcanonical
    apply Finset.mem_image.mpr
    exact ⟨term, Finset.mem_univ term, hcanonical⟩

/-- A canonical fiber is exactly the corresponding two-leg swap orbit. -/
theorem canonicalQuadraticSwapRepresentative_fiber_eq_swapOrbit
    {N : Nat} [NeZero N] {representative : QuadraticPhaseTerm N}
    (hrepresentative : representative ∈ quadraticSwapOrbitRepresentatives N) :
    Finset.univ.filter
        (fun candidate : QuadraticPhaseTerm N ↦
          canonicalQuadraticSwapRepresentative candidate = representative) =
      quadraticSwapOrbit representative := by
  classical
  have hcanonical :
      canonicalQuadraticSwapRepresentative representative = representative :=
    (mem_quadraticSwapOrbitRepresentatives_iff representative).mp
      hrepresentative
  ext candidate
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hc
    have hchoice :=
      canonicalQuadraticSwapRepresentative_mem_swapOrbit candidate
    rcases (mem_quadraticSwapOrbit_iff
        (canonicalQuadraticSwapRepresentative candidate) candidate).mp
        hchoice with h | h
    · rw [hc] at h
      exact h.symm ▸ (by simp [quadraticSwapOrbit] :
        representative ∈ quadraticSwapOrbit representative)
    · have hcand : candidate = swapQuadraticPhaseTerm representative := by
        rw [hc] at h
        simpa only [swapQuadraticPhaseTerm_involutive] using
          (congrArg swapQuadraticPhaseTerm h).symm
      exact (mem_quadraticSwapOrbit_iff candidate representative).mpr
        (Or.inr hcand)
  · intro hmem
    rw [canonicalQuadraticSwapRepresentative_eq_of_mem_swapOrbit hmem,
      hcanonical]

/-- One outer ordered term after summing its right swap orbit.  The single
factor `card` is correct here because the outer ordered term has not yet been
deduplicated. -/
def freeQuadraticOrderedLeftSwapWeight
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (term : QuadraticPhaseTerm N) : Complex :=
  ((quadraticSwapOrbit term).card : Complex) *
    (Complex.normSq
      (freeQuadraticDuhamelCoefficient
        coupling m observed radius term) : Complex) *
    (finiteTimeResonanceWeight
      (quadraticPhaseMismatch frequency observed term) time : Complex)

/-- The orbit-cardinality-weighted sum while retaining all ordered outer
terms. -/
def freeQuadraticOrderedLeftSwapWeightSum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) : Complex :=
  ∑ term : QuadraticPhaseTerm N,
    freeQuadraticOrderedLeftSwapWeight
      coupling m observed radius frequency time term

/-- Summing the admissible right partners of one still-ordered outer term
produces exactly one factor of the swap-orbit cardinality. -/
theorem sum_right_intraOrbit_eq_orderedLeftSwapWeight
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (left : QuadraticPhaseTerm N) :
    (∑ right : QuadraticPhaseTerm N,
      if quadraticPhaseCharge left = quadraticPhaseCharge right ∧
          right ∈ quadraticSwapOrbit left then
        freeQuadraticSameChargePairValue coupling m observed radius frequency
          time left right
      else 0) =
      freeQuadraticOrderedLeftSwapWeight
        coupling m observed radius frequency time left := by
  classical
  let base : Complex :=
    (Complex.normSq
      (freeQuadraticDuhamelCoefficient
        coupling m observed radius left) : Complex) *
      (finiteTimeResonanceWeight
        (quadraticPhaseMismatch frequency observed left) time : Complex)
  calc
    (∑ right : QuadraticPhaseTerm N,
      if quadraticPhaseCharge left = quadraticPhaseCharge right ∧
          right ∈ quadraticSwapOrbit left then
        freeQuadraticSameChargePairValue coupling m observed radius frequency
          time left right
      else 0) =
      ∑ right ∈ quadraticSwapOrbit left,
        freeQuadraticSameChargePairValue coupling m observed radius frequency
          time left right := by
      calc
        (∑ right : QuadraticPhaseTerm N,
          if quadraticPhaseCharge left = quadraticPhaseCharge right ∧
              right ∈ quadraticSwapOrbit left then
            freeQuadraticSameChargePairValue
              coupling m observed radius frequency time left right
          else 0) =
          ∑ right : QuadraticPhaseTerm N,
            if right ∈ quadraticSwapOrbit left then
              freeQuadraticSameChargePairValue
                coupling m observed radius frequency time left right
            else 0 := by
          apply Finset.sum_congr rfl
          intro right hright
          by_cases hmem : right ∈ quadraticSwapOrbit left
          · have hcharge :
                quadraticPhaseCharge left = quadraticPhaseCharge right :=
              (quadraticPhaseCharge_eq_of_mem_swapOrbit hmem).symm
            simp [hmem, hcharge]
          · simp [hmem]
        _ = ∑ right ∈ quadraticSwapOrbit left,
            freeQuadraticSameChargePairValue
              coupling m observed radius frequency time left right := by
          simp
    _ = ∑ _right ∈ quadraticSwapOrbit left, base := by
      apply Finset.sum_congr rfl
      intro right hright
      exact freeQuadraticSameChargePairValue_eq_orbitBase
        coupling m observed radius frequency time left
        (by simp [quadraticSwapOrbit]) hright
    _ = ((quadraticSwapOrbit left).card : Complex) * base := by
      simp [nsmul_eq_mul]
    _ = freeQuadraticOrderedLeftSwapWeight
        coupling m observed radius frequency time left := by
      simp only [freeQuadraticOrderedLeftSwapWeight, base]
      ring

/-- Exact ordered-left formula for the complete intra-orbit part.  Its
coefficient is `card`, not `card²`, because every member of a non-fixed orbit
still appears separately in the outer sum. -/
theorem freeQuadraticSwapIntraOrbitCollisionSum_eq_orderedLeftCardSum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    freeQuadraticSwapIntraOrbitCollisionSum
        coupling m observed radius frequency time =
      freeQuadraticOrderedLeftSwapWeightSum
        coupling m observed radius frequency time := by
  classical
  unfold freeQuadraticSwapIntraOrbitCollisionSum
    freeQuadraticOrderedLeftSwapWeightSum
  apply Finset.sum_congr rfl
  intro left hleft
  exact sum_right_intraOrbit_eq_orderedLeftSwapWeight
    coupling m observed radius frequency time left

/-- The ordered-left weight is constant throughout one swap orbit. -/
theorem freeQuadraticOrderedLeftSwapWeight_eq_of_mem_swapOrbit
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    {candidate term : QuadraticPhaseTerm N}
    (hmem : candidate ∈ quadraticSwapOrbit term) :
    freeQuadraticOrderedLeftSwapWeight
        coupling m observed radius frequency time candidate =
      freeQuadraticOrderedLeftSwapWeight
        coupling m observed radius frequency time term := by
  rcases (mem_quadraticSwapOrbit_iff candidate term).mp hmem with h | h
  · rw [h]
  · rw [h]
    unfold freeQuadraticOrderedLeftSwapWeight
    rw [quadraticSwapOrbit_swap, freeQuadraticDuhamelCoefficient_swap,
      quadraticPhaseMismatch_swap]

/-- One canonical fiber sums to the complete coherent contribution of that
orbit.  The second factor of `card` comes from the size of the outer fiber. -/
theorem sum_canonicalFiber_orderedLeftWeight_eq_swapOrbitContribution
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    {representative : QuadraticPhaseTerm N}
    (hrepresentative : representative ∈ quadraticSwapOrbitRepresentatives N) :
    (∑ candidate ∈ Finset.univ.filter
        (fun candidate : QuadraticPhaseTerm N ↦
          canonicalQuadraticSwapRepresentative candidate = representative),
      freeQuadraticOrderedLeftSwapWeight
        coupling m observed radius frequency time candidate) =
      freeQuadraticSwapOrbitContribution
        coupling m observed radius frequency time representative := by
  classical
  rw [canonicalQuadraticSwapRepresentative_fiber_eq_swapOrbit
    hrepresentative]
  calc
    (∑ candidate ∈ quadraticSwapOrbit representative,
      freeQuadraticOrderedLeftSwapWeight
        coupling m observed radius frequency time candidate) =
      ∑ _candidate ∈ quadraticSwapOrbit representative,
        freeQuadraticOrderedLeftSwapWeight
          coupling m observed radius frequency time representative := by
      apply Finset.sum_congr rfl
      intro candidate hcandidate
      exact freeQuadraticOrderedLeftSwapWeight_eq_of_mem_swapOrbit
        coupling m observed radius frequency time hcandidate
    _ = ((quadraticSwapOrbit representative).card : Complex) ^ 2 *
        (Complex.normSq
          (freeQuadraticDuhamelCoefficient
            coupling m observed radius representative) : Complex) *
        (finiteTimeResonanceWeight
          (quadraticPhaseMismatch frequency observed representative) time :
            Complex) := by
      unfold freeQuadraticOrderedLeftSwapWeight
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = freeQuadraticSwapOrbitContribution
        coupling m observed radius frequency time representative := by
      rw [freeQuadraticSwapOrbitContribution_eq_card_sq_mul]

/-- The exact no-double-counted representative-orbit collision sum. -/
def freeQuadraticSwapRepresentativeCollisionSum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) : Complex :=
  ∑ representative ∈ quadraticSwapOrbitRepresentatives N,
    freeQuadraticSwapOrbitContribution
      coupling m observed radius frequency time representative

/-- Exact global orbit reindexing: the original intra-orbit double sum is a
finite sum of complete contributions over one representative per swap orbit. -/
theorem freeQuadraticSwapIntraOrbitCollisionSum_eq_representativeSum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    freeQuadraticSwapIntraOrbitCollisionSum
        coupling m observed radius frequency time =
      freeQuadraticSwapRepresentativeCollisionSum
        coupling m observed radius frequency time := by
  classical
  rw [freeQuadraticSwapIntraOrbitCollisionSum_eq_orderedLeftCardSum]
  unfold freeQuadraticOrderedLeftSwapWeightSum
    freeQuadraticSwapRepresentativeCollisionSum
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (QuadraticPhaseTerm N)))
    (t := quadraticSwapOrbitRepresentatives N)
    (g := canonicalQuadraticSwapRepresentative)
    (fun term _hterm ↦ Finset.mem_image.mpr
      ⟨term, Finset.mem_univ term, rfl⟩)
    (freeQuadraticOrderedLeftSwapWeight
      coupling m observed radius frequency time)]
  apply Finset.sum_congr rfl
  intro representative hrepresentative
  exact sum_canonicalFiber_orderedLeftWeight_eq_swapOrbitContribution
    coupling m observed radius frequency time hrepresentative

/-- Card-squared form after the outer ordered terms have been deduplicated.
This is the form that exposes multiplicity one for repeated fixed inputs and
multiplicity four for a genuine two-element swap orbit. -/
theorem freeQuadraticSwapRepresentativeCollisionSum_eq_cardSqSum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    freeQuadraticSwapRepresentativeCollisionSum
        coupling m observed radius frequency time =
      ∑ representative ∈ quadraticSwapOrbitRepresentatives N,
        ((quadraticSwapOrbit representative).card : Complex) ^ 2 *
          (Complex.normSq
            (freeQuadraticDuhamelCoefficient
              coupling m observed radius representative) : Complex) *
          (finiteTimeResonanceWeight
            (quadraticPhaseMismatch frequency observed representative) time :
              Complex) := by
  classical
  unfold freeQuadraticSwapRepresentativeCollisionSum
  apply Finset.sum_congr rfl
  intro representative hrepresentative
  exact freeQuadraticSwapOrbitContribution_eq_card_sq_mul
    coupling m observed radius frequency time representative

/-- Full coherent gain split into the explicitly card-squared representative
collision sum and the unchanged cross-orbit coherent remainder. -/
theorem freeQuadraticFullSameChargePairSum_eq_representativeCardSq_add_cross
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    freeQuadraticFullSameChargePairSum
        coupling m observed radius frequency time =
      (∑ representative ∈ quadraticSwapOrbitRepresentatives N,
        ((quadraticSwapOrbit representative).card : Complex) ^ 2 *
          (Complex.normSq
            (freeQuadraticDuhamelCoefficient
              coupling m observed radius representative) : Complex) *
          (finiteTimeResonanceWeight
            (quadraticPhaseMismatch frequency observed representative) time :
              Complex)) +
        freeQuadraticCrossSwapOrbitCoherentRemainder
          coupling m observed radius frequency time := by
  rw [freeQuadraticFullSameChargePairSum_eq_intraOrbit_add_crossOrbit,
    freeQuadraticSwapIntraOrbitCollisionSum_eq_representativeSum,
    freeQuadraticSwapRepresentativeCollisionSum_eq_cardSqSum]

end

end ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
