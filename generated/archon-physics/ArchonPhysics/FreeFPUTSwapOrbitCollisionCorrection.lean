import ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
import ArchonPhysics.FreeFPUTHaarResonanceReduction

/-!
# Swap-orbit correction to the free FPUT collision sum

Quadratic FPUT terms use ordered input pairs.  The involution exchanging both
input legs has one- or two-element orbits.  This module computes the complete
same-charge ordered-pair contribution internal to one such orbit.  A fixed
orbit contributes one diagonal weight.  A non-fixed orbit contains four
ordered pairs (two diagonal and two cross terms), and its coherent
contribution is four times one coefficient norm square.

Terms in distinct swap orbits can still carry the same phase charge.  We do
not assume otherwise.  The final theorem therefore splits the full
same-charge pair sum into the no-double-counted intra-orbit collision sum and
an explicit cross-orbit coherent remainder.  No cancellation or smallness of
that remainder, nonlinear random-phase propagation, or kinetic limit is
claimed.
-/

namespace ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTHaarResonanceReduction
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTTensorPhaseExpansion

open scoped ComplexConjugate

noncomputable section

/-- Membership in the input-swap orbit means being the original ordered term
or its simultaneous input swap. -/
theorem mem_quadraticSwapOrbit_iff
    {N : Nat} [NeZero N] (candidate term : QuadraticPhaseTerm N) :
    candidate ∈ quadraticSwapOrbit term ↔
      candidate = term ∨ candidate = swapQuadraticPhaseTerm term := by
  simp [quadraticSwapOrbit]

/-- The orbit finset does not depend on which of its two possible ordered
representatives is used. -/
@[simp] theorem quadraticSwapOrbit_swap
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    quadraticSwapOrbit (swapQuadraticPhaseTerm term) =
      quadraticSwapOrbit term := by
  ext candidate
  simp only [mem_quadraticSwapOrbit_iff,
    swapQuadraticPhaseTerm_involutive]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h

/-- Every member of one swap orbit has the representative's phase charge. -/
theorem quadraticPhaseCharge_eq_of_mem_swapOrbit
    {N : Nat} [NeZero N] {candidate term : QuadraticPhaseTerm N}
    (hmem : candidate ∈ quadraticSwapOrbit term) :
    quadraticPhaseCharge candidate = quadraticPhaseCharge term := by
  rcases (mem_quadraticSwapOrbit_iff candidate term).mp hmem with h | h
  · rw [h]
  · rw [h, quadraticPhaseCharge_swap]

/-- Every member of one swap orbit has the representative's exact mismatch. -/
theorem quadraticPhaseMismatch_eq_of_mem_swapOrbit
    {N : Nat} [NeZero N]
    (frequency : Lattice.Site N → Real) (observed : Lattice.Site N)
    {candidate term : QuadraticPhaseTerm N}
    (hmem : candidate ∈ quadraticSwapOrbit term) :
    quadraticPhaseMismatch frequency observed candidate =
      quadraticPhaseMismatch frequency observed term := by
  rcases (mem_quadraticSwapOrbit_iff candidate term).mp hmem with h | h
  · rw [h]
  · rw [h, quadraticPhaseMismatch_swap]

/-- Every member of one swap orbit has the representative's deterministic
free-Duhamel coefficient. -/
theorem freeQuadraticDuhamelCoefficient_eq_of_mem_swapOrbit
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    {candidate term : QuadraticPhaseTerm N}
    (hmem : candidate ∈ quadraticSwapOrbit term) :
    freeQuadraticDuhamelCoefficient coupling m observed radius candidate =
      freeQuadraticDuhamelCoefficient coupling m observed radius term := by
  rcases (mem_quadraticSwapOrbit_iff candidate term).mp hmem with h | h
  · rw [h]
  · rw [h, freeQuadraticDuhamelCoefficient_swap]

/-- The ordered-pair summand occurring in the normalized free-FPUT Haar
second moment.  The finite-time resonance weight is attached to the left
term, as in the exact same-charge formula. -/
def freeQuadraticSameChargePairValue
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (left right : QuadraticPhaseTerm N) : Complex :=
  freeQuadraticDuhamelCoefficient coupling m observed radius left *
    starRingEnd Complex
      (freeQuadraticDuhamelCoefficient coupling m observed radius right) *
    (finiteTimeResonanceWeight
      (quadraticPhaseMismatch frequency observed left) time : Complex)

/-- Inside one swap orbit, every ordered pair has the same physical summand:
one coefficient norm square times the common resonance weight. -/
theorem freeQuadraticSameChargePairValue_eq_orbitBase
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (term : QuadraticPhaseTerm N) {left right : QuadraticPhaseTerm N}
    (hleft : left ∈ quadraticSwapOrbit term)
    (hright : right ∈ quadraticSwapOrbit term) :
    freeQuadraticSameChargePairValue coupling m observed radius frequency
        time left right =
      (Complex.normSq
          (freeQuadraticDuhamelCoefficient
            coupling m observed radius term) : Complex) *
        (finiteTimeResonanceWeight
          (quadraticPhaseMismatch frequency observed term) time : Complex) := by
  unfold freeQuadraticSameChargePairValue
  rw [freeQuadraticDuhamelCoefficient_eq_of_mem_swapOrbit
      coupling m observed radius hleft,
    freeQuadraticDuhamelCoefficient_eq_of_mem_swapOrbit
      coupling m observed radius hright,
    quadraticPhaseMismatch_eq_of_mem_swapOrbit
      frequency observed hleft,
    Complex.mul_conj]

/-- Complete same-charge ordered-pair contribution internal to one input-swap
orbit.  The selector is retained explicitly to match the global Haar formula. -/
def freeQuadraticSwapOrbitContribution
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (term : QuadraticPhaseTerm N) : Complex :=
  ∑ left ∈ quadraticSwapOrbit term,
    ∑ right ∈ quadraticSwapOrbit term,
      if quadraticPhaseCharge left = quadraticPhaseCharge right then
        freeQuadraticSameChargePairValue coupling m observed radius frequency
          time left right
      else 0

/-- General orbit-cardinality formula.  It simultaneously covers fixed and
non-fixed terms and makes the ordered-pair multiplicity explicit. -/
theorem freeQuadraticSwapOrbitContribution_eq_card_sq_mul
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (term : QuadraticPhaseTerm N) :
    freeQuadraticSwapOrbitContribution coupling m observed radius frequency
        time term =
      ((quadraticSwapOrbit term).card : Complex) ^ 2 *
        (Complex.normSq
          (freeQuadraticDuhamelCoefficient
            coupling m observed radius term) : Complex) *
        (finiteTimeResonanceWeight
          (quadraticPhaseMismatch frequency observed term) time : Complex) := by
  let base : Complex :=
    (Complex.normSq
      (freeQuadraticDuhamelCoefficient
        coupling m observed radius term) : Complex) *
      (finiteTimeResonanceWeight
        (quadraticPhaseMismatch frequency observed term) time : Complex)
  calc
    freeQuadraticSwapOrbitContribution coupling m observed radius frequency
        time term =
      ∑ left ∈ quadraticSwapOrbit term,
        ∑ right ∈ quadraticSwapOrbit term, base := by
      unfold freeQuadraticSwapOrbitContribution
      apply Finset.sum_congr rfl
      intro left hleft
      apply Finset.sum_congr rfl
      intro right hright
      have hcharge :
          quadraticPhaseCharge left = quadraticPhaseCharge right :=
        (quadraticPhaseCharge_eq_of_mem_swapOrbit hleft).trans
          (quadraticPhaseCharge_eq_of_mem_swapOrbit hright).symm
      rw [if_pos hcharge]
      exact freeQuadraticSameChargePairValue_eq_orbitBase
        coupling m observed radius frequency time term hleft hright
    _ = ((quadraticSwapOrbit term).card : Complex) ^ 2 * base := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = ((quadraticSwapOrbit term).card : Complex) ^ 2 *
        (Complex.normSq
          (freeQuadraticDuhamelCoefficient
            coupling m observed radius term) : Complex) *
        (finiteTimeResonanceWeight
          (quadraticPhaseMismatch frequency observed term) time : Complex) := by
      simp only [base]
      ring

/-- A fixed swap orbit has one ordered pair and contributes one literal
coefficient norm square times the resonance weight. -/
theorem freeQuadraticSwapOrbitContribution_fixed
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (term : QuadraticPhaseTerm N)
    (hfixed : swapQuadraticPhaseTerm term = term) :
    freeQuadraticSwapOrbitContribution coupling m observed radius frequency
        time term =
      (Complex.normSq
          (freeQuadraticDuhamelCoefficient
            coupling m observed radius term) : Complex) *
        (finiteTimeResonanceWeight
          (quadraticPhaseMismatch frequency observed term) time : Complex) := by
  rw [freeQuadraticSwapOrbitContribution_eq_card_sq_mul,
    card_quadraticSwapOrbit_eq_one_of_fixed term hfixed]
  norm_num

/-- A non-fixed swap orbit has four ordered pairs.  Its complete coherent
contribution is `4 * normSq C * W_T`, not the two-term diagonal value. -/
theorem freeQuadraticSwapOrbitContribution_nonfixed
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (term : QuadraticPhaseTerm N)
    (hnotFixed : swapQuadraticPhaseTerm term ≠ term) :
    freeQuadraticSwapOrbitContribution coupling m observed radius frequency
        time term =
      4 *
        (Complex.normSq
          (freeQuadraticDuhamelCoefficient
            coupling m observed radius term) : Complex) *
        (finiteTimeResonanceWeight
          (quadraticPhaseMismatch frequency observed term) time : Complex) := by
  rw [freeQuadraticSwapOrbitContribution_eq_card_sq_mul,
    card_quadraticSwapOrbit_eq_two_of_ne term hnotFixed]
  norm_num

/-- The full same-charge ordered-pair sum before any input-swap grouping. -/
def freeQuadraticFullSameChargePairSum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) : Complex :=
  ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
    if quadraticPhaseCharge left = quadraticPhaseCharge right then
      freeQuadraticSameChargePairValue coupling m observed radius frequency
        time left right
    else 0

/-- No-double-counted intra-orbit collision sum.  Every ordered pair is
included exactly once, and only when both entries lie in the same swap orbit. -/
def freeQuadraticSwapIntraOrbitCollisionSum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) : Complex :=
  ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
    if quadraticPhaseCharge left = quadraticPhaseCharge right ∧
        right ∈ quadraticSwapOrbit left then
      freeQuadraticSameChargePairValue coupling m observed radius frequency
        time left right
    else 0

/-- Same-charge coherent pairs belonging to distinct input-swap orbits.  This
is retained explicitly; no vanishing, cancellation, or asymptotic estimate is
asserted. -/
def freeQuadraticCrossSwapOrbitCoherentRemainder
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) : Complex :=
  ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
    if quadraticPhaseCharge left = quadraticPhaseCharge right ∧
        right ∉ quadraticSwapOrbit left then
      freeQuadraticSameChargePairValue coupling m observed radius frequency
        time left right
    else 0

/-- Exact global partition: swap-orbit collision pairs plus every remaining
same-charge cross-orbit coherent pair.  This is the honest replacement for an
incorrect purely diagonal or naively deduplicated collision sum. -/
theorem freeQuadraticFullSameChargePairSum_eq_intraOrbit_add_crossOrbit
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    freeQuadraticFullSameChargePairSum coupling m observed radius frequency
        time =
      freeQuadraticSwapIntraOrbitCollisionSum
          coupling m observed radius frequency time +
        freeQuadraticCrossSwapOrbitCoherentRemainder
          coupling m observed radius frequency time := by
  classical
  unfold freeQuadraticFullSameChargePairSum
    freeQuadraticSwapIntraOrbitCollisionSum
    freeQuadraticCrossSwapOrbitCoherentRemainder
  calc
    (∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
      if quadraticPhaseCharge left = quadraticPhaseCharge right then
        freeQuadraticSameChargePairValue coupling m observed radius frequency
          time left right
      else 0) =
      ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
        ((if quadraticPhaseCharge left = quadraticPhaseCharge right ∧
            right ∈ quadraticSwapOrbit left then
          freeQuadraticSameChargePairValue coupling m observed radius frequency
            time left right
        else 0) +
        (if quadraticPhaseCharge left = quadraticPhaseCharge right ∧
            right ∉ quadraticSwapOrbit left then
          freeQuadraticSameChargePairValue coupling m observed radius frequency
            time left right
        else 0)) := by
      apply Finset.sum_congr rfl
      intro left hleft
      apply Finset.sum_congr rfl
      intro right hright
      by_cases hcharge :
          quadraticPhaseCharge left = quadraticPhaseCharge right
      · by_cases horbit : right ∈ quadraticSwapOrbit left
        · simp [hcharge, horbit]
        · simp [hcharge, horbit]
      · simp [hcharge]
    _ =
      (∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
        if quadraticPhaseCharge left = quadraticPhaseCharge right ∧
            right ∈ quadraticSwapOrbit left then
          freeQuadraticSameChargePairValue coupling m observed radius frequency
            time left right
        else 0) +
      ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
        if quadraticPhaseCharge left = quadraticPhaseCharge right ∧
            right ∉ quadraticSwapOrbit left then
          freeQuadraticSameChargePairValue coupling m observed radius frequency
            time left right
        else 0 := by
      simp only [Finset.sum_add_distrib]

end

end ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
