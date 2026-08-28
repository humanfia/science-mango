import ArchonPhysics.FreeFPUTNonzeroChargeFiberClassification
import ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
import ArchonPhysics.FreeFPUTZeroChargeFiberDecay

/-!
# Cross-swap-orbit coherence is confined to the zero-charge fiber

Equality of a nonzero quadratic FPUT phase charge determines the two signed
inputs up to exchange.  Consequently, every same-charge ordered pair lying
in distinct input-swap orbits has charge zero.  This module uses that exact
classification to rewrite the cross-orbit coherent remainder as a sum over
zero-charge pairs only.

The cross-orbit remainder is not identified with the complete zero-charge
fiber.  The latter also contains zero-charge pairs internal to individual
swap orbits.  We retain the exact identity

`full zero-charge pairs = intra-orbit zero-charge pairs + cross-orbit pairs`.

Finally the cross-orbit sum is factored into a time-independent coherent
coefficient and the zero-charge resonance weight.  At a fixed positive
output frequency this gives an explicit `O(T⁻¹)` norm bound.  No
volume-uniform acoustic gap, nonlinear random-phase propagation, or kinetic
limit is asserted.
-/

namespace ArchonPhysics.FreeFPUTCrossOrbitZeroChargeBridge

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTNonzeroChargeFiberClassification
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.FreeFPUTZeroChargeFiberDecay

open scoped ComplexConjugate

noncomputable section

/-- The cross-orbit coherent coefficient in the exceptional zero-charge
fiber, before multiplication by its common finite-time resonance weight. -/
def freeQuadraticZeroChargeCrossOrbitCoefficient
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real) : Complex :=
  ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
    if quadraticPhaseCharge left = 0 ∧
        quadraticPhaseCharge right = 0 ∧
        right ∉ quadraticSwapOrbit left then
      freeQuadraticDuhamelCoefficient coupling m observed radius left *
        starRingEnd Complex
          (freeQuadraticDuhamelCoefficient coupling m observed radius right)
    else 0

/-- The same zero-charge cross-orbit pairs with their exact finite-time
ordered-pair value. -/
def freeQuadraticZeroChargeCrossOrbitPairSum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) : Complex :=
  ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
    if quadraticPhaseCharge left = 0 ∧
        quadraticPhaseCharge right = 0 ∧
        right ∉ quadraticSwapOrbit left then
      freeQuadraticSameChargePairValue coupling m observed radius frequency
        time left right
    else 0

/-- The complete zero-charge ordered-pair sum, including both intra- and
cross-swap-orbit pairs. -/
def freeQuadraticFullZeroChargePairSum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) : Complex :=
  ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
    if quadraticPhaseCharge left = 0 ∧ quadraticPhaseCharge right = 0 then
      freeQuadraticSameChargePairValue coupling m observed radius frequency
        time left right
    else 0

/-- The portion of the zero-charge fiber internal to individual swap orbits.
This is the term that must be retained when comparing the cross remainder
with the complete zero-charge coherent fiber. -/
def freeQuadraticZeroChargeIntraOrbitPairSum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) : Complex :=
  ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
    if quadraticPhaseCharge left = 0 ∧
        quadraticPhaseCharge right = 0 ∧
        right ∈ quadraticSwapOrbit left then
      freeQuadraticSameChargePairValue coupling m observed radius frequency
        time left right
    else 0

/-- A same-charge cross-orbit pair is necessarily in the zero-charge fiber.
This is the precise point where the nonzero charge-fiber classification is
used. -/
theorem sameCharge_crossSwapOrbit_imp_both_zero
    {N : Nat} [NeZero N] (left right : QuadraticPhaseTerm N)
    (hcharge : quadraticPhaseCharge left = quadraticPhaseCharge right)
    (hcross : right ∉ quadraticSwapOrbit left) :
    quadraticPhaseCharge left = 0 ∧ quadraticPhaseCharge right = 0 := by
  have hleft :=
    quadraticPhaseCharge_eq_zero_of_eq_and_not_mem_swapOrbit
      left right hcharge hcross
  exact ⟨hleft, hcharge.symm.trans hleft⟩

/-- Exact support reduction of the global cross-orbit coherent remainder:
all and only zero-charge cross-orbit ordered pairs remain. -/
theorem freeQuadraticCrossSwapOrbitCoherentRemainder_eq_zeroChargePairSum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    freeQuadraticCrossSwapOrbitCoherentRemainder
        coupling m observed radius frequency time =
      freeQuadraticZeroChargeCrossOrbitPairSum
        coupling m observed radius frequency time := by
  classical
  unfold freeQuadraticCrossSwapOrbitCoherentRemainder
    freeQuadraticZeroChargeCrossOrbitPairSum
  apply Finset.sum_congr rfl
  intro left hleft
  apply Finset.sum_congr rfl
  intro right hright
  by_cases hcharge :
      quadraticPhaseCharge left = quadraticPhaseCharge right
  · by_cases hcross : right ∉ quadraticSwapOrbit left
    · have hzero :=
        sameCharge_crossSwapOrbit_imp_both_zero left right hcharge hcross
      rw [if_pos ⟨hcharge, hcross⟩,
        if_pos ⟨hzero.1, hzero.2, hcross⟩]
    · rw [if_neg (fun h ↦ hcross h.2),
        if_neg (fun h ↦ hcross h.2.2)]
  · have hnotBothZero :
        ¬ (quadraticPhaseCharge left = 0 ∧
          quadraticPhaseCharge right = 0) := by
      rintro ⟨hleftZero, hrightZero⟩
      exact hcharge (hleftZero.trans hrightZero.symm)
    rw [if_neg (fun h ↦ hcharge h.1),
      if_neg (fun h ↦ hnotBothZero ⟨h.1, h.2.1⟩)]

/-- Exact zero-charge partition.  In particular, the cross-orbit term is not
the full zero-charge fiber unless the displayed intra-orbit term vanishes. -/
theorem freeQuadraticFullZeroChargePairSum_eq_intra_add_cross
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    freeQuadraticFullZeroChargePairSum
        coupling m observed radius frequency time =
      freeQuadraticZeroChargeIntraOrbitPairSum
          coupling m observed radius frequency time +
        freeQuadraticZeroChargeCrossOrbitPairSum
          coupling m observed radius frequency time := by
  classical
  unfold freeQuadraticFullZeroChargePairSum
    freeQuadraticZeroChargeIntraOrbitPairSum
    freeQuadraticZeroChargeCrossOrbitPairSum
  calc
    (∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
      if quadraticPhaseCharge left = 0 ∧ quadraticPhaseCharge right = 0 then
        freeQuadraticSameChargePairValue coupling m observed radius frequency
          time left right
      else 0) =
      ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
        ((if quadraticPhaseCharge left = 0 ∧
              quadraticPhaseCharge right = 0 ∧
              right ∈ quadraticSwapOrbit left then
            freeQuadraticSameChargePairValue
              coupling m observed radius frequency time left right
          else 0) +
          (if quadraticPhaseCharge left = 0 ∧
              quadraticPhaseCharge right = 0 ∧
              right ∉ quadraticSwapOrbit left then
            freeQuadraticSameChargePairValue
              coupling m observed radius frequency time left right
          else 0)) := by
      apply Finset.sum_congr rfl
      intro left hleft
      apply Finset.sum_congr rfl
      intro right hright
      by_cases hzero :
          quadraticPhaseCharge left = 0 ∧ quadraticPhaseCharge right = 0
      · by_cases horbit : right ∈ quadraticSwapOrbit left
        · simp [hzero.1, hzero.2, horbit]
        · simp [hzero.1, hzero.2, horbit]
      · have hnotTripleMem :
            ¬ (quadraticPhaseCharge left = 0 ∧
              quadraticPhaseCharge right = 0 ∧
              right ∈ quadraticSwapOrbit left) :=
          fun h ↦ hzero ⟨h.1, h.2.1⟩
        have hnotTripleNotMem :
            ¬ (quadraticPhaseCharge left = 0 ∧
              quadraticPhaseCharge right = 0 ∧
              right ∉ quadraticSwapOrbit left) :=
          fun h ↦ hzero ⟨h.1, h.2.1⟩
        simp [hzero, hnotTripleMem, hnotTripleNotMem]
    _ =
      (∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
        if quadraticPhaseCharge left = 0 ∧
            quadraticPhaseCharge right = 0 ∧
            right ∈ quadraticSwapOrbit left then
          freeQuadraticSameChargePairValue
            coupling m observed radius frequency time left right
        else 0) +
      ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
        if quadraticPhaseCharge left = 0 ∧
            quadraticPhaseCharge right = 0 ∧
            right ∉ quadraticSwapOrbit left then
          freeQuadraticSameChargePairValue
            coupling m observed radius frequency time left right
        else 0 := by
      simp only [Finset.sum_add_distrib]

/-- Difference form of the preceding exact partition. -/
theorem freeQuadraticZeroChargeCrossOrbitPairSum_eq_full_sub_intra
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    freeQuadraticZeroChargeCrossOrbitPairSum
        coupling m observed radius frequency time =
      freeQuadraticFullZeroChargePairSum
          coupling m observed radius frequency time -
        freeQuadraticZeroChargeIntraOrbitPairSum
          coupling m observed radius frequency time := by
  rw [freeQuadraticFullZeroChargePairSum_eq_intra_add_cross]
  ring

/-- The zero-charge cross-orbit pair sum factors through one common
finite-time resonance weight. -/
theorem freeQuadraticZeroChargeCrossOrbitPairSum_eq_coefficient_mul_weight
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    freeQuadraticZeroChargeCrossOrbitPairSum
        coupling m observed radius frequency time =
      freeQuadraticZeroChargeCrossOrbitCoefficient
          coupling m observed radius *
        (finiteTimeResonanceWeight
          (outputChargeMismatch (frequency observed)
            (0 : Lattice.Site N → Int) frequency) time : Complex) := by
  classical
  unfold freeQuadraticZeroChargeCrossOrbitPairSum
    freeQuadraticZeroChargeCrossOrbitCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro left hleft
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro right hright
  by_cases hkeep :
      quadraticPhaseCharge left = 0 ∧
        quadraticPhaseCharge right = 0 ∧
        right ∉ quadraticSwapOrbit left
  · rw [if_pos hkeep, if_pos hkeep]
    unfold freeQuadraticSameChargePairValue quadraticPhaseMismatch
    rw [hkeep.1]
  · rw [if_neg hkeep, if_neg hkeep]
    simp

/-- Fixed-positive-output `O(T⁻¹)` control of the complete cross-orbit
coherent remainder.  The prefactor is the norm of its exact, time-independent
zero-charge cross coefficient. -/
theorem norm_freeQuadraticCrossSwapOrbitCoherentRemainder_le_inverseTime
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) {time : Real}
    (hfrequency : 0 < frequency observed) (htime : 0 < time) :
    ‖freeQuadraticCrossSwapOrbitCoherentRemainder
        coupling m observed radius frequency time‖ ≤
      ‖freeQuadraticZeroChargeCrossOrbitCoefficient
        coupling m observed radius‖ *
        (4 / (frequency observed ^ 2 * time)) := by
  rw [freeQuadraticCrossSwapOrbitCoherentRemainder_eq_zeroChargePairSum,
    freeQuadraticZeroChargeCrossOrbitPairSum_eq_coefficient_mul_weight,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (finiteTimeResonanceWeight_nonneg _ _)]
  exact mul_le_mul_of_nonneg_left
    (zeroChargeResonanceWeight_le_four_div_sq_mul_time
      observed frequency hfrequency htime)
    (norm_nonneg _)

end

end ArchonPhysics.FreeFPUTCrossOrbitZeroChargeBridge
