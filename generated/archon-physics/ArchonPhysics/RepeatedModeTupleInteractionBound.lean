import ArchonPhysics.CanonicalCollisionSoftLegBound
import ArchonPhysics.CanonicalJointFrequencyPermutationSymmetry

/-!
# Repeated-label three-mode tuples

Equality of two tuple labels does not force a cubic interaction coefficient
to vanish.  Orthogonality controls quadratic expressions, whereas a repeated
three-leg coefficient contains

`sum_j u k j ^ 2 * u q j`.

The exact Parseval sum of its square over `q` is the inverse-participation
ratio `sum_j u k j ^ 4`.  Thus the unconditional per-site estimate is only
`O(1)`.  An `O(1/N)` estimate requires a quantitative delocalization input of
order `IPR <= C/N`; it does not follow from orthogonality alone.
-/

namespace ArchonPhysics.RepeatedModeTupleInteractionBound

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionSoftLegBound
open ArchonPhysics.CanonicalJointFrequencyPermutationSymmetry
open ArchonPhysics.ComplexRegularizedMarkedLegBridge
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.ThreeLegKernelApproximationAlgebra
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open scoped BigOperators Matrix

noncomputable section

section AbstractParseval

variable {mode bond : Type*} [Fintype mode] [DecidableEq mode]
  [Fintype bond] [DecidableEq bond]

/-- Cubic coefficient in which the first two labels coincide. -/
def repeatedCubicCoefficient (u : mode -> bond -> Real)
    (k q : mode) : Real :=
  ∑ j, u k j ^ 2 * u q j

/-- Inverse-participation ratio of one normalized frame vector. -/
def inverseParticipationRatio (u : mode -> bond -> Real) (k : mode) : Real :=
  ∑ j, u k j ^ 4

/-- A square orthonormal row frame is also column orthonormal. -/
theorem column_orthonormal_of_orthonormal_of_card_eq
    (u : mode -> bond -> Real)
    (hcard : Fintype.card mode = Fintype.card bond)
    (horth : forall k q,
      ∑ j, u k j * u q j = if k = q then 1 else 0)
    (j l : bond) :
    (∑ k, u k j * u k l) = if j = l then 1 else 0 := by
  let U : Matrix mode bond Real := u
  have hright : U * U.transpose = 1 := by
    ext k q
    change (∑ x, u k x * u q x) = if k = q then 1 else 0
    exact horth k q
  have hleft : U.transpose * U = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq mode bond Real hcard).mp hright
  have hentry := congrArg (fun M : Matrix bond bond Real => M j l) hleft
  rw [Matrix.mul_apply] at hentry
  simp_rw [Matrix.transpose_apply] at hentry
  simpa [U, Matrix.one_apply] using hentry

omit [DecidableEq bond] in
/-- Parseval identity for a repeated-label cubic coefficient. -/
theorem sum_repeatedCubicCoefficient_sq_eq_inverseParticipationRatio
    (u : mode -> bond -> Real)
    (hcard : Fintype.card mode = Fintype.card bond)
    (horth : forall k q,
      ∑ j, u k j * u q j = if k = q then 1 else 0)
    (k : mode) :
    (∑ q, repeatedCubicCoefficient u k q ^ 2) =
      inverseParticipationRatio u k := by
  classical
  have hcolumn := column_orthonormal_of_orthonormal_of_card_eq
    u hcard horth
  unfold repeatedCubicCoefficient inverseParticipationRatio
  calc
    (∑ q, (∑ j, u k j ^ 2 * u q j) ^ 2) =
        ∑ q, ∑ j, ∑ l,
          (u k j ^ 2 * u q j) * (u k l ^ 2 * u q l) := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.mul_sum]
    _ = ∑ j, ∑ l, ∑ q,
        (u k j ^ 2 * u q j) * (u k l ^ 2 * u q l) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ l,
        (u k j ^ 2 * u k l ^ 2) * (∑ q, u q j * u q l) := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro l _hl
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      ring
    _ = ∑ j, u k j ^ 4 := by
      apply Finset.sum_congr rfl
      intro j _hj
      simp_rw [hcolumn]
      simp
      ring

omit [Fintype mode] [DecidableEq bond] in
/-- Every inverse-participation ratio of a normalized orthogonal row is at
most one.  This is sharp for a coordinate basis, so orthogonality alone gives
no volume decay. -/
theorem inverseParticipationRatio_le_one
    (u : mode -> bond -> Real)
    (horth : forall k q,
      ∑ j, u k j * u q j = if k = q then 1 else 0)
    (k : mode) : inverseParticipationRatio u k <= 1 := by
  have hnorm : (∑ j, u k j ^ 2) = 1 := by
    simpa [pow_two] using horth k k
  unfold inverseParticipationRatio
  calc
    (∑ j, u k j ^ 4) = ∑ j, (u k j ^ 2) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ <= (∑ j, u k j ^ 2) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg
        (fun j _hj => sq_nonneg (u k j))
    _ = 1 := by rw [hnorm]; norm_num


/-- Orthogonality alone cannot force a repeated cubic coefficient to vanish:
the one-dimensional orthonormal frame has repeated coefficient exactly one. -/
theorem repeatedCubicCoefficient_unit_eq_one :
    repeatedCubicCoefficient (fun _ : Unit => fun _ : Unit => (1 : Real))
      () () = 1 := by
  simp [repeatedCubicCoefficient]

end AbstractParseval

section HarmonicRepeatedTuples

/-- A double contraction of three rank-one kernels with the first two
factors equal is the square of the repeated cubic coefficient. -/
theorem doubleSum_repeated_rankOne_eq
    {bond : Type*} [Fintype bond]
    (a b : Real) (u v : bond -> Real) :
    (∑ j, ∑ l,
      (a * u j * u l) * (a * u j * u l) * (b * v j * v l)) =
      a ^ 2 * b * (∑ j, u j ^ 2 * v j) ^ 2 := by
  calc
    (∑ j, ∑ l,
      (a * u j * u l) * (a * u j * u l) * (b * v j * v l)) =
        ∑ j, ∑ l, a ^ 2 * b *
          ((u j ^ 2 * v j) * (u l ^ 2 * v l)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro l _hl
      ring
    _ = a ^ 2 * b * (∑ j, u j ^ 2 * v j) ^ 2 := by
      have hsquare :
          (∑ j, u j ^ 2 * v j) ^ 2 =
            ∑ j, ∑ l, (u j ^ 2 * v j) * (u l ^ 2 * v l) := by
        rw [pow_two, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [Finset.mul_sum]
      rw [hsquare, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.mul_sum]

/-- The active one-leg coefficient after physical inverse-frequency
normalization.  It is zero for a totalized repeated eigenvalue, but equality
of two tuple labels does not make it zero. -/
def harmonicActiveNormalizedCoefficient {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : OrderedModeIndex N) : Real :=
  activeOrderedEigenvalue m k *
    (2 * orderedModeFrequency (harmonicHermitian m) k)⁻¹

/-- Exact edge-frame formula for a tuple whose first two labels coincide. -/
theorem harmonicOrderedNormalizedInteractionWeight_repeated_zero_one_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k q : OrderedModeIndex N) :
    harmonicOrderedNormalizedInteractionWeight m ![k, k, q] =
      harmonicActiveNormalizedCoefficient m k ^ 2 *
        harmonicActiveNormalizedCoefficient m q *
          repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m) k q ^ 2 := by
  unfold harmonicOrderedNormalizedInteractionWeight
    harmonicOrderedInteractionWeightSq orderedInteractionWeightSq
    harmonicActiveNormalizedCoefficient repeatedCubicCoefficient
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.prod_univ_three, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_inv_rev]
  simp_rw [projectedBondKernel_eq_activeOrderedEigenvalue_mul_edgeFrame]
  rw [doubleSum_repeated_rankOne_eq]
  ring

/-- Total positive collision weight on the equality plane `mode 0 = mode 1`,
parametrized without duplication by the common label and the remaining
label. -/
def positiveRepeatedZeroOneInteractionWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) : Real := by
  classical
  exact ∑ k, ∑ q,
    if IsPositiveOrderedTriple m ![k, k, q] then
      harmonicOrderedNormalizedInteractionWeight m ![k, k, q]
    else 0

/-- Total positive collision weight on `mode 0 = mode 2`. -/
def positiveRepeatedZeroTwoInteractionWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) : Real := by
  classical
  exact ∑ k, ∑ q,
    if IsPositiveOrderedTriple m ![k, q, k] then
      harmonicOrderedNormalizedInteractionWeight m ![k, q, k]
    else 0

/-- Total positive collision weight on `mode 1 = mode 2`. -/
def positiveRepeatedOneTwoInteractionWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) : Real := by
  classical
  exact ∑ k, ∑ q,
    if IsPositiveOrderedTriple m ![q, k, k] then
      harmonicOrderedNormalizedInteractionWeight m ![q, k, k]
    else 0


/-- Swapping legs one and two transports `0 = 1` to `0 = 2`. -/
theorem harmonicOrderedNormalizedInteractionWeight_repeated_zero_two_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k q : OrderedModeIndex N) :
    harmonicOrderedNormalizedInteractionWeight m ![k, q, k] =
      harmonicOrderedNormalizedInteractionWeight m ![k, k, q] := by
  let e : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  have htuple :
      (![k, k, q] : OrderedModeTriple N) ∘ e = ![k, q, k] := by
    funext r
    fin_cases r <;> simp [e, Function.comp_apply, Equiv.swap_apply_def]
  rw [← htuple]
  exact harmonicOrderedNormalizedInteractionWeight_perm m ![k, k, q] e

/-- Swapping legs zero and two transports `0 = 1` to `1 = 2`. -/
theorem harmonicOrderedNormalizedInteractionWeight_repeated_one_two_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k q : OrderedModeIndex N) :
    harmonicOrderedNormalizedInteractionWeight m ![q, k, k] =
      harmonicOrderedNormalizedInteractionWeight m ![k, k, q] := by
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  have htuple :
      (![k, k, q] : OrderedModeTriple N) ∘ e = ![q, k, k] := by
    funext r
    fin_cases r <;> simp [e, Function.comp_apply, Equiv.swap_apply_def]
  rw [← htuple]
  exact harmonicOrderedNormalizedInteractionWeight_perm m ![k, k, q] e

/-- The positive filters of the `0 = 1` and `0 = 2` parametrizations agree. -/
theorem isPositive_repeated_zero_two_iff_zero_one
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k q : OrderedModeIndex N) :
    IsPositiveOrderedTriple m ![k, q, k] ↔
      IsPositiveOrderedTriple m ![k, k, q] := by
  simp only [IsPositiveOrderedTriple]
  constructor <;> intro h r <;> fin_cases r
  · exact h 0
  · exact h 2
  · exact h 1
  · exact h 0
  · exact h 2
  · exact h 0

/-- The positive filters of the `0 = 1` and `1 = 2` parametrizations agree. -/
theorem isPositive_repeated_one_two_iff_zero_one
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k q : OrderedModeIndex N) :
    IsPositiveOrderedTriple m ![q, k, k] ↔
      IsPositiveOrderedTriple m ![k, k, q] := by
  simp only [IsPositiveOrderedTriple]
  constructor <;> intro h r <;> fin_cases r
  · exact h 1
  · exact h 1
  · exact h 0
  · exact h 2
  · exact h 0
  · exact h 0

/-- All three labeled equality planes have the same total weight. -/
theorem positiveRepeatedPairInteractionWeights_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    positiveRepeatedZeroTwoInteractionWeight m =
        positiveRepeatedZeroOneInteractionWeight m ∧
      positiveRepeatedOneTwoInteractionWeight m =
        positiveRepeatedZeroOneInteractionWeight m := by
  constructor
  · unfold positiveRepeatedZeroTwoInteractionWeight
      positiveRepeatedZeroOneInteractionWeight
    apply Finset.sum_congr rfl
    intro k _hk
    apply Finset.sum_congr rfl
    intro q _hq
    rw [isPositive_repeated_zero_two_iff_zero_one]
    split_ifs
    · exact harmonicOrderedNormalizedInteractionWeight_repeated_zero_two_eq
        m k q
    · rfl
  · unfold positiveRepeatedOneTwoInteractionWeight
      positiveRepeatedZeroOneInteractionWeight
    apply Finset.sum_congr rfl
    intro k _hk
    apply Finset.sum_congr rfl
    intro q _hq
    rw [isPositive_repeated_one_two_iff_zero_one]
    split_ifs
    · exact harmonicOrderedNormalizedInteractionWeight_repeated_one_two_eq
        m k q
    · rfl

/-- The positive filter can be removed from the repeated-label sum because
every nonpositive tuple already has totalized inverse-frequency weight zero. -/
theorem positiveRepeatedZeroOneInteractionWeight_eq_unfiltered
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    positiveRepeatedZeroOneInteractionWeight m =
      ∑ k, ∑ q, harmonicOrderedNormalizedInteractionWeight m ![k, k, q] := by
  classical
  unfold positiveRepeatedZeroOneInteractionWeight
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hpositive : IsPositiveOrderedTriple m ![k, k, q]
  · simp [hpositive]
  · simp [hpositive,
      harmonicOrderedNormalizedInteractionWeight_eq_zero_of_not_positive
        m ![k, k, q] hpositive]

/-- The active normalized coefficient is nonnegative. -/
theorem harmonicActiveNormalizedCoefficient_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k : OrderedModeIndex N) :
    0 <= harmonicActiveNormalizedCoefficient m k := by
  classical
  unfold harmonicActiveNormalizedCoefficient activeOrderedEigenvalue
  split_ifs
  · exact mul_nonneg (harmonicHermitian_orderedEigenvalue_nonneg m k)
      (inv_nonneg.mpr (mul_nonneg zero_le_two (Real.sqrt_nonneg _)))
  · simp

/-- A deterministic frequency ceiling bounds every active normalized leg by
half that ceiling. -/
theorem harmonicActiveNormalizedCoefficient_le_half_ceiling
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (ceiling : Real)
    (hfrequency : forall k,
      orderedModeFrequency (harmonicHermitian m) k <= ceiling)
    (k : OrderedModeIndex N) :
    harmonicActiveNormalizedCoefficient m k <= ceiling / 2 := by
  have hnonneg := harmonicActiveNormalizedCoefficient_nonneg m k
  have hactive :=
    abs_activeOrderedEigenvalue_mul_inv_two_frequency_le m k
  change |harmonicActiveNormalizedCoefficient m k| <=
    orderedModeFrequency (harmonicHermitian m) k / 2 at hactive
  rw [abs_of_nonneg hnonneg] at hactive
  exact hactive.trans (div_le_div_of_nonneg_right (hfrequency k) (by norm_num))

/-- Exact harmonic specialization of the repeated-label Parseval identity. -/
theorem sum_harmonicRepeatedCubicCoefficient_sq_eq_ipr
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k : OrderedModeIndex N) :
    (∑ q, repeatedCubicCoefficient
      (harmonicNormalizedEdgeFrame m) k q ^ 2) =
      inverseParticipationRatio (harmonicNormalizedEdgeFrame m) k := by
  exact sum_repeatedCubicCoefficient_sq_eq_inverseParticipationRatio
    (harmonicNormalizedEdgeFrame m) (by simp [Lattice.Site])
      (harmonicNormalizedEdgeFrame_orthonormal_unconditional m) k

/-- Parseval reduces the complete repeated-label collision weight to the sum
of edge-frame inverse-participation ratios. -/
theorem positiveRepeatedZeroOneInteractionWeight_le_ipr_sum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (ceiling : Real) (hceiling : 0 <= ceiling)
    (hfrequency : forall k,
      orderedModeFrequency (harmonicHermitian m) k <= ceiling) :
    positiveRepeatedZeroOneInteractionWeight m <=
      (ceiling / 2) ^ 3 *
        ∑ k, inverseParticipationRatio
          (harmonicNormalizedEdgeFrame m) k := by
  rw [positiveRepeatedZeroOneInteractionWeight_eq_unfiltered]
  calc
    (∑ k, ∑ q, harmonicOrderedNormalizedInteractionWeight m ![k, k, q]) <=
        ∑ k, ∑ q, (ceiling / 2) ^ 3 *
          repeatedCubicCoefficient
            (harmonicNormalizedEdgeFrame m) k q ^ 2 := by
      apply Finset.sum_le_sum
      intro k _hk
      apply Finset.sum_le_sum
      intro q _hq
      rw [harmonicOrderedNormalizedInteractionWeight_repeated_zero_one_eq]
      have hk0 := harmonicActiveNormalizedCoefficient_nonneg m k
      have hq0 := harmonicActiveNormalizedCoefficient_nonneg m q
      have hkb := harmonicActiveNormalizedCoefficient_le_half_ceiling
        m ceiling hfrequency k
      have hqb := harmonicActiveNormalizedCoefficient_le_half_ceiling
        m ceiling hfrequency q
      have hhalf : 0 <= ceiling / 2 := div_nonneg hceiling (by norm_num)
      have hcoefficient :
          harmonicActiveNormalizedCoefficient m k ^ 2 *
              harmonicActiveNormalizedCoefficient m q <=
            (ceiling / 2) ^ 3 := by
        calc
          harmonicActiveNormalizedCoefficient m k ^ 2 *
              harmonicActiveNormalizedCoefficient m q <=
              (ceiling / 2) ^ 2 * (ceiling / 2) := by
            exact mul_le_mul
              (pow_le_pow_left₀ hk0 hkb 2) hqb hq0 (sq_nonneg _)
          _ = (ceiling / 2) ^ 3 := by ring
      exact mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg _)
    _ = (ceiling / 2) ^ 3 *
        ∑ k, inverseParticipationRatio
          (harmonicNormalizedEdgeFrame m) k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [<- Finset.mul_sum,
        sum_harmonicRepeatedCubicCoefficient_sq_eq_ipr]

/-- If every edge eigenmode has `IPR <= rho`, the per-site repeated-label
weight is at most `(ceiling/2)^3 * rho`. -/
theorem positiveRepeatedZeroOneInteractionWeight_div_volume_le_of_ipr
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (ceiling rho : Real) (hceiling : 0 <= ceiling)
    (hfrequency : forall k,
      orderedModeFrequency (harmonicHermitian m) k <= ceiling)
    (hipr : forall k,
      inverseParticipationRatio (harmonicNormalizedEdgeFrame m) k <= rho) :
    positiveRepeatedZeroOneInteractionWeight m / (N : Real) <=
      (ceiling / 2) ^ 3 * rho := by
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hiprSum :
      (∑ k, inverseParticipationRatio
        (harmonicNormalizedEdgeFrame m) k) <= (N : Real) * rho := by
    calc
      (∑ k, inverseParticipationRatio
          (harmonicNormalizedEdgeFrame m) k) <= ∑ _k, rho := by
        exact Finset.sum_le_sum fun k _hk => hipr k
      _ = (N : Real) * rho := by simp [Lattice.Site]
  calc
    positiveRepeatedZeroOneInteractionWeight m / (N : Real) <=
        ((ceiling / 2) ^ 3 *
          ∑ k, inverseParticipationRatio
            (harmonicNormalizedEdgeFrame m) k) / (N : Real) :=
      div_le_div_of_nonneg_right
        (positiveRepeatedZeroOneInteractionWeight_le_ipr_sum
          m ceiling hceiling hfrequency) hN.le
    _ <= ((ceiling / 2) ^ 3 * ((N : Real) * rho)) / (N : Real) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hiprSum
          (pow_nonneg (div_nonneg hceiling (by norm_num)) 3)) hN.le
    _ = (ceiling / 2) ^ 3 * rho := by field_simp


/-- Explicit `O(1/N)` corollary under the missing delocalization estimate
`IPR <= C/N`. -/
theorem positiveRepeatedZeroOneInteractionWeight_div_volume_le_inv_volume
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (ceiling C : Real) (hceiling : 0 <= ceiling)
    (hfrequency : forall k,
      orderedModeFrequency (harmonicHermitian m) k <= ceiling)
    (hipr : forall k,
      inverseParticipationRatio (harmonicNormalizedEdgeFrame m) k <=
        C / (N : Real)) :
    positiveRepeatedZeroOneInteractionWeight m / (N : Real) <=
      (ceiling / 2) ^ 3 * (C / (N : Real)) :=
  positiveRepeatedZeroOneInteractionWeight_div_volume_le_of_ipr
    m ceiling (C / (N : Real)) hceiling hfrequency hipr

/-- Orthogonality alone gives only the sharp uniform `O(1)` per-site bound. -/
theorem positiveRepeatedZeroOneInteractionWeight_div_volume_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (ceiling : Real) (hceiling : 0 <= ceiling)
    (hfrequency : forall k,
      orderedModeFrequency (harmonicHermitian m) k <= ceiling) :
    positiveRepeatedZeroOneInteractionWeight m / (N : Real) <=
      (ceiling / 2) ^ 3 := by
  simpa using
    (positiveRepeatedZeroOneInteractionWeight_div_volume_le_of_ipr
      m ceiling 1 hceiling hfrequency (fun k =>
        inverseParticipationRatio_le_one
          (harmonicNormalizedEdgeFrame m)
          (harmonicNormalizedEdgeFrame_orthonormal_unconditional m) k))


/-- The same orthogonality-only bound holds simultaneously for all three
labeled repeated-pair planes. -/
theorem positiveRepeatedPairInteractionWeights_div_volume_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (ceiling : Real) (hceiling : 0 <= ceiling)
    (hfrequency : forall k,
      orderedModeFrequency (harmonicHermitian m) k <= ceiling) :
    positiveRepeatedZeroOneInteractionWeight m / (N : Real) <=
        (ceiling / 2) ^ 3 ∧
      positiveRepeatedZeroTwoInteractionWeight m / (N : Real) <=
        (ceiling / 2) ^ 3 ∧
      positiveRepeatedOneTwoInteractionWeight m / (N : Real) <=
        (ceiling / 2) ^ 3 := by
  have hmain := positiveRepeatedZeroOneInteractionWeight_div_volume_le
    m ceiling hceiling hfrequency
  rcases positiveRepeatedPairInteractionWeights_eq m with ⟨hzeroTwo, honeTwo⟩
  refine ⟨hmain, ?_, ?_⟩
  · simpa [hzeroTwo] using hmain
  · simpa [honeTwo] using hmain

/-! ## Decay-channel resonance audit -/

/-- If the incoming label equals the first outgoing label, the remaining
positive frequency is exactly the (nonzero) mismatch magnitude. -/
theorem orderedThreeWaveMismatch_decay_eq_neg_two_of_zero_eq_one
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (heq : modes 0 = modes 1) :
    orderedThreeWaveMismatch m decayInteractionSign modes =
      -orderedModeFrequency (harmonicHermitian m) (modes 2) := by
  rw [orderedThreeWaveMismatch_decay_eq, heq]
  ring

/-- The analogous identity for equality of legs zero and two. -/
theorem orderedThreeWaveMismatch_decay_eq_neg_one_of_zero_eq_two
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (heq : modes 0 = modes 2) :
    orderedThreeWaveMismatch m decayInteractionSign modes =
      -orderedModeFrequency (harmonicHermitian m) (modes 1) := by
  rw [orderedThreeWaveMismatch_decay_eq, heq]
  ring

/-- Equality of the two outgoing labels does not force an off-resonant
mismatch: it leaves the possible relation `omega_0 = 2 * omega_1`. -/
theorem orderedThreeWaveMismatch_decay_eq_zero_sub_two_mul_of_one_eq_two
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (heq : modes 1 = modes 2) :
    orderedThreeWaveMismatch m decayInteractionSign modes =
      orderedModeFrequency (harmonicHermitian m) (modes 0) -
        2 * orderedModeFrequency (harmonicHermitian m) (modes 1) := by
  rw [orderedThreeWaveMismatch_decay_eq, ← heq]
  ring

/-- A hard lower frequency band turns a `0 = 1` tuple into a quantitative
off-resonance tuple. -/
theorem eta_le_abs_orderedThreeWaveMismatch_decay_of_zero_eq_one
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) {eta : Real}
    (heq : modes 0 = modes 1)
    (hband : eta <=
      orderedModeFrequency (harmonicHermitian m) (modes 2)) :
    eta <= |orderedThreeWaveMismatch m decayInteractionSign modes| := by
  rw [orderedThreeWaveMismatch_decay_eq_neg_two_of_zero_eq_one m modes heq,
    abs_neg]
  have hnonneg : 0 <= orderedModeFrequency
      (harmonicHermitian m) (modes 2) := by
    unfold orderedModeFrequency
    exact Real.sqrt_nonneg _
  rw [abs_of_nonneg hnonneg]
  exact hband

/-- Hard-band off-resonance for a `0 = 2` tuple. -/
theorem eta_le_abs_orderedThreeWaveMismatch_decay_of_zero_eq_two
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) {eta : Real}
    (heq : modes 0 = modes 2)
    (hband : eta <=
      orderedModeFrequency (harmonicHermitian m) (modes 1)) :
    eta <= |orderedThreeWaveMismatch m decayInteractionSign modes| := by
  rw [orderedThreeWaveMismatch_decay_eq_neg_one_of_zero_eq_two m modes heq,
    abs_neg]
  have hnonneg : 0 <= orderedModeFrequency
      (harmonicHermitian m) (modes 1) := by
    unfold orderedModeFrequency
    exact Real.sqrt_nonneg _
  rw [abs_of_nonneg hnonneg]
  exact hband

end HarmonicRepeatedTuples

end

end ArchonPhysics.RepeatedModeTupleInteractionBound
