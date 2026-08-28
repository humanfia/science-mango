import ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
import ArchonPhysics.FreeFPUTBinaryTreeTimeWeightSummation
import ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples

/-!
# Catalan majorants and summable arbitrary-order FPUT Picard tails

At fixed output momentum, an order-`r` quadratic FPUT history has exactly
`catalan r * 4^r * N^r` raw choices and at most `16^r * N^r` choices.  This
file combines that proved finite-volume count with a transparent analytic
single-history input.

If every raw history has norm at most

`A * (q / (16 * N))^r`,

then the complete order-`r` sum has norm at most `A * q^r`.  Hence, for
`0 <= q < 1`, the tail beginning at order `R` is absolutely summable and is
bounded by `A * q^R / (1 - q)`; this envelope tends to zero as `R -> infinity`.

If the exact time-simplex factor is retained, the proved identity for its
sum over all tree shapes removes the Catalan loss.  The sharper input

`A * (q / (4 * N))^r * binaryTreeTimeSimplexWeight tree T`

therefore gives the order bound `A * (q*T)^r` and the corresponding geometric
tail whenever `q*T < 1`.

The final section connects the analytic input to the recursive coefficient
already defined by `PhyslibFPUTBinaryInteractionTreeCouples`: uniform leaf,
vertex and edge bounds give the explicit per-tree majorant

`L^(r+1) * (V * E^2)^r`.

Time-ordered integrals and small divisors are not silently estimated here.
They must be included in the supplied history coefficient or in its stated
single-history bound.  No kinetic equation or continuum limit is assumed.
-/

namespace ArchonPhysics.FreeFPUTCatalanPicardTailMajorant

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.FreeFPUTBinaryTreeTimeSimplexWeight
open ArchonPhysics.FreeFPUTBinaryTreeTimeWeightSummation
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open Filter Topology

noncomputable section

/-! ## Fixed-root arbitrary-order sums -/

/-- The complete raw-history sum at a fixed root and fixed perturbative
order. -/
def fixedRootRawHistoryOrderSum
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (r : Nat) : Complex :=
  ∑ history : FixedRootRawHistoryIndex N r rootMomentum,
    coefficient r history

/-- The infinite order tail beginning at order `R`.  Summability is proved
below from the explicit Catalan majorant. -/
def fixedRootRawHistoryTail
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (R : Nat) : Complex :=
  ∑' n : Nat,
    fixedRootRawHistoryOrderSum N rootMomentum coefficient (n + R)

/-- Natural scale which exactly cancels the proved `16^r N^r` raw-history
majorant. -/
def singleHistoryCatalanScale (N : Nat) (q : Real) (r : Nat) : Real :=
  (q / (16 * (N : Real))) ^ r

/-- Natural scale after retaining the exact tree-simplex weight.  The shape
sum has no Catalan factor, so only `4^r` signs and `N^r` momenta must be
cancelled. -/
def singleHistoryExactTimeScale (N : Nat) (q : Real) (r : Nat) : Real :=
  (q / (4 * (N : Real))) ^ r

theorem singleHistoryCatalanScale_nonneg
    (N : Nat) {q : Real} (hq : 0 <= q) (r : Nat) :
    0 <= singleHistoryCatalanScale N q r := by
  unfold singleHistoryCatalanScale
  positivity

theorem singleHistoryExactTimeScale_nonneg
    (N : Nat) {q : Real} (hq : 0 <= q) (r : Nat) :
    0 <= singleHistoryExactTimeScale N q r := by
  unfold singleHistoryExactTimeScale
  positivity

/-- Cast form of the proved raw-history cardinality majorant. -/
theorem card_fixedRootRawHistoryIndex_cast_le
    (N r : Nat) [NeZero N] (rootMomentum : Site N) :
    (Fintype.card (FixedRootRawHistoryIndex N r rootMomentum) : Real) <=
      (16 : Real) ^ r * (N : Real) ^ r := by
  exact_mod_cast card_fixedRootRawHistoryIndex_le rootMomentum

/-- Exact Catalan-counted order bound before replacing `catalan r` by
`4^r`. -/
theorem norm_fixedRootRawHistoryOrderSum_le_exactCatalan
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    {A q : Real} (_hA : 0 <= A) (_hq : 0 <= q)
    (hsingle : forall r history,
      ‖coefficient r history‖ <=
        A * singleHistoryCatalanScale N q r)
    (r : Nat) :
    ‖fixedRootRawHistoryOrderSum N rootMomentum coefficient r‖ <=
      (catalan r * 4 ^ r * N ^ r : Nat) *
        (A * singleHistoryCatalanScale N q r) := by
  classical
  unfold fixedRootRawHistoryOrderSum
  calc
    ‖∑ history : FixedRootRawHistoryIndex N r rootMomentum,
        coefficient r history‖ <=
        ∑ history : FixedRootRawHistoryIndex N r rootMomentum,
          ‖coefficient r history‖ := norm_sum_le _ _
    _ <= ∑ _history : FixedRootRawHistoryIndex N r rootMomentum,
          A * singleHistoryCatalanScale N q r := by
      apply Finset.sum_le_sum
      intro history _historyMem
      exact hsingle r history
    _ = (Fintype.card
          (FixedRootRawHistoryIndex N r rootMomentum) : Real) *
          (A * singleHistoryCatalanScale N q r) := by simp
    _ = (catalan r * 4 ^ r * N ^ r : Nat) *
          (A * singleHistoryCatalanScale N q r) := by
      rw [card_fixedRootRawHistoryIndex rootMomentum]

/-- The key Catalan majorant: the entire order-`r` sum is geometric after
the `16^r N^r` combinatorial proliferation has been paid for. -/
theorem norm_fixedRootRawHistoryOrderSum_le_geometric
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    {A q : Real} (hA : 0 <= A) (hq : 0 <= q)
    (hsingle : forall r history,
      ‖coefficient r history‖ <=
        A * singleHistoryCatalanScale N q r)
    (r : Nat) :
    ‖fixedRootRawHistoryOrderSum N rootMomentum coefficient r‖ <=
      A * q ^ r := by
  classical
  have hscale0 : 0 <= singleHistoryCatalanScale N q r :=
    singleHistoryCatalanScale_nonneg N hq r
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  calc
    ‖fixedRootRawHistoryOrderSum N rootMomentum coefficient r‖ <=
        (Fintype.card
          (FixedRootRawHistoryIndex N r rootMomentum) : Real) *
          (A * singleHistoryCatalanScale N q r) := by
      unfold fixedRootRawHistoryOrderSum
      calc
        ‖∑ history : FixedRootRawHistoryIndex N r rootMomentum,
            coefficient r history‖ <=
            ∑ history : FixedRootRawHistoryIndex N r rootMomentum,
              ‖coefficient r history‖ := norm_sum_le _ _
        _ <= ∑ _history : FixedRootRawHistoryIndex N r rootMomentum,
              A * singleHistoryCatalanScale N q r := by
          apply Finset.sum_le_sum
          intro history _historyMem
          exact hsingle r history
        _ = _ := by simp
    _ <= ((16 : Real) ^ r * (N : Real) ^ r) *
          (A * singleHistoryCatalanScale N q r) := by
      gcongr
      exact card_fixedRootRawHistoryIndex_cast_le N r rootMomentum
    _ = A * q ^ r := by
      unfold singleHistoryCatalanScale
      rw [div_pow]
      field_simp [hN]
      rw [mul_pow]
      ring

/-! ## Absolute summability and the explicit tail -/

theorem summable_shifted_geometric
    {A q : Real} (hq0 : 0 <= q) (hq1 : q < 1) (R : Nat) :
    Summable (fun n : Nat => A * q ^ (n + R)) := by
  have hqAbs : |q| < 1 := by simpa [abs_of_nonneg hq0] using hq1
  have hbase : Summable (fun n : Nat => q ^ n) :=
    summable_geometric_of_abs_lt_one hqAbs
  simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using
    hbase.mul_left (A * q ^ R)

theorem tsum_shifted_geometric
    {A q : Real} (hq0 : 0 <= q) (hq1 : q < 1) (R : Nat) :
    (∑' n : Nat, A * q ^ (n + R)) = A * q ^ R / (1 - q) := by
  have hqAbs : |q| < 1 := by simpa [abs_of_nonneg hq0] using hq1
  calc
    (∑' n : Nat, A * q ^ (n + R)) =
        (A * q ^ R) * ∑' n : Nat, q ^ n := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [pow_add]
      ring
    _ = (A * q ^ R) * (1 - q)⁻¹ := by
      rw [tsum_geometric_of_abs_lt_one hqAbs]
    _ = A * q ^ R / (1 - q) := by
      rw [div_eq_mul_inv]

/-- The sequence of complete order sums is absolutely summable whenever the
post-counting ratio is strictly smaller than one. -/
theorem summable_norm_fixedRootRawHistoryOrderSum
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    {A q : Real} (hA : 0 <= A) (hq0 : 0 <= q) (hq1 : q < 1)
    (hsingle : forall r history,
      ‖coefficient r history‖ <=
        A * singleHistoryCatalanScale N q r) :
    Summable (fun r : Nat =>
      ‖fixedRootRawHistoryOrderSum N rootMomentum coefficient r‖) := by
  exact (summable_shifted_geometric hq0 hq1 0).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun r => by
      simpa using norm_fixedRootRawHistoryOrderSum_le_geometric
        N rootMomentum coefficient hA hq0 hsingle r)

/-- Consequently the complex arbitrary-order series itself is summable. -/
theorem summable_fixedRootRawHistoryOrderSum
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    {A q : Real} (hA : 0 <= A) (hq0 : 0 <= q) (hq1 : q < 1)
    (hsingle : forall r history,
      ‖coefficient r history‖ <=
        A * singleHistoryCatalanScale N q r) :
    Summable (fun r : Nat =>
      fixedRootRawHistoryOrderSum N rootMomentum coefficient r) :=
  (summable_norm_fixedRootRawHistoryOrderSum
    N rootMomentum coefficient hA hq0 hq1 hsingle).of_norm

/-- Explicit infinite-tail estimate.  This is a genuine consequence of the
single-history bound and the proved Catalan count, rather than a supplied
`error -> 0` hypothesis. -/
theorem norm_fixedRootRawHistoryTail_le_geometric
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    {A q : Real} (hA : 0 <= A) (hq0 : 0 <= q) (hq1 : q < 1)
    (hsingle : forall r history,
      ‖coefficient r history‖ <=
        A * singleHistoryCatalanScale N q r)
    (R : Nat) :
    ‖fixedRootRawHistoryTail N rootMomentum coefficient R‖ <=
      A * q ^ R / (1 - q) := by
  let orderSum : Nat -> Complex := fun r =>
    fixedRootRawHistoryOrderSum N rootMomentum coefficient r
  have hpoint (n : Nat) :
      ‖orderSum (n + R)‖ <= A * q ^ (n + R) :=
    norm_fixedRootRawHistoryOrderSum_le_geometric
      N rootMomentum coefficient hA hq0 hsingle (n + R)
  have hgeom : Summable (fun n : Nat => A * q ^ (n + R)) :=
    summable_shifted_geometric hq0 hq1 R
  have hnorm : Summable (fun n : Nat => ‖orderSum (n + R)‖) :=
    hgeom.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  unfold fixedRootRawHistoryTail
  change ‖∑' n : Nat, orderSum (n + R)‖ <= _
  calc
    ‖∑' n : Nat, orderSum (n + R)‖ <=
        ∑' n : Nat, ‖orderSum (n + R)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ <= ∑' n : Nat, A * q ^ (n + R) :=
      hnorm.tsum_le_tsum hpoint hgeom
    _ = A * q ^ R / (1 - q) :=
      tsum_shifted_geometric hq0 hq1 R

theorem geometricTailEnvelope_tendsto_zero
    {A q : Real} (hq0 : 0 <= q) (hq1 : q < 1) :
    Tendsto (fun R : Nat => A * q ^ R / (1 - q))
      atTop (nhds 0) := by
  have hpow : Tendsto (fun R : Nat => q ^ R) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    hpow.const_mul (A / (1 - q))

/-- The norm of the actual complex tail tends to zero as the truncation
order tends to infinity. -/
theorem norm_fixedRootRawHistoryTail_tendsto_zero
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    {A q : Real} (hA : 0 <= A) (hq0 : 0 <= q) (hq1 : q < 1)
    (hsingle : forall r history,
      ‖coefficient r history‖ <=
        A * singleHistoryCatalanScale N q r) :
    Tendsto (fun R : Nat =>
      ‖fixedRootRawHistoryTail N rootMomentum coefficient R‖)
      atTop (nhds 0) := by
  apply squeeze_zero'
      (g := fun R : Nat => A * q ^ R / (1 - q))
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · exact Eventually.of_forall fun R =>
      norm_fixedRootRawHistoryTail_le_geometric
        N rootMomentum coefficient hA hq0 hq1 hsingle R
  · exact geometricTailEnvelope_tendsto_zero hq0 hq1

/-! ## Exact time-simplex-weighted histories -/

/-- Before discarding any tree-factorial gain, the complete order sum is
controlled by the exact proved sum of time-simplex weights over the raw
history family. -/
theorem norm_fixedRootRawHistoryOrderSum_le_exactTimeSimplex
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    {A q T : Real} (_hA : 0 <= A) (_hq : 0 <= q) (_hT : 0 <= T)
    (hsingle : forall r history,
      ‖coefficient r history‖ <=
        A * singleHistoryExactTimeScale N q r *
          binaryTreeTimeSimplexWeight history.1.1 T)
    (r : Nat) :
    ‖fixedRootRawHistoryOrderSum N rootMomentum coefficient r‖ <=
      A * singleHistoryExactTimeScale N q r *
        fixedRootRawHistoryTimeWeight r rootMomentum T := by
  classical
  rw [fixedRootRawHistoryTimeWeight_eq]
  unfold fixedRootRawHistoryOrderSum
  have htimeWeight :
      (∑ history : FixedRootRawHistoryIndex N r rootMomentum,
        binaryTreeTimeSimplexWeight history.1.1 T) =
        (4 ^ r * N ^ r : Nat) * T ^ r := by
    calc
      (∑ history : FixedRootRawHistoryIndex N r rootMomentum,
          binaryTreeTimeSimplexWeight history.1.1 T) =
          fixedRootRawHistoryTimeWeight r rootMomentum T := by
        unfold fixedRootRawHistoryTimeWeight
        let explicitHistory :=
          Σ tree : BinaryInteractionTreeOfOrder r,
            Σ decoration : BinarySignDecoration tree.1,
              {momentum :
                  (signedMomentumTreeOfDecoration
                    tree.1 decoration).LeafPosition → Site N //
                (signedMomentumTreeOfDecoration
                  tree.1 decoration).leafMomentumToRoot momentum =
                    rootMomentum}
        let reindex :
            FixedRootRawHistoryIndex N r rootMomentum ≃
              explicitHistory := Equiv.refl _
        let explicitHistoryFintype : Fintype explicitHistory :=
          @Sigma.instFintype
            (BinaryInteractionTreeOfOrder r)
            (fun tree =>
              Σ decoration : BinarySignDecoration tree.1,
                {momentum :
                    (signedMomentumTreeOfDecoration
                      tree.1 decoration).LeafPosition → Site N //
                  (signedMomentumTreeOfDecoration
                    tree.1 decoration).leafMomentumToRoot momentum =
                      rootMomentum})
            (fun tree =>
              @Sigma.instFintype
                (BinarySignDecoration tree.1)
                (fun decoration =>
                  {momentum :
                      (signedMomentumTreeOfDecoration
                        tree.1 decoration).LeafPosition → Site N //
                    (signedMomentumTreeOfDecoration
                      tree.1 decoration).leafMomentumToRoot momentum =
                        rootMomentum})
                (fun _decoration => inferInstance)
                (binarySignDecorationFintype tree.1))
            (binaryInteractionTreeOfOrderFintype r)
        calc
          (∑ history : FixedRootRawHistoryIndex N r rootMomentum,
              binaryTreeTimeSimplexWeight history.1.1 T) =
              @Finset.sum explicitHistory Real
                inferInstance
                (@Finset.univ explicitHistory explicitHistoryFintype)
                (fun history =>
                  binaryTreeTimeSimplexWeight history.1.1 T) := by
            exact @Fintype.sum_equiv
              (FixedRootRawHistoryIndex N r rootMomentum)
              explicitHistory Real
              (fixedRootRawHistoryIndexFintype N r rootMomentum)
              explicitHistoryFintype inferInstance reindex
              (fun history =>
                binaryTreeTimeSimplexWeight history.1.1 T)
              (fun history =>
                binaryTreeTimeSimplexWeight history.1.1 T)
              (fun _history => rfl)
          _ = fixedRootRawHistoryTimeWeight r rootMomentum T := by
            unfold fixedRootRawHistoryTimeWeight
            rw [Fintype.sum_sigma]
            apply Finset.sum_congr rfl
            intro tree _treeMem
            rw [Fintype.sum_sigma]
      _ = (4 ^ r * N ^ r : Nat) * T ^ r :=
        fixedRootRawHistoryTimeWeight_eq
          r rootMomentum T
  calc
    ‖∑ history : FixedRootRawHistoryIndex N r rootMomentum,
        coefficient r history‖ <=
        ∑ history : FixedRootRawHistoryIndex N r rootMomentum,
          ‖coefficient r history‖ := norm_sum_le _ _
    _ <= ∑ history : FixedRootRawHistoryIndex N r rootMomentum,
          A * singleHistoryExactTimeScale N q r *
            binaryTreeTimeSimplexWeight history.1.1 T := by
      apply Finset.sum_le_sum
      intro history _historyMem
      exact hsingle r history
    _ = A * singleHistoryExactTimeScale N q r *
          ((4 ^ r * N ^ r : Nat) * T ^ r) := by
      rw [← htimeWeight, Finset.mul_sum]

/-- Dropping only the positive tree factorial converts the exact weighted
bound to the explicit post-counting ratio `(q*T)^r`. -/
theorem norm_fixedRootRawHistoryOrderSum_le_timeSimplexGeometric
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    {A q T : Real} (hA : 0 <= A) (hq : 0 <= q) (hT : 0 <= T)
    (hsingle : forall r history,
      ‖coefficient r history‖ <=
        A * singleHistoryExactTimeScale N q r *
          binaryTreeTimeSimplexWeight history.1.1 T)
    (r : Nat) :
    ‖fixedRootRawHistoryOrderSum N rootMomentum coefficient r‖ <=
      A * (q * T) ^ r := by
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  calc
    ‖fixedRootRawHistoryOrderSum N rootMomentum coefficient r‖ <=
        A * singleHistoryExactTimeScale N q r *
          fixedRootRawHistoryTimeWeight r rootMomentum T :=
      norm_fixedRootRawHistoryOrderSum_le_exactTimeSimplex
        N rootMomentum coefficient hA hq hT hsingle r
    _ = A * (q * T) ^ r := by
      rw [fixedRootRawHistoryTimeWeight_eq]
      norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      unfold singleHistoryExactTimeScale
      rw [div_pow]
      field_simp [hN]
      rw [mul_pow, mul_pow]
      ring

/-- Exact simplex-weighted histories are summable whenever `q*T < 1`; the
tail has the explicit geometric envelope with ratio `q*T`. -/
theorem norm_fixedRootRawHistoryTimeSimplexTail_le
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    {A q T : Real} (hA : 0 <= A) (hq : 0 <= q) (hT : 0 <= T)
    (hcontract : q * T < 1)
    (hsingle : forall r history,
      ‖coefficient r history‖ <=
        A * singleHistoryExactTimeScale N q r *
          binaryTreeTimeSimplexWeight history.1.1 T)
    (R : Nat) :
    ‖fixedRootRawHistoryTail N rootMomentum coefficient R‖ <=
      A * (q * T) ^ R / (1 - q * T) := by
  have hratio0 : 0 <= q * T := mul_nonneg hq hT
  let orderSum : Nat -> Complex := fun r =>
    fixedRootRawHistoryOrderSum N rootMomentum coefficient r
  have hpoint (n : Nat) :
      ‖orderSum (n + R)‖ <= A * (q * T) ^ (n + R) :=
    norm_fixedRootRawHistoryOrderSum_le_timeSimplexGeometric
      N rootMomentum coefficient hA hq hT hsingle (n + R)
  have hgeom : Summable (fun n : Nat => A * (q * T) ^ (n + R)) :=
    summable_shifted_geometric hratio0 hcontract R
  have hnorm : Summable (fun n : Nat => ‖orderSum (n + R)‖) :=
    hgeom.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  unfold fixedRootRawHistoryTail
  change ‖∑' n : Nat, orderSum (n + R)‖ <= _
  calc
    ‖∑' n : Nat, orderSum (n + R)‖ <=
        ∑' n : Nat, ‖orderSum (n + R)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ <= ∑' n : Nat, A * (q * T) ^ (n + R) :=
      hnorm.tsum_le_tsum hpoint hgeom
    _ = A * (q * T) ^ R / (1 - q * T) :=
      tsum_shifted_geometric hratio0 hcontract R

/-- The exact-simplex-weighted tail vanishes with the truncation order in
the same transparent short-time window `q*T < 1`. -/
theorem norm_fixedRootRawHistoryTimeSimplexTail_tendsto_zero
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    {A q T : Real} (hA : 0 <= A) (hq : 0 <= q) (hT : 0 <= T)
    (hcontract : q * T < 1)
    (hsingle : forall r history,
      ‖coefficient r history‖ <=
        A * singleHistoryExactTimeScale N q r *
          binaryTreeTimeSimplexWeight history.1.1 T) :
    Tendsto (fun R : Nat =>
      ‖fixedRootRawHistoryTail N rootMomentum coefficient R‖)
      atTop (nhds 0) := by
  have hratio0 : 0 <= q * T := mul_nonneg hq hT
  apply squeeze_zero'
      (g := fun R : Nat => A * (q * T) ^ R / (1 - q * T))
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · exact Eventually.of_forall fun R =>
      norm_fixedRootRawHistoryTimeSimplexTail_le
        N rootMomentum coefficient hA hq hT hcontract hsingle R
  · exact geometricTailEnvelope_tendsto_zero hratio0 hcontract

/-! ## Equivalent per-vertex analytic-cost formulation -/

theorem singleHistoryCatalanScale_scaledVertexCost
    (N r : Nat) [NeZero N] (rho : Real) :
    singleHistoryCatalanScale N (16 * (N : Real) * rho) r =
      rho ^ r := by
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  unfold singleHistoryCatalanScale
  congr 1
  field_simp [hN]

/-- Exact-time analogue of `singleHistoryCatalanScale_scaledVertexCost`.
The exact tree-factorial sum leaves only four sign choices and one free
momentum per vertex. -/
theorem singleHistoryExactTimeScale_scaledVertexCost
    (N r : Nat) [NeZero N] (rho : Real) :
    singleHistoryExactTimeScale N (4 * (N : Real) * rho) r =
      rho ^ r := by
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  unfold singleHistoryExactTimeScale
  congr 1
  field_simp [hN]

/-- Natural physical reading of the majorant.  If one integrated vertex
costs `rho` apart from its exact simplex weight, the exact tree-factorial
sum leaves the effective ratio `4*N*rho*T`. -/
theorem norm_fixedRootRawHistoryOrderSum_le_of_perVertexTimeSimplexCost
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    {A rho T : Real} (hA : 0 <= A) (hrho : 0 <= rho) (hT : 0 <= T)
    (hsingle : forall r history,
      ‖coefficient r history‖ <=
        A * rho ^ r *
          binaryTreeTimeSimplexWeight history.1.1 T)
    (r : Nat) :
    ‖fixedRootRawHistoryOrderSum N rootMomentum coefficient r‖ <=
      A * (4 * (N : Real) * rho * T) ^ r := by
  let q : Real := 4 * (N : Real) * rho
  have hq : 0 <= q := by
    dsimp [q]
    positivity
  have hsingle' : forall order history,
      ‖coefficient order history‖ <=
        A * singleHistoryExactTimeScale N q order *
          binaryTreeTimeSimplexWeight history.1.1 T := by
    intro order history
    simpa [q, singleHistoryExactTimeScale_scaledVertexCost] using
      hsingle order history
  simpa [q, mul_assoc] using
    norm_fixedRootRawHistoryOrderSum_le_timeSimplexGeometric
      N rootMomentum coefficient hA hq hT hsingle' r

/-- With the same physical per-vertex cost, the all-orders tail is summable
under the explicit short-time/weak-coupling condition
`4*N*rho*T < 1`. -/
theorem norm_fixedRootRawHistoryTail_le_of_perVertexTimeSimplexCost
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    {A rho T : Real} (hA : 0 <= A) (hrho : 0 <= rho) (hT : 0 <= T)
    (hcontract : 4 * (N : Real) * rho * T < 1)
    (hsingle : forall r history,
      ‖coefficient r history‖ <=
        A * rho ^ r *
          binaryTreeTimeSimplexWeight history.1.1 T)
    (R : Nat) :
    ‖fixedRootRawHistoryTail N rootMomentum coefficient R‖ <=
      A * (4 * (N : Real) * rho * T) ^ R /
        (1 - 4 * (N : Real) * rho * T) := by
  let q : Real := 4 * (N : Real) * rho
  have hq : 0 <= q := by
    dsimp [q]
    positivity
  have hsingle' : forall order history,
      ‖coefficient order history‖ <=
        A * singleHistoryExactTimeScale N q order *
          binaryTreeTimeSimplexWeight history.1.1 T := by
    intro order history
    simpa [q, singleHistoryExactTimeScale_scaledVertexCost] using
      hsingle order history
  simpa [q, mul_assoc] using
    norm_fixedRootRawHistoryTimeSimplexTail_le
      N rootMomentum coefficient hA hq hT hcontract hsingle' R

/-! ## Connection to the existing recursive Physlib tree coefficient -/

/-- Uniform deterministic bounds on the three pieces of the existing
recursive `BinaryTreeCoefficientKernel`. -/
structure BinaryTreeCoefficientKernelMajorant {Mode : Type*}
    (kernel : BinaryTreeCoefficientKernel Mode) where
  leafBound : Real
  vertexBound : Real
  edgeBound : Real
  leafBound_nonneg : 0 <= leafBound
  vertexBound_nonneg : 0 <= vertexBound
  edgeBound_nonneg : 0 <= edgeBound
  norm_leafCoefficient_le : forall mode,
    ‖kernel.leafCoefficient mode‖ <= leafBound
  norm_vertexCoefficient_le : forall output left right,
    ‖kernel.vertexCoefficient output left right‖ <= vertexBound
  norm_edgeCoefficient_le : forall isLeaf mode sign value,
    ‖kernel.edgeCoefficient isLeaf mode sign value‖ <=
      edgeBound * ‖value‖

/-- The local vertex together with its two reconstructed child edges costs
at most `vertexBound * edgeBound^2`. -/
def BinaryTreeCoefficientKernelMajorant.branchBound
    {Mode : Type*} {kernel : BinaryTreeCoefficientKernel Mode}
    (bound : BinaryTreeCoefficientKernelMajorant kernel) : Real :=
  bound.vertexBound * bound.edgeBound ^ 2

theorem BinaryTreeCoefficientKernelMajorant.branchBound_nonneg
    {Mode : Type*} {kernel : BinaryTreeCoefficientKernel Mode}
    (bound : BinaryTreeCoefficientKernelMajorant kernel) :
    0 <= bound.branchBound := by
  unfold branchBound
  exact mul_nonneg bound.vertexBound_nonneg
    (sq_nonneg bound.edgeBound)

/-- Actual recursive Physlib coefficient bound at every binary order. -/
theorem BinaryTreeCoefficientKernelMajorant.norm_binaryTreeCoefficient_le
    {Mode : Type*} {kernel : BinaryTreeCoefficientKernel Mode}
    (bound : BinaryTreeCoefficientKernelMajorant kernel)
    (tree : RandomEigenmodeBinaryTree Mode) :
    ‖binaryTreeCoefficient kernel tree‖ <=
      bound.leafBound ^ (tree.shape.order + 1) *
        bound.branchBound ^ tree.shape.order := by
  induction tree with
  | leaf mode =>
      simpa [RandomEigenmodeBinaryTree.shape,
        BinaryInteractionTree.order, branchBound] using
        bound.norm_leafCoefficient_le mode
  | node output leftSign rightSign left right hleft hright =>
      rw [binaryTreeCoefficient_node, norm_mul, norm_mul]
      calc
        ‖kernel.vertexCoefficient output left.rootMode right.rootMode‖ *
              ‖kernel.edgeCoefficient left.isLeaf left.rootMode leftSign
                (binaryTreeCoefficient kernel left)‖ *
              ‖kernel.edgeCoefficient right.isLeaf right.rootMode rightSign
                (binaryTreeCoefficient kernel right)‖ <=
            bound.vertexBound *
              (bound.edgeBound * ‖binaryTreeCoefficient kernel left‖) *
              (bound.edgeBound * ‖binaryTreeCoefficient kernel right‖) := by
          apply mul_le_mul
          · exact mul_le_mul
              (bound.norm_vertexCoefficient_le _ _ _)
              (bound.norm_edgeCoefficient_le _ _ _ _)
              (norm_nonneg _)
              bound.vertexBound_nonneg
          · exact bound.norm_edgeCoefficient_le _ _ _ _
          · exact norm_nonneg _
          · exact mul_nonneg bound.vertexBound_nonneg
              (mul_nonneg bound.edgeBound_nonneg (norm_nonneg _))
        _ <= bound.vertexBound *
              (bound.edgeBound *
                (bound.leafBound ^ (left.shape.order + 1) *
                  bound.branchBound ^ left.shape.order)) *
              (bound.edgeBound *
                (bound.leafBound ^ (right.shape.order + 1) *
                  bound.branchBound ^ right.shape.order)) := by
          have hleftScaled :
              bound.edgeBound * ‖binaryTreeCoefficient kernel left‖ <=
                bound.edgeBound *
                  (bound.leafBound ^ (left.shape.order + 1) *
                    bound.branchBound ^ left.shape.order) :=
            mul_le_mul_of_nonneg_left hleft bound.edgeBound_nonneg
          have hrightScaled :
              bound.edgeBound * ‖binaryTreeCoefficient kernel right‖ <=
                bound.edgeBound *
                  (bound.leafBound ^ (right.shape.order + 1) *
                    bound.branchBound ^ right.shape.order) :=
            mul_le_mul_of_nonneg_left hright bound.edgeBound_nonneg
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hleftScaled
              bound.vertexBound_nonneg
          · exact hrightScaled
          · exact mul_nonneg bound.edgeBound_nonneg (norm_nonneg _)
          · exact mul_nonneg bound.vertexBound_nonneg
              (mul_nonneg bound.edgeBound_nonneg
                (mul_nonneg
                  (pow_nonneg bound.leafBound_nonneg _)
                  (pow_nonneg bound.branchBound_nonneg _)))
        _ = bound.leafBound ^
                ((RandomEigenmodeBinaryTree.shape
                  (.node output leftSign rightSign left right)).order + 1) *
              bound.branchBound ^
                (RandomEigenmodeBinaryTree.shape
                  (.node output leftSign rightSign left right)).order := by
          simp only [RandomEigenmodeBinaryTree.shape,
            BinaryInteractionTree.order, branchBound]
          rw [pow_add, pow_add, pow_succ, pow_succ]
          ring

/-- A directly checkable sufficient condition for the single-history input:
if `leafBound <= A` and the leaf-times-branch factor is at most
`q/(16N)`, then every existing recursive Physlib tree coefficient has the
needed volume-normalized geometric bound. -/
theorem BinaryTreeCoefficientKernelMajorant.norm_binaryTreeCoefficient_le_catalanScale
    {Mode : Type*} {kernel : BinaryTreeCoefficientKernel Mode}
    (bound : BinaryTreeCoefficientKernelMajorant kernel)
    (N : Nat) [NeZero N] {A q : Real}
    (hA : 0 <= A) (hq : 0 <= q)
    (hleafA : bound.leafBound <= A)
    (hbranch : bound.leafBound * bound.branchBound <=
      q / (16 * (N : Real)))
    (tree : RandomEigenmodeBinaryTree Mode) :
    ‖binaryTreeCoefficient kernel tree‖ <=
      A * singleHistoryCatalanScale N q tree.shape.order := by
  have hbranch0 : 0 <= bound.branchBound := bound.branchBound_nonneg
  have hratio0 : 0 <= q / (16 * (N : Real)) := by positivity
  have hleafBranch0 : 0 <= bound.leafBound * bound.branchBound :=
    mul_nonneg bound.leafBound_nonneg hbranch0
  calc
    ‖binaryTreeCoefficient kernel tree‖ <=
        bound.leafBound ^ (tree.shape.order + 1) *
          bound.branchBound ^ tree.shape.order :=
      bound.norm_binaryTreeCoefficient_le tree
    _ = bound.leafBound *
          (bound.leafBound * bound.branchBound) ^ tree.shape.order := by
      rw [pow_succ, mul_pow]
      ring
    _ <= A * (q / (16 * (N : Real))) ^ tree.shape.order := by
      exact mul_le_mul hleafA
        (pow_le_pow_left₀ hleafBranch0 hbranch tree.shape.order)
        (pow_nonneg hleafBranch0 tree.shape.order) hA
    _ = A * singleHistoryCatalanScale N q tree.shape.order := by
      rfl

/-! ## Direct fixed-root adapter for realized Physlib trees -/

/-- Sum the existing recursive Physlib coefficient after realizing every raw
fixed-root momentum history as a decorated random-eigenmode binary tree.
The realization map is deliberately explicit: a future physical adapter must
prove that it preserves perturbative order. -/
def fixedRootRealizedKernelOrderSum
    {Mode : Type*} (kernel : BinaryTreeCoefficientKernel Mode)
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (realize : (r : Nat) ->
      FixedRootRawHistoryIndex N r rootMomentum ->
        RandomEigenmodeBinaryTree Mode)
    (r : Nat) : Complex :=
  fixedRootRawHistoryOrderSum N rootMomentum
    (fun order history =>
      binaryTreeCoefficient kernel (realize order history)) r

/-- Infinite tail of the realized recursive Physlib coefficients. -/
def fixedRootRealizedKernelTail
    {Mode : Type*} (kernel : BinaryTreeCoefficientKernel Mode)
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (realize : (r : Nat) ->
      FixedRootRawHistoryIndex N r rootMomentum ->
        RandomEigenmodeBinaryTree Mode)
    (R : Nat) : Complex :=
  fixedRootRawHistoryTail N rootMomentum
    (fun order history =>
      binaryTreeCoefficient kernel (realize order history)) R

/-- Local kernel smallness plus an order-preserving realization gives the
complete fixed-root order bound `A q^r`. -/
theorem norm_fixedRootRealizedKernelOrderSum_le_geometric
    {Mode : Type*} {kernel : BinaryTreeCoefficientKernel Mode}
    (bound : BinaryTreeCoefficientKernelMajorant kernel)
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (realize : (r : Nat) ->
      FixedRootRawHistoryIndex N r rootMomentum ->
        RandomEigenmodeBinaryTree Mode)
    (horder : forall r history, (realize r history).shape.order = r)
    {A q : Real} (hA : 0 <= A) (hq : 0 <= q)
    (hleafA : bound.leafBound <= A)
    (hbranch : bound.leafBound * bound.branchBound <=
      q / (16 * (N : Real)))
    (r : Nat) :
    ‖fixedRootRealizedKernelOrderSum
        kernel N rootMomentum realize r‖ <= A * q ^ r := by
  unfold fixedRootRealizedKernelOrderSum
  apply norm_fixedRootRawHistoryOrderSum_le_geometric
    N rootMomentum _ hA hq
  intro order history
  have htree := bound.norm_binaryTreeCoefficient_le_catalanScale
    N hA hq hleafA hbranch (realize order history)
  simpa [horder order history] using htree

/-- The realized recursive Physlib tail inherits the explicit geometric
bound. -/
theorem norm_fixedRootRealizedKernelTail_le_geometric
    {Mode : Type*} {kernel : BinaryTreeCoefficientKernel Mode}
    (bound : BinaryTreeCoefficientKernelMajorant kernel)
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (realize : (r : Nat) ->
      FixedRootRawHistoryIndex N r rootMomentum ->
        RandomEigenmodeBinaryTree Mode)
    (horder : forall r history, (realize r history).shape.order = r)
    {A q : Real} (hA : 0 <= A) (hq0 : 0 <= q) (hq1 : q < 1)
    (hleafA : bound.leafBound <= A)
    (hbranch : bound.leafBound * bound.branchBound <=
      q / (16 * (N : Real)))
    (R : Nat) :
    ‖fixedRootRealizedKernelTail
        kernel N rootMomentum realize R‖ <= A * q ^ R / (1 - q) := by
  unfold fixedRootRealizedKernelTail
  apply norm_fixedRootRawHistoryTail_le_geometric
    N rootMomentum _ hA hq0 hq1
  intro order history
  have htree := bound.norm_binaryTreeCoefficient_le_catalanScale
    N hA hq0 hleafA hbranch (realize order history)
  simpa [horder order history] using htree

/-- In particular, the realized recursive Physlib tail vanishes in norm as
the truncation order tends to infinity. -/
theorem norm_fixedRootRealizedKernelTail_tendsto_zero
    {Mode : Type*} {kernel : BinaryTreeCoefficientKernel Mode}
    (bound : BinaryTreeCoefficientKernelMajorant kernel)
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (realize : (r : Nat) ->
      FixedRootRawHistoryIndex N r rootMomentum ->
        RandomEigenmodeBinaryTree Mode)
    (horder : forall r history, (realize r history).shape.order = r)
    {A q : Real} (hA : 0 <= A) (hq0 : 0 <= q) (hq1 : q < 1)
    (hleafA : bound.leafBound <= A)
    (hbranch : bound.leafBound * bound.branchBound <=
      q / (16 * (N : Real))) :
    Tendsto (fun R : Nat =>
      ‖fixedRootRealizedKernelTail
        kernel N rootMomentum realize R‖) atTop (nhds 0) := by
  unfold fixedRootRealizedKernelTail
  apply norm_fixedRootRawHistoryTail_tendsto_zero
    N rootMomentum _ hA hq0 hq1
  intro order history
  have htree := bound.norm_binaryTreeCoefficient_le_catalanScale
    N hA hq0 hleafA hbranch (realize order history)
  simpa [horder order history] using htree

end

end ArchonPhysics.FreeFPUTCatalanPicardTailMajorant
