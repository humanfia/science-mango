import ArchonPhysics.FreeFPUTBranchingNonresonantOrderBound

/-!
# Regular/irregular splitting of fixed-root branching FPUT histories

This module partitions every finite fixed-root raw-history family according
to the already proved cumulative-gap predicate
`FullyNonresonantBranchingHistory gamma`.  The partition is an actual
`Finset.filter` partition, so the complete order sum is exactly the sum of
its regular and irregular parts.

The regular part inherits the deterministic branching oscillatory bounds.
The irregular part is deliberately left as an explicit finite sum.  Thus no
small-denominator, recollision, or probabilistic estimate is hidden in the
split: those missing estimates are isolated in one named term.  A final
cardinality interface records exactly what a future counting or probability
argument would have to supply.
-/

namespace ArchonPhysics.FreeFPUTBranchingRegularIrregularSplit

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.FreeFPUTCatalanPicardTailMajorant
open ArchonPhysics.FreeFPUTBranchingOscillatoryShuffle
open ArchonPhysics.FreeFPUTBranchingNonresonantOrderBound
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open Filter Topology

noncomputable section

/-! ## Exact finite partition -/

/-- Fixed-root histories whose every tree-order linear extension has all
cumulative phase gaps at least `gamma`. -/
def fixedRootRegularBranchingHistories
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (gamma : Real) (r : Nat) :
    Finset (FixedRootRawHistoryIndex N r rootMomentum) := by
  classical
  exact Finset.univ.filter fun history =>
    FullyNonresonantBranchingHistory gamma history.1.1
      (phaseAssignment r history)

/-- The complementary fixed-root family.  This is the precise locus of a
small cumulative denominator in at least one linear extension. -/
def fixedRootIrregularBranchingHistories
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (gamma : Real) (r : Nat) :
    Finset (FixedRootRawHistoryIndex N r rootMomentum) := by
  classical
  exact Finset.univ.filter fun history =>
    ¬ FullyNonresonantBranchingHistory gamma history.1.1
      (phaseAssignment r history)

@[simp] theorem mem_fixedRootRegularBranchingHistories
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (gamma : Real) (r : Nat)
    (history : FixedRootRawHistoryIndex N r rootMomentum) :
    history ∈ fixedRootRegularBranchingHistories
        N rootMomentum phaseAssignment gamma r ↔
      FullyNonresonantBranchingHistory gamma history.1.1
        (phaseAssignment r history) := by
  classical
  simp [fixedRootRegularBranchingHistories]

@[simp] theorem mem_fixedRootIrregularBranchingHistories
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (gamma : Real) (r : Nat)
    (history : FixedRootRawHistoryIndex N r rootMomentum) :
    history ∈ fixedRootIrregularBranchingHistories
        N rootMomentum phaseAssignment gamma r ↔
      ¬ FullyNonresonantBranchingHistory gamma history.1.1
        (phaseAssignment r history) := by
  classical
  simp [fixedRootIrregularBranchingHistories]

/-- The regular and irregular cardinalities add to the exact raw-history
cardinality.  This is the bookkeeping bridge for future bad-history counts. -/
theorem card_fixedRootRegular_add_card_fixedRootIrregular
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (gamma : Real) (r : Nat) :
    (fixedRootRegularBranchingHistories
        N rootMomentum phaseAssignment gamma r).card +
      (fixedRootIrregularBranchingHistories
        N rootMomentum phaseAssignment gamma r).card =
      Fintype.card (FixedRootRawHistoryIndex N r rootMomentum) := by
  classical
  unfold fixedRootRegularBranchingHistories
    fixedRootIrregularBranchingHistories
  exact Finset.card_filter_add_card_filter_not _

/-- Regular contribution at one perturbative order. -/
def fixedRootRegularBranchingOrderSum
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (gamma : Real)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (r : Nat) : Complex :=
  ∑ history ∈ fixedRootRegularBranchingHistories
      N rootMomentum phaseAssignment gamma r,
    coefficient r history

/-- Irregular contribution at one perturbative order. -/
def fixedRootIrregularBranchingOrderSum
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (gamma : Real)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (r : Nat) : Complex :=
  ∑ history ∈ fixedRootIrregularBranchingHistories
      N rootMomentum phaseAssignment gamma r,
    coefficient r history

/-- Exact regular/irregular decomposition of the complete fixed-root order
sum. -/
theorem fixedRootRawHistoryOrderSum_eq_regular_add_irregular
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (gamma : Real)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (r : Nat) :
    fixedRootRawHistoryOrderSum N rootMomentum coefficient r =
      fixedRootRegularBranchingOrderSum
          N rootMomentum phaseAssignment gamma coefficient r +
        fixedRootIrregularBranchingOrderSum
          N rootMomentum phaseAssignment gamma coefficient r := by
  classical
  unfold fixedRootRawHistoryOrderSum
    fixedRootRegularBranchingOrderSum
    fixedRootIrregularBranchingOrderSum
    fixedRootRegularBranchingHistories
    fixedRootIrregularBranchingHistories
  exact (Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (FixedRootRawHistoryIndex N r rootMomentum))
    (fun history => FullyNonresonantBranchingHistory gamma history.1.1
      (phaseAssignment r history))
    (fun history => coefficient r history)).symm

/-! ## Deterministic control of the regular part -/

/-- A single regular branching coefficient inherits the factorial
shape-uniform bound. -/
theorem norm_fixedRootBranchingCoefficient_le_factorial_of_regular
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (amplitude :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    {A rho gamma : Real} (hA : 0 <= A) (hrho : 0 <= rho)
    (hgamma : 0 < gamma)
    (hamplitude : forall r history,
      ‖amplitude r history‖ <= A * rho ^ r)
    (time : Real) (r : Nat)
    (history : FixedRootRawHistoryIndex N r rootMomentum)
    (hregular : FullyNonresonantBranchingHistory gamma history.1.1
      (phaseAssignment r history)) :
    ‖fixedRootBranchingOscillatoryHistoryCoefficient
        N rootMomentum amplitude phaseAssignment time r history‖ <=
      A * rho ^ r * (r.factorial : Real) * (2 / gamma) ^ r := by
  have hbranch :=
    norm_branchingOscillatoryDuhamelIntegral_le_factorial_order
      hgamma history.1.1 (phaseAssignment r history) hregular time
  rw [history.1.2] at hbranch
  unfold fixedRootBranchingOscillatoryHistoryCoefficient
  rw [norm_mul]
  calc
    ‖amplitude r history‖ *
        ‖branchingOscillatoryDuhamelIntegral history.1.1
          (phaseAssignment r history) time‖ <=
      (A * rho ^ r) *
        ((r.factorial : Real) * (2 / gamma) ^ r) := by
      exact mul_le_mul (hamplitude r history) hbranch
        (norm_nonneg _)
        (mul_nonneg hA (pow_nonneg hrho r))
    _ = A * rho ^ r * (r.factorial : Real) * (2 / gamma) ^ r := by
      ring

/-- At one order, the entire regular sum is controlled by its exact regular
cardinality times the deterministic factorial history bound. -/
theorem norm_fixedRootRegularBranchingOrderSum_le_factorial
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (amplitude :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    {A rho gamma : Real} (hA : 0 <= A) (hrho : 0 <= rho)
    (hgamma : 0 < gamma)
    (hamplitude : forall r history,
      ‖amplitude r history‖ <= A * rho ^ r)
    (time : Real) (r : Nat) :
    ‖fixedRootRegularBranchingOrderSum N rootMomentum phaseAssignment gamma
        (fixedRootBranchingOscillatoryHistoryCoefficient
          N rootMomentum amplitude phaseAssignment time) r‖ <=
      ((fixedRootRegularBranchingHistories
          N rootMomentum phaseAssignment gamma r).card : Real) *
        (A * rho ^ r * (r.factorial : Real) * (2 / gamma) ^ r) := by
  classical
  unfold fixedRootRegularBranchingOrderSum
  calc
    ‖∑ history ∈ fixedRootRegularBranchingHistories
          N rootMomentum phaseAssignment gamma r,
        fixedRootBranchingOscillatoryHistoryCoefficient
          N rootMomentum amplitude phaseAssignment time r history‖ <=
      ∑ history ∈ fixedRootRegularBranchingHistories
          N rootMomentum phaseAssignment gamma r,
        ‖fixedRootBranchingOscillatoryHistoryCoefficient
          N rootMomentum amplitude phaseAssignment time r history‖ :=
      norm_sum_le _ _
    _ <= ∑ _history ∈ fixedRootRegularBranchingHistories
          N rootMomentum phaseAssignment gamma r,
        A * rho ^ r * (r.factorial : Real) * (2 / gamma) ^ r := by
      apply Finset.sum_le_sum
      intro history hhistory
      exact norm_fixedRootBranchingCoefficient_le_factorial_of_regular
        N rootMomentum amplitude phaseAssignment hA hrho hgamma
          hamplitude time r history
          ((mem_fixedRootRegularBranchingHistories
            N rootMomentum phaseAssignment gamma r history).mp hhistory)
    _ = ((fixedRootRegularBranchingHistories
            N rootMomentum phaseAssignment gamma r).card : Real) *
          (A * rho ^ r * (r.factorial : Real) * (2 / gamma) ^ r) := by
      simp

/-- Exact-extension-weighted amplitudes recover the geometric bound for one
regular history without requiring all histories to be regular. -/
theorem norm_fixedRootBranchingCoefficient_le_geometric_of_regular
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (amplitude :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    {A rho gamma : Real} (_hA : 0 <= A) (_hrho : 0 <= rho)
    (hgamma : 0 < gamma)
    (hamplitudeWeighted : forall r history,
      ‖amplitude r history‖ *
          ((branchingPhaseLinearExtensions history.1.1
            (phaseAssignment r history)).length : Real) <=
        A * rho ^ r)
    (time : Real) (r : Nat)
    (history : FixedRootRawHistoryIndex N r rootMomentum)
    (hregular : FullyNonresonantBranchingHistory gamma history.1.1
      (phaseAssignment r history)) :
    ‖fixedRootBranchingOscillatoryHistoryCoefficient
        N rootMomentum amplitude phaseAssignment time r history‖ <=
      A * (2 * rho / gamma) ^ r := by
  have hbranch :=
    norm_branchingOscillatoryDuhamelIntegral_le_linearExtensionCard
      hgamma history.1.1 (phaseAssignment r history) hregular time
  rw [history.1.2] at hbranch
  unfold fixedRootBranchingOscillatoryHistoryCoefficient
  rw [norm_mul]
  calc
    ‖amplitude r history‖ *
        ‖branchingOscillatoryDuhamelIntegral history.1.1
          (phaseAssignment r history) time‖ <=
      ‖amplitude r history‖ *
        (((branchingPhaseLinearExtensions history.1.1
          (phaseAssignment r history)).length : Real) *
            (2 / gamma) ^ r) :=
      mul_le_mul_of_nonneg_left hbranch (norm_nonneg _)
    _ = (‖amplitude r history‖ *
          ((branchingPhaseLinearExtensions history.1.1
            (phaseAssignment r history)).length : Real)) *
        (2 / gamma) ^ r := by ring
    _ <= (A * rho ^ r) * (2 / gamma) ^ r :=
      mul_le_mul_of_nonneg_right (hamplitudeWeighted r history)
        (pow_nonneg (by positivity) r)
    _ = A * (2 * rho / gamma) ^ r := by
      rw [show 2 * rho / gamma = rho * (2 / gamma) by ring, mul_pow]
      ring

/-! ## Geometric regular tail and the explicit irregular blocker -/

/-- Infinite tail of only the regular histories. -/
def fixedRootRegularBranchingTail
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (gamma : Real)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (R : Nat) : Complex :=
  ∑' n : Nat, fixedRootRegularBranchingOrderSum
    N rootMomentum phaseAssignment gamma coefficient (n + R)

/-- A regular fixed-root tail is geometric under the same transparent
extension-weighted amplitude scale as the all-regular theorem. -/
theorem fixedRootRegularBranching_tail_certificate
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (amplitude :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    {A rho gamma q : Real} (hA : 0 <= A) (hrho : 0 <= rho)
    (hgamma : 0 < gamma) (hq0 : 0 <= q) (hq1 : q < 1)
    (hratio : 2 * rho / gamma <= q / (16 * (N : Real)))
    (hamplitudeWeighted : forall r history,
      ‖amplitude r history‖ *
          ((branchingPhaseLinearExtensions history.1.1
            (phaseAssignment r history)).length : Real) <=
        A * rho ^ r)
    (time : Real) :
    (forall r,
      ‖fixedRootRegularBranchingOrderSum N rootMomentum phaseAssignment gamma
          (fixedRootBranchingOscillatoryHistoryCoefficient
            N rootMomentum amplitude phaseAssignment time) r‖ <=
        A * q ^ r) ∧
    (forall R,
      ‖fixedRootRegularBranchingTail N rootMomentum phaseAssignment gamma
          (fixedRootBranchingOscillatoryHistoryCoefficient
            N rootMomentum amplitude phaseAssignment time) R‖ <=
        A * q ^ R / (1 - q)) ∧
    Tendsto (fun R : Nat =>
      ‖fixedRootRegularBranchingTail N rootMomentum phaseAssignment gamma
          (fixedRootBranchingOscillatoryHistoryCoefficient
            N rootMomentum amplitude phaseAssignment time) R‖)
      atTop (nhds 0) := by
  classical
  let coefficient := fixedRootBranchingOscillatoryHistoryCoefficient
    N rootMomentum amplitude phaseAssignment time
  let regularCoefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex :=
    fun r history =>
      if FullyNonresonantBranchingHistory gamma history.1.1
          (phaseAssignment r history) then
        coefficient r history
      else 0
  have hsingle : forall r history,
      ‖regularCoefficient r history‖ <=
        A * singleHistoryCatalanScale N q r := by
    intro r history
    by_cases hregular : FullyNonresonantBranchingHistory gamma history.1.1
        (phaseAssignment r history)
    · rw [show regularCoefficient r history = coefficient r history by
          simp [regularCoefficient, hregular]]
      have hratio0 : 0 <= 2 * rho / gamma := by positivity
      calc
        ‖coefficient r history‖ <= A * (2 * rho / gamma) ^ r :=
          norm_fixedRootBranchingCoefficient_le_geometric_of_regular
            N rootMomentum amplitude phaseAssignment hA hrho hgamma
              hamplitudeWeighted time r history hregular
        _ <= A * (q / (16 * (N : Real))) ^ r := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hratio0 hratio r) hA
        _ = A * singleHistoryCatalanScale N q r := rfl
    · rw [show regularCoefficient r history = 0 by
          simp [regularCoefficient, hregular]]
      simpa using
        (mul_nonneg hA (singleHistoryCatalanScale_nonneg N hq0 r))
  have horderEq : forall r,
      fixedRootRegularBranchingOrderSum N rootMomentum phaseAssignment gamma
          coefficient r =
        fixedRootRawHistoryOrderSum N rootMomentum regularCoefficient r := by
    intro r
    classical
    unfold fixedRootRegularBranchingOrderSum
      fixedRootRegularBranchingHistories
      fixedRootRawHistoryOrderSum
    dsimp only [regularCoefficient]
    rw [Finset.sum_filter]
  have horder : forall r,
      ‖fixedRootRegularBranchingOrderSum N rootMomentum phaseAssignment gamma
          coefficient r‖ <= A * q ^ r := by
    intro r
    rw [horderEq r]
    exact norm_fixedRootRawHistoryOrderSum_le_geometric
      N rootMomentum regularCoefficient hA hq0 hsingle r
  have htailEq : forall R,
      fixedRootRegularBranchingTail N rootMomentum phaseAssignment gamma
          coefficient R =
        fixedRootRawHistoryTail N rootMomentum regularCoefficient R := by
    intro R
    unfold fixedRootRegularBranchingTail fixedRootRawHistoryTail
    apply tsum_congr
    intro n
    exact horderEq (n + R)
  refine ⟨horder, ?_, ?_⟩
  · intro R
    rw [htailEq R]
    exact norm_fixedRootRawHistoryTail_le_geometric
      N rootMomentum regularCoefficient hA hq0 hq1 hsingle R
  · have hlimit := norm_fixedRootRawHistoryTail_tendsto_zero
        N rootMomentum regularCoefficient hA hq0 hq1 hsingle
    simpa only [← htailEq] using hlimit

/-! ## Finite tails: no summability assumption on irregular histories -/

/-- Finite perturbative tail over orders `[R,S)`. -/
def fixedRootBranchingFiniteTail
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (R S : Nat) : Complex :=
  ∑ r ∈ Finset.Ico R S,
    fixedRootRawHistoryOrderSum N rootMomentum coefficient r

/-- Finite regular tail over orders `[R,S)`. -/
def fixedRootRegularBranchingFiniteTail
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (gamma : Real)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (R S : Nat) : Complex :=
  ∑ r ∈ Finset.Ico R S,
    fixedRootRegularBranchingOrderSum
      N rootMomentum phaseAssignment gamma coefficient r

/-- Finite irregular tail over orders `[R,S)`. -/
def fixedRootIrregularBranchingFiniteTail
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (gamma : Real)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (R S : Nat) : Complex :=
  ∑ r ∈ Finset.Ico R S,
    fixedRootIrregularBranchingOrderSum
      N rootMomentum phaseAssignment gamma coefficient r

/-- Exact finite-tail partition. -/
theorem fixedRootBranchingFiniteTail_eq_regular_add_irregular
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (gamma : Real)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (R S : Nat) :
    fixedRootBranchingFiniteTail N rootMomentum coefficient R S =
      fixedRootRegularBranchingFiniteTail
          N rootMomentum phaseAssignment gamma coefficient R S +
        fixedRootIrregularBranchingFiniteTail
          N rootMomentum phaseAssignment gamma coefficient R S := by
  classical
  unfold fixedRootBranchingFiniteTail
    fixedRootRegularBranchingFiniteTail
    fixedRootIrregularBranchingFiniteTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  exact fixedRootRawHistoryOrderSum_eq_regular_add_irregular
    N rootMomentum phaseAssignment gamma coefficient r

/-- If the regular order bounds are geometric, every finite tail is bounded
by one explicit irregular sum plus the infinite regular envelope. -/
theorem norm_fixedRootBranchingFiniteTail_le_irregular_add_geometric
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (gamma : Real)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    {A q : Real} (hA : 0 <= A) (hq0 : 0 <= q) (hq1 : q < 1)
    (hregular : forall r,
      ‖fixedRootRegularBranchingOrderSum
          N rootMomentum phaseAssignment gamma coefficient r‖ <=
        A * q ^ r)
    (R S : Nat) :
    ‖fixedRootBranchingFiniteTail N rootMomentum coefficient R S‖ <=
      ‖fixedRootIrregularBranchingFiniteTail
          N rootMomentum phaseAssignment gamma coefficient R S‖ +
        A * q ^ R / (1 - q) := by
  rw [fixedRootBranchingFiniteTail_eq_regular_add_irregular]
  calc
    ‖fixedRootRegularBranchingFiniteTail
          N rootMomentum phaseAssignment gamma coefficient R S +
        fixedRootIrregularBranchingFiniteTail
          N rootMomentum phaseAssignment gamma coefficient R S‖ <=
      ‖fixedRootIrregularBranchingFiniteTail
          N rootMomentum phaseAssignment gamma coefficient R S‖ +
        ‖fixedRootRegularBranchingFiniteTail
          N rootMomentum phaseAssignment gamma coefficient R S‖ := by
      simpa [add_comm] using norm_add_le
        (fixedRootRegularBranchingFiniteTail
          N rootMomentum phaseAssignment gamma coefficient R S)
        (fixedRootIrregularBranchingFiniteTail
          N rootMomentum phaseAssignment gamma coefficient R S)
    _ <= ‖fixedRootIrregularBranchingFiniteTail
          N rootMomentum phaseAssignment gamma coefficient R S‖ +
        ∑ r ∈ Finset.Ico R S, A * q ^ r := by
      apply add_le_add_right
      unfold fixedRootRegularBranchingFiniteTail
      calc
        ‖∑ r ∈ Finset.Ico R S,
            fixedRootRegularBranchingOrderSum
              N rootMomentum phaseAssignment gamma coefficient r‖ <=
          ∑ r ∈ Finset.Ico R S,
            ‖fixedRootRegularBranchingOrderSum
              N rootMomentum phaseAssignment gamma coefficient r‖ :=
            norm_sum_le _ _
        _ <= ∑ r ∈ Finset.Ico R S, A * q ^ r := by
          exact Finset.sum_le_sum fun r _hr => hregular r
    _ <= ‖fixedRootIrregularBranchingFiniteTail
          N rootMomentum phaseAssignment gamma coefficient R S‖ +
        A * q ^ R / (1 - q) := by
      apply add_le_add_right
      calc
        ∑ r ∈ Finset.Ico R S, A * q ^ r =
            A * ∑ r ∈ Finset.Ico R S, q ^ r := by
          rw [Finset.mul_sum]
        _ <= A * (q ^ R / (1 - q)) := by
          exact mul_le_mul_of_nonneg_left
            (geom_sum_Ico_le_of_lt_one hq0 hq1) hA
        _ = A * q ^ R / (1 - q) := by ring

/-! ## Transparent bad-history cardinality interface -/

/-- A supplied uniform bound on each irregular coefficient converts an
explicit bad-history count into an irregular-sum estimate.  The theorem does
not assert that the count is small. -/
theorem norm_fixedRootIrregularBranchingOrderSum_le_card_mul
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (gamma : Real)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (r : Nat) {B : Real} (_hB : 0 <= B)
    (hcoefficient : forall history,
      history ∈ fixedRootIrregularBranchingHistories
          N rootMomentum phaseAssignment gamma r ->
        ‖coefficient r history‖ <= B) :
    ‖fixedRootIrregularBranchingOrderSum
        N rootMomentum phaseAssignment gamma coefficient r‖ <=
      ((fixedRootIrregularBranchingHistories
          N rootMomentum phaseAssignment gamma r).card : Real) * B := by
  classical
  unfold fixedRootIrregularBranchingOrderSum
  calc
    ‖∑ history ∈ fixedRootIrregularBranchingHistories
          N rootMomentum phaseAssignment gamma r,
        coefficient r history‖ <=
      ∑ history ∈ fixedRootIrregularBranchingHistories
          N rootMomentum phaseAssignment gamma r,
        ‖coefficient r history‖ := norm_sum_le _ _
    _ <= ∑ _history ∈ fixedRootIrregularBranchingHistories
          N rootMomentum phaseAssignment gamma r, B := by
      exact Finset.sum_le_sum fun history hhistory =>
        hcoefficient history hhistory
    _ = ((fixedRootIrregularBranchingHistories
            N rootMomentum phaseAssignment gamma r).card : Real) * B := by
      simp

/-- External counting input `card irregular <= badCount` is consumed without
strengthening it into an unstated probability claim. -/
theorem norm_fixedRootIrregularBranchingOrderSum_le_count_budget
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (gamma : Real)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (r badCount : Nat) {B : Real} (hB : 0 <= B)
    (hbadCount :
      (fixedRootIrregularBranchingHistories
        N rootMomentum phaseAssignment gamma r).card <= badCount)
    (hcoefficient : forall history,
      history ∈ fixedRootIrregularBranchingHistories
          N rootMomentum phaseAssignment gamma r ->
        ‖coefficient r history‖ <= B) :
    ‖fixedRootIrregularBranchingOrderSum
        N rootMomentum phaseAssignment gamma coefficient r‖ <=
      (badCount : Real) * B := by
  calc
    ‖fixedRootIrregularBranchingOrderSum
        N rootMomentum phaseAssignment gamma coefficient r‖ <=
      ((fixedRootIrregularBranchingHistories
          N rootMomentum phaseAssignment gamma r).card : Real) * B :=
      norm_fixedRootIrregularBranchingOrderSum_le_card_mul
        N rootMomentum phaseAssignment gamma coefficient r hB hcoefficient
    _ <= (badCount : Real) * B := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hbadCount) hB

end

end ArchonPhysics.FreeFPUTBranchingRegularIrregularSplit
