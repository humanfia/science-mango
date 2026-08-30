import ArchonPhysics.CanonicalIIDCoerciveParentDistinctChildRepeatedClosure
import ArchonPhysics.FreeFPUTCatalanPicardTailMajorant

/-!
# Catalan bounds for the remaining higher-order FPUT histories

The controlled repeated collision sectors and the parent-distinct
child-repeated sector leave a genuinely higher-order remainder.  This file
does not assume that remainder is small.  It records what follows from the
actual raw-history count and transparent per-history estimates.

At order `r` and fixed output momentum there are exactly

`catalan r * 4^r * N^r`

raw quadratic FPUT histories.  Splitting every such label into regular and
repeated classes gives an order bound by this exact capacity times the sum of
the two displayed pointwise majorants.  Summing finitely many orders gives a
uniform finite Picard-window estimate with no convergence assumption.

If both per-history estimates pay the stronger factor
`(q / (16*N))^r`, the all-orders tail beginning at `R` has the explicit
geometric ceiling `(Aregular + Arepeated) * q^R / (1-q)`.  For a varying
kinetic schedule, convergence is therefore reduced to convergence of this
literal envelope.

Finally, the file proves the sharp obstruction for a bare time-simplex
Duhamel estimate.  If one vertex only gains one coupling factor `C*|g|`, then
at `T = tau/g^2` its post-counting ratio is
`4*N*C*tau/|g|`.  For positive `C,tau` this cannot remain below one as
`g -> 0`, even when `N` is merely at least one.  Thus a kinetic-scale tail
proof needs additional oscillatory/small-denominator gain beyond the raw
time-simplex estimate; increasing the truncation order alone does not repair
the missing contraction.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveHigherRemainderCatalanBound

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveRepeatedHistoryKineticBound
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.FreeFPUTCatalanPicardTailMajorant
open ArchonPhysics.Lattice
open Filter Topology

noncomputable section

/-! ## Finite-order estimates with no summability assumption -/

/-- The finite Picard window containing orders
`R, R+1, ..., R+length-1`. -/
def fixedRootRawHistoryFiniteWindow
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (R length : Nat) : Complex :=
  ∑ n ∈ Finset.range length,
    fixedRootRawHistoryOrderSum N rootMomentum coefficient (n + R)

/-- Exact-capacity bound for one order after every actual raw history label
is classified as repeated or regular.  The two per-history estimates remain
separate hypotheses and no limiting statement is inserted. -/
theorem norm_fixedRootRawHistoryOrderSum_le_exactCapacity_regular_add_repeated
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (repeated :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Prop)
    (regularMajorant repeatedMajorant : Nat -> Real)
    (hregular_nonneg : forall r, 0 <= regularMajorant r)
    (hrepeated_nonneg : forall r, 0 <= repeatedMajorant r)
    (hregular : forall r history, ¬ repeated r history ->
      ‖coefficient r history‖ <= regularMajorant r)
    (hrepeated : forall r history, repeated r history ->
      ‖coefficient r history‖ <= repeatedMajorant r)
    (r : Nat) :
    ‖fixedRootRawHistoryOrderSum N rootMomentum coefficient r‖ <=
      (fixedRootRawHistoryCapacity N r : Real) *
        (regularMajorant r + repeatedMajorant r) := by
  classical
  unfold fixedRootRawHistoryOrderSum
  calc
    ‖∑ history : FixedRootRawHistoryIndex N r rootMomentum,
        coefficient r history‖ <=
        ∑ history : FixedRootRawHistoryIndex N r rootMomentum,
          ‖coefficient r history‖ := norm_sum_le _ _
    _ <= ∑ _history : FixedRootRawHistoryIndex N r rootMomentum,
          (regularMajorant r + repeatedMajorant r) := by
      apply Finset.sum_le_sum
      intro history _hhistory
      by_cases hhistory : repeated r history
      · exact (hrepeated r history hhistory).trans <| by
          linarith [hregular_nonneg r]
      · exact (hregular r history hhistory).trans <| by
          linarith [hrepeated_nonneg r]
    _ = (Fintype.card
          (FixedRootRawHistoryIndex N r rootMomentum) : Real) *
          (regularMajorant r + repeatedMajorant r) := by
      simp
      ring
    _ = (fixedRootRawHistoryCapacity N r : Real) *
          (regularMajorant r + repeatedMajorant r) := by
      rw [card_fixedRootRawHistoryIndex rootMomentum]
      rfl

/-- Finite-order uniform remainder bound.  It is valid for arbitrary
majorants and arbitrary window length; in particular it remains meaningful
when the associated infinite series is not contractive. -/
theorem norm_fixedRootRawHistoryFiniteWindow_le_exactCapacity_sum
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (repeated :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Prop)
    (regularMajorant repeatedMajorant : Nat -> Real)
    (hregular_nonneg : forall r, 0 <= regularMajorant r)
    (hrepeated_nonneg : forall r, 0 <= repeatedMajorant r)
    (hregular : forall r history, ¬ repeated r history ->
      ‖coefficient r history‖ <= regularMajorant r)
    (hrepeated : forall r history, repeated r history ->
      ‖coefficient r history‖ <= repeatedMajorant r)
    (R length : Nat) :
    ‖fixedRootRawHistoryFiniteWindow
        N rootMomentum coefficient R length‖ <=
      ∑ n ∈ Finset.range length,
        (fixedRootRawHistoryCapacity N (n + R) : Real) *
          (regularMajorant (n + R) + repeatedMajorant (n + R)) := by
  classical
  unfold fixedRootRawHistoryFiniteWindow
  calc
    ‖∑ n ∈ Finset.range length,
        fixedRootRawHistoryOrderSum
          N rootMomentum coefficient (n + R)‖ <=
      ∑ n ∈ Finset.range length,
        ‖fixedRootRawHistoryOrderSum
          N rootMomentum coefficient (n + R)‖ := norm_sum_le _ _
    _ <= ∑ n ∈ Finset.range length,
        (fixedRootRawHistoryCapacity N (n + R) : Real) *
          (regularMajorant (n + R) + repeatedMajorant (n + R)) := by
      apply Finset.sum_le_sum
      intro n _hn
      exact
        norm_fixedRootRawHistoryOrderSum_le_exactCapacity_regular_add_repeated
          N rootMomentum coefficient repeated regularMajorant repeatedMajorant
          hregular_nonneg hrepeated_nonneg hregular hrepeated (n + R)

/-! ## Summable tail under a transparent post-counting contraction -/

/-- If regular and repeated histories separately pay the full
`16^r*N^r` combinatorial cost with the same ratio `q`, their union has the
explicit all-orders Catalan tail bound. -/
theorem norm_fixedRootRawHistoryTail_le_of_regular_repeated_catalanScale
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (repeated :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Prop)
    {Aregular Arepeated q : Real}
    (hAregular : 0 <= Aregular) (hArepeated : 0 <= Arepeated)
    (hq0 : 0 <= q) (hq1 : q < 1)
    (hregular : forall r history, ¬ repeated r history ->
      ‖coefficient r history‖ <=
        Aregular * singleHistoryCatalanScale N q r)
    (hrepeated : forall r history, repeated r history ->
      ‖coefficient r history‖ <=
        Arepeated * singleHistoryCatalanScale N q r)
    (R : Nat) :
    ‖fixedRootRawHistoryTail N rootMomentum coefficient R‖ <=
      (Aregular + Arepeated) * q ^ R / (1 - q) := by
  have hscale (r : Nat) : 0 <= singleHistoryCatalanScale N q r :=
    singleHistoryCatalanScale_nonneg N hq0 r
  have hsingle : forall r history,
      ‖coefficient r history‖ <=
        (Aregular + Arepeated) * singleHistoryCatalanScale N q r := by
    intro r history
    by_cases hhistory : repeated r history
    · exact (hrepeated r history hhistory).trans <|
        mul_le_mul_of_nonneg_right (by linarith) (hscale r)
    · exact (hregular r history hhistory).trans <|
        mul_le_mul_of_nonneg_right (by linarith) (hscale r)
  exact norm_fixedRootRawHistoryTail_le_geometric
    N rootMomentum coefficient (add_nonneg hAregular hArepeated)
      hq0 hq1 hsingle R

/-- Minimal schedule-level closure statement: after the finite-history proof
has produced the literal Catalan envelope, its convergence is the only
remaining analytic condition. -/
theorem higherRemainder_tendsto_zero_of_varyingCatalanEnvelope
    (higherRemainder A q : Nat -> Real) (R : Nat -> Nat)
    (hhigher_nonneg : forall n, 0 <= higherRemainder n)
    (hbound : forall n,
      higherRemainder n <= A n * q n ^ R n / (1 - q n))
    (henvelope : Tendsto
      (fun n => A n * q n ^ R n / (1 - q n)) atTop (nhds 0)) :
    Tendsto higherRemainder atTop (nhds 0) := by
  exact squeeze_zero'
    (Eventually.of_forall hhigher_nonneg)
    (Eventually.of_forall hbound) henvelope

/-- A convenient uniform version: a fixed post-counting ratio `q < 1` and a
truncation schedule `R n -> infinity` force the explicit remainder to zero. -/
theorem higherRemainder_tendsto_zero_of_uniformCatalanRatio
    (higherRemainder : Nat -> Real) (R : Nat -> Nat)
    {A q : Real} (hq0 : 0 <= q) (hq1 : q < 1)
    (hR : Tendsto R atTop atTop)
    (hhigher_nonneg : forall n, 0 <= higherRemainder n)
    (hbound : forall n,
      higherRemainder n <= A * q ^ R n / (1 - q)) :
    Tendsto higherRemainder atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall hhigher_nonneg
  · exact Eventually.of_forall hbound
  · exact (geometricTailEnvelope_tendsto_zero
      (A := A) hq0 hq1).comp hR

/-! ## Kinetic-time obstruction for a bare Duhamel vertex estimate -/

/-- Exact kinetic-time form of the post-counting ratio when a single
integrated vertex contributes only `C*|g|` before its time-simplex weight. -/
theorem linearCoupling_kineticCatalanRatio_eq
    (N : Nat) [NeZero N] (C tau g : Real) (hg : g ≠ 0) :
    4 * (N : Real) * (C * |g|) * (tau / g ^ 2) =
      (4 * (N : Real) * C * tau) / |g| := by
  have habs : |g| ≠ 0 := abs_ne_zero.mpr hg
  rw [← sq_abs g]
  field_simp [habs]

/-- Bare kinetic-time contractivity would force the coupling to stay larger
than the positive volume-dependent scale `4*N*C*tau`. -/
theorem linearCoupling_kineticCatalanRatio_lt_one_forces
    (N : Nat) [NeZero N] (C tau g : Real)
    (hg : g ≠ 0)
    (hcontract :
      4 * (N : Real) * (C * |g|) * (tau / g ^ 2) < 1) :
    4 * (N : Real) * C * tau < |g| := by
  rw [linearCoupling_kineticCatalanRatio_eq N C tau g hg] at hcontract
  simpa using (div_lt_iff₀ (abs_pos.mpr hg)).mp hcontract

/-- Sharp obstruction: for positive vertex constant and kinetic time, the
bare time-simplex Catalan ratio cannot be eventually contractive along any
nonzero weak-coupling sequence, even if the volume schedule is only known to
be at least one. -/
theorem not_eventually_linearCoupling_kineticCatalanRatio_lt_one
    (size : Nat -> Nat) (C tau : Real) (hC : 0 < C) (htau : 0 < tau)
    (g : Nat -> Real) (hg0 : forall n, g n ≠ 0)
    (hg : Tendsto g atTop (nhds 0)) :
    ¬ ∀ᶠ n in atTop,
      4 * ((size n + 1 : Nat) : Real) * (C * |g n|) *
          (tau / (g n) ^ 2) < 1 := by
  intro heventual
  have hscale : 0 < 4 * C * tau := by positivity
  have hsmall : ∀ᶠ n in atTop, |g n| < 4 * C * tau :=
    ((tendsto_order.1 hg.abs).2 _ (by simpa using hscale))
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 heventual
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 hsmall
  let n := max n₁ n₂
  have hcontract := hn₁ n (le_max_left n₁ n₂)
  have hsmalln := hn₂ n (le_max_right n₁ n₂)
  let N := size n + 1
  have hN : (1 : Real) <= (N : Real) := by
    dsimp [N]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (size n))
  have hforced : 4 * (N : Real) * C * tau < |g n| :=
    linearCoupling_kineticCatalanRatio_lt_one_forces
      N C tau (g n) (hg0 n) hcontract
  have hbase : 4 * C * tau <= 4 * (N : Real) * C * tau := by
    nlinarith
  linarith

end

end ArchonPhysics.CanonicalIIDCoerciveHigherRemainderCatalanBound
