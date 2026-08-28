import ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell

/-!
# Equal-mass periodic FPUT: trivial `2 ↔ 2` shell counting

For a fixed output mode `k₀`, the two-free-mode parametrization of the
momentum shell has two elementary zero-mismatch lines:

* `k₂ = k₀`, corresponding to `(k₂,k₃) = (k₀,k₁)`;
* `k₂ = k₁`, corresponding to `(k₂,k₃) = (k₁,k₀)`.

Their intersection is the single point `(k₀,k₀)`, so their union has
exactly `2N - 1` points.  We separate this union from its complement and then
reduce any near-resonant count on the complement to a uniform bound on the
fixed-first-coordinate slices.

This is an exact finite-volume counting layer.  The uniform analytic slice
bound itself, and every continuum or kinetic limit, remain separate inputs.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoTrivialShellCounting

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.Lattice

noncomputable section

/-! ## The two trivial pairing lines -/

/-- The direct pairing line `k₂ = k₀` in the two-free-mode plane. -/
def directPairingParameterLine
    {N : Nat} [NeZero N] (k₀ : Site N) : Finset (Site N × Site N) :=
  Finset.univ.image (fun k₁ : Site N ↦ (k₁, k₀))

/-- The exchange pairing line `k₂ = k₁` in the two-free-mode plane. -/
def exchangePairingParameterLine
    (N : Nat) [NeZero N] : Finset (Site N × Site N) :=
  Finset.univ.image (fun k₁ : Site N ↦ (k₁, k₁))

/-- The union of both elementary pairing lines. -/
def trivialPairingParameterLocus
    {N : Nat} [NeZero N] (k₀ : Site N) : Finset (Site N × Site N) :=
  directPairingParameterLine k₀ ∪ exchangePairingParameterLine N

@[simp] theorem mem_directPairingParameterLine_iff
    {N : Nat} [NeZero N] (k₀ : Site N) (free : Site N × Site N) :
    free ∈ directPairingParameterLine k₀ ↔ free.2 = k₀ := by
  simp [directPairingParameterLine, Prod.ext_iff, eq_comm]

@[simp] theorem mem_exchangePairingParameterLine_iff
    {N : Nat} [NeZero N] (free : Site N × Site N) :
    free ∈ exchangePairingParameterLine N ↔ free.2 = free.1 := by
  simp [exchangePairingParameterLine, Prod.ext_iff, eq_comm]

@[simp] theorem mem_trivialPairingParameterLocus_iff
    {N : Nat} [NeZero N] (k₀ : Site N) (free : Site N × Site N) :
    free ∈ trivialPairingParameterLocus k₀ ↔
      free.2 = k₀ ∨ free.2 = free.1 := by
  simp [trivialPairingParameterLocus]

theorem card_directPairingParameterLine
    {N : Nat} [NeZero N] (k₀ : Site N) :
    (directPairingParameterLine k₀).card = N := by
  unfold directPairingParameterLine
  rw [Finset.card_image_of_injective _ (Prod.mk_left_injective k₀)]
  simp

theorem card_exchangePairingParameterLine
    (N : Nat) [NeZero N] :
    (exchangePairingParameterLine N).card = N := by
  unfold exchangePairingParameterLine
  rw [Finset.card_image_of_injective _]
  · simp
  · intro left right hp
    exact congrArg Prod.fst hp

/-- The two pairing lines meet only at `(k₀,k₀)`. -/
theorem direct_inter_exchangePairingParameterLine
    {N : Nat} [NeZero N] (k₀ : Site N) :
    directPairingParameterLine k₀ ∩ exchangePairingParameterLine N =
      {(k₀, k₀)} := by
  ext free
  simp only [Finset.mem_inter, mem_directPairingParameterLine_iff,
    mem_exchangePairingParameterLine_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hsecond, hdiag⟩
    apply Prod.ext
    · exact hdiag.symm.trans hsecond
    · exact hsecond
  · intro hfree
    subst free
    exact ⟨rfl, rfl⟩

/-- Exact finite count of the elementary zero-mismatch locus. -/
theorem card_trivialPairingParameterLocus
    {N : Nat} [NeZero N] (k₀ : Site N) :
    (trivialPairingParameterLocus k₀).card = 2 * N - 1 := by
  have hunion := Finset.card_union_add_card_inter
    (directPairingParameterLine k₀) (exchangePairingParameterLine N)
  rw [direct_inter_exchangePairingParameterLine k₀,
    card_directPairingParameterLine k₀,
    card_exchangePairingParameterLine N] at hunion
  simp only [Finset.card_singleton] at hunion
  change (trivialPairingParameterLocus k₀).card + 1 = N + N at hunion
  omega

/-! ## Zero mismatch and the nontrivial complement -/

/-- Every point on either elementary pairing line has zero reduced mismatch. -/
theorem reducedTwoToTwoMismatch_eq_zero_of_mem_trivialPairingParameterLocus
    {N : Nat} [NeZero N] (k₀ : Site N) (free : Site N × Site N)
    (hfree : free ∈ trivialPairingParameterLocus k₀) :
    reducedTwoToTwoMismatch k₀ free.1 free.2 = 0 := by
  rw [mem_trivialPairingParameterLocus_iff] at hfree
  rcases hfree with hdirect | hexchange
  · rw [hdirect]
    exact reducedTwoToTwoMismatch_pairing_left k₀ free.1
  · rw [hexchange]
    exact reducedTwoToTwoMismatch_pairing_right k₀ free.1

/-- All two-free-mode parameters outside the two elementary pairing lines. -/
def nontrivialPairingParameterLocus
    {N : Nat} [NeZero N] (k₀ : Site N) : Finset (Site N × Site N) :=
  Finset.univ \ trivialPairingParameterLocus k₀

@[simp] theorem mem_nontrivialPairingParameterLocus_iff
    {N : Nat} [NeZero N] (k₀ : Site N) (free : Site N × Site N) :
    free ∈ nontrivialPairingParameterLocus k₀ ↔
      free.2 ≠ k₀ ∧ free.2 ≠ free.1 := by
  simp [nontrivialPairingParameterLocus, not_or]

theorem trivial_union_nontrivialPairingParameterLocus
    {N : Nat} [NeZero N] (k₀ : Site N) :
    trivialPairingParameterLocus k₀ ∪
        nontrivialPairingParameterLocus k₀ = Finset.univ := by
  unfold nontrivialPairingParameterLocus
  exact Finset.union_sdiff_of_subset (Finset.subset_univ _)

theorem trivial_disjoint_nontrivialPairingParameterLocus
    {N : Nat} [NeZero N] (k₀ : Site N) :
    Disjoint (trivialPairingParameterLocus k₀)
      (nontrivialPairingParameterLocus k₀) := by
  unfold nontrivialPairingParameterLocus
  exact Finset.disjoint_sdiff

/-- The exact partition cardinality: trivial plus nontrivial parameters fill
the entire `N²` two-free-mode plane. -/
theorem card_nontrivial_add_card_trivialPairingParameterLocus
    {N : Nat} [NeZero N] (k₀ : Site N) :
    (nontrivialPairingParameterLocus k₀).card +
        (trivialPairingParameterLocus k₀).card = N ^ 2 := by
  unfold nontrivialPairingParameterLocus
  rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ
    (trivialPairingParameterLocus k₀))]
  simp [Fintype.card_prod, ZMod.card, pow_two]

/-- Equivalently, the nontrivial complement has the total count minus the
exact `2N-1` elementary locus. -/
theorem card_nontrivialPairingParameterLocus
    {N : Nat} [NeZero N] (k₀ : Site N) :
    (nontrivialPairingParameterLocus k₀).card =
      N ^ 2 - (2 * N - 1) := by
  rw [← card_trivialPairingParameterLocus k₀]
  unfold nontrivialPairingParameterLocus
  calc
    (Finset.univ \ trivialPairingParameterLocus k₀).card =
        (Finset.univ : Finset (Site N × Site N)).card -
          (trivialPairingParameterLocus k₀).card :=
      Finset.card_sdiff_of_subset (Finset.subset_univ _)
    _ = N ^ 2 - (trivialPairingParameterLocus k₀).card := by
      simp [Fintype.card_prod, ZMod.card, pow_two]

/-! ## Near-resonant complement and slice reduction -/

/-- Nontrivial two-free-mode parameters whose reduced mismatch lies in the
closed window of width `Δ`. -/
def nearResonantNontrivialPairs
    {N : Nat} [NeZero N] (k₀ : Site N) (Δ : Real) :
    Finset (Site N × Site N) :=
  (nontrivialPairingParameterLocus k₀).filter fun free ↦
    |reducedTwoToTwoMismatch k₀ free.1 free.2| ≤ Δ

/-- The fixed-`k₁` slice of any finite set of two-free-mode parameters. -/
def firstCoordinateSlice
    {N : Nat} [NeZero N] (pairs : Finset (Site N × Site N))
    (k₁ : Site N) : Finset (Site N × Site N) :=
  pairs.filter fun free ↦ free.1 = k₁

/-- Generic finite slice-count reduction.  A bound `B` on every fixed first
coordinate slice gives the global bound `N B`; this is the precise analytic
input needed by the subsequent near-resonance estimate. -/
theorem card_pairs_le_volume_mul_of_firstCoordinateSlice_le
    {N B : Nat} [NeZero N] (pairs : Finset (Site N × Site N))
    (hslice : ∀ k₁ : Site N, (firstCoordinateSlice pairs k₁).card ≤ B) :
    pairs.card ≤ N * B := by
  have hcount := Finset.card_le_mul_card_image_of_maps_to
    (s := pairs) (t := (Finset.univ : Finset (Site N)))
    (f := fun free : Site N × Site N ↦ free.1)
    (by simp) B (by
      intro k₁ _hk₁
      simpa [firstCoordinateSlice] using hslice k₁)
  simpa [ZMod.card, Nat.mul_comm] using hcount

/-- Specialized reduction for the nontrivial `Δ`-near-resonant shell. -/
theorem card_nearResonantNontrivialPairs_le_volume_mul
    {N B : Nat} [NeZero N] (k₀ : Site N) (Δ : Real)
    (hslice : ∀ k₁ : Site N,
      (firstCoordinateSlice (nearResonantNontrivialPairs k₀ Δ) k₁).card ≤ B) :
    (nearResonantNontrivialPairs k₀ Δ).card ≤ N * B :=
  card_pairs_le_volume_mul_of_firstCoordinateSlice_le
    (nearResonantNontrivialPairs k₀ Δ) hslice

end

end ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoTrivialShellCounting
