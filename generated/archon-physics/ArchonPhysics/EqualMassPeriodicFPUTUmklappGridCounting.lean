import ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
import ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoTrivialShellCounting
import ArchonPhysics.EqualMassPeriodicFPUTUmklappTransversality

/-!
# Equal-mass periodic FPUT: conditional Umklapp Fourier-grid counting

The principal Fourier grid has spacing `2π/N`.  This module converts a real
diameter bound into an exact finite-mode count.  It then applies the
conditional Umklapp transversality estimate to each fixed-`k₁` slice and
feeds that bound into the existing `N × slice` counting reduction.

The branch identification, common transverse interval, and derivative lower
bound are explicit inputs.  In particular, this module does not assert that
the hypotheses hold globally or automatically for every finite shell.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTUmklappGridCounting

open Set
open ArchonPhysics
open ArchonPhysics.Lattice
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoTrivialShellCounting
open ArchonPhysics.EqualMassPeriodicFPUTUmklappTransversality

noncomputable section

/-! ## A generic grid-diameter count -/

/-- A finite subset of the principal `2π/N` grid with pairwise real
distance at most `D`, where `D` is no larger than `B` grid spacings, has at
most `B+1` points. -/
theorem card_gridModes_le_add_one_of_pairwise_distance_le
    {N B : Nat} [NeZero N] (modes : Finset (Site N)) {D : Real}
    (hdistance : ∀ k ∈ modes, ∀ l ∈ modes,
      dist (gridWaveNumber N k) (gridWaveNumber N l) ≤ D)
    (hwidth : D ≤ 2 * Real.pi * (B : Real) / (N : Real)) :
    modes.card ≤ B + 1 := by
  by_cases hmodes : modes.Nonempty
  · let values : Finset Nat := modes.image fun k ↦ k.val
    have hvalues : values.Nonempty := hmodes.image _
    let lo : Nat := values.min' hvalues
    let hi : Nat := values.max' hvalues
    have hloMem : lo ∈ values := values.min'_mem hvalues
    have hhiMem : hi ∈ values := values.max'_mem hvalues
    obtain ⟨klo, hklo, hkloVal⟩ := Finset.mem_image.mp hloMem
    obtain ⟨khi, hkhi, hkhiVal⟩ := Finset.mem_image.mp hhiMem
    have hlohi : lo ≤ hi := values.min'_le _ hhiMem
    have hNpos : (0 : Real) < (N : Real) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hvalCast : (lo : Real) ≤ (hi : Real) := by exact_mod_cast hlohi
    have hgridOrder : gridWaveNumber N klo ≤ gridWaveNumber N khi := by
      unfold gridWaveNumber
      rw [hkloVal, hkhiVal]
      apply (div_le_div_iff_of_pos_right hNpos).2
      exact mul_le_mul_of_nonneg_left hvalCast (by positivity)
    have hspan : gridWaveNumber N khi - gridWaveNumber N klo ≤ D := by
      have hp := hdistance klo hklo khi hkhi
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hgridOrder), neg_sub] at hp
      exact hp
    have hspacing :
        gridWaveNumber N khi - gridWaveNumber N klo =
          2 * Real.pi * ((hi - lo : Nat) : Real) / (N : Real) := by
      unfold gridWaveNumber
      rw [hkhiVal, hkloVal, Nat.cast_sub hlohi]
      ring
    rw [hspacing] at hspan
    have hquotient :
        2 * Real.pi * ((hi - lo : Nat) : Real) / (N : Real) ≤
          2 * Real.pi * (B : Real) / (N : Real) :=
      hspan.trans hwidth
    have hscaled :
        2 * Real.pi * ((hi - lo : Nat) : Real) ≤
          2 * Real.pi * (B : Real) :=
      (div_le_div_iff_of_pos_right hNpos).mp hquotient
    have hcastSpan : ((hi - lo : Nat) : Real) ≤ (B : Real) :=
      (mul_le_mul_iff_of_pos_left
        (by positivity : (0 : Real) < 2 * Real.pi)).mp hscaled
    have hnatSpan : hi - lo ≤ B := by exact_mod_cast hcastSpan
    have hvaluesSubset : values ⊆ Finset.Icc lo hi := by
      intro value hvalue
      exact Finset.mem_Icc.mpr
        ⟨values.min'_le value hvalue, values.le_max' value hvalue⟩
    have hcardValues : values.card ≤ hi + 1 - lo := by
      simpa only [Nat.card_Icc] using Finset.card_le_card hvaluesSubset
    have hcardImage : values.card = modes.card := by
      unfold values
      exact Finset.card_image_of_injective _ (ZMod.val_injective N)
    rw [← hcardImage]
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hmodes]
    simp

/-- Interval form of the grid count: if every sampled wave number lies in
`[a,a+D]` and `D` is at most `B` spacings, there are at most `B+1` modes. -/
theorem card_gridModes_le_add_one_of_mem_interval
    {N B : Nat} [NeZero N] (modes : Finset (Site N))
    {a D : Real}
    (hinterval : ∀ k ∈ modes, gridWaveNumber N k ∈ Icc a (a + D))
    (hwidth : D ≤ 2 * Real.pi * (B : Real) / (N : Real)) :
    modes.card ≤ B + 1 := by
  apply card_gridModes_le_add_one_of_pairwise_distance_le (D := D) modes
  · intro k hk l hl
    have hkIcc := hinterval k hk
    have hlIcc := hinterval l hl
    have hkLower : a ≤ gridWaveNumber N k := hkIcc.1
    have hkUpper : gridWaveNumber N k ≤ a + D := hkIcc.2
    have hlLower : a ≤ gridWaveNumber N l := hlIcc.1
    have hlUpper : gridWaveNumber N l ≤ a + D := hlIcc.2
    rw [Real.dist_eq]
    refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;> linarith
  · exact hwidth

/-! ## Fixed-first-coordinate second-mode slices -/

/-- The actual `k₂` modes occurring in the fixed-`k₁` slice of a pair
set. -/
def secondCoordinateSlice
    {N : Nat} [NeZero N] (pairs : Finset (Site N × Site N))
    (k₁ : Site N) : Finset (Site N) :=
  Finset.univ.filter fun k₂ ↦ (k₁, k₂) ∈ pairs

@[simp] theorem mem_secondCoordinateSlice_iff
    {N : Nat} [NeZero N] (pairs : Finset (Site N × Site N))
    (k₁ k₂ : Site N) :
    k₂ ∈ secondCoordinateSlice pairs k₁ ↔ (k₁, k₂) ∈ pairs := by
  simp [secondCoordinateSlice]

theorem firstCoordinateSlice_eq_image_secondCoordinateSlice
    {N : Nat} [NeZero N] (pairs : Finset (Site N × Site N))
    (k₁ : Site N) :
    firstCoordinateSlice pairs k₁ =
      (secondCoordinateSlice pairs k₁).image (fun k₂ ↦ (k₁, k₂)) := by
  ext free
  simp only [firstCoordinateSlice, Finset.mem_filter, Finset.mem_image,
    mem_secondCoordinateSlice_iff]
  constructor
  · rintro ⟨hfree, hfirst⟩
    refine ⟨free.2, ?_, ?_⟩
    · rw [← hfirst]
      simpa using hfree
    · apply Prod.ext
      · exact hfirst.symm
      · rfl
  · rintro ⟨k₂, hpair, rfl⟩
    exact ⟨hpair, rfl⟩

theorem card_firstCoordinateSlice_eq_secondCoordinateSlice
    {N : Nat} [NeZero N] (pairs : Finset (Site N × Site N))
    (k₁ : Site N) :
    (firstCoordinateSlice pairs k₁).card =
      (secondCoordinateSlice pairs k₁).card := by
  rw [firstCoordinateSlice_eq_image_secondCoordinateSlice]
  exact Finset.card_image_of_injective _ (Prod.mk_right_injective k₁)

/-! ## Conditional Umklapp slice and total counts -/

/-- On one fixed-`k₁` slice, an explicit common Umklapp branch and
fixed-sign transverse interval turn the continuum diameter bound into a
finite Fourier-mode count. -/
theorem card_nearResonantNontrivial_secondCoordinateSlice_le
    {N B : Nat} [NeZero N] {k₀ k₁ : Site N}
    {a b γ Δ : Real}
    (hγ : 0 < γ) (hΔ : 0 ≤ Δ)
    (htransverse : UmklappK₂FixedSignTransverseOn
      (gridWaveNumber N k₀) (gridWaveNumber N k₁) a b γ)
    (hinterval : ∀ k₂ ∈ secondCoordinateSlice
        (nearResonantNontrivialPairs k₀ Δ) k₁,
      gridWaveNumber N k₂ ∈ Icc a b)
    (humklapp : ∀ k₂ ∈ secondCoordinateSlice
        (nearResonantNontrivialPairs k₀ Δ) k₁,
      reducedTwoToTwoMismatch k₀ k₁ k₂ =
        umklappReducedFourWaveMismatch
          (gridWaveNumber N k₀) (gridWaveNumber N k₁)
            (gridWaveNumber N k₂))
    (hwidth : 2 * Δ / γ ≤
      2 * Real.pi * (B : Real) / (N : Real)) :
    (secondCoordinateSlice
      (nearResonantNontrivialPairs k₀ Δ) k₁).card ≤ B + 1 := by
  apply card_gridModes_le_add_one_of_pairwise_distance_le _
  · intro k₂ hk₂ l₂ hl₂
    apply umklapp_nearResonant_pair_distance_le hγ hΔ htransverse
      (hinterval k₂ hk₂) (hinterval l₂ hl₂)
    · have hkpair : (k₁, k₂) ∈ nearResonantNontrivialPairs k₀ Δ :=
        (mem_secondCoordinateSlice_iff _ _ _).mp hk₂
      have hknear := (Finset.mem_filter.mp hkpair).2
      rw [humklapp k₂ hk₂] at hknear
      exact hknear
    · have hlpair : (k₁, l₂) ∈ nearResonantNontrivialPairs k₀ Δ :=
        (mem_secondCoordinateSlice_iff _ _ _).mp hl₂
      have hlnear := (Finset.mem_filter.mp hlpair).2
      rw [humklapp l₂ hl₂] at hlnear
      exact hlnear
  · exact hwidth

/-- Total conditional count after applying the fixed-first-coordinate slice
reduction.  The hypotheses explicitly certify a common transverse Umklapp
description for every nontrivial near-resonant slice. -/
theorem card_nearResonantNontrivialPairs_le_volume_mul_add_one
    {N B : Nat} [NeZero N] (k₀ : Site N)
    {a b : Site N → Real} {γ Δ : Real}
    (hγ : 0 < γ) (hΔ : 0 ≤ Δ)
    (htransverse : ∀ k₁ : Site N,
      UmklappK₂FixedSignTransverseOn
        (gridWaveNumber N k₀) (gridWaveNumber N k₁)
          (a k₁) (b k₁) γ)
    (hinterval : ∀ (k₁ : Site N) k₂,
      k₂ ∈ secondCoordinateSlice
          (nearResonantNontrivialPairs k₀ Δ) k₁ →
        gridWaveNumber N k₂ ∈ Icc (a k₁) (b k₁))
    (humklapp : ∀ (k₁ : Site N) k₂,
      k₂ ∈ secondCoordinateSlice
          (nearResonantNontrivialPairs k₀ Δ) k₁ →
        reducedTwoToTwoMismatch k₀ k₁ k₂ =
          umklappReducedFourWaveMismatch
            (gridWaveNumber N k₀) (gridWaveNumber N k₁)
              (gridWaveNumber N k₂))
    (hwidth : 2 * Δ / γ ≤
      2 * Real.pi * (B : Real) / (N : Real)) :
    (nearResonantNontrivialPairs k₀ Δ).card ≤ N * (B + 1) := by
  apply card_nearResonantNontrivialPairs_le_volume_mul k₀ Δ
  intro k₁
  rw [card_firstCoordinateSlice_eq_secondCoordinateSlice]
  exact card_nearResonantNontrivial_secondCoordinateSlice_le
    hγ hΔ (htransverse k₁) (hinterval k₁) (humklapp k₁) hwidth

end

end ArchonPhysics.EqualMassPeriodicFPUTUmklappGridCounting
