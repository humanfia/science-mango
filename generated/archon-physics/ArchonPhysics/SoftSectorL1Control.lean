import ArchonPhysics.EquipartitionEntropy

/-!
# Finite `l1` control of a soft modal sector

For the normalized all-mode observable, a small set of acoustically soft modes
does not require uniform modewise relaxation.  Its contribution to the `l1`
distance is controlled by its actual energy mass and its uniform modal mass.
This is the deterministic finite-volume inequality behind an edge/bulk split.

No decay, collision-frequency, or thermodynamic-limit statement is asserted.
-/

namespace ArchonPhysics.SoftSectorL1Control

open ArchonPhysics.EquipartitionEntropy

noncomputable section

/-- Total weight carried by a selected finite modal sector. -/
def sectorWeight {ι : Type} (sector : Finset ι) (w : ι → Real) : Real :=
  ∑ i ∈ sector, w i

/-- The selected sector's contribution to a finite `l1` distance. -/
def sectorL1Contribution {ι : Type} (sector : Finset ι)
    (w u : ι → Real) : Real :=
  ∑ i ∈ sector, |w i - u i|

/-- The discrepancy of total mass in a sector is bounded by its `l1`
contribution. -/
theorem abs_sectorWeight_sub_le_sectorL1Contribution
    {ι : Type} (sector : Finset ι) (w u : ι → Real) :
    |sectorWeight sector w - sectorWeight sector u| ≤
      sectorL1Contribution sector w u := by
  unfold sectorWeight sectorL1Contribution
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

/-- For nonnegative weights, the sector contribution is at most the sum of
the two sector masses. -/
theorem sectorL1Contribution_le_add_sectorWeight
    {ι : Type} (sector : Finset ι) (w u : ι → Real)
    (hw : ∀ i ∈ sector, 0 ≤ w i)
    (hu : ∀ i ∈ sector, 0 ≤ u i) :
    sectorL1Contribution sector w u ≤
      sectorWeight sector w + sectorWeight sector u := by
  unfold sectorL1Contribution sectorWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_le]
  constructor <;> linarith [hw i hi, hu i hi]

/-- Uniform energy assigns a sector its fraction of the total mode count. -/
theorem sectorWeight_uniformWeights
    {ι : Type} [Fintype ι] (sector : Finset ι) :
    sectorWeight sector (uniformWeights : ι → Real) =
      (sector.card : Real) / (Fintype.card ι : Real) := by
  simp [sectorWeight, uniformWeights, div_eq_mul_inv]

/-- Exact two-sided finite-volume control used for an acoustic edge sector:

`|p(S) - |S|/M| ≤ contribution(S) ≤ p(S) + |S|/M`.
-/
theorem softSector_l1_bounds
    {ι : Type} [Fintype ι] (sector : Finset ι) (p : ι → Real)
    (hp : ∀ i ∈ sector, 0 ≤ p i) :
    |sectorWeight sector p -
        (sector.card : Real) / (Fintype.card ι : Real)| ≤
        sectorL1Contribution sector p
          (uniformWeights : ι → Real) ∧
      sectorL1Contribution sector p
          (uniformWeights : ι → Real) ≤
        sectorWeight sector p +
          (sector.card : Real) / (Fintype.card ι : Real) := by
  have huniform : ∀ i ∈ sector,
      0 ≤ (uniformWeights : ι → Real) i := by
    intro i hi
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  rw [← sectorWeight_uniformWeights sector]
  exact ⟨abs_sectorWeight_sub_le_sectorL1Contribution sector p
      (uniformWeights : ι → Real),
    sectorL1Contribution_le_add_sectorWeight sector p
      (uniformWeights : ι → Real) hp huniform⟩

/-- A sector contribution is bounded by the full all-mode `l1` distance. -/
theorem sectorL1Contribution_le_l1Distance
    {ι : Type} [Fintype ι] (sector : Finset ι) (w u : ι → Real) :
    sectorL1Contribution sector w u ≤ l1Distance w u := by
  unfold sectorL1Contribution l1Distance
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ sector)
    (fun _ _ _ ↦ abs_nonneg _)

/-- Exact soft/hard decomposition of the all-mode L1 distance. -/
theorem l1Distance_eq_sector_add_complement
    {ι : Type} [Fintype ι] [DecidableEq ι] (sector : Finset ι) (w u : ι → Real) :
    l1Distance w u =
      sectorL1Contribution sector w u +
        sectorL1Contribution (Finset.univ \ sector) w u := by
  unfold l1Distance sectorL1Contribution
  have hsubset : sector ⊆ (Finset.univ : Finset ι) :=
    Finset.subset_univ sector
  calc
    (∑ i ∈ (Finset.univ : Finset ι), |w i - u i|) =
        (∑ i ∈ Finset.univ \ sector, |w i - u i|) +
          ∑ i ∈ sector, |w i - u i| :=
      (Finset.sum_sdiff (f := fun i ↦ |w i - u i|) hsubset).symm
    _ = (∑ i ∈ sector, |w i - u i|) +
        ∑ i ∈ Finset.univ \ sector, |w i - u i| := add_comm _ _

/-- A uniform pointwise hard-sector error gives a cardinality-weighted bound. -/
theorem complementSectorL1Contribution_le_card_mul
    {ι : Type} [Fintype ι] [DecidableEq ι] (sector : Finset ι) (w u : ι → Real)
    (bound : Real)
    (hbound : ∀ i ∈ Finset.univ \ sector, |w i - u i| ≤ bound) :
    sectorL1Contribution (Finset.univ \ sector) w u ≤
      ((Finset.univ \ sector).card : Real) * bound := by
  calc
    sectorL1Contribution (Finset.univ \ sector) w u ≤
        ∑ _i ∈ Finset.univ \ sector, bound :=
      Finset.sum_le_sum hbound
    _ = ((Finset.univ \ sector).card : Real) * bound := by
      simp only [Finset.sum_const, nsmul_eq_mul]

/-- Finite-volume edge/bulk estimate. The soft sector is controlled only by
its energy and mode fraction; quantitative relaxation is needed solely on the
hard complement. -/
theorem l1Distance_uniform_le_soft_mass_add_fraction_add_hard
    {ι : Type} [Fintype ι] [DecidableEq ι] (sector : Finset ι) (p : ι → Real)
    (hp : ∀ i ∈ sector, 0 ≤ p i) :
    l1Distance p (uniformWeights : ι → Real) ≤
      sectorWeight sector p +
        (sector.card : Real) / (Fintype.card ι : Real) +
          sectorL1Contribution (Finset.univ \ sector) p
            (uniformWeights : ι → Real) := by
  rw [l1Distance_eq_sector_add_complement sector p
    (uniformWeights : ι → Real)]
  exact add_le_add_left (softSector_l1_bounds sector p hp).2 _

/-- The same edge/bulk estimate with a pointwise hard-sector error bound. -/
theorem l1Distance_uniform_le_soft_mass_add_fraction_add_card_mul
    {ι : Type} [Fintype ι] [DecidableEq ι] (sector : Finset ι) (p : ι → Real)
    (bound : Real) (hp : ∀ i ∈ sector, 0 ≤ p i)
    (hbound : ∀ i ∈ Finset.univ \ sector,
      |p i - (uniformWeights : ι → Real) i| ≤ bound) :
    l1Distance p (uniformWeights : ι → Real) ≤
      sectorWeight sector p +
        (sector.card : Real) / (Fintype.card ι : Real) +
          ((Finset.univ \ sector).card : Real) * bound := by
  have hsoft := l1Distance_uniform_le_soft_mass_add_fraction_add_hard
    sector p hp
  have hhard := complementSectorL1Contribution_le_card_mul sector p
    (uniformWeights : ι → Real) bound hbound
  linarith

end

end ArchonPhysics.SoftSectorL1Control
