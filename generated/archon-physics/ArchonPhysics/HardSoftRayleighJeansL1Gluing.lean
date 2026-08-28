import ArchonPhysics.SoftSectorL1Control
import ArchonPhysics.ResonantThreeWaveHardFrequencyRayleighJeansEquilibrium

/-!
# Gluing hard-band Rayleigh--Jeans relaxation to full-frequency L1 relaxation

An independently normalized hard subsystem converges naturally to the
uniform distribution on its hard modes, not directly to the full-system
weight `1 / M`.  This module supplies the missing normalization estimate.
For a probability profile `p`, the full `L1` deficit is bounded by

`hard-normalized deficit + 2 * (soft mass + soft mode fraction)`.

Consequently hard-band Rayleigh--Jeans relaxation and vanishing soft mass and
cardinality glue to full-frequency normalized-energy `L1` relaxation.  This
does not place the full acoustic action `T / omega` in `L-infinity`.
-/

namespace ArchonPhysics.HardSoftRayleighJeansL1Gluing

open Filter
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.ResonantThreeWaveHardFrequencyRestriction
open ArchonPhysics.ResonantThreeWaveHardFrequencyRayleighJeansEquilibrium
open ArchonPhysics.ResonantThreeWaveKineticEquilibrium
open ArchonPhysics.SoftSectorL1Control

noncomputable section

/-- Modes below a supplied frequency cutoff. -/
def softFrequencySector {ι : Type} [Fintype ι]
    (frequency : ι → Real) (cutoff : Real) : Finset ι := by
  classical
  exact Finset.univ.filter fun i ↦ frequency i < cutoff

/-- The `L1` deficit inside a sector after renormalizing by the sector's own
mass, relative to the uniform distribution on that sector. -/
def normalizedSectorL1Deficit {ι : Type} [Fintype ι]
    (sector : Finset ι) (p : ι → Real) : Real :=
  sectorL1Contribution sector
    (fun i ↦ p i / sectorWeight sector p)
    (fun _ ↦ ((sector.card : Real))⁻¹)

theorem normalizedSectorL1Deficit_nonneg
    {ι : Type} [Fintype ι] (sector : Finset ι) (p : ι → Real) :
    0 ≤ normalizedSectorL1Deficit sector p := by
  unfold normalizedSectorL1Deficit sectorL1Contribution
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- A positive-mass, nonempty sector's contribution relative to the full
uniform target is controlled by its internally normalized deficit plus the
mismatch between its actual mass and its full-uniform target mass. -/
theorem sectorL1Contribution_uniform_le_mass_mul_normalized_add_mismatch
    {ι : Type} [Fintype ι] [Nonempty ι]
    (sector : Finset ι) (p : ι → Real)
    (hsector : sector.Nonempty)
    (hmass : 0 < sectorWeight sector p) :
    sectorL1Contribution sector p (uniformWeights : ι → Real) ≤
      sectorWeight sector p * normalizedSectorL1Deficit sector p +
        |sectorWeight sector p -
          (sector.card : Real) / (Fintype.card ι : Real)| := by
  have hsectorCard : 0 < (sector.card : Real) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr hsector)
  have htotalCard : 0 < (Fintype.card ι : Real) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hscale :
      (∑ i ∈ sector,
          |p i - sectorWeight sector p / (sector.card : Real)|) =
        sectorWeight sector p * normalizedSectorL1Deficit sector p := by
    unfold normalizedSectorL1Deficit sectorL1Contribution
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      |p i - sectorWeight sector p / (sector.card : Real)| =
          |sectorWeight sector p *
            (p i / sectorWeight sector p -
              ((sector.card : Real))⁻¹)| := by
        congr 1
        field_simp [ne_of_gt hmass, ne_of_gt hsectorCard]
      _ = |sectorWeight sector p| *
          |p i / sectorWeight sector p -
            ((sector.card : Real))⁻¹| := abs_mul _ _
      _ = sectorWeight sector p *
          |p i / sectorWeight sector p -
            ((sector.card : Real))⁻¹| := by
        rw [abs_of_pos hmass]
  have htarget :
      (∑ _i ∈ sector,
          |sectorWeight sector p / (sector.card : Real) -
            ((Fintype.card ι : Real))⁻¹|) =
        |sectorWeight sector p -
          (sector.card : Real) / (Fintype.card ι : Real)| := by
    rw [Finset.sum_const, nsmul_eq_mul]
    calc
      (sector.card : Real) *
          |sectorWeight sector p / (sector.card : Real) -
            ((Fintype.card ι : Real))⁻¹| =
          |(sector.card : Real)| *
            |sectorWeight sector p / (sector.card : Real) -
              ((Fintype.card ι : Real))⁻¹| := by
        rw [abs_of_pos hsectorCard]
      _ = |(sector.card : Real) *
          (sectorWeight sector p / (sector.card : Real) -
            ((Fintype.card ι : Real))⁻¹)| := (abs_mul _ _).symm
      _ = |sectorWeight sector p -
          (sector.card : Real) / (Fintype.card ι : Real)| := by
        congr 1
        field_simp [ne_of_gt hsectorCard, ne_of_gt htotalCard]
  unfold sectorL1Contribution
  calc
    (∑ i ∈ sector,
        |p i - (uniformWeights : ι → Real) i|) ≤
        ∑ i ∈ sector,
          (|p i - sectorWeight sector p / (sector.card : Real)| +
            |sectorWeight sector p / (sector.card : Real) -
              ((Fintype.card ι : Real))⁻¹|) := by
      apply Finset.sum_le_sum
      intro i hi
      unfold uniformWeights
      calc
        |p i - ((Fintype.card ι : Real))⁻¹| =
            |(p i - sectorWeight sector p / (sector.card : Real)) +
              (sectorWeight sector p / (sector.card : Real) -
                ((Fintype.card ι : Real))⁻¹)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    _ = (∑ i ∈ sector,
          |p i - sectorWeight sector p / (sector.card : Real)|) +
        ∑ _i ∈ sector,
          |sectorWeight sector p / (sector.card : Real) -
            ((Fintype.card ι : Real))⁻¹| := Finset.sum_add_distrib
    _ = _ := by rw [hscale, htarget]

/-- For a nonnegative probability profile, the hard-sector mass mismatch is
bounded by the soft mass plus the soft uniform target fraction. -/
theorem hardSector_mass_mismatch_le_soft_mass_add_fraction
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (soft : Finset ι) (p : ι → Real)
    (hp : ∀ i, 0 ≤ p i) (htotal : totalWeight p = 1) :
    |sectorWeight (Finset.univ \ soft) p -
        ((Finset.univ \ soft).card : Real) /
          (Fintype.card ι : Real)| ≤
      sectorWeight soft p +
        (soft.card : Real) / (Fintype.card ι : Real) := by
  have htotalCard : 0 < (Fintype.card ι : Real) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hsoftMass : 0 ≤ sectorWeight soft p := by
    unfold sectorWeight
    exact Finset.sum_nonneg fun i _ ↦ hp i
  have hsoftFraction :
      0 ≤ (soft.card : Real) / (Fintype.card ι : Real) := by positivity
  have hweightSplit :
      sectorWeight (Finset.univ \ soft) p + sectorWeight soft p = 1 := by
    rw [← htotal]
    unfold sectorWeight totalWeight
    exact Finset.sum_sdiff (Finset.subset_univ soft)
  have hcardSplit :
      ((Finset.univ \ soft).card : Real) /
          (Fintype.card ι : Real) +
        (soft.card : Real) / (Fintype.card ι : Real) = 1 := by
    rw [← add_div]
    have hcard :=
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ soft)
    rw [← Nat.cast_add, hcard, Finset.card_univ]
    exact div_self (ne_of_gt htotalCard)
  have heq :
      sectorWeight (Finset.univ \ soft) p -
          ((Finset.univ \ soft).card : Real) /
            (Fintype.card ι : Real) =
        (soft.card : Real) / (Fintype.card ι : Real) -
          sectorWeight soft p := by
    linarith
  rw [heq]
  calc
    |(soft.card : Real) / (Fintype.card ι : Real) - sectorWeight soft p| ≤
        |(soft.card : Real) / (Fintype.card ι : Real)| +
          |sectorWeight soft p| := abs_sub _ _
    _ = _ := by rw [abs_of_nonneg hsoftFraction, abs_of_nonneg hsoftMass]; ring

/-- Finite hard/soft gluing estimate with the hard subsystem normalized by
its own mass.  This is the normalization bridge absent from the basic
edge/bulk estimate. -/
theorem l1Distance_uniform_le_hardNormalized_add_two_soft
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (soft : Finset ι) (p : ι → Real)
    (hp : ∀ i, 0 ≤ p i) (htotal : totalWeight p = 1)
    (hhard : (Finset.univ \ soft).Nonempty)
    (hhardMass : 0 < sectorWeight (Finset.univ \ soft) p) :
    l1Distance p (uniformWeights : ι → Real) ≤
      normalizedSectorL1Deficit (Finset.univ \ soft) p +
        (sectorWeight soft p +
          (soft.card : Real) / (Fintype.card ι : Real)) +
        (sectorWeight soft p +
          (soft.card : Real) / (Fintype.card ι : Real)) := by
  have hsoftMass : 0 ≤ sectorWeight soft p := by
    unfold sectorWeight
    exact Finset.sum_nonneg fun i _ ↦ hp i
  have hhardMassNonneg :
      0 ≤ sectorWeight (Finset.univ \ soft) p := hhardMass.le
  have hweightSplit :
      sectorWeight (Finset.univ \ soft) p + sectorWeight soft p = 1 := by
    rw [← htotal]
    unfold sectorWeight totalWeight
    exact Finset.sum_sdiff (Finset.subset_univ soft)
  have hhardMassLeOne : sectorWeight (Finset.univ \ soft) p ≤ 1 := by
    linarith
  have hdeficitNonneg :
      0 ≤ normalizedSectorL1Deficit (Finset.univ \ soft) p :=
    normalizedSectorL1Deficit_nonneg _ _
  have hsoftContribution :
      sectorL1Contribution soft p (uniformWeights : ι → Real) ≤
        sectorWeight soft p +
          (soft.card : Real) / (Fintype.card ι : Real) :=
    (softSector_l1_bounds soft p fun i _ ↦ hp i).2
  have hhardContribution₀ :=
    sectorL1Contribution_uniform_le_mass_mul_normalized_add_mismatch
      (Finset.univ \ soft) p hhard hhardMass
  have hmassMismatch :=
    hardSector_mass_mismatch_le_soft_mass_add_fraction soft p hp htotal
  have hhardContribution :
      sectorL1Contribution (Finset.univ \ soft) p
          (uniformWeights : ι → Real) ≤
        normalizedSectorL1Deficit (Finset.univ \ soft) p +
          (sectorWeight soft p +
            (soft.card : Real) / (Fintype.card ι : Real)) := by
    calc
      _ ≤ sectorWeight (Finset.univ \ soft) p *
            normalizedSectorL1Deficit (Finset.univ \ soft) p +
          |sectorWeight (Finset.univ \ soft) p -
            ((Finset.univ \ soft).card : Real) /
              (Fintype.card ι : Real)| := hhardContribution₀
      _ ≤ normalizedSectorL1Deficit (Finset.univ \ soft) p +
          |sectorWeight (Finset.univ \ soft) p -
            ((Finset.univ \ soft).card : Real) /
              (Fintype.card ι : Real)| := by
        gcongr
        exact mul_le_of_le_one_left hdeficitNonneg hhardMassLeOne
      _ ≤ normalizedSectorL1Deficit (Finset.univ \ soft) p +
          (sectorWeight soft p +
            (soft.card : Real) / (Fintype.card ι : Real)) := by
        gcongr
  rw [l1Distance_eq_sector_add_complement soft p
    (uniformWeights : ι → Real)]
  linarith

/-- Thermodynamic hard/soft gluing: convergence to the independently
normalized hard Rayleigh--Jeans energy target, together with vanishing soft
mass and soft mode fraction, implies full normalized-energy `L1` relaxation. -/
theorem tendsto_l1Distance_uniform_of_hardNormalized_edge_bulk
    (M : Nat → Nat)
    (soft : ∀ n, Finset (Fin (M n)))
    (p : ∀ n, Fin (M n) → Real)
    (hM : ∀ n, 0 < M n)
    (hp : ∀ n i, 0 ≤ p n i)
    (htotal : ∀ n, totalWeight (p n) = 1)
    (hhard : ∀ n, (Finset.univ \ soft n).Nonempty)
    (hhardMass : ∀ n,
      0 < sectorWeight (Finset.univ \ soft n) (p n))
    (hsoft : Tendsto
      (fun n ↦ sectorWeight (soft n) (p n)) atTop (nhds 0))
    (hfraction : Tendsto
      (fun n ↦ (soft n).card / (M n : Real)) atTop (nhds 0))
    (hhardRelaxation : Tendsto
      (fun n ↦ normalizedSectorL1Deficit
        (Finset.univ \ soft n) (p n)) atTop (nhds 0)) :
    Tendsto
      (fun n ↦ l1Distance (p n)
        (uniformWeights : Fin (M n) → Real)) atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    unfold l1Distance
    exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  · intro n
    let _ : Nonempty (Fin (M n)) := Fin.pos_iff_nonempty.mp (hM n)
    simpa only [Fintype.card_fin] using
      l1Distance_uniform_le_hardNormalized_add_two_soft
        (soft n) (p n) (hp n) (htotal n) (hhard n) (hhardMass n)
  · have hsoftTotal := hsoft.add hfraction
    simpa only [zero_add] using
      (hhardRelaxation.add hsoftTotal).add hsoftTotal

/-- Concrete cutoff-scheduled form of the gluing theorem.  The hard input is
now exactly convergence of the energy profile to its own normalized
hard-band Rayleigh--Jeans target. -/
theorem tendsto_l1Distance_uniform_of_hardRJ_cutoff
    (M : Nat → Nat)
    (frequency : ∀ n, Fin (M n) → Real)
    (cutoff : Nat → Real)
    (p : ∀ n, Fin (M n) → Real)
    (hM : ∀ n, 0 < M n)
    (hp : ∀ n i, 0 ≤ p n i)
    (htotal : ∀ n, totalWeight (p n) = 1)
    (hhard : ∀ n,
      (Finset.univ \ softFrequencySector (frequency n) (cutoff n)).Nonempty)
    (hhardMass : ∀ n,
      0 < sectorWeight
        (Finset.univ \ softFrequencySector (frequency n) (cutoff n)) (p n))
    (hsoft : Tendsto
      (fun n ↦ sectorWeight
        (softFrequencySector (frequency n) (cutoff n)) (p n))
      atTop (nhds 0))
    (hfraction : Tendsto
      (fun n ↦ (softFrequencySector (frequency n) (cutoff n)).card /
        (M n : Real)) atTop (nhds 0))
    (hhardRJ : Tendsto
      (fun n ↦ normalizedSectorL1Deficit
        (Finset.univ \ softFrequencySector (frequency n) (cutoff n)) (p n))
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦ l1Distance (p n)
        (uniformWeights : Fin (M n) → Real)) atTop (nhds 0) := by
  exact tendsto_l1Distance_uniform_of_hardNormalized_edge_bulk
    M (fun n ↦ softFrequencySector (frequency n) (cutoff n)) p
    hM hp htotal hhard hhardMass hsoft hfraction hhardRJ

/-- The hard-band Rayleigh--Jeans representative has exactly zero internally
normalized modal-energy deficit on every nonempty finite hard sector. -/
theorem hardBandRayleighJeans_normalizedSectorL1Deficit_eq_zero
    {Mode : Type} [MeasurableSpace Mode] [Fintype Mode]
    (collision : ResonantThreeWaveMeasure Mode)
    {cutoff temperature : Real} (hcutoff : 0 < cutoff)
    (htemperature : 0 < temperature)
    (hard : Finset Mode) (hhard : hard.Nonempty) :
    normalizedSectorL1Deficit hard
      (fun mode ↦
        (hardFrequencyRestriction collision cutoff).frequency mode *
          rayleighJeansAction temperature
            (hardFrequencyRestriction collision cutoff).frequency mode) = 0 := by
  have henergy :
      (fun mode ↦
        (hardFrequencyRestriction collision cutoff).frequency mode *
          rayleighJeansAction temperature
            (hardFrequencyRestriction collision cutoff).frequency mode) =
        fun _ ↦ temperature := by
    funext mode
    exact frequency_mul_rayleighJeansAction
      (hardFrequencyRestriction collision cutoff) temperature cutoff hcutoff
      (cutoff_le_hardFrequencyRestriction_frequency collision cutoff) mode
  rw [henergy]
  unfold normalizedSectorL1Deficit sectorL1Contribution sectorWeight
  apply Finset.sum_eq_zero
  intro mode hmode
  rw [abs_eq_zero]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : 0 < (hard.card : Real) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr hhard)
  field_simp [ne_of_gt htemperature, ne_of_gt hcard]
  ring

end

end ArchonPhysics.HardSoftRayleighJeansL1Gluing
