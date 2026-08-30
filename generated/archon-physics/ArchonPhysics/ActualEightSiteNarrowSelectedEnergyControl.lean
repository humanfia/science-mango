import ArchonPhysics.ActualEightSiteCenterAdjugateContractionCertificate
import ArchonPhysics.ActualEightSiteNarrowEndpointPhysicalTransport
import ArchonPhysics.ActualEightSiteNarrowPathSpectrumControl

/-!
# Uniform selected-energy control on the narrow eight-site path

Exact endpoint root boxes and coordinatewise spectral monotonicity sandwich
the full physical path spectrum.  The three collision ranks `(3,5,6)` stay
within `10⁻³⁴` of the fixed rational center energies.
-/

open Set

namespace ArchonPhysics.ActualEightSiteNarrowSelectedEnergyControl

open ArchonPhysics
open ArchonPhysics.ActualEightSiteCenterAdjugateContractionCertificate
open ArchonPhysics.ActualEightSiteEndpointPhysicalTransport
open ArchonPhysics.ActualEightSiteExactDecayIVTBridge
open ArchonPhysics.ActualEightSiteNarrowBirdRootBoxes
open ArchonPhysics.ActualEightSiteNarrowEndpointPhysicalTransport
open ArchonPhysics.ActualEightSiteNarrowOrderedRootBoxes
open ArchonPhysics.ActualEightSiteNarrowPathSpectrumControl
open ArchonPhysics.ActualEightSiteNarrowProjectorMinorBridge
open ArchonPhysics.FinEightOrderedRootBoxes
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomEnsemble

noncomputable section

theorem actualEightSitePathFinDual_eq_reindexed (t : Real) :
    actualEightSitePathFinDual t = reindexedFullEightDual t := rfl

theorem orderedEigenvalue_narrowRight_le_actualEightSitePathFinDual
    {t : Real}
    (ht : t ∈ Icc actualEightSiteNarrowLower actualEightSiteNarrowUpper)
    (k : Fin 8) :
    orderedEigenvalue narrowRightHermitian k ≤
      orderedEigenvalue (actualEightSitePathFinDual t) k := by
  have htunit := actualEightSiteNarrow_mem_unit ht
  have hU : actualEightSiteNarrowUpper ∈
      Icc actualEightSiteNarrowLower actualEightSiteNarrowUpper :=
    ⟨actualEightSiteNarrowLower_lt_upper.le, le_rfl⟩
  have hUunit := actualEightSiteNarrow_mem_unit hU
  have hmono :
      orderedEigenvalue
          (actualEightSitePathFinDual actualEightSiteNarrowUpper) k ≤
        orderedEigenvalue (actualEightSitePathFinDual t) k :=
    orderedEigenvalue_actualEightSitePathFinDual_antitone
      htunit hUunit ht.2 k
  rw [actualEightSitePathFinDual_eq_reindexed,
    reindexedFullEightDual_narrowUpper_eq_narrowRightHermitian] at hmono
  exact hmono

theorem orderedEigenvalue_actualEightSitePathFinDual_le_narrowLeft
    {t : Real}
    (ht : t ∈ Icc actualEightSiteNarrowLower actualEightSiteNarrowUpper)
    (k : Fin 8) :
    orderedEigenvalue (actualEightSitePathFinDual t) k ≤
      orderedEigenvalue narrowLeftHermitian k := by
  have htunit := actualEightSiteNarrow_mem_unit ht
  have hL : actualEightSiteNarrowLower ∈
      Icc actualEightSiteNarrowLower actualEightSiteNarrowUpper :=
    ⟨le_rfl, actualEightSiteNarrowLower_lt_upper.le⟩
  have hLunit := actualEightSiteNarrow_mem_unit hL
  have hmono :
      orderedEigenvalue (actualEightSitePathFinDual t) k ≤
        orderedEigenvalue
          (actualEightSitePathFinDual actualEightSiteNarrowLower) k :=
    orderedEigenvalue_actualEightSitePathFinDual_antitone
      hLunit htunit ht.1 k
  rw [actualEightSitePathFinDual_eq_reindexed
      actualEightSiteNarrowLower,
    reindexedFullEightDual_narrowLower_eq_narrowLeftHermitian] at hmono
  exact hmono

theorem actualEightSitePathFinDual_positive_rank_mem_globalBox
    {t : Real}
    (ht : t ∈ Icc actualEightSiteNarrowLower actualEightSiteNarrowUpper)
    (k : Fin 7) :
    orderedEigenvalue (actualEightSitePathFinDual t) (Fin.castAdd 1 k) ∈
      Ioo (narrowRightLower k) (narrowLeftUpper k) := by
  have hright := narrowRight_orderedEigenvalue_mem k
  have hleft := narrowLeft_orderedEigenvalue_mem k
  exact ⟨
    hright.1.trans_le
      (orderedEigenvalue_narrowRight_le_actualEightSitePathFinDual
        ht (Fin.castAdd 1 k)),
    (orderedEigenvalue_actualEightSitePathFinDual_le_narrowLeft
      ht (Fin.castAdd 1 k)).trans_lt hleft.2⟩

theorem actualEightSiteSelectedEndpointEnergy_center_box (r : Fin 3) :
    (centerEnergy r : Real) - (1 : Real) / 10 ^ 34 <
        orderedEigenvalue narrowRightHermitian
          (actualEightSiteDecayModes r) ∧
      orderedEigenvalue narrowLeftHermitian
          (actualEightSiteDecayModes r) <
        (centerEnergy r : Real) + (1 : Real) / 10 ^ 34 := by
  fin_cases r
  · constructor
    · exact lt_trans (by
        norm_num [centerEnergy, narrowRightLower, narrowRightBoundary,
          narrowLowerBoundaryIndex, narrowRightBoundaryScaled,
          narrowRightClearing]) narrowRight_rank_three_mem.1
    · exact lt_trans narrowLeft_rank_three_mem.2 (by
        norm_num [centerEnergy, narrowLeftUpper, narrowLeftBoundary,
          narrowUpperBoundaryIndex, narrowLeftBoundaryScaled,
          narrowLeftClearing])
  · constructor
    · exact lt_trans (by
        norm_num [centerEnergy, narrowRightLower, narrowRightBoundary,
          narrowLowerBoundaryIndex, narrowRightBoundaryScaled,
          narrowRightClearing]) narrowRight_rank_five_mem.1
    · exact lt_trans narrowLeft_rank_five_mem.2 (by
        norm_num [centerEnergy, narrowLeftUpper, narrowLeftBoundary,
          narrowUpperBoundaryIndex, narrowLeftBoundaryScaled,
          narrowLeftClearing])
  · constructor
    · exact lt_trans (by
        norm_num [centerEnergy, narrowRightLower, narrowRightBoundary,
          narrowLowerBoundaryIndex, narrowRightBoundaryScaled,
          narrowRightClearing]) narrowRight_rank_six_mem.1
    · exact lt_trans narrowLeft_rank_six_mem.2 (by
        norm_num [centerEnergy, narrowLeftUpper, narrowLeftBoundary,
          narrowUpperBoundaryIndex, narrowLeftBoundaryScaled,
          narrowLeftClearing])

theorem actualEightSiteSelectedEnergy_close_center
    {t : Real}
    (ht : t ∈ Icc actualEightSiteNarrowLower actualEightSiteNarrowUpper)
    (r : Fin 3) :
    |orderedEigenvalue (actualEightSitePathFinDual t)
        (actualEightSiteDecayModes r) - (centerEnergy r : Real)| ≤
      (1 : Real) / 10 ^ 34 := by
  have hright :=
    orderedEigenvalue_narrowRight_le_actualEightSitePathFinDual ht
      (actualEightSiteDecayModes r)
  have hleft :=
    orderedEigenvalue_actualEightSitePathFinDual_le_narrowLeft ht
      (actualEightSiteDecayModes r)
  have hcenter := actualEightSiteSelectedEndpointEnergy_center_box r
  rw [abs_le]
  constructor <;> linarith

theorem actualEightSitePathFinDual_last_eq_zero
    {t : Real}
    (ht : t ∈ Icc actualEightSiteNarrowLower actualEightSiteNarrowUpper) :
    orderedEigenvalue (actualEightSitePathFinDual t) (7 : Fin 8) = 0 := by
  have hright :=
    orderedEigenvalue_narrowRight_le_actualEightSitePathFinDual
      ht (7 : Fin 8)
  have hleft :=
    orderedEigenvalue_actualEightSitePathFinDual_le_narrowLeft
      ht (7 : Fin 8)
  have hrzero : orderedEigenvalue narrowRightHermitian (7 : Fin 8) = 0 := by
    rw [narrowRight_orderedEigenvalue_eq_rootsWithZero, rootsWithZero_last]
  have hlzero : orderedEigenvalue narrowLeftHermitian (7 : Fin 8) = 0 := by
    rw [narrowLeft_orderedEigenvalue_eq_rootsWithZero, rootsWithZero_last]
  linarith

end

end ArchonPhysics.ActualEightSiteNarrowSelectedEnergyControl
